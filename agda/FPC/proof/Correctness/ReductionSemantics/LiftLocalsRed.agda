{-

  Correctness of lift locals (Monμ → Impμ) by a forward simulation of
  the GlobalFunμ reduction semantics of the Monμ program (its embedding,
  ⌜_⌝ₚ) by the Impμ machine (FPC/Semantics/AbstractMachines/Imp.agda), as for
  typed lift locals (ISWIM/proof/Correctness/Reduction/LiftLocalsRed.agda).

  A machine state decodes to a term (D): its expression, in the stack of
  lets of its continuation (plug). An expression of Impμ decodes to a
  term given a term for each initialized slot (SubI, ⟦_⟧ⁱ): a read of a
  slot decodes to the slot's term, and x := e₁; e₂ to a let whose body
  sees slot x as the bound variable (ext-slot). The expression of a
  state decodes with the values of its frame (env). The decoding of a
  let's body, with the value of the let substituted, is the decoding in
  the frame where slot x holds that value (bind-dec), and a lifted
  expression decodes to the Monμ expression with the slots' terms
  substituted for its variables (⟦lift⟧).

  The source is the decoding, or one step before it (Lag): a simple
  expression that computes a value (a component, a primitive, an
  unfold) does so in the step that hands the value to the continuation,
  so a state whose expression is one decodes to its value, which the
  source reaches in one step (catch). The target also enters a let in a
  step of its own, which decodes to the same term.

  Unlike the typed pipeline's, the continuations of the Impμ machine do
  not say the type of the result, so a state decodes to a pair of a type
  (fin) and a term of that type, and the source runs on such pairs
  (redΣ, which is equivalent: pairs, FPC/proof/Framework/ReductionAll.agda).
  Nothing fails.

-}

module FPC.proof.Correctness.ReductionSemantics.LiftLocalsRed where

open import FPC.Language.Type hiding (_[_])
open import Framework.Membership using (_⊑_; here⊑; ⊑-∋; ⊑-trans)
import FPC.Language.GlobalFun as C
open C using (Tm; Code; DSig; sig; Args)
import FPC.Language.Mon as Mon
open Mon using (⌜_⌝ₚ)
open import FPC.Language.Imp
import FPC.Compiler.LiftLocals as LL
open LL using (lift; lift-body; lift-program; binds; binds-⊒; Inited;
  inited-ext)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup) renaming (map to
  All-map)
open import FPC.Semantics.Slots using (read; write; empty; params; _∷_; ∙_)
open import FPC.proof.Framework.AllProp using (lookup-map)
open import FPC.proof.Framework.SlotsProp using (params-arg; params-env)
open import Semantics.Observation
open import Framework.Smallstep Obs using (Machine; Next; next; stop; Step;
  Steps; zero; suc; ε; _◅_)
open import proof.Framework.Smallstep Obs using (plus; step⁺)
open import proof.Framework.Simulation Obs using (Answers≺; stops; steps;
  stutters; runs; Lag; lag; lag-fsim; equivalent; answers-at; equiv-trans)
open import proof.Framework.Reduction Obs o-error using (Red; val; error; to;
  step-in; toNext; reduction; Frame; frame; frame-id; frame-∘; val-in;
  step-in-to)
open import proof.Framework.ReductionVec Obs o-error using (cong₃)
open import FPC.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_;
  obsΣ; redΣ; pairs)
open import Semantics.Reduction.Smallstep using (Equivalent)
import FPC.proof.Semantics.ReductionSemantics.GlobalFun as T
open T using (Value; value-red; sub; ren; exts; tmK; tmL; _•_; ∅; _[_];
  sub-id; sub-sub; wk-[])
import FPC.Semantics.AbstractMachines.Imp as I
import FPC.Semantics.AbstractMachines.GlobalFun as C5ₘ
open I using (Val; code; pack; const; tup; inl; inr; fold; Res; value;
  call; Cont; halt; assignK; State; eval)
import Language.Prim as P

open import Data.Bool using (true; false)
open import Data.Empty.Irrelevant using (⊥-elim)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; cong₂; subst)
open import Relation.Nullary using (does)

module _ {Σ' : List DSig} where

  {- Decoding -----------------------------------------------------------------}

  {- a machine value as a value term -}
  ⌞_⌟ : ∀ {A} → Val Σ' A → Tm Σ' [] A
  ⌞_⌟ᵛ : ∀ {Δ} → All (Val Σ') Δ → All (Tm Σ' []) Δ
  ⌞ code f ⌟ = C.fun-ref f
  ⌞ pack v w ⌟ = C.pair ⌞ v ⌟ ⌞ w ⌟
  ⌞ const {B} c ⌟ = C.lit B c
  ⌞ tup vs ⌟ = C.tuple ⌞ vs ⌟ᵛ
  ⌞ inl v ⌟ = C.inl ⌞ v ⌟
  ⌞ inr v ⌟ = C.inr ⌞ v ⌟
  ⌞ fold v ⌟ = C.fold ⌞ v ⌟
  ⌞ [] ⌟ᵛ = []
  ⌞ v ∷ vs ⌟ᵛ = ⌞ v ⌟ ∷ ⌞ vs ⌟ᵛ

  value-⌞⌟ : ∀ {A} (v : Val Σ' A) → Value ⌞ v ⌟
  values-⌞⌟ : ∀ {Δ} (vs : All (Val Σ') Δ) → Each Value ⌞ vs ⌟ᵛ
  value-⌞⌟ (code f) = T.fun-ref
  value-⌞⌟ (pack v w) = T.pair (value-⌞⌟ v) (value-⌞⌟ w)
  value-⌞⌟ (const c) = T.lit
  value-⌞⌟ (tup vs) = T.tuple (values-⌞⌟ vs)
  value-⌞⌟ (inl v) = T.inl (value-⌞⌟ v)
  value-⌞⌟ (inr v) = T.inr (value-⌞⌟ v)
  value-⌞⌟ (fold v) = T.fold (value-⌞⌟ v)
  values-⌞⌟ [] = []
  values-⌞⌟ (v ∷ vs) = value-⌞⌟ v ∷ values-⌞⌟ vs

  obs-⌞⌟ : ∀ {A} (v : Val Σ' A) → T.obs ⌞ v ⌟ ≡ I.obs v
  obss-⌞⌟ : ∀ {Δ} (vs : All (Val Σ') Δ) → T.obss ⌞ vs ⌟ᵛ ≡ C5ₘ.obs-all vs
  obs-⌞⌟ (code f) = refl
  obs-⌞⌟ (pack v w) = refl
  obs-⌞⌟ (const c) = refl
  obs-⌞⌟ (tup vs) = cong o-tuple (obss-⌞⌟ vs)
  obs-⌞⌟ (inl v) = cong o-inl (obs-⌞⌟ v)
  obs-⌞⌟ (inr v) = cong o-inr (obs-⌞⌟ v)
  obs-⌞⌟ (fold v) = obs-⌞⌟ v
  obss-⌞⌟ [] = refl
  obss-⌞⌟ (v ∷ vs) = cong₂ _∷_ (obs-⌞⌟ v) (obss-⌞⌟ vs)

  {- a term for each initialized slot -}
  record SubI (Γ Δ : Ctx) (I : Inits Δ) : Set where
    constructor sb
    field
      term : ∀ {B} (x : Δ ∋ B) → .(x ∈ I) → Tm Σ' Γ B
  open SubI

  {- pointwise equal -}
  record _≗_ {Γ Δ} {I : Inits Δ} (σ σ' : SubI Γ Δ I) : Set where
    constructor pw
    field
      ≗-at : ∀ {B} (x : Δ ∋ B) .(i : x ∈ I) → term σ x i ≡ term σ' x i
  open _≗_

  {- the frame's values -}
  env : ∀ {Δ I} → I.Frame Σ' Δ I → SubI [] Δ I
  env φ = sb λ x i → ⌞ read φ x i ⌟

  {- the slots after slot 0 -}
  tl : ∀ {Γ Δ A b} {I : Inits Δ} → SubI Γ (A ∷ Δ) (b ∷ I) → SubI Γ Δ I
  tl σ = sb λ z k → term σ (S z) k

  {- slot x, written, as the variable bound last -}
  ext-slot : ∀ {Γ Δ A} {I : Inits Δ} (x : Δ ∋ A)
    → SubI Γ Δ I
    → SubI (A ∷ Γ) Δ (I ⊕ x)
  ext-slot {I = b ∷ I} Z σ =
    sb λ { Z j → C.` Z ; (S y) j → ren S (term σ (S y) j) }
  ext-slot {I = b ∷ I} (S x) σ =
    sb λ { Z j → ren S (term σ Z j) ; (S y) j → term (ext-slot x (tl σ)) y j }

  {- Impμ in GlobalFunμ, given the terms of the slots -}
  ⟦_⟧ᵃ : ∀ {Γ Δ I A} → Atm Σ' Δ I A → SubI Γ Δ I → Tm Σ' Γ A
  ⟦ var x i ⟧ᵃ σ = term σ x i
  ⟦ lit B c ⟧ᵃ σ = C.lit B c
  ⟦ ref f ⟧ᵃ σ = C.fun-ref f

  ⟦_⟧ᵛ : ∀ {Γ Δ I Δs} → All (Atm Σ' Δ I) Δs → SubI Γ Δ I
    → All (Tm Σ' Γ) Δs
  ⟦ [] ⟧ᵛ σ = []
  ⟦ a ∷ as ⟧ᵛ σ = ⟦ a ⟧ᵃ σ ∷ ⟦ as ⟧ᵛ σ

  ⟦_⟧ˢ : ∀ {Γ Δ I A} → Simple Σ' Δ I A → SubI Γ Δ I → Tm Σ' Γ A
  ⟦ atm a ⟧ˢ σ = ⟦ a ⟧ᵃ σ
  ⟦ pair a b ⟧ˢ σ = C.pair (⟦ a ⟧ᵃ σ) (⟦ b ⟧ᵃ σ)
  ⟦ callc a b ⟧ˢ σ = C.callc (⟦ a ⟧ᵃ σ) (⟦ b ⟧ᵃ σ)
  ⟦ tuple as ⟧ˢ σ = C.tuple (⟦ as ⟧ᵛ σ)
  ⟦ get i a ⟧ˢ σ = C.get i (⟦ a ⟧ᵃ σ)
  ⟦ inl a ⟧ˢ σ = C.inl (⟦ a ⟧ᵃ σ)
  ⟦ inr a ⟧ˢ σ = C.inr (⟦ a ⟧ᵃ σ)
  ⟦ prim p a b ⟧ˢ σ = C.prim p (⟦ a ⟧ᵃ σ) (⟦ b ⟧ᵃ σ)
  ⟦ fold a ⟧ˢ σ = C.fold (⟦ a ⟧ᵃ σ)
  ⟦ unfold a ⟧ˢ σ = C.unfold (⟦ a ⟧ᵃ σ)

  ⟦_⟧ⁱ : ∀ {Γ Δ I A} → Exp Σ' Δ I A → SubI Γ Δ I → Tm Σ' Γ A
  ⟦ simple s ⟧ⁱ σ = ⟦ s ⟧ˢ σ
  ⟦ assign x _ e₁ e₂ ⟧ⁱ σ = C.let′ (⟦ e₁ ⟧ⁱ σ) (⟦ e₂ ⟧ⁱ (ext-slot x σ))
  ⟦ case a x _ y _ e₁ e₂ ⟧ⁱ σ =
    C.case (⟦ a ⟧ᵃ σ) (⟦ e₁ ⟧ⁱ (ext-slot x σ)) (⟦ e₂ ⟧ⁱ (ext-slot y σ))

  {- The decoding and the terms of the slots ----------------------------------}

  ext-slot-cong : ∀ {Γ Δ A} {I : Inits Δ} (x : Δ ∋ A) {σ σ' : SubI Γ Δ I}
    → σ ≗ σ'
    → ext-slot x σ ≗ ext-slot x σ'
  ext-slot-cong {I = b ∷ I} Z h =
    pw λ { Z j → refl ; (S y) j → cong (ren S) (≗-at h (S y) j) }
  ext-slot-cong {I = b ∷ I} (S x) {σ} {σ'} h =
    pw λ { Z j → cong (ren S) (≗-at h Z j)
         ; (S y) j →
             ≗-at
               (ext-slot-cong x {tl σ} {tl σ'} (pw λ z k → ≗-at h (S z) k))
               y j }

  congᵃ : ∀ {Γ Δ I A} (a : Atm Σ' Δ I A) {σ σ' : SubI Γ Δ I}
    → σ ≗ σ'
    → ⟦ a ⟧ᵃ σ ≡ ⟦ a ⟧ᵃ σ'
  congᵃ (var x i) h = ≗-at h x i
  congᵃ (lit B c) h = refl
  congᵃ (ref f) h = refl

  congᵛ : ∀ {Γ Δ I Δs} (as : All (Atm Σ' Δ I) Δs) {σ σ' : SubI Γ Δ I}
    → σ ≗ σ'
    → ⟦ as ⟧ᵛ σ ≡ ⟦ as ⟧ᵛ σ'
  congᵛ [] h = refl
  congᵛ (a ∷ as) h = cong₂ _∷_ (congᵃ a h) (congᵛ as h)

  congˢ : ∀ {Γ Δ I A} (s : Simple Σ' Δ I A) {σ σ' : SubI Γ Δ I}
    → σ ≗ σ'
    → ⟦ s ⟧ˢ σ ≡ ⟦ s ⟧ˢ σ'
  congˢ (atm a) h = congᵃ a h
  congˢ (pair a b) h = cong₂ C.pair (congᵃ a h) (congᵃ b h)
  congˢ (callc a b) h = cong₂ C.callc (congᵃ a h) (congᵃ b h)
  congˢ (tuple as) h = cong C.tuple (congᵛ as h)
  congˢ (get i a) h = cong (C.get i) (congᵃ a h)
  congˢ (inl a) h = cong C.inl (congᵃ a h)
  congˢ (inr a) h = cong C.inr (congᵃ a h)
  congˢ (prim p a b) h = cong₂ (C.prim p) (congᵃ a h) (congᵃ b h)
  congˢ (fold a) h = cong C.fold (congᵃ a h)
  congˢ (unfold a) h = cong C.unfold (congᵃ a h)

  congⁱ : ∀ {Γ Δ I A} (e : Exp Σ' Δ I A) {σ σ' : SubI Γ Δ I}
    → σ ≗ σ'
    → ⟦ e ⟧ⁱ σ ≡ ⟦ e ⟧ⁱ σ'
  congⁱ (simple s) h = congˢ s h
  congⁱ (assign x _ e₁ e₂) h =
    cong₂ C.let′ (congⁱ e₁ h) (congⁱ e₂ (ext-slot-cong x h))
  congⁱ (case a x _ y _ e₁ e₂) h =
    cong₃ C.case (congᵃ a h) (congⁱ e₁ (ext-slot-cong x h))
      (congⁱ e₂ (ext-slot-cong y h))

  {- a substitution after the decoding, and into the terms of the slots -}
  _⨾_ : ∀ {Γ Γ' Δ} {I : Inits Δ} → SubI Γ Δ I
    → (∀ {B} → Γ ∋ B → Tm Σ' Γ' B) → SubI Γ' Δ I
  σ ⨾ τ = sb λ x i → sub τ (term σ x i)

  ext-slot-sub : ∀ {Γ Γ' Δ A} {I : Inits Δ} (x : Δ ∋ A) (σ : SubI Γ Δ I)
    (τ : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B)
    → (ext-slot x σ ⨾ exts tmK τ) ≗ ext-slot x (σ ⨾ τ)
  ext-slot-sub {I = b ∷ I} Z σ τ =
    pw λ { Z j → refl
         ; (S y) j → T.Laws.exts-ren tmL τ (term σ (S y) j) }
  ext-slot-sub {I = b ∷ I} (S x) σ τ =
    pw λ { Z j → T.Laws.exts-ren tmL τ (term σ Z j)
         ; (S y) j → ≗-at (ext-slot-sub x (tl σ) τ) y j }

  subᵃ : ∀ {Γ Γ' Δ I A} (τ : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B) (σ : SubI Γ Δ I)
    (a : Atm Σ' Δ I A)
    → sub τ (⟦ a ⟧ᵃ σ) ≡ ⟦ a ⟧ᵃ (σ ⨾ τ)
  subᵃ τ σ (var x i) = refl
  subᵃ τ σ (lit B c) = refl
  subᵃ τ σ (ref f) = refl

  subᵛ : ∀ {Γ Γ' Δ I Δs} (τ : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B) (σ : SubI Γ Δ I)
    (as : All (Atm Σ' Δ I) Δs)
    → T.travs tmK τ (⟦ as ⟧ᵛ σ) ≡ ⟦ as ⟧ᵛ (σ ⨾ τ)
  subᵛ τ σ [] = refl
  subᵛ τ σ (a ∷ as) = cong₂ _∷_ (subᵃ τ σ a) (subᵛ τ σ as)

  subˢ : ∀ {Γ Γ' Δ I A} (τ : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B) (σ : SubI Γ Δ I)
    (s : Simple Σ' Δ I A)
    → sub τ (⟦ s ⟧ˢ σ) ≡ ⟦ s ⟧ˢ (σ ⨾ τ)
  subˢ τ σ (atm a) = subᵃ τ σ a
  subˢ τ σ (pair a b) = cong₂ C.pair (subᵃ τ σ a) (subᵃ τ σ b)
  subˢ τ σ (callc a b) = cong₂ C.callc (subᵃ τ σ a) (subᵃ τ σ b)
  subˢ τ σ (tuple as) = cong C.tuple (subᵛ τ σ as)
  subˢ τ σ (get i a) = cong (C.get i) (subᵃ τ σ a)
  subˢ τ σ (inl a) = cong C.inl (subᵃ τ σ a)
  subˢ τ σ (inr a) = cong C.inr (subᵃ τ σ a)
  subˢ τ σ (prim p a b) = cong₂ (C.prim p) (subᵃ τ σ a) (subᵃ τ σ b)
  subˢ τ σ (fold a) = cong C.fold (subᵃ τ σ a)
  subˢ τ σ (unfold a) = cong C.unfold (subᵃ τ σ a)

  subⁱ : ∀ {Γ Γ' Δ I A} (τ : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B) (σ : SubI Γ Δ I)
    (e : Exp Σ' Δ I A)
    → sub τ (⟦ e ⟧ⁱ σ) ≡ ⟦ e ⟧ⁱ (σ ⨾ τ)
  subⁱ τ σ (simple s) = subˢ τ σ s
  subⁱ τ σ (assign x _ e₁ e₂) =
    cong₂ C.let′ (subⁱ τ σ e₁)
      (trans (subⁱ (exts tmK τ) (ext-slot x σ) e₂)
        (congⁱ e₂ (ext-slot-sub x σ τ)))
  subⁱ τ σ (case a x _ y _ e₁ e₂) =
    cong₃ C.case (subᵃ τ σ a)
      (trans (subⁱ (exts tmK τ) (ext-slot x σ) e₁)
        (congⁱ e₁ (ext-slot-sub x σ τ)))
      (trans (subⁱ (exts tmK τ) (ext-slot y σ) e₂)
        (congⁱ e₂ (ext-slot-sub y σ τ)))

  {- the value w for the bound variable: the frame with w in slot x -}
  ext-slot-[] : ∀ {Δ A} {I : Inits Δ} (φ : I.Frame Σ' Δ I) (x : Δ ∋ A)
    (w : Val Σ' A)
    → (ext-slot x (env φ) ⨾ (⌞ w ⌟ • ∅)) ≗ env (write φ x w)
  ext-slot-[] (u ∷ φ) Z w =
    pw λ { Z j → refl ; (S y) j → wk-[] ⌞ read φ y j ⌟ ⌞ w ⌟ }
  ext-slot-[] (∙ φ) Z w =
    pw λ { Z j → refl ; (S y) j → wk-[] ⌞ read φ y j ⌟ ⌞ w ⌟ }
  ext-slot-[] (u ∷ φ) (S x) w =
    pw λ { Z j → wk-[] ⌞ u ⌟ ⌞ w ⌟
         ; (S y) j → ≗-at (ext-slot-[] φ x w) y j }
  ext-slot-[] (∙ φ) (S x) w =
    pw λ { Z j → ⊥-elim j ; (S y) j → ≗-at (ext-slot-[] φ x w) y j }

  bind-dec : ∀ {Δ A B} {I : Inits Δ} (φ : I.Frame Σ' Δ I) (x : Δ ∋ A)
    (w : Val Σ' A) (e : Exp Σ' Δ (I ⊕ x) B)
    → ⟦ e ⟧ⁱ (ext-slot x (env φ)) [ ⌞ w ⌟ ] ≡ ⟦ e ⟧ⁱ (env (write φ x w))
  bind-dec φ x w e =
    trans (subⁱ (⌞ w ⌟ • ∅) (ext-slot x (env φ)) e)
      (congⁱ e (ext-slot-[] φ x w))

  {- The decoding of lift locals ---------------------------------------------}

  ext-slot-same : ∀ {Γ Δ A} {I : Inits Δ} (x : Δ ∋ A) (σ : SubI Γ Δ I)
    .(j : x ∈ I ⊕ x)
    → term (ext-slot x σ) x j ≡ C.` Z
  ext-slot-same {I = b ∷ I} Z σ j = refl
  ext-slot-same {I = b ∷ I} (S x) σ j = ext-slot-same x (tl σ) j

  ext-slot-other : ∀ {Γ Δ A B} {I : Inits Δ} (x : Δ ∋ A) (σ : SubI Γ Δ I)
    (y : Δ ∋ B)
    → .(yi : y ∈ I)
    → .(x ∉ I)
    → .(j : y ∈ I ⊕ x)
    → term (ext-slot x σ) y j ≡ ren S (term σ y yi)
  ext-slot-other {I = true ∷ I} Z σ Z yi xn j = ⊥-elim xn
  ext-slot-other {I = false ∷ I} Z σ Z yi xn j = ⊥-elim yi
  ext-slot-other {I = b ∷ I} Z σ (S y) yi xn j = refl
  ext-slot-other {I = b ∷ I} (S x) σ Z yi xn j = refl
  ext-slot-other {I = b ∷ I} (S x) σ (S y) yi xn j =
    ext-slot-other x (tl σ) y yi xn j

  {- substitutions that agree on every variable -}
  sub-cong : ∀ {Γ Γ' A} {τ τ' : ∀ {B} → Γ ∋ B → Tm Σ' Γ' B}
    → (∀ {B} (z : Γ ∋ B) → τ z ≡ τ' z)
    → (M : Tm Σ' Γ A)
    → sub τ M ≡ sub τ' M
  sub-cong {τ = τ} h M =
    trans (cong (sub τ) (sym (sub-id (λ _ → refl) M))) (sub-sub h M)

  {- the terms of the variables' slots ρ -}
  slots : ∀ {Γ Γ' Δ} {I : Inits Δ} (ρ : LL.Slots Γ Δ) → .(Inited ρ I)
    → SubI Γ' Δ I → ∀ {B} → Γ ∋ B → Tm Σ' Γ' B
  slots ρ ok σ z = term σ (ρ z) (ok z)

  ⟦lift⟧ᵃ : ∀ {Γ Γ' Δ A} {I : Inits Δ} (ρ : LL.Slots Γ Δ) .(ok : Inited ρ I)
    (σ : SubI Γ' Δ I) (a : Mon.Atm Σ' Γ A)
    → ⟦ LL.atom ρ ok a ⟧ᵃ σ ≡ sub (slots ρ ok σ) Mon.⌜ a ⌝ᵃ
  ⟦lift⟧ᵃ ρ ok σ (Mon.var x) = refl
  ⟦lift⟧ᵃ ρ ok σ (Mon.lit B c) = refl
  ⟦lift⟧ᵃ ρ ok σ (Mon.ref f) = refl

  ⟦lift⟧ᵛ : ∀ {Γ Γ' Δ Δs} {I : Inits Δ} (ρ : LL.Slots Γ Δ)
    .(ok : Inited ρ I) (σ : SubI Γ' Δ I) (as : All (Mon.Atm Σ' Γ) Δs)
    → ⟦ LL.atoms ρ ok as ⟧ᵛ σ ≡ T.travs tmK (slots ρ ok σ) Mon.⌜ as ⌝ᵛ
  ⟦lift⟧ᵛ ρ ok σ [] = refl
  ⟦lift⟧ᵛ ρ ok σ (a ∷ as) = cong₂ _∷_ (⟦lift⟧ᵃ ρ ok σ a) (⟦lift⟧ᵛ ρ ok σ as)

  {- the bound variable is slot x, the others are in their slots ρ -}
  bound : ∀ {Γ Γ' Δ A} {I : Inits Δ} (x : Δ ∋ A) (ρ : LL.Slots Γ Δ)
    .(ok : Inited ρ I) (σ : SubI Γ' Δ I)
    → .(x ∉ I)
    → ∀ {B} (z : (A ∷ Γ) ∋ B)
    → slots (LL.ext x ρ) (inited-ext {I = I} x ρ ok) (ext-slot x σ) z
      ≡ exts tmK (slots ρ ok σ) z
  bound x ρ ok σ xn Z = ext-slot-same x σ _
  bound x ρ ok σ xn (S z) = ext-slot-other x σ (ρ z) (ok z) xn _

  ⟦lift⟧ : ∀ {Γ Γ' Δ D A} {I : Inits Δ} (e : Mon.Exp Σ' Γ A)
    (q : binds e D ⊑ Δ) (ρ : LL.Slots Γ Δ) .(ok : Inited ρ I)
    .(o : Only (⊑-trans (binds-⊒ e D) q) I) (σ : SubI Γ' Δ I)
    → ⟦ lift e q ρ ok o ⟧ⁱ σ ≡ sub (slots ρ ok σ) Mon.⌜ e ⌝
  ⟦lift⟧ (Mon.atm a) q ρ ok o σ = ⟦lift⟧ᵃ ρ ok σ a
  ⟦lift⟧ (Mon.pair a b) q ρ ok o σ =
    cong₂ C.pair (⟦lift⟧ᵃ ρ ok σ a) (⟦lift⟧ᵃ ρ ok σ b)
  ⟦lift⟧ (Mon.callc a b) q ρ ok o σ =
    cong₂ C.callc (⟦lift⟧ᵃ ρ ok σ a) (⟦lift⟧ᵃ ρ ok σ b)
  ⟦lift⟧ (Mon.tuple as) q ρ ok o σ = cong C.tuple (⟦lift⟧ᵛ ρ ok σ as)
  ⟦lift⟧ (Mon.get i a) q ρ ok o σ = cong (C.get i) (⟦lift⟧ᵃ ρ ok σ a)
  ⟦lift⟧ (Mon.inl a) q ρ ok o σ = cong C.inl (⟦lift⟧ᵃ ρ ok σ a)
  ⟦lift⟧ (Mon.inr a) q ρ ok o σ = cong C.inr (⟦lift⟧ᵃ ρ ok σ a)
  ⟦lift⟧ (Mon.prim p a b) q ρ ok o σ =
    cong₂ (C.prim p) (⟦lift⟧ᵃ ρ ok σ a) (⟦lift⟧ᵃ ρ ok σ b)
  ⟦lift⟧ (Mon.fold a) q ρ ok o σ = cong C.fold (⟦lift⟧ᵃ ρ ok σ a)
  ⟦lift⟧ (Mon.unfold a) q ρ ok o σ = cong C.unfold (⟦lift⟧ᵃ ρ ok σ a)
  ⟦lift⟧ {I = I} (Mon.let′ e₁ e₂) q ρ ok o σ =
    cong₂ C.let′ (⟦lift⟧ e₁ q₁ ρ ok (only₁ o) σ)
      (trans
        (⟦lift⟧ e₂ q (LL.ext x ρ) (inited-ext {I = I} x ρ ok) (only₂ o)
          (ext-slot x σ))
        (sub-cong (bound x ρ ok σ (fresh o)) Mon.⌜ e₂ ⌝))
    where open LL.Let {I = I} e₁ e₂ q
  ⟦lift⟧ {I = I} (Mon.case a e₁ e₂) q ρ ok o σ =
    cong₃ C.case (⟦lift⟧ᵃ ρ ok σ a)
      (trans
        (⟦lift⟧ e₁ q₁ (LL.ext x ρ) (inited-ext {I = I} x ρ ok) (only₁ o)
          (ext-slot x σ))
        (sub-cong (bound x ρ ok σ (fresh₁ o)) Mon.⌜ e₁ ⌝))
      (trans
        (⟦lift⟧ e₂ q (LL.ext y ρ) (inited-ext {I = I} y ρ ok) (only₂ o)
          (ext-slot y σ))
        (sub-cong (bound y ρ ok σ (fresh₂ o)) Mon.⌜ e₂ ⌝))
    where open LL.Case {I = I} a e₁ e₂ q

  {- an atom, and atoms -}
  atom-⌞⌟ : ∀ {Δ I A} (φ : I.Frame Σ' Δ I) (a : Atm Σ' Δ I A)
    → ⟦ a ⟧ᵃ (env φ) ≡ ⌞ I.atom φ a ⌟
  atom-⌞⌟ φ (var x i) = refl
  atom-⌞⌟ φ (lit B c) = refl
  atom-⌞⌟ φ (ref f) = refl

  atoms-⌞⌟ : ∀ {Δ I Δ'} (φ : I.Frame Σ' Δ I) (as : All (Atm Σ' Δ I) Δ')
    → ⟦ as ⟧ᵛ (env φ) ≡ ⌞ All-map (I.atom φ) as ⌟ᵛ
  atoms-⌞⌟ φ [] = refl
  atoms-⌞⌟ φ (a ∷ as) = cong₂ _∷_ (atom-⌞⌟ φ a) (atoms-⌞⌟ φ as)

  lookup-⌞⌟ : ∀ {Δ A} (vs : All (Val Σ') Δ) (i : Δ ∋ A)
    → lookup ⌞ vs ⌟ᵛ i ≡ ⌞ lookup vs i ⌟
  lookup-⌞⌟ (v ∷ vs) Z = refl
  lookup-⌞⌟ (v ∷ vs) (S i) = lookup-⌞⌟ vs i

  out-⌞⌟ : ∀ p n m → T.out {Σ'} {[]} p n m ≡ ⌞ I.δᵀ p n m ⌟
  out-⌞⌟ P.sub n m = refl
  out-⌞⌟ P.eq n m with does (n Z.≟ m)
  ... | true = refl
  ... | false = refl

  {- The machine --------------------------------------------------------------}

  module _ (ds : All (λ s → Mon.Exp Σ' (Args s) (DSig.cod s)) Σ') {A₀}
    (e₀ : Mon.Exp Σ' [] A₀) where

    ds₁ : All (Code Σ') Σ'
    ds₁ = All-map Mon.⌜_⌝ ds

    ds₂ : All (λ s → Body Σ' (Args s) (DSig.cod s)) Σ'
    ds₂ = All-map lift-body ds

    red₁ : ∀ {A} → Tm Σ' [] A → Red (Tm Σ' [] A)
    red₁ = T.red ds₁

    {- what a simple expression does, in both -}
    data SV {Δ I} (φ : I.Frame Σ' Δ I) : ∀ {A} → Simple Σ' Δ I A → Res A
      → Set where
      val0 : ∀ {A} {s : Simple Σ' Δ I A} {v} → ⟦ s ⟧ˢ (env φ) ≡ ⌞ v ⌟
        → SV φ s (value v)
      val1 : ∀ {A} {s : Simple Σ' Δ I A} {v}
        → red₁ (⟦ s ⟧ˢ (env φ)) ≡ to ⌞ v ⌟ → SV φ s (value v)
      cal : ∀ {Δ' A B} {s : Simple Σ' Δ I B} {f : Σ' ∋ sig Δ' A B} {e w}
        → ⟦ s ⟧ˢ (env φ) ≡ C.callc (C.pair (C.fun-ref f) ⌞ e ⌟) ⌞ w ⌟
          → SV φ s (call (pack (code f) e) w)

    sv : ∀ {Δ I A} (s : Simple Σ' Δ I A) (φ : I.Frame Σ' Δ I)
      → SV φ s (I.run s φ)
    sv (atm a) φ = val0 (atom-⌞⌟ φ a)
    sv (pair a b) φ = val0 (cong₂ C.pair (atom-⌞⌟ φ a) (atom-⌞⌟ φ b))
    sv (callc a b) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | pack (code f) e | ea = cal (cong₂ C.callc ea (atom-⌞⌟ φ b))
    sv (tuple as) φ = val0 (cong C.tuple (atoms-⌞⌟ φ as))
    sv (get i a) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | tup vs | ea = val1 (trans (cong (λ X → red₁ (C.get i X)) ea)
                               (trans
                                   (val-in (value-red (T.tuple (values-⌞⌟ vs))))
                                     (cong to (lookup-⌞⌟ vs i))))
    sv (inl a) φ = val0 (cong C.inl (atom-⌞⌟ φ a))
    sv (inr a) φ = val0 (cong C.inr (atom-⌞⌟ φ a))
    sv (prim p a b) φ with I.atom φ a | atom-⌞⌟ φ a | I.atom φ b | atom-⌞⌟ φ b
    ... | const n | ea | const m | eb =
      val1
      (trans (cong₂ (λ X Y → red₁ (C.prim p X Y)) ea eb)
        (cong to (out-⌞⌟ p n m)))
    sv (fold a) φ = val0 (cong C.fold (atom-⌞⌟ φ a))
    sv (unfold a) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | fold v | ea =
      val1
      (trans (cong (λ X → red₁ (C.unfold X)) ea)
        (val-in (value-red (T.fold (value-⌞⌟ v)))))

    {- the type of the result of a continuation, and its stack of lets -}
    fin : ∀ {A} → Cont Σ' A → Type
    fin {A} halt = A
    fin (assignK x φ e κ) = fin κ

    plug : ∀ {A} (κ : Cont Σ' A) → Tm Σ' [] A → Tm Σ' [] (fin κ)
    plug halt M = M
    plug (assignK x φ e κ) M =
      plug κ (C.let′ M (⟦ e ⟧ⁱ (ext-slot x (env φ))))

    plug-frame : ∀ {A} (κ : Cont Σ' A) → Frame red₁ red₁ (plug κ)
    plug-frame halt = frame-id
    plug-frame (assignK x φ e κ) = frame-∘ (frame _ λ _ → refl) (plug-frame κ)

    TmΣ : Set
    TmΣ = Σ Type (Tm Σ' [])

    redΣ₁ : TmΣ → Red TmΣ
    redΣ₁ = redΣ T.obs red₁

    {- in the source's machine, on pairs -}
    plugΣ : ∀ {A} (κ : Cont Σ' A) → Frame red₁ redΣ₁ (λ M → fin κ , plug κ M)
    plugΣ κ = frame-∘ (plug-frame κ) (frame (λ _ → val) λ _ → refl)

    {- the decoding of a state, and its value when it is a simple expression -}
    Dsyn : State Σ' → TmΣ
    Dsyn (eval e φ κ) = fin κ , plug κ (⟦ e ⟧ⁱ (env φ))

    res-tm : ∀ {A} → Res A → Tm Σ' [] A → Tm Σ' [] A
    res-tm (value v) X = ⌞ v ⌟
    res-tm (call f w) X = X

    D : State Σ' → TmΣ
    D (eval (simple s) φ κ) =
      fin κ , plug κ (res-tm (I.run s φ) (⟦ s ⟧ˢ (env φ)))
    D s = Dsyn s

    L₁ L₂ : Machine
    L₁ = reduction (obsΣ T.obs red₁) redΣ₁ (A₀ , Mon.⌜ e₀ ⌝)
    L₂ = I.sem (program ds₂ (lift-body e₀))

    {- the source reaches the decoding in at most one step -}
    catch : ∀ s → (D s ≡ Dsyn s) ⊎ Step L₁ (Dsyn s) (D s)
    catch (eval (simple s) φ κ) with I.run s φ | sv s φ
    ... | value v | val0 e = inj₁ (cong (λ X → fin κ , plug κ X) (sym e))
    ... | value v | val1 e = inj₂ (cong (toNext _) (step-in-to (plugΣ κ) e))
    ... | call _ _ | cal e = inj₁ refl
    catch (eval (assign x _ e₁ e₂) φ κ) = inj₁ refl
    catch (eval (case a x _ y _ e₁ e₂) φ κ) = inj₁ refl

    R : TmΣ → State Σ' → Set
    R M s = M ≡ D s

    lag-of : ∀ s → Σ[ i ∈ ℕ ] Lag L₁ R i (Dsyn s) s
    lag-of s with catch s
    ... | inj₁ e = 0 , lag zero (sym e)
    ... | inj₂ st = 1 , lag (suc st zero) refl

    {- a target step before an answer -}
    pre : ∀ {i a s s'}
      → Step L₂ s s'
      → Answers≺ L₂ (Lag L₁ R) i a s'
      → Answers≺ L₂ (Lag L₁ R) i a s
    pre st (stops fin) = runs (step⁺ st) fin
    pre st (steps (plus st' σ) m) = steps (plus st (st' ◅ σ)) m
    pre st (stutters _ m) = steps (step⁺ st) m
    pre st (runs (plus st' σ) fin) = runs (plus st (st' ◅ σ)) fin

    Ans : State Σ' → Set
    Ans s = ∀ {i} → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ (D s)) s

    {- the source reaches what the target reaches -}
    to-lag : ∀ {i} M {s s'}
      → Machine.step L₁ M ≡ next (Dsyn s')
      → Step L₂ s s'
      → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ M) s
    to-lag M e st = answers-at e (steps (step⁺ st) (proj₂ (lag-of _)))

    {- a value to the continuation -}
    value-ans : ∀ {Δ I A} (s : Simple Σ' Δ I A) (φ : I.Frame Σ' Δ I)
      (κ : Cont Σ' A) (v : Val Σ' A)
      → I.run s φ ≡ value v
      → ∀ {i}
      → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ (fin κ , plug κ ⌞ v ⌟))
        (eval (simple s) φ κ)
    value-ans s φ halt v e =
      answers-at (cong (toNext _) (val-in (value-red (value-⌞⌟ v))))
        (stops
            (trans (cong (λ r → I.res ds₂ r halt) e)
              (cong stop (sym (obs-⌞⌟ v)))))
    value-ans s φ (assignK x φ' e₂ κ) v e =
      to-lag
        (fin κ , plug κ (C.let′ ⌞ v ⌟ (⟦ e₂ ⟧ⁱ (ext-slot x (env φ')))))
        (cong (toNext _) (step-in-to (plugΣ κ)
                (trans (val-in (value-red (value-⌞⌟ v)))
                    (cong to (bind-dec φ' x v e₂)))))
        (cong (λ r → I.res ds₂ r (assignK x φ' e₂ κ)) e)

    {- the body of definition f, entered with e and w -}
    call-dec : ∀ {Δ' A B} (f : Σ' ∋ sig Δ' A B) (e : Val Σ' (tup Δ'))
      (w : Val Σ' A)
      → sub (⌞ w ⌟ • ⌞ e ⌟ • ∅) (lookup ds₁ f)
        ≡ ⟦ Body.exp (lookup ds₂ f) ⟧ⁱ
            (env (params (Body.params (lookup ds₂ f)) e w))
    call-dec {Δ'} {A} {B} f e w =
      trans (cong (sub (⌞ w ⌟ • ⌞ e ⌟ • ∅)) (lookup-map Mon.⌜_⌝ ds f))
        (sym
          (trans
            (cong (λ b → ⟦ Body.exp b ⟧ⁱ (env (params (Body.params b) e w)))
              (lookup-map lift-body ds f))
            (trans
              (⟦lift⟧ d here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p)
                (env (params p e w)))
              (sub-cong
                (λ { Z → cong ⌞_⌟ (params-arg p e w _)
                   ; (S Z) → cong ⌞_⌟ (params-env p e w _) })
                Mon.⌜ d ⌝))))
      where d = lookup ds f
            p = binds-⊒ d (Args (sig Δ' A B))

    sim : ∀ {Δ I A} (e : Exp Σ' Δ I A) (φ : I.Frame Σ' Δ I) (κ : Cont Σ' A)
      → Ans (eval e φ κ)
    sim (simple s) φ κ with I.run s φ in e | sv s φ
    ... | value v | _ = value-ans s φ κ v e
    ... | call (pack (code f) e') w | cal r rewrite r =
      to-lag (fin κ , plug κ (C.callc (C.pair (C.fun-ref f) ⌞ e' ⌟) ⌞ w ⌟))
        (cong (toNext _) (step-in-to (plugΣ κ)
        (trans (val-in (value-red (T.pair T.fun-ref (value-⌞⌟ e'))))
            (trans (val-in (value-red (value-⌞⌟ w)))
          (cong to (call-dec f e' w))))))
        (cong (λ x → I.res ds₂ x κ) e)
    sim (assign x _ e₁ e₂) φ κ with catch (eval e₁ φ (assignK x φ e₂ κ))
    ... | inj₁ eq =
      pre refl
      (subst (λ X → Answers≺ L₂ (Lag L₁ R) _ (Machine.step L₁ X) _) eq
        (sim e₁ φ (assignK x φ e₂ κ)))
    ... | inj₂ st = answers-at st (steps (step⁺ refl) (lag zero refl))
    sim (case a x _ y _ e₁ e₂) φ κ with I.atom φ a in eq | atom-⌞⌟ φ a
    ... | inl w | ea rewrite ea =
      to-lag
        (fin κ
          , plug κ
          (C.case (C.inl ⌞ w ⌟) (⟦ e₁ ⟧ⁱ (ext-slot x (env φ)))
            (⟦ e₂ ⟧ⁱ (ext-slot y (env φ)))))
        (cong (toNext _) (step-in-to (plugΣ κ)
          (trans (val-in (value-red (T.inl (value-⌞⌟ w))))
              (cong to (bind-dec φ x w e₁)))))
        (cong
            (λ v →
              next
                (I.choose v (λ u → eval e₁ (write φ x u) κ)
                  (λ u → eval e₂ (write φ y u) κ))) eq)
    ... | inr w | ea rewrite ea =
      to-lag
        (fin κ
          , plug κ
          (C.case (C.inr ⌞ w ⌟) (⟦ e₁ ⟧ⁱ (ext-slot x (env φ)))
            (⟦ e₂ ⟧ⁱ (ext-slot y (env φ)))))
        (cong (toNext _) (step-in-to (plugΣ κ)
          (trans (val-in (value-red (T.inr (value-⌞⌟ w))))
              (cong to (bind-dec φ y w e₂)))))
        (cong
            (λ v →
              next
                (I.choose v (λ u → eval e₁ (write φ x u) κ)
                  (λ u → eval e₂ (write φ y u) κ))) eq)

    correct : Equivalent L₁ L₂
    correct =
      equivalent
      (lag-fsim
        (subst (λ X → Σ[ i ∈ ℕ ] Lag L₁ R i X (Machine.start L₂)) start-eq
          (lag-of (Machine.start L₂)))
        λ { {s₂ = eval e φ κ} refl → sim e φ κ })
      where p = binds-⊒ e₀ []
            start-eq : Dsyn (Machine.start L₂) ≡ (A₀ , Mon.⌜ e₀ ⌝)
            start-eq =
              cong (A₀ ,_)
                (trans
                  (⟦lift⟧ e₀ here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p)
                    (env (empty (binds e₀ []))))
                  (sub-id (λ ()) Mon.⌜ e₀ ⌝))

{- The end theorem ------------------------------------------------------------}

lift-locals-correct : ∀ {A} (P : Mon.Program A)
  → Equivalent (T.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (Mon.program ds e₀) =
  equiv-trans (pairs T.obs (T.red _) _) (correct ds e₀)
