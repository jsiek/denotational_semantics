{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compiler/LiftLocals.agda) in the graph model with errors, against the
  continuation-passing semantics of Imp (Semantics/GraphErr/ImpK.agda):

    lift-locals-correct : ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧₅

  The proof is that of the graph model
  (proof/Correctness/Graph/{LiftLocalsCommon,LiftLocalsCorrectK}.agda):
  at depth d the store agrees with the environment (Agree), the variables
  from d on are out of scope (Scope), and lift n d m run with a
  continuation that means K, given a store that agrees, means K of the
  meaning of m (lift-sem). What changes with errors:

  * K is a bind (K⟨_⟩), and it commutes with a let, which is a bind
    (letᵐ-≫=), by associativity, and with a case (𝒞ᵐ-≫=). Both need the
    continuation to use only a finite part of its argument (KOK), which
    the bodies of Clos5 do (body-continuous) and binds keep (≫=-fin).
  * Every assignment that lift makes is within the frame, so the frame
    checks (frameᵐ) never err; a variable out of scope is a slot beyond
    the frame, which errs (init), as it does in Clos5.
  * Code bodies run in frames of max(2, 2 + height) slots, which is
    2 + height.

  No precondition: the pass is correct for every monadic program.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (Results; RRs; RRs-refl; mono-≃)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (nthD-≃)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErr.Prim using (primᵐ-≃)
open import Untyped.Language.Clos5 using (program; Args)
import Untyped.Language.Clos5 as C5
open import Untyped.Language.Mon
import Untyped.Language.Imp as I
import Language.ISWIM as ISWIM
open import Untyped.Compiler.LiftLocals using (lift; height; lift-atom; lift-atoms; lift-defs; lift-program)
open import Compiler.EncloseScope using (Closed)
open import Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp)
open import Untyped.Compiler.RCO using (rco-program-mon)
open import Untyped.proof.Semantics.GraphErr.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ; ⟦⟧[]-monotone; Clos5ᵐ-con; table-con; body-mono; body-continuous)
  renaming (init to init₅)
open import Untyped.Semantics.GraphErr.ImpK
  using (Store; read; _[_↦_]; frameᵐ; 𝒜; 𝒜s; frame; Kont; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ; init)
  renaming (table to tableᴷ)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import proof.Framework.GraphModel.OpsBase using (Mono₁; Finitary)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; _≟_; _<?_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; +-suc; m≤m⊔n; m≤n⊔m; m≤m+n; m∸n≤m; ≮⇒≥; <-irrefl; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (Lift) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module Untyped.proof.Correctness.GraphErr.LiftLocalsCorrect where

{- Slots and stores ----------------------------------------------------------------}

read-at : ∀ {n σ y} → y < n → read n σ y ≡ σ y
read-at {n} {σ} {y} y<n with y <? n
... | yes _ = refl
... | no y≮n = ⊥-elim (y≮n y<n)

read-out : ∀ n σ → read n σ n ≡ init
read-out n σ with n <? n
... | yes n<n = ⊥-elim (<-irrefl refl n<n)
... | no _ = refl

upd-at : ∀ σ {X} x → (σ [ x ↦ X ]) x ≡ X
upd-at σ x with x ≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)

upd-< : ∀ {σ X y d} → y < d → (σ [ d ↦ X ]) y ≃ σ y
upd-< {σ} {X} {y} {d} y<d with y ≟ d
... | yes refl = ⊥-elim (<-irrefl refl y<d)
... | no _ = ≃-refl

slot-< : ∀ {x d} → x < d → d ∸ suc x < d
slot-< {x} {suc d} _ = s≤s (m∸n≤m d x)

checked-at : ∀ {n x D E} → x < n → frameᵐ n x D E ≃ E
checked-at {n} {x} x<n with x <? n
... | yes _ = ≃-refl
... | no x≮n = ⊥-elim (x≮n x<n)

{- the frame is large enough for what lift assigns at depth d -}
fits : ∀ {d n} k → d + suc k ≤ n → suc d + k ≤ n
fits {d} {n} k H = subst (_≤ n) (+-suc d k) H

fits-< : ∀ {d n} k → suc d + k ≤ n → d < n
fits-< {d} k H = ≤-trans (s≤s (m≤m+n d k)) H

⊔ˡ : ∀ {d n} a b → d + (a ⊔ b) ≤ n → d + a ≤ n
⊔ˡ {d} a b H = ≤-trans (+-mono-≤ (≤-refl {d}) (m≤m⊔n a b)) H

⊔ʳ : ∀ {d n} a b → d + (a ⊔ b) ≤ n → d + b ≤ n
⊔ʳ {d} a b H = ≤-trans (+-mono-≤ (≤-refl {d}) (m≤n⊔m a b)) H

{- The invariant ---------------------------------------------------------------------}

record Agree (d : ℕ) (σ : Store) (ρ : Env Value) : Set where
  constructor agree
  field at : ∀ x → x < d → σ (d ∸ suc x) ≃ ρ x
open Agree public

Scope : ℕ → Env Value → Set
Scope d ρ = ∀ x → d ≤ x → ρ x ≃ init

agree-ext : ∀ {d σ ρ X} → Agree d σ ρ → Agree (suc d) (σ [ d ↦ X ]) (X • ρ)
agree-ext {d} {σ} A = agree λ { zero _ → ≃-reflexive (upd-at σ d)
  ; (suc x) (s≤s x<d) → ≃-trans (upd-< (slot-< x<d)) (at A x x<d) }

scope-ext : ∀ {d ρ X} → Scope d ρ → Scope (suc d) (X • ρ)
scope-ext O (suc x) (s≤s d≤x) = O x d≤x

weak : ∀ {d σ ρ X} → Agree (suc d) σ (X • ρ) → Agree d σ ρ
weak A = agree λ x x<d → at A (suc x) (s≤s x<d)

agree-frame : ∀ X Y → Agree 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y = agree λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) }

scope-frame : ∀ X Y → Scope 2 (Y • X • (λ _ → init))
scope-frame X Y = λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl }

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

{- Atoms ----------------------------------------------------------------------------}

module AtomsSame {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  atom-≃ : ∀ {n d h σ ρ M} (a : Atom M) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → 𝒜 T n σ (lift-atom n d a) ≃ ⟦ M ⟧[ T' ] ρ
  atom-≃ {n} {d} {h} {σ} (var x) H O A with x <? d
  ... | yes x<d = ≃-trans (≃-reflexive (read-at (<-≤-trans (slot-< x<d) (≤-trans (m≤m+n d h) H)))) (at A x x<d)
  ... | no x≮d = ≃-trans (≃-reflexive (read-out n σ)) (≃-sym (O x (≮⇒≥ x≮d)))
  atom-≃ (lit B k) _ _ _ = ≃-refl
  atom-≃ (ref k) _ _ _ = TT k

  atoms-≃ : ∀ {n d h σ ρ k} {Ms : Args (replicate k ■)} (as : Atoms Ms) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → (Q : ∀ m → Results (𝒫 Value) (replicate m ■) → Set)
    → (∀ {m Ds Es} → RRs _ Ds Es → Q m Es → Q m Ds)
    → Q k (⟦ Ms ⟧₊[ T' ] ρ) → Q (length (lift-atoms n d as)) (𝒜s T n σ (lift-atoms n d as))
  atoms-≃ [] H O A Q resp q = q
  atoms-≃ (a ∷ as) H O A Q resp q =
    atoms-≃ as H O A (λ m Ds → Q (suc m) ⟨ _ , Ds ⟩) (λ eq → resp ⟨ up ≃-refl , eq ⟩)
      (resp ⟨ up (atom-≃ a H O A) , RRs-refl _ ⟩ q)

{- The main lemma -----------------------------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T' k)) where

  open AtomsSame TT

  Ret : ℕ → Store → Env Value → Maybe (𝒫 Value → 𝒫 Value) → Kont → Set₁
  Ret d σ ρ k κ = ∀ D σ' → Con D → Agree d σ' ρ → κ D σ' ≃ K⟨ k ⟩ D

  {- a result D that means M -}
  ret : ∀ {d σ ρ k κ} M {D} → KOK k → Con-env ρ → Ret d σ ρ k κ → Agree d σ ρ → D ≃ ⟦ M ⟧[ T' ] ρ
    → κ D σ ≃ K⟨ k ⟩ (⟦ M ⟧[ T' ] ρ)
  ret {k = k} M ok cρ κ≃ A eq = ≃-trans (κ≃ _ _ (Con-⊆ (Clos5ᵐ-con T' TC M cρ) (proj₁ eq)) A) (K-≃ k ok eq)

  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} k {κ : Kont} → KOK k → d + height m ≤ n → Scope d ρ → Agree d σ ρ
    → nonempty-env ρ → Con-env ρ → Ret d σ ρ k κ
    → ⟦ lift n d m ⟧ᴷ[ T ] n σ κ ≃ K⟨ k ⟩ (⟦ M ⟧[ T' ] ρ)
  lift-sem (atom {M} a) k ok H O A NE cρ κ≃ = ret M ok cρ κ≃ A (atom-≃ a H O A)
  lift-sem (app {As} (a ∷ b ∷ c ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.app C5.⦅ As ⦆) ok cρ κ≃ A
    (callᵐ-≃ (atom-≃ a H O A) (atom-≃ b H O A) (atom-≃ c H O A))
  lift-sem (pair {As} (a ∷ b ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.pair-op C5.⦅ As ⦆) ok cρ κ≃ A
    (pairᵐ-≃ (atom-≃ a H O A) (atom-≃ b H O A))
  lift-sem (fst {As} (a ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.fst-op C5.⦅ As ⦆) ok cρ κ≃ A (carᵐ-≃ (atom-≃ a H O A))
  lift-sem (snd {As} (a ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.snd-op C5.⦅ As ⦆) ok cρ κ≃ A (cdrᵐ-≃ (atom-≃ a H O A))
  lift-sem (tuple {k'} {Ms} as) {ρ = ρ} k ok H O A NE cρ κ≃ = ret (C5.tuple k' C5.⦅ Ms ⦆) ok cρ κ≃ A
    (atoms-≃ as H O A (λ m Ds → 𝒯ᵐ m Ds ≃ 𝒯ᵐ k' (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯ᵐ-≃ m (nthD-≃ _ _ eq)) q) ≃-refl)
  lift-sem (get {i = i} {As} (a ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.get i C5.⦅ As ⦆) ok cρ κ≃ A (projᵐ-≃ i (atom-≃ a H O A))
  lift-sem (inl {As} (a ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.inl-op C5.⦅ As ⦆) ok cρ κ≃ A (inlᵐ-≃ (atom-≃ a H O A))
  lift-sem (inr {As} (a ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.inr-op C5.⦅ As ⦆) ok cρ κ≃ A (inrᵐ-≃ (atom-≃ a H O A))
  lift-sem (prim {p} {As} (a ∷ b ∷ [])) k ok H O A NE cρ κ≃ = ret (C5.prim p C5.⦅ As ⦆) ok cρ κ≃ A
    (primᵐ-≃ p (atom-≃ a H O A) (atom-≃ b H O A))
  lift-sem (case {L} {M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} k {κ} ok H O A NE cρ κ≃ =
    ≃-trans (checked-at (fits-< _ (fits {d} _ H)))
    (≃-trans (𝒞ᵐ-≃ {F = λ X → ⟦ lift n (suc d) m₁ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₁ ⟧[ T' ] (X • ρ))}
                   {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))}
                   (atom-≃ a H O A)
                   (λ V ne cV _ → lift-sem m₁ k ok (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext A)
                                 (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con cV) cρ)
                                 (λ D σ' cD A' → κ≃ D σ' cD (weak A')))
                   (λ V ne cV _ → lift-sem m₂ k ok (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext A)
                                 (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con cV) cρ)
                                 (λ D σ' cD A' → κ≃ D σ' cD (weak A'))))
             (≃-sym (case-law k ok {F₁ = λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
                       (Clos5ᵐ-con T' TC L cρ) (body-mono T' M₁ ρ) (body-mono T' M₂ ρ))))
    where H' = fits {d} (height m₁ ⊔ height m₂) H
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} k {κ} ok H O A NE cρ κ≃ =
    ≃-trans (lift-sem m₁ (just G) okG (⊔ˡ {d} (height m₁) _ H) O A NE cρ κ₁≃)
            (≃-sym (≃-trans (K-≃ k ok (letᵐ-≫= (body-mono T' M₂ ρ) cM₁ (λ c → body-continuous T' M₂ ρ NE _ c)))
                            (let-law k ok {⟦ M₁ ⟧[ T' ] ρ} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)})))
    where
    cM₁ = Clos5ᵐ-con T' TC M₁ cρ
    H₂ = fits {d} _ (⊔ʳ (height m₁) _ H)
    G = λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))
    okG = K-ok k ok (body-mono T' M₂ ρ) (body-continuous T' M₂ ρ NE)
    κ₁≃ : Ret d σ ρ (just G) (λ D σ' → frameᵐ n d D (letᵐ ⟨ D , ⟨ (λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ) , ptt ⟩ ⟩))
    κ₁≃ D σ' cD A' = ≃-trans (checked-at (fits-< _ H₂))
      (≃-trans (letᵐ-≃ ≃-refl λ V ne cV _ → lift-sem m₂ k ok H₂ (scope-ext O) (agree-ext A')
                              (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con cV) cρ)
                              (λ D' σ'' cD' A'' → κ≃ D' σ'' cD' (weak A'')))
               (letᵐ-≫= (proj₁ okG) cD (λ c → proj₂ okG _ c)))

{- Programs ---------------------------------------------------------------------}

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᴷ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  ΛΛᵐ-≃′ λ X Y neX cX _ neY cY _ → lift-sem (table-lift ms) (table-con Ns) m nothing (up tt) ≤-refl
    (scope-frame (mem X) (mem Y)) (agree-frame (mem X) (mem Y))
    (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neX)) (E≢[]⇒nonempty-mem neY))
    (Con-• (≈⇒Con cY) (Con-• (≈⇒Con cX) (λ _ → Con-⌈⌉ ω))) (λ _ _ _ _ → ≃-refl)
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-locals-correct : ∀ (P : C5.Program) (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ
lift-locals-correct (program ds M) ⟨ ms , m ⟩ =
  lift-sem (table-lift ms) (table-con ds) m nothing (up tt) ≤-refl (λ x _ → ≃-refl) (agree λ x ())
    (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ _ _ _ → ≃-refl)

{- the compiler's programs -}
lift-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile-imp M ⟧ᴷₚ ≃ ⟦ compile-mon M ⟧ₚ
lift-correct-compile M _ = lift-locals-correct (compile-mon M) (rco-program-mon (compile M))
