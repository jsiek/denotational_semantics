{-

  Adequacy of the Scott-domain semantics of FPC for its clocked
  interpreter: if the meaning of a closed program is defined (not ⊥),
  the interpreter returns a value from some clock on.

  The proof is the textbook one (Plotkin's FPC notes; Winskel, ch. 13):
  a logical relation between the elements of 𝔻 and the interpreter's
  values, and a fundamental lemma, by induction on the term. A function
  value is related to a closure when the closure, called on related
  arguments, returns related results; at a recursive type the relation
  is defined in terms of itself, negatively, so it cannot be defined by
  recursion on types (nor on the untyped values of 𝔻). As for split
  (Mu/proof/Correctness/ScottDomains/SplitRel.agda), it is defined by
  recursion on the stages of the bilimit 𝔻 (proof/Framework/Scott/Stages.agda):
  R n s v relates an approximation s : 𝓓 n of depth n to a value v; at a
  function, the argument is at the same depth n, and the result of the
  call is too (Ev n). This is Pitts's minimal-invariant argument made
  concrete: an element is related when all of its approximations are
  (Rel), and the relation of the approximations is downward closed and
  admissible (R-mono, R-sup), and survives moving between stages (R-π,
  R-ε). An evaluation is a value that the interpreter returns from some
  clock on (_⊢_⇓_, Stable), under a propositional truncation, so that
  the relation is a proposition; the interpreter is deterministic, so a
  relation with a value is one too (Σ⇓-prop).

  The fundamental lemma (fund) has one case where a call runs: an
  application, where the closure is called on the meaning a of its
  argument, but the relation says what calls on approximations e k a
  of a give; the result of the call on a is their sup, so the call on a
  returns a related value (lim, by admissibility).

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Base using (ap₂)

open import Framework.Primitives using (Base; base-rep; Int)
open import Framework.abt.GSubst using (_•_)
open import Language.Prim using (Prim; sub; eq; int; bool) renaming (δ to δᴾ)
open import Mu.Language.Type using (Type; Ctx; _⇒_; tup; _⊹_; μ; base; out-ty; _∋_; Z; S; idx)
  renaming (unroll to unrollᵗ)
open import Mu.Language.FPC
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos; All₂)
open import Mu.Semantics.ClockedInterpreters.FPC
  renaming (Val to Value; Env to Envᵢ; const to cv; δ to δᵥ)
open import proof.Semantics.Interp.Clock using (Result; ret; _>>=_; Stable; st-now; st-bind; stable-unique)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; length; []; _∷_)
open import Data.Nat using (_+_; s≤s)
open import Naturals.Order using (≤-succ)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary using (does; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
import Data.Nat as Nat
import Data.Empty
import Data.Product as P

module Mu.proof.Adequacy.ScottDomains.LogRel
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe
  renaming (Env to Envᵈ; app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; case to caseᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (abs; letᶜ-β)
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧; ⟦_⟧s)
open import Mu.Semantics.ScottDomains.Closed pt fe pe using (ρ₀)

{- Evaluation ------------------------------------------------------------------------}

{- M returns v from some clock on -}
infix 4 _⊢_⇓_
record _⊢_⇓_ {Γ A} (γ : Envᵢ Γ) (M : Tm Γ A) (v : Value A) : 𝓤₀ ̇ where
  constructor ev
  field run : Stable (λ ck → eval ck γ M) (ret v)
open _⊢_⇓_ public

private
 ret-inj : {X : 𝓤₀ ̇ } {a b : X} → _≡_ {A = Result X} (ret a) (ret b) → a ＝ b
 ret-inj ≡-refl = refl

∥⇓∥-det : ∀ {Γ A} {γ : Envᵢ Γ} {M : Tm Γ A} {v₁ v₂} → ∥ γ ⊢ M ⇓ v₁ ∥ → ∥ γ ⊢ M ⇓ v₂ ∥ → v₁ ＝ v₂
∥⇓∥-det = ∥∥-rec₂ K-is-set (λ e₁ e₂ → ret-inj (stable-unique (run e₁) (run e₂)))

{- a value, at every clock; one step after a value -}
now : ∀ {Γ A} {γ : Envᵢ Γ} {M : Tm Γ A} {v} → (∀ ck → eval ck γ M ≡ ret v) → ∥ γ ⊢ M ⇓ v ∥
now e = ∣ ev (st-now e) ∣

then : ∀ {Γ A B} {γ : Envᵢ Γ} {M : Tm Γ A} {M' : Tm Γ B} {v w} {g : ℕ → Value A → Result (Value B)}
  → (∀ ck → eval ck γ M' ≡ (eval ck γ M >>= g ck)) → (∀ ck → g ck v ≡ ret w) → ∥ γ ⊢ M ⇓ v ∥ → ∥ γ ⊢ M' ⇓ w ∥
then {γ = γ} {M} {M'} {w = w} {g} e₁ e₂ = ∥∥-functor (λ e → ev (stable-≡ (st-bind (run e) (st-now e₂))))
 where
  stable-≡ : Stable (λ ck → eval ck γ M >>= g ck) (ret w) → Stable (λ ck → eval ck γ M') (ret w)
  stable-≡ σ = P.proj₁ σ P., (λ ck le → Eq.trans (e₁ ck) (P.proj₂ σ ck le))

{- a call of a closure whose body returns v from clock c on returns v from c + 1 on -}
st-call : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {γ : Envᵢ Δ} {w v} → (w ∷ γ) ⊢ N ⇓ v
  → Stable (λ ck → call ck (pack (code N) (tup γ)) w) (ret v)
st-call (ev σ) = succ (P.proj₁ σ) P., (λ { (succ ck) (s≤s le) → P.proj₂ σ ck le })

Evals : ∀ {Γ Δ} → Envᵢ Γ → All (Tm Γ) Δ → All Value Δ → 𝓤₀ ̇
Evals γ = All₂ (λ M v → γ ⊢ M ⇓ v)

evals-st : ∀ {Γ Δ} {γ : Envᵢ Γ} (Ms : All (Tm Γ) Δ) {vs} → Evals γ Ms vs → Stable (λ ck → evals ck γ Ms) (ret vs)
evals-st [] All₂.[] = st-now (λ _ → ≡-refl)
evals-st (M ∷ Ms) (e All₂.∷ es) = st-bind (run e) (st-bind (evals-st Ms es) (st-now (λ _ → ≡-refl)))

{- a value with an evaluation is unique -}
Σ⇓-prop : ∀ {Γ B} {γ : Envᵢ Γ} {N : Tm Γ B} (P : Value B → 𝓤₁ ̇ ) → ((v : Value B) → is-prop (P v))
  → is-prop (Σ v ꞉ Value B , ∥ γ ⊢ N ⇓ v ∥ × P v)
Σ⇓-prop {γ = γ} {N} P P-prop (v₁ , t₁ , m₁) (v₂ , t₂ , m₂) = go (∥⇓∥-det {γ = γ} {M = N} t₁ t₂) t₁ t₂ m₁ m₂
 where
  go : {v₁ v₂ : Value _} → v₁ ＝ v₂ → (t₁ : ∥ γ ⊢ N ⇓ v₁ ∥) (t₂ : ∥ γ ⊢ N ⇓ v₂ ∥) (m₁ : P v₁) (m₂ : P v₂)
     → (v₁ , t₁ , m₁) ＝ (v₂ , t₂ , m₂)
  go {v} refl t₁ t₂ m₁ m₂ = ap₂ (λ a b → v , a , b) (∥∥-is-prop t₁ t₂) (P-prop v m₁ m₂)

{- The relation, by stages ---------------------------------------------------------}

{- the tag of a value of 𝔻 related to an interpreter value -}
data Shape : Tag → {A : Type} → Value A → 𝓤₀ ̇ where
  s-con : ∀ {B} {c : base-rep B} → Shape (con B c) (cv c)
  s-tup : ∀ {Δ} {vs : All Value Δ} → Shape (tup (length Δ)) (tup vs)
  s-left : ∀ {A B} {v : Value A} → Shape left (inl {B = B} v)
  s-right : ∀ {A B} {v : Value B} → Shape right (inr {A = A} v)
  s-fun : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {γ : Envᵢ Δ} → Shape fun (pack (code N) (tup γ))
  s-fold : ∀ {t A} {v : Value (unrollᵗ A)} → Shape t v → Shape t (fold {A} v)

Shape-prop : ∀ {t A} {v : Value A} → is-prop (Shape t v)
Shape-prop s-con s-con = refl
Shape-prop s-tup s-tup = refl
Shape-prop s-left s-left = refl
Shape-prop s-right s-right = refl
Shape-prop s-fun s-fun = refl
Shape-prop (s-fold e) (s-fold e') = ap s-fold (Shape-prop e e')

{- R n s v: the approximation s of depth n is related to v; Match n u v
   and Pay n e x, the same for its unrolling u and payload x; Ev n s N γ:
   if s is defined, N in γ returns a value related to it -}
R : (n : ℕ) {A : Type} → ⟨ 𝓓 n ⟩ → Value A → 𝓤₁ ̇
Match : (n : ℕ) {A : Type} → ⟨ obj Val (𝓓 n) ⟩ → Value A → 𝓤₁ ̇
Pay : (n : ℕ) {t : Tag} {A : Type} {v : Value A} → Shape t v → ⟨ obj (Payload t) (𝓓 n) ⟩ → 𝓤₁ ̇
Tup : (n : ℕ) {Δ : Ctx} → All Value Δ → (Fin (length Δ) → ⟨ 𝓓 n ⟩) → 𝓤₁ ̇
Ev : (n : ℕ) {Γ : Ctx} {B : Type} → ⟨ 𝓓 n ⟩ → Tm Γ B → Envᵢ Γ → 𝓤₁ ̇
Res : (n : ℕ) {Γ : Ctx} {B : Type} → ⟨ obj Val (𝓓 n) ⟩ → Tm Γ B → Envᵢ Γ → 𝓤₁ ̇

R zero s v = 𝟙
R (succ n) s v = (p : is-defined s) → Match n (value s p) v

Match n (t , x) v = Σ e ꞉ Shape t v , Pay n e x

Pay n s-con x = 𝟙
Pay n (s-tup {vs = vs}) xs = Tup n vs xs
Pay n (s-left {v = v}) x = R n x v
Pay n (s-right {v = v}) x = R n x v
Pay n (s-fun {A = A} {N = N} {γ = γ}) h = (x : ⟨ 𝓓 n ⟩) (w : Value A) → R n x w → Ev n (h · x) N (w ∷ γ)
Pay n (s-fold e) x = Pay n e x

Tup n [] xs = 𝟙
Tup n (v ∷ vs) xs = R n (xs zero) v × Tup n vs (λ i → xs (suc i))

Ev zero s N γ = 𝟙
Ev (succ n) s N γ = (p : is-defined s) → Res n (value s p) N γ

Res n {B = B} u N γ = Σ v ꞉ Value B , ∥ γ ⊢ N ⇓ v ∥ × Match n u v

{- The relation is a proposition -------------------------------------------------}

R-prop : (n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Value A) → is-prop (R n s v)
Match-prop : (n : ℕ) {A : Type} (u : ⟨ obj Val (𝓓 n) ⟩) (v : Value A) → is-prop (Match n u v)
Pay-prop : (n : ℕ) {t : Tag} {A : Type} {v : Value A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 n) ⟩) → is-prop (Pay n e x)
Tup-prop : (n : ℕ) {Δ : Ctx} (vs : All Value Δ) (xs : Fin (length Δ) → ⟨ 𝓓 n ⟩) → is-prop (Tup n vs xs)
Ev-prop : (n : ℕ) {Γ : Ctx} {B : Type} (s : ⟨ 𝓓 n ⟩) (N : Tm Γ B) (γ : Envᵢ Γ) → is-prop (Ev n s N γ)

R-prop zero s v = 𝟙-is-prop
R-prop (succ n) s v = Π-is-prop fe (λ p → Match-prop n (value s p) v)

Match-prop n (t , x) v = Σ-is-prop Shape-prop (λ e → Pay-prop n e x)

Pay-prop n s-con x = 𝟙-is-prop
Pay-prop n (s-tup {vs = vs}) xs = Tup-prop n vs xs
Pay-prop n (s-left {v = v}) x = R-prop n x v
Pay-prop n (s-right {v = v}) x = R-prop n x v
Pay-prop n (s-fun {N = N} {γ = γ}) h =
  Π-is-prop fe (λ x → Π-is-prop fe (λ w → Π-is-prop fe (λ _ → Ev-prop n (h · x) N (w ∷ γ))))
Pay-prop n (s-fold e) x = Pay-prop n e x

Tup-prop n [] xs = 𝟙-is-prop
Tup-prop n (v ∷ vs) xs = ×-is-prop (R-prop n (xs zero) v) (Tup-prop n vs (λ i → xs (suc i)))

Ev-prop zero s N γ = 𝟙-is-prop
Ev-prop (succ n) s N γ = Π-is-prop fe (λ p → Σ⇓-prop {γ = γ} {N = N} (Match n (value s p)) (Match-prop n (value s p)))

{- the payload of a related value, at a given shape -}
Pay-at : ∀ {n t A} {v : Value A} {x : ⟨ obj (Payload t) (𝓓 n) ⟩} (e : Shape t v) → Match n (t , x) v → Pay n e x
Pay-at {n} {x = x} e (e' , m) = transport (λ e → Pay n e x) (Shape-prop e' e) m

{- a result related to a value that N returns -}
Res→Match : ∀ {n Γ B} {u : ⟨ obj Val (𝓓 n) ⟩} {N : Tm Γ B} {γ : Envᵢ Γ} {v} → Res n u N γ → ∥ γ ⊢ N ⇓ v ∥ → Match n u v
Res→Match {n} {u = u} {N} {γ} (v' , t' , m) t = transport (Match n u) (∥⇓∥-det {γ = γ} {M = N} t' t) m

Ev→R : ∀ {n Γ B} {s : ⟨ 𝓓 n ⟩} {N : Tm Γ B} {γ : Envᵢ Γ} {v} → Ev n s N γ → ∥ γ ⊢ N ⇓ v ∥ → R n s v
Ev→R {zero} h t = ⋆
Ev→R {succ n} {N = N} {γ} h t p = Res→Match {N = N} {γ} (h p) t

{- Downward closed in the approximation ---------------------------------------------}

R-mono : (n : ℕ) {A : Type} (s s' : ⟨ 𝓓 n ⟩) (v : Value A) → s' ⊑⟨ 𝓓 n ⟩ s → R n s v → R n s' v
Match-mono : (n : ℕ) {A : Type} (u u' : ⟨ obj Val (𝓓 n) ⟩) (v : Value A)
  → u' ⊑⟨ obj Val (𝓓 n) ⟩ u → Match n u v → Match n u' v
Pay-mono : (n : ℕ) {t : Tag} {A : Type} {v : Value A} (e : Shape t v) (x x' : ⟨ obj (Payload t) (𝓓 n) ⟩)
  → x' ⊑⟨ obj (Payload t) (𝓓 n) ⟩ x → Pay n e x → Pay n e x'
Tup-mono : (n : ℕ) {Δ : Ctx} (vs : All Value Δ) (xs xs' : Fin (length Δ) → ⟨ 𝓓 n ⟩)
  → ((i : Fin (length Δ)) → xs' i ⊑⟨ 𝓓 n ⟩ xs i) → Tup n vs xs → Tup n vs xs'
Ev-mono : (n : ℕ) {Γ : Ctx} {B : Type} (s s' : ⟨ 𝓓 n ⟩) (N : Tm Γ B) (γ : Envᵢ Γ)
  → s' ⊑⟨ 𝓓 n ⟩ s → Ev n s N γ → Ev n s' N γ

R-mono zero s s' v le h = ⋆
R-mono (succ n) s s' v (f , g) h p' = Match-mono n (value s (f p')) (value s' p') v (g p') (h (f p'))

Match-mono n (t , x) (.t , x') v (refl , le) (e , m) = e , Pay-mono n e x x' le m

Pay-mono n s-con x x' le m = ⋆
Pay-mono n (s-tup {vs = vs}) xs xs' le m = Tup-mono n vs xs xs' le m
Pay-mono n (s-left {v = v}) x x' le m = R-mono n x x' v le m
Pay-mono n (s-right {v = v}) x x' le m = R-mono n x x' v le m
Pay-mono n (s-fun {N = N} {γ = γ}) h h' le m x w r = Ev-mono n (h · x) (h' · x) N (w ∷ γ) (le x) (m x w r)
Pay-mono n (s-fold e) x x' le m = Pay-mono n e x x' le m

Tup-mono n [] xs xs' le m = ⋆
Tup-mono n (v ∷ vs) xs xs' le (r , m) =
  R-mono n (xs zero) (xs' zero) v (le zero) r , Tup-mono n vs _ _ (λ i → le (suc i)) m

Ev-mono zero s s' N γ le h = ⋆
Ev-mono (succ n) s s' N γ (f , g) h p' =
  let (v , t , m) = h (f p') in v , t , Match-mono n (value s (f p')) (value s' p') v (g p') m

{- Admissible: closed under directed sups of the approximation ------------------------}

R-sup : (n : ℕ) {A : Type} (v : Value A) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩) (δ : is-Directed (𝓓 n) α)
  → ((i : I) → R n (α i) v) → R n (∐ (𝓓 n) {I} {α} δ) v
Match-sup : (n : ℕ) {A : Type} (v : Value A) {K : 𝓤₀ ̇ } (β : K → ⟨ obj Val (𝓓 n) ⟩)
  (ε : is-Directed (obj Val (𝓓 n)) β) → ((k : K) → Match n (β k) v) → Match n (∐ (obj Val (𝓓 n)) {K} {β} ε) v
Pay-sup : (n : ℕ) {t : Tag} {A : Type} {v : Value A} (e : Shape t v) {I : 𝓤₀ ̇ }
  (β : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (δ : is-Directed (obj (Payload t) (𝓓 n)) β)
  → ((i : I) → Pay n e (β i)) → Pay n e (∐ (obj (Payload t) (𝓓 n)) {I} {β} δ)
Tup-sup : (n : ℕ) {Δ : Ctx} (vs : All Value Δ) {I : 𝓤₀ ̇ } (β : I → Fin (length Δ) → ⟨ 𝓓 n ⟩)
  (δs : (i : Fin (length Δ)) → is-Directed (𝓓 n) (λ j → β j i))
  → ((j : I) → Tup n vs (β j)) → Tup n vs (λ i → ∐ (𝓓 n) (δs i))
Ev-sup : (n : ℕ) {Γ : Ctx} {B : Type} (N : Tm Γ B) (γ : Envᵢ Γ) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩)
  (δ : is-Directed (𝓓 n) α) → ((i : I) → Ev n (α i) N γ) → Ev n (∐ (𝓓 n) {I} {α} δ) N γ
Res-sup : (n : ℕ) {Γ : Ctx} {B : Type} (N : Tm Γ B) (γ : Envᵢ Γ) {K : 𝓤₀ ̇ } (β : K → ⟨ obj Val (𝓓 n) ⟩)
  (ε : is-Directed (obj Val (𝓓 n)) β) → ((k : K) → Res n (β k) N γ) → Res n (∐ (obj Val (𝓓 n)) {K} {β} ε) N γ

R-sup zero v α δ h = ⋆
R-sup (succ n) v α δ h = stage-sup-ind n α δ (λ u → Match n u v) (Match-sup n v) h

Match-sup n v β ε h =
  Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n)) (λ t x → Match n (t , x) v) Q-sup β ε h
 where
  Q-sup : (t : Tag) {I : 𝓤₀ ̇ } (β' : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (δ : is-Directed (obj (Payload t) (𝓓 n)) β')
    → ((i : I) → Match n (t , β' i) v) → Match n (t , ∐ (obj (Payload t) (𝓓 n)) {I} {β'} δ) v
  Q-sup t β' δ h' =
    ∥∥-rec (Match-prop n _ v)
      (λ i → pr₁ (h' i) , Pay-sup n (pr₁ (h' i)) β' δ (λ j → Pay-at (pr₁ (h' i)) (h' j)))
      (inhabited-if-Directed (obj (Payload t) (𝓓 n)) β' δ)

Pay-sup n s-con β δ h = ⋆
Pay-sup n (s-tup {vs = vs}) β δ h = Tup-sup n vs β (component-is-directed (Fin _) (𝓓 n) β δ) h
Pay-sup n (s-left {v = v}) β δ h = R-sup n v β δ h
Pay-sup n (s-right {v = v}) β δ h = R-sup n v β δ h
Pay-sup n (s-fun {N = N} {γ = γ}) β δ h x w r =
  Ev-sup n N (w ∷ γ) (λ j → β j · x) (pointwise-directed (𝓓 n) (𝓓 n) β δ x) (λ j → h j x w r)
Pay-sup n (s-fold e) β δ h = Pay-sup n e β δ h

Tup-sup n [] β δs h = ⋆
Tup-sup n (v ∷ vs) β δs h =
  R-sup n v (λ j → β j zero) (δs zero) (λ j → pr₁ (h j)) ,
  Tup-sup n vs (λ j i → β j (suc i)) (λ i → δs (suc i)) (λ j → pr₂ (h j))

Ev-sup zero N γ α δ h = ⋆
Ev-sup (succ n) N γ α δ h = stage-sup-ind n α δ (λ u → Res n u N γ) (Res-sup n N γ) h

Res-sup n N γ {K} β ε h =
  ∥∥-rec (Σ⇓-prop {γ = γ} {N = N} (Match n u) (Match-prop n u)) go (inhabited-if-Directed (obj Val (𝓓 n)) β ε)
 where
  u = ∐ (obj Val (𝓓 n)) {K} {β} ε
  go : K → Res n u N γ
  go k₀ = let (v , t , _) = h k₀ in v , t , Match-sup n v β ε (λ k → Res→Match {N = N} {γ} (h k) t)

{- Moving between stages ---------------------------------------------------------------}

R-π : (n : ℕ) {A : Type} (s : ⟨ 𝓓 (succ n) ⟩) (v : Value A) → R (succ n) s v → R n (π n s) v
R-ε : (n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Value A) → R n s v → R (succ n) (ε n s) v
Pay-π : (n : ℕ) {t : Tag} {A : Type} {v : Value A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 (succ n)) ⟩)
  → Pay (succ n) e x → Pay n e (fmap (Payload t) (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) x)
Pay-ε : (n : ℕ) {t : Tag} {A : Type} {v : Value A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 n) ⟩)
  → Pay n e x → Pay (succ n) e (fmap (Payload t) (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) x)
Tup-π : (n : ℕ) {Δ : Ctx} (vs : All Value Δ) (xs : Fin (length Δ) → ⟨ 𝓓 (succ n) ⟩)
  → Tup (succ n) vs xs → Tup n vs (λ i → π n (xs i))
Tup-ε : (n : ℕ) {Δ : Ctx} (vs : All Value Δ) (xs : Fin (length Δ) → ⟨ 𝓓 n ⟩)
  → Tup n vs xs → Tup (succ n) vs (λ i → ε n (xs i))
Ev-π : (n : ℕ) {Γ : Ctx} {B : Type} (s : ⟨ 𝓓 (succ n) ⟩) (N : Tm Γ B) (γ : Envᵢ Γ)
  → Ev (succ n) s N γ → Ev n (π n s) N γ
Ev-ε : (n : ℕ) {Γ : Ctx} {B : Type} (s : ⟨ 𝓓 n ⟩) (N : Tm Γ B) (γ : Envᵢ Γ)
  → Ev n s N γ → Ev (succ n) (ε n s) N γ

R-π zero s v h = ⋆
R-π (succ n) s v h = transport (λ - → R (succ n) - v) (π-succ n s ⁻¹) (λ p →
  pr₁ (h p) , Pay-π n (pr₁ (h p)) (pr₂ (value s p)) (pr₂ (h p)))

R-ε zero s v h p = 𝟘-elim (ε-zero-undefined s p)
R-ε (succ n) s v h = transport (λ - → R (succ (succ n)) - v) (ε-succ n s ⁻¹) (λ p →
  pr₁ (h p) , Pay-ε n (pr₁ (h p)) (pr₂ (value s p)) (pr₂ (h p)))

Pay-π n s-con x m = ⋆
Pay-π n (s-tup {vs = vs}) xs m = Tup-π n vs xs m
Pay-π n (s-left {v = v}) x m = R-π n x v m
Pay-π n (s-right {v = v}) x m = R-π n x v m
Pay-π n (s-fun {N = N} {γ = γ}) h m y w r = Ev-π n (h · ε n y) N (w ∷ γ) (m (ε n y) w (R-ε n y w r))
Pay-π n (s-fold e) x m = Pay-π n e x m

Pay-ε n s-con x m = ⋆
Pay-ε n (s-tup {vs = vs}) xs m = Tup-ε n vs xs m
Pay-ε n (s-left {v = v}) x m = R-ε n x v m
Pay-ε n (s-right {v = v}) x m = R-ε n x v m
Pay-ε n (s-fun {N = N} {γ = γ}) h m y w r = Ev-ε n (h · π n y) N (w ∷ γ) (m (π n y) w (R-π n y w r))
Pay-ε n (s-fold e) x m = Pay-ε n e x m

Tup-π n [] xs m = ⋆
Tup-π n (v ∷ vs) xs (r , m) = R-π n (xs zero) v r , Tup-π n vs (λ i → xs (suc i)) m

Tup-ε n [] xs m = ⋆
Tup-ε n (v ∷ vs) xs (r , m) = R-ε n (xs zero) v r , Tup-ε n vs (λ i → xs (suc i)) m

Ev-π zero s N γ h = ⋆
Ev-π (succ n) s N γ h = transport (λ - → Ev (succ n) - N γ) (π-succ n s ⁻¹) (λ p →
  let (v , t , e , m) = h p in v , t , e , Pay-π n e (pr₂ (value s p)) m)

Ev-ε zero s N γ h p = 𝟘-elim (ε-zero-undefined s p)
Ev-ε (succ n) s N γ h = transport (λ - → Ev (succ (succ n)) - N γ) (ε-succ n s ⁻¹) (λ p →
  let (v , t , e , m) = h p in v , t , e , Pay-ε n e (pr₂ (value s p)) m)

R-πs : (k n : ℕ) {A : Type} (s : ⟨ 𝓓 (k + n) ⟩) (v : Value A) → R (k + n) s v → R n (πs k n s) v
R-πs zero n s v h = h
R-πs (succ k) n s v h = R-πs k n (π (k + n) s) v (R-π (k + n) s v h)

R-εs : (k n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Value A) → R n s v → R (k + n) (εs k n s) v
R-εs zero n s v h = h
R-εs (succ k) n s v h = R-ε (k + n) (εs k n s) v (R-εs k n s v h)

{- The relation between elements of 𝔻 and values: every approximation is related -------}

record Rel {A : Type} (d : ⟨ 𝔻 ⟩) (v : Value A) : 𝓤₁ ̇ where
  constructor rel
  field stage : (n : ℕ) → R n (π∞ n · d) v
open Rel public

Rel-prop : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Value A} → is-prop (Rel d v)
Rel-prop {d = d} {v} (rel f) (rel g) = ap rel (dfunext fe (λ n → R-prop n (π∞ n · d) v (f n) (g n)))

{- an approximation related at its stage is related -}
Rel-ε : ∀ {A} (n : ℕ) {s : ⟨ 𝓓 n ⟩} {v : Value A} → R n s v → Rel (ε∞ n · s) v
Rel-ε n {s} {v} h = rel λ m → go m (split m n)
 where
  down : (m k n : ℕ) → n ＝ k + m → (s : ⟨ 𝓓 n ⟩) → R n s v → R m (π∞ m · (ε∞ n · s)) v
  down m k .(k + m) refl s h = transport (λ - → R m - v) (π∞-ε∞-down k m s ⁻¹) (R-πs k m s v h)
  up : (k m : ℕ) → m ＝ k + n → R m (π∞ m · (ε∞ n · s)) v
  up k .(k + n) refl = transport (λ - → R (k + n) - v) (π∞-ε∞-up k n s ⁻¹) (R-εs k n s v h)
  go : (m : ℕ) → Split m n → R m (π∞ m · (ε∞ n · s)) v
  go m (lower k e) = down m k n e s h
  go m (higher k e) = up k m e

{- the approximation of depth n of a payload -}
approx : (n : ℕ) (t : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t) (𝓓 n) ⟩
approx n t x = fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x

{- a value made with a tag, with related payloads at every depth -}
Rel-inj : ∀ {t A} {v : Value A} (x : ⟨ obj (Payload t) 𝔻 ⟩) (e : Shape t v)
  → ((n : ℕ) → Pay n e (approx n t x)) → Rel (inj t · x) v
Rel-inj {t} {v = v} x e h = rel λ
  { zero → ⋆
  ; (succ n) → transport (λ - → R (succ n) - v) (π∞-inj n t x ⁻¹) (λ _ → e , h n) }

{- and conversely: a defined element related to v is made with a tag of
   the shape of v, with related payloads at every depth -}
Inv : ∀ {A} → ⟨ 𝔻 ⟩ → Value A → 𝓤₁ ̇
Inv {A} d v = Σ t ꞉ Tag , Σ x ꞉ ⟨ obj (Payload t) 𝔻 ⟩ , (d ＝ inj t · x) × (Σ e ꞉ Shape t v , ((n : ℕ) → Pay n e (approx n t x)))

Rel-inv : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Value A} → Rel d v → defined d → Inv d v
Rel-inv {d = d} {v} r q = t , x , inj-view d q , pr₁ (V 0) , (λ n → Pay-at (pr₁ (V 0)) (V n))
 where
  t = pr₁ (view d q)
  x = pr₂ (view d q)
  V : (n : ℕ) → Match n (t , approx n t x) v
  V n = transport (λ - → R (succ n) - v) (π∞-inj n t x)
          (stage (transport (λ - → Rel - v) (inj-view d q) r) (succ n)) ⋆

Rel-fold : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Value (unrollᵗ A)} → Rel d v → Rel d (fold {A} v)
Rel-fold r = rel λ { zero → ⋆ ; (succ n) p → s-fold (pr₁ (stage r (succ n) p)) , pr₂ (stage r (succ n) p) }

private
 unfold-Match : ∀ {n A} {u : ⟨ obj Val (𝓓 n) ⟩} {v : Value (unrollᵗ A)} → Match n u (fold {A} v) → Match n u v
 unfold-Match (s-fold e , m) = e , m

Rel-unfold : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Value (unrollᵗ A)} → Rel d (fold {A} v) → Rel d v
Rel-unfold r = rel λ { zero → ⋆ ; (succ n) p → unfold-Match (stage r (succ n) p) }

{- Related results -------------------------------------------------------------------}

{- if d is defined, N in γ returns a value related to d -}
RelE : ∀ {Γ A} → ⟨ 𝔻 ⟩ → Tm Γ A → Envᵢ Γ → 𝓤₁ ̇
RelE {A = A} d N γ = defined d → Σ v ꞉ Value A , ∥ γ ⊢ N ⇓ v ∥ × Rel d v

RelE-＝ : ∀ {Γ A} {d d' : ⟨ 𝔻 ⟩} {N : Tm Γ A} {γ : Envᵢ Γ} → d ＝ d' → RelE d' N γ → RelE d N γ
RelE-＝ refl h = h

RelE-strict : ∀ {Γ A} {N : Tm Γ A} {γ : Envᵢ Γ} (g : DCPO[ 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩)
  → (defined d → RelE (g · d) N γ) → RelE (strict · g · d) N γ
RelE-strict {N = N} {γ} g d h q = RelE-＝ {N = N} {γ = γ} (strict-defined g d q') (h q') q
 where
  q' = seq-defined-l d (g · d) q

Ev-from-RelE : ∀ {Γ A} {d : ⟨ 𝔻 ⟩} {N : Tm Γ A} {γ : Envᵢ Γ} → RelE d N γ → (n : ℕ) → Ev n (π∞ n · d) N γ
Ev-from-RelE h zero = ⋆
Ev-from-RelE {d = d} h (succ n) p = let (v , t , r) = h (π∞-defined n d p) in v , t , stage r (succ n) p

{- a call on a: the results on its approximations e k a, related at depth
   k, give a result related to the call on a, their sup -}
lim : ∀ {Γ B} {N : Tm Γ B} {γ : Envᵢ Γ} (f : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩)
  → ((k : ℕ) → Ev k (π∞ k · (f · e k a)) N γ) → RelE (f · a) N γ
lim {B = B} {N} {γ} f a h q = ∥∥-rec (Σ⇓-prop {γ = γ} {N = N} (Rel (f · a)) (λ v → Rel-prop)) found some
 where
  g : (n : ℕ) → DCPO[ 𝔻 , 𝓓 n ]
  g n = ∘₁ 𝔻 𝔻 (𝓓 n) f (π∞ n)
  δ : (n : ℕ) → is-Directed (𝓓 n) (λ k → g n · e k a)
  δ n = image-is-directed' 𝔻 (𝓓 n) (g n) {ℕ} {λ k → e k a} (e-directed a)
  sup : (n : ℕ) → π∞ n · (f · a) ＝ ∐ (𝓓 n) (δ n)
  sup n = approx-∐ (𝓓 n) (g n) a
  some : ∥ Σ k ꞉ ℕ , defined (f · e k a) ∥
  some = ∥∥-functor (λ (k , p) → k , π∞-defined 0 (f · e k a) p)
           (stage-sup-defined 0 (λ k → g 1 · e k a) (δ 1)
              (transport is-defined (sup 1) (defined-π∞ 0 (f · a) q)))
  found : (Σ k ꞉ ℕ , defined (f · e k a)) → Σ v ꞉ Value B , ∥ γ ⊢ N ⇓ v ∥ × Rel (f · a) v
  found (k , qk) = v , t , rel stages
   where
    qK : defined (f · e (succ k) a)
    qK = defined-mono _ _ (monotone-if-continuous 𝔻 𝔻 f _ _ (e-mono a k (succ k) (≤-succ k))) qk
    v = pr₁ (h (succ k) (defined-π∞ k _ qK))
    t = pr₁ (pr₂ (h (succ k) (defined-π∞ k _ qK)))
    below : (n k : ℕ) → R n (π∞ n · (f · e k a)) v
    below n k = R-mono n (π∞ n · (f · e (k + n) a)) (π∞ n · (f · e k a)) v
                  (monotone-if-continuous 𝔻 (𝓓 n) (g n) _ _ (e-mono a k (k + n) (≤+ k n)))
                  (transport (λ - → R n - v) (πs-π∞ k n (f · e (k + n) a))
                     (R-πs k n _ v (Ev→R {N = N} {γ} (h (k + n)) t)))
    stages : (n : ℕ) → R n (π∞ n · (f · a)) v
    stages n = transport (λ - → R n - v) (sup n ⁻¹) (R-sup n v (λ k → g n · e k a) (δ n) (below n))

{- The fundamental lemma ----------------------------------------------------------------}

{- related environments -}
G : ∀ {Γ} → ⟨ Envᵈ ⟩ → Envᵢ Γ → 𝓤₁ ̇
G {Γ} ρ γ = ∀ {A} (x : Γ ∋ A) → Rel (ρ (idx x)) (lookup γ x)

G-ext : ∀ {Γ A} {ρ : ⟨ Envᵈ ⟩} {γ : Envᵢ Γ} {d : ⟨ 𝔻 ⟩} {v : Value A} → G ρ γ → Rel d v → G (d • ρ) (v ∷ γ)
G-ext g r Z = r
G-ext g r (S x) = g x

{- a component of a tuple -}
Tup-lookup : ∀ {n Δ A} (vs : All Value Δ) (xs : Fin (length Δ) → ⟨ 𝓓 n ⟩) (i : Δ ∋ A)
  → Tup n vs xs → R n (xs (pos i)) (lookup vs i)
Tup-lookup (v ∷ vs) xs Z (r , _) = r
Tup-lookup (v ∷ vs) xs (S i) (_ , m) = Tup-lookup vs (λ j → xs (suc j)) i m

proj-inj : (k : ℕ) (xs : Fin k → ⟨ 𝔻 ⟩) (i : Fin k) → proj i · (inj (tup k) · xs) ＝ xs i
proj-inj k xs i = case-inj 𝔻⊥ (proj-br i) (tup k) xs ∙ at-k (k Nat.≟ k)
 where
  at-k : (q : Dec (k Eq.≡ k)) → at-tup k k i q · xs ＝ xs i
  at-k (yes Eq.refl) = refl
  at-k (no ¬q) = Data.Empty.⊥-elim (¬q Eq.refl)

Rel-unit : Rel unit (tup [])
Rel-unit = Rel-inj _ s-tup (λ n → ⋆)

{- the injections, unfolded -}
inl-is : (a : ⟨ 𝔻 ⟩) → inlᵈ · a ＝ seq · a · (inj left · a)
inl-is a = refl

inr-is : (a : ⟨ 𝔻 ⟩) → inrᵈ · a ＝ seq · a · (inj right · a)
inr-is a = refl

{- the results of the primitives -}
Rel-out : ∀ p n m → Rel (out (δᴾ p n m)) (δᵥ p (cv n) (cv m))
Rel-out sub n m = Rel-inj ⋆ s-con (λ _ → ⋆)
Rel-out eq n m = Rel-bool (does (n ≟ℤ m))
 where
  Rel-bool : (b : Bool) → Rel {out-ty eq} (out (bool b)) (if b then inl (tup []) else inr (tup []))
  Rel-bool true = transport (λ - → Rel - (inl (tup []))) ((inl-is unit ∙ seq-defined unit (inj left · unit) unit-defined) ⁻¹)
                    (Rel-inj unit s-left (stage Rel-unit))
  Rel-bool false = transport (λ - → Rel - (inr (tup []))) ((inr-is unit ∙ seq-defined unit (inj right · unit) unit-defined) ⁻¹)
                     (Rel-inj unit s-right (stage Rel-unit))

{- a function value, applied -}
app-inj : (h : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩) → appᵈ · (inj fun · h) · a ＝ strict · h · a
app-inj h a = ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br fun h)

strict-is : (h : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩) → strict · h · a ＝ seq · a · (h · a)
strict-is h a = refl

{- what a term returns, with a value related to d -}
Out : ∀ {Γ A} → ⟨ 𝔻 ⟩ → Tm Γ A → Envᵢ Γ → 𝓤₁ ̇
Out {A = A} d M γ = Σ v ꞉ Value A , ∥ γ ⊢ M ⇓ v ∥ × Rel d v

{- an application: the operator returns a closure, related to a function
   value f = inj fun h; the call on the argument's value runs the body -}
fund-app : ∀ {Γ A B} {γ : Envᵢ Γ} (L : Tm Γ (A ⇒ B)) (M : Tm Γ A) (f a : ⟨ 𝔻 ⟩)
  → Out f L γ → RelE a M γ → RelE (appᵈ · f · a) (app L M) γ
fund-app {γ = γ} L M f a (pack (code N) (tup γ') , tL , rL) hM q = body (Rel-inv rL (app-defined f a q))
 where
  body : Inv f (pack (code N) (tup γ')) → Out (appᵈ · f · a) (app L M) γ
  body (_ , h , eqf , s-fun , mL) =
    v , ∥∥-functor₃ (λ eL eM eN → ev (st-bind (run eL) (st-bind (run eM) (st-call eN)))) tL tM tN ,
    transport (λ - → Rel - v) (eqA ⁻¹) rN
   where
    eq₁ : appᵈ · f · a ＝ strict · h · a
    eq₁ = ap (λ - → appᵈ · - · a) eqf ∙ app-inj h a
    q' : defined (seq · a · (h · a))
    q' = transport defined (eq₁ ∙ strict-is h a) q
    qa : defined a
    qa = seq-defined-l a (h · a) q'
    eqA : appᵈ · f · a ＝ h · a
    eqA = eq₁ ∙ strict-defined h a qa
    vM = pr₁ (hM qa)
    tM = pr₁ (pr₂ (hM qa))
    rM = pr₂ (pr₂ (hM qa))
    resN : Out (h · a) N (vM ∷ γ')
    resN = lim {N = N} {γ = vM ∷ γ'} h a (λ k → mL k (π∞ k · a) vM (stage rM k)) (seq-defined-r a (h · a) q')
    v = pr₁ resN
    tN = pr₁ (pr₂ resN)
    rN = pr₂ (pr₂ resN)

{- a let: the body runs in the environment extended with the value of M -}
fund-let : ∀ {Γ A B} {ρ : ⟨ Envᵈ ⟩} {γ : Envᵢ Γ} (M : Tm Γ A) (N : Tm (A ∷ Γ) B)
  → RelE (⟦ M ⟧ · ρ) M γ → (∀ {d v} → Rel d v → RelE (⟦ N ⟧ · (d • ρ)) N (v ∷ γ))
  → RelE (⟦ let′ M N ⟧ · ρ) (let′ M N) γ
fund-let {ρ = ρ} {γ} M N hM hN q =
  v , ∥∥-functor₂ (λ eM eN → ev (st-bind (run eM) (run eN))) tM tN ,
  transport (λ - → Rel - v) ((eq₀ ∙ seq-defined a (⟦ N ⟧ · (a • ρ)) qa) ⁻¹) rN
 where
  a : ⟨ 𝔻 ⟩
  a = ⟦ M ⟧ · ρ
  eq₀ : ⟦ let′ M N ⟧ · ρ ＝ seq · a · (⟦ N ⟧ · (a • ρ))
  eq₀ = letᶜ-β ⟦ M ⟧ ⟦ N ⟧ ρ
  q' : defined (seq · a · (⟦ N ⟧ · (a • ρ)))
  q' = transport defined eq₀ q
  qa : defined a
  qa = seq-defined-l a (⟦ N ⟧ · (a • ρ)) q'
  vM = pr₁ (hM qa)
  tM = pr₁ (pr₂ (hM qa))
  rM = pr₂ (pr₂ (hM qa))
  resN : Out (⟦ N ⟧ · (a • ρ)) N (vM ∷ γ)
  resN = hN rM (seq-defined-r a (⟦ N ⟧ · (a • ρ)) q')
  v = pr₁ resN
  tN = pr₁ (pr₂ resN)
  rN = pr₂ (pr₂ resN)

fund : ∀ {Γ A} (M : Tm Γ A) {ρ : ⟨ Envᵈ ⟩} {γ : Envᵢ Γ} → G ρ γ → RelE (⟦ M ⟧ · ρ) M γ
funds : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ : ⟨ Envᵈ ⟩} {γ : Envᵢ Γ} → G ρ γ
  → ((i : Fin (length Δ)) → defined ((⟦ Ms ⟧s · ρ) i))
  → Σ vs ꞉ All Value Δ , ∥ Evals γ Ms vs ∥ × ((n : ℕ) → Tup n vs (λ i → π∞ n · (⟦ Ms ⟧s · ρ) i))

fund (` x) {ρ} {γ} g q = lookup γ x , now {γ = γ} {M = ` x} (λ _ → ≡-refl) , g x

fund (lam N) {ρ} {γ} g q =
  pack (code N) (tup γ) , now {γ = γ} {M = lam N} (λ _ → ≡-refl) ,
  Rel-inj (strict · (abs ⟦ N ⟧ · ρ)) s-fun body
 where
  body : (n : ℕ) → Pay n (s-fun {N = N} {γ}) (approx n fun (strict · (abs ⟦ N ⟧ · ρ)))
  body n x w r = Ev-from-RelE {N = N} {γ = w ∷ γ}
                   (RelE-strict {N = N} {γ = w ∷ γ} (abs ⟦ N ⟧ · ρ) (ε∞ n · x)
                      (λ _ → fund N {(ε∞ n · x) • ρ} {w ∷ γ} (G-ext g (Rel-ε n r)))) n

fund (app L M) {ρ} {γ} g q =
  fund-app L M (⟦ L ⟧ · ρ) (⟦ M ⟧ · ρ) (fund L g (app-defined (⟦ L ⟧ · ρ) (⟦ M ⟧ · ρ) q)) (fund M g) q

fund (lit B c) {ρ} {γ} g q = cv c , now {γ = γ} {M = lit B c} (λ _ → ≡-refl) , Rel-inj ⋆ s-con (λ _ → ⋆)

fund (tuple {Δ} Ms) {ρ} {γ} g q =
  tup vs , ∥∥-functor (λ es → ev (st-bind (evals-st Ms es) (st-now (λ _ → ≡-refl)))) ts ,
  transport (λ - → Rel - (tup vs)) ((tuple-is (length Δ) ds ∙ guard-defined (length Δ) ds def (inj (tup (length Δ)) · ds)) ⁻¹)
    (Rel-inj ds s-tup rs)
 where
  ds : Fin (length Δ) → ⟨ 𝔻 ⟩
  ds = ⟦ Ms ⟧s · ρ
  def : (i : Fin (length Δ)) → defined (ds i)
  def = tuple-defined← (length Δ) ds q
  res = funds Ms {ρ} {γ} g def
  vs = pr₁ res
  ts = pr₁ (pr₂ res)
  rs = pr₂ (pr₂ res)

fund (get {Δ} i M) {ρ} {γ} g q = get-case (fund M {ρ} {γ} g qm)
 where
  m : ⟨ 𝔻 ⟩
  m = ⟦ M ⟧ · ρ
  qm : defined m
  qm = proj-defined (pos i) m q
  get-case : Out m M γ → Out (proj (pos i) · m) (get i M) γ
  get-case (tup vs , t , r) = body (Rel-inv r qm)
   where
    body : Inv m (tup vs) → Out (proj (pos i) · m) (get i M) γ
    body (_ , xs , eqm , s-tup , mm) =
      lookup vs i , then (λ _ → ≡-refl) (λ _ → ≡-refl) t ,
      transport (λ - → Rel - (lookup vs i)) ((ap (proj (pos i) ·_) eqm ∙ proj-inj (length Δ) xs (pos i)) ⁻¹)
        (rel (λ n → Tup-lookup vs (λ j → π∞ n · xs j) i (mm n)))

fund (inl M) {ρ} {γ} g q =
  inl v , then (λ _ → ≡-refl) (λ _ → ≡-refl) t ,
  transport (λ - → Rel - (inl v)) ((inl-is a ∙ seq-defined a (inj left · a) qa) ⁻¹) (Rel-inj a s-left (stage r))
 where
  a : ⟨ 𝔻 ⟩
  a = ⟦ M ⟧ · ρ
  qa : defined a
  qa = seq-defined-l a (inj left · a) (transport defined (inl-is a) q)
  res : Out a M γ
  res = fund M {ρ} {γ} g qa
  v = pr₁ res
  t = pr₁ (pr₂ res)
  r = pr₂ (pr₂ res)

fund (inr M) {ρ} {γ} g q =
  inr v , then (λ _ → ≡-refl) (λ _ → ≡-refl) t ,
  transport (λ - → Rel - (inr v)) ((inr-is a ∙ seq-defined a (inj right · a) qa) ⁻¹) (Rel-inj a s-right (stage r))
 where
  a : ⟨ 𝔻 ⟩
  a = ⟦ M ⟧ · ρ
  qa : defined a
  qa = seq-defined-l a (inj right · a) (transport defined (inr-is a) q)
  res : Out a M γ
  res = fund M {ρ} {γ} g qa
  v = pr₁ res
  t = pr₁ (pr₂ res)
  r = pr₂ (pr₂ res)

fund {Γ} (case {C = C} L M N) {ρ} {γ} g q = case-case (fund L {ρ} {γ} g ql)
 where
  l : ⟨ 𝔻 ⟩
  l = ⟦ L ⟧ · ρ
  b : ⟨ Br ⟩
  b = (strict · (abs ⟦ M ⟧ · ρ) , strict · (abs ⟦ N ⟧ · ρ))
  ql : defined l
  ql = cases-defined l b q
  {- the branch N', on the payload x of l, related to a' -}
  branch-ok : ∀ {A'} (N' : Tm (A' ∷ Γ) C) {a' : Value A'} (x : ⟨ 𝔻 ⟩)
    → cases · l · b ＝ strict · (abs ⟦ N' ⟧ · ρ) · x → Rel x a'
    → (∀ {v} → ∥ (a' ∷ γ) ⊢ N' ⇓ v ∥ → ∥ γ ⊢ case L M N ⇓ v ∥) → Out (cases · l · b) (case L M N) γ
  branch-ok N' {a'} x eqb rx run' = v , run' tN , transport (λ - → Rel - v) (eqb ⁻¹) rN
   where
    res : Out (strict · (abs ⟦ N' ⟧ · ρ) · x) N' (a' ∷ γ)
    res = RelE-strict {N = N'} {γ = a' ∷ γ} (abs ⟦ N' ⟧ · ρ) x (λ _ → fund N' {x • ρ} {a' ∷ γ} (G-ext g rx))
            (transport defined eqb q)
    v = pr₁ res
    tN = pr₁ (pr₂ res)
    rN = pr₂ (pr₂ res)
  case-case : Out l L γ → Out (cases · l · b) (case L M N) γ
  case-case (inl a' , tL , rL) = body (Rel-inv rL ql)
   where
    body : Inv l (inl a') → Out (cases · l · b) (case L M N) γ
    body (_ , x , eql , s-left , ml) =
      branch-ok M x (ap (λ - → cases · - · b) eql ∙ ap (_· b) (case-inj (Br ⟹𝔻) cases-br left x)) (rel ml)
        (∥∥-functor₂ (λ eL eM → ev (st-bind (run eL) (run eM))) tL)
  case-case (inr a' , tL , rL) = body (Rel-inv rL ql)
   where
    body : Inv l (inr a') → Out (cases · l · b) (case L M N) γ
    body (_ , x , eql , s-right , ml) =
      branch-ok N x (ap (λ - → cases · - · b) eql ∙ ap (_· b) (case-inj (Br ⟹𝔻) cases-br right x)) (rel ml)
        (∥∥-functor₂ (λ eL eN → ev (st-bind (run eL) (run eN))) tL)

fund (prim p L M) {ρ} {γ} g q = prim-case (fund L {ρ} {γ} g ql)
 where
  l m : ⟨ 𝔻 ⟩
  l = ⟦ L ⟧ · ρ
  m = ⟦ M ⟧ · ρ
  ql : defined l
  ql = primD-defined₁ p l m q
  prim-case : Out l L γ → Out (primD p · l · m) (prim p L M) γ
  prim-case (cv n , tL , rL) = body (Rel-inv rL ql)
   where
    body : Inv l (cv n) → Out (primD p · l · m) (prim p L M) γ
    body (_ , x , eql , s-con , _) = prim-case₂ (fund M {ρ} {γ} g qm)
     where
      eq₁ : primD p · l · m ＝ caseᵈ 𝔻⊥ (prim-br₂ p n) · m
      eq₁ = ap (λ - → primD p · - · m) eql ∙ ap (_· m) (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) (con Int n) x)
      qm : defined m
      qm = case-defined (prim-br₂ p n) m (transport defined eq₁ q)
      prim-case₂ : Out m M γ → Out (primD p · l · m) (prim p L M) γ
      prim-case₂ (cv n' , tM , rM) = body₂ (Rel-inv rM qm)
       where
        body₂ : Inv m (cv n') → Out (primD p · l · m) (prim p L M) γ
        body₂ (_ , y , eqm , s-con , _) =
          δᵥ p (cv n) (cv n') ,
          ∥∥-functor₂ (λ eL eM → ev (st-bind (run eL) (st-bind (run eM) (st-now (λ _ → ≡-refl))))) tL tM ,
          transport (λ - → Rel - (δᵥ p (cv n) (cv n')))
            ((eq₁ ∙ ap (caseᵈ 𝔻⊥ (prim-br₂ p n) ·_) eqm ∙ case-inj 𝔻⊥ (prim-br₂ p n) (con Int n') y) ⁻¹)
            (Rel-out p n n')

fund (let′ M N) g q = fund-let M N (fund M g) (λ r → fund N (G-ext g r)) q

fund (fold M) {ρ} {γ} g q = fold v , then (λ _ → ≡-refl) (λ _ → ≡-refl) t , Rel-fold r
 where
  res : Out (⟦ M ⟧ · ρ) M γ
  res = fund M {ρ} {γ} g q
  v = pr₁ res
  t = pr₁ (pr₂ res)
  r = pr₂ (pr₂ res)

fund (unfold M) {ρ} {γ} g q = unfold-case (fund M {ρ} {γ} g q)
 where
  unfold-case : Out (⟦ M ⟧ · ρ) M γ → Out (⟦ M ⟧ · ρ) (unfold M) γ
  unfold-case (fold v , t , r) = v , then (λ _ → ≡-refl) (λ _ → ≡-refl) t , Rel-unfold r

funds [] g def = [] , ∣ All₂.[] ∣ , (λ n → ⋆)
funds (M ∷ Ms) {ρ} {γ} g def =
  (v ∷ vs) , ∥∥-functor₂ (λ e es → e All₂.∷ es) t ts , (λ n → stage r n , rs n)
 where
  res = fund M {ρ} {γ} g (def zero)
  v = pr₁ res
  t = pr₁ (pr₂ res)
  r = pr₂ (pr₂ res)
  res' = funds Ms {ρ} {γ} g (λ i → def (suc i))
  vs = pr₁ res'
  ts = pr₁ (pr₂ res')
  rs = pr₂ (pr₂ res')

{- Adequacy -------------------------------------------------------------------------}

{- a closed program whose meaning is defined returns a value from some clock on -}
adequate : ∀ {A} (M : Tm [] A) → defined (⟦ M ⟧ · ρ₀) → Σ v ꞉ Value A , ∥ [] ⊢ M ⇓ v ∥
adequate M q = pr₁ res , pr₁ (pr₂ res)
 where
  res = fund M {ρ₀} {[]} (λ ()) q
