{-

  Correctness of optimize (Closμ → Closμ) in the graph model
  (Mu/Semantics/GraphModel/Clos.agda), as for typed optimize
  (proof/Correctness/Graph/OptimizeCorrect.agda).

  ⟦ M ⟧ ρ ≃ ⟦ opt M r ⟧ ρ' when ρ and ρ' agree through r on the
  variables that M uses (Agree), and ρ is nonempty on all variables in
  scope (NE). Every case but the closure is a congruence. The free
  variables of a closure and the kept ones are related by the selection
  (Th): a kept one is equal, a dropped one is a variable, so nonempty.
  Hence the two closures' guards hold together, and the environments of
  the codes agree through squeeze on the variables the code uses.

-}

module Mu.proof.Correctness.GraphModel.OptimizeCorrect where

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.TypedGraph using (guard-≃)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.proof.Semantics.GraphModel.Clos using (⟦_⟧; ⟦_⟧s; fv-env)
open import Mu.Compiler.Optimize
open import Mu.proof.Semantics.GraphModel.Binders using (Body-≃; lam-≃; let-≃; case-≃; ne-≃)
open import Mu.Framework.AllUtil using (All; []; _∷_; Flags; kept; select; sq; squeeze; pos; ∨-l; ∨-r)

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (fromWitness)

NE : Ctx → Env Value → Set
NE Γ ρ = ∀ {C} (x : Γ ∋ C) → nonempty (ρ (idx x))

Agree : ∀ {Γ Γ'} (u : ∀ {C} → Γ ∋ C → Bool) → Ren u Γ' → Env Value → Env Value → Set
Agree u r ρ ρ' = ∀ {C} x (t : T (u {C} x)) → ρ (idx x) ≃ ρ' (idx (r x t))

ext-ne : ∀ {Γ A ρ X} → nonempty X → NE Γ ρ → NE (A ∷ Γ) (X • ρ)
ext-ne v V Z = v
ext-ne v V (S x) = V x

Rs : Ctx → Set₁
Rs Δ = Results (𝒫 Value) (replicate (length Δ) ■)

{- the kept free variables: equal; the dropped ones: nonempty -}
data Th : ∀ {Δ} (fl : Flags Δ) → Rs Δ → Rs (kept fl) → Set₁ where
  [] : Th [] ptt ptt
  keep : ∀ {A Δ fl x y xs ys} → x ≃ y → Th {Δ} fl xs ys → Th {A ∷ Δ} (true ∷ fl) ⟨ x , xs ⟩ ⟨ y , ys ⟩
  drop : ∀ {A Δ fl x xs ys} → nonempty x → Th {Δ} fl xs ys → Th {A ∷ Δ} (false ∷ fl) ⟨ x , xs ⟩ ys

th-ne→ : ∀ {Δ fl Ds Es} → Th {Δ} fl Ds Es → (∀ i → nonempty (nthD Ds i)) → ∀ j → nonempty (nthD Es j)
th-ne→ (keep e th) ne zero = ne-≃ e (ne zero)
th-ne→ (keep e th) ne (suc j) = th-ne→ th (λ i → ne (suc i)) j
th-ne→ (drop _ th) ne j = th-ne→ th (λ i → ne (suc i)) j

th-ne← : ∀ {Δ fl Ds Es} → Th {Δ} fl Ds Es → (∀ j → nonempty (nthD Es j)) → ∀ i → nonempty (nthD Ds i)
th-ne← (keep e th) ne zero = ne-≃ (≃-sym e) (ne zero)
th-ne← (keep e th) ne (suc i) = th-ne← th (λ j → ne (suc j)) i
th-ne← (drop x th) ne zero = x
th-ne← (drop x th) ne (suc i) = th-ne← th ne i

{- a kept free variable means the same in the two codes' environments -}
th-fv : ∀ {Δ fl Ds Es C} → Th {Δ} fl Ds Es → (i : Δ ∋ C) (k : T (Mu.Framework.AllUtil.lookup fl i))
  → fv-env (length Δ) Ds (idx i) ≃ fv-env (length (kept fl)) Es (idx (sq fl i k))
th-fv (keep e th) Z k = e
th-fv (keep e th) (S i) k = th-fv th i k
th-fv (drop _ th) (S i) k = th-fv th i k

fv-ne : ∀ {Δ C} {Ds : Rs Δ} → (∀ i → nonempty (nthD Ds i)) → (i : Δ ∋ C) → nonempty (fv-env (length Δ) Ds (idx i))
fv-ne ne Z = ne zero
fv-ne ne (S i) = fv-ne (λ j → ne (suc j)) i

opt-ok : ∀ {Γ Γ' A} (M : Tm Γ A) {r : Ren (uses M) Γ'} {ρ ρ'} → NE Γ ρ → Agree (uses M) r ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ opt M r ⟧ ρ'
opts-ok : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ ρ'} → NE Γ ρ → Agree (usesA Ms) r ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ opts Ms r ⟧s ρ') i

{- a body under a binder, for the variables its binder's term uses -}
under : ∀ {Γ Γ' A B} (N : Tm (B ∷ Γ) A) {r : Ren (λ x → uses N (S x)) Γ'} {ρ ρ'} → NE Γ ρ → Agree (λ x → uses N (S x)) r ρ ρ'
  → Body-≃ (λ X → ⟦ N ⟧ (X • ρ)) (λ X → ⟦ opt N (ext {u = uses N} r) ⟧ (X • ρ'))
under N V ag X ne _ = opt-ok N (ext-ne ne V) λ { Z _ → ≃-refl ; (S x) t → ag x t }

th-ok : ∀ {Γ Γ' Δ} (u : ∀ {C} → Δ ∋ C → Bool) (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ ρ'}
  → NE Γ ρ → Agree (usesA Ms) r ρ ρ' → Th (flags u Ms) (⟦ Ms ⟧s ρ) (⟦ select (flags u Ms) (opts Ms r) ⟧s ρ')
th-ok u [] V ag = []
th-ok u (M ∷ Ms) V ag with keep? M (u Z) | fl-ok M (u Z)
... | true | _ = keep (opt-ok M V (λ x t → ag x (∨-l _ t))) (th-ok (λ x → u (S x)) Ms V (λ x t → ag x (∨-r (uses M x) t)))
... | false | var-fv {x = x} = drop (V x) (th-ok (λ x → u (S x)) Ms V (λ x t → ag x (∨-r (uses M x) t)))

opt-ok (` x) V ag = ag x (fromWitness refl)
opt-ok (clos {Δ} N Ms) V ag =
  guard-≃ (length Δ) (length (kept (keeps N Ms))) (th-ne→ th) (th-ne← th) λ ne → lam-≃ λ W neW _ →
    opt-ok N (ext-ne neW (fv-ne ne)) λ { Z _ → ≃-refl ; (S i) t → th-fv th i (covers N Ms (S i) t) }
  where th = th-ok (λ x → uses N (S x)) Ms V ag
opt-ok (app L M) V ag = ⋆-≃ (opt-ok L V (λ x t → ag x (∨-l _ t))) (opt-ok M V (λ x t → ag x (∨-r (uses L x) t)))
opt-ok (lit B c) V ag = ≃-refl
opt-ok (tuple {Δ} Ms) V ag = 𝒯-≃ (length Δ) (opts-ok Ms V ag)
opt-ok (get i M) V ag = proj-≃ (pos i) (opt-ok M V ag)
opt-ok (inl M) V ag = inl-≃ (opt-ok M V ag)
opt-ok (inr M) V ag = inr-≃ (opt-ok M V ag)
opt-ok (case L M N) V ag =
  case-≃ (opt-ok L V (λ x t → ag x (∨-l _ t)))
    (under M V λ x t → ag x (∨-r (uses L x) (∨-l (uses N (S x)) t)))
    (under N V λ x t → ag x (∨-r (uses L x) (∨-r (uses M (S x)) t)))
opt-ok (prim p L M) V ag = primD-≃ p (opt-ok L V (λ x t → ag x (∨-l _ t))) (opt-ok M V (λ x t → ag x (∨-r (uses L x) t)))
opt-ok (let′ M N) V ag = let-≃ (opt-ok M V (λ x t → ag x (∨-l _ t))) (under N V λ x t → ag x (∨-r (uses M x) t))
opt-ok (fold M) V ag = opt-ok M V ag
opt-ok (unfold M) V ag = opt-ok M V ag

opts-ok (M ∷ Ms) V ag zero = opt-ok M V (λ x t → ag x (∨-l _ t))
opts-ok (M ∷ Ms) V ag (suc i) = opts-ok Ms V (λ x t → ag x (∨-r (uses M x) t)) i

optimize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ optimize-program M ⟧ ρ₀
optimize-correct M = opt-ok M (λ ()) (λ ())
