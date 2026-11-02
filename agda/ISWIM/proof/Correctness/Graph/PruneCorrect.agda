{-

  Correctness of typed prune (Clos2ᵀ → Clos2ᵀ) in the graph model
  (Semantics/Graph/Typed/Clos2.agda).

  ⟦ M ⟧ ρ ≃ ⟦ opt r M ⟧ ρ' when ρ and ρ' agree through r on the
  variables that M uses (Agree), and ρ is nonempty on all variables in
  scope (NE). Every case but the closure is a congruence. The free
  variables of a closure and the kept ones are related by the selection
  (Th): a kept one is equal, a dropped one is a variable, so nonempty.
  Hence the two closures' guards hold together, and the environments of
  the codes agree through squeeze on the variables the code uses.

-}

module proof.Correctness.Graph.PruneCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.TypedGraph using (guard-≃)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Language.Typed.Type
open import Language.Typed.Clos2
open import proof.Semantics.Graph.Typed.Ops using (project-≃)
open import proof.Semantics.Graph.Typed.Clos2 using (⟦_⟧; ⟦_⟧s; fv-env; fv-env-nth)
open import Compiler.Prune
open import Framework.VecSelect
open import proof.Framework.VecSelect

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary.Decidable using (fromWitness)

NE : ∀ k → Env Value → Set
NE k ρ = ∀ (x : Fin k) → nonempty (ρ (toℕ x))

Agree : ∀ {k k'} → (Fin k → Bool) → (Fin k → Fin k') → Env Value → Env Value → Set
Agree u r ρ ρ' = ∀ x → T (u x) → ρ (toℕ x) ≃ ρ' (toℕ (r x))

ext-agree : ∀ {k k' u r ρ ρ' X} → Agree {k} {k'} (λ x → u (suc x)) r ρ ρ' → Agree u (ext r) (X • ρ) (X • ρ')
ext-agree ag zero _ = ≃-refl
ext-agree ag (suc x) t = ag x t

ext-ne : ∀ {k ρ X} → nonempty X → NE k ρ → NE (suc k) (X • ρ)
ext-ne v V zero = v
ext-ne v V (suc x) = V x

{- the free variables of a closure, as a vector -}
vec : ∀ n → Results (𝒫 Value) (replicate n ■) → Vec (𝒫 Value) n
vec zero _ = []
vec (suc n) ⟨ X , Xs ⟩ = X ∷ vec n Xs

vec-nth : ∀ n Xs (i : Fin n) → lookup (vec n Xs) i ≡ nthD Xs i
vec-nth (suc n) ⟨ X , Xs ⟩ zero = refl
vec-nth (suc n) ⟨ X , Xs ⟩ (suc i) = vec-nth n Xs i

code-env : ∀ n Xs Y (x : Fin (suc n)) → (Y • fv-env n Xs) (toℕ x) ≡ lookup (Y ∷ vec n Xs) x
code-env n Xs Y zero = refl
code-env (suc n) ⟨ X , Xs ⟩ Y (suc zero) = refl
code-env (suc n) ⟨ X , Xs ⟩ Y (suc (suc i)) = code-env n Xs X (suc i)

{- the kept free variables: equal; the dropped ones: nonempty -}
data Th : ∀ {n} (fl : Vec Bool n) → Vec (𝒫 Value) n → Vec (𝒫 Value) (count fl) → Set₁ where
  [] : Th [] [] []
  keep : ∀ {n fl x y xs ys} → x ≃ y → Th {n} fl xs ys → Th (true ∷ fl) (x ∷ xs) (y ∷ ys)
  drop : ∀ {n fl x xs ys} → nonempty x → Th {n} fl xs ys → Th (false ∷ fl) (x ∷ xs) ys

th-thin : ∀ {n fl xs ys} → Th {n} fl xs ys → Thin _≃_ fl xs ys
th-thin [] = []
th-thin (keep e th) = keep e (th-thin th)
th-thin (drop _ th) = drop (th-thin th)

ANE : ∀ {n} → Vec (𝒫 Value) n → Set
ANE xs = ∀ i → nonempty (lookup xs i)

th-ne→ : ∀ {n fl xs ys} → Th {n} fl xs ys → ANE xs → ANE ys
th-ne→ (keep e th) ne zero = let ⟨ d , d∈ ⟩ = ne zero in ⟨ d , proj₁ e d d∈ ⟩
th-ne→ (keep e th) ne (suc j) = th-ne→ th (λ i → ne (suc i)) j
th-ne→ (drop _ th) ne j = th-ne→ th (λ i → ne (suc i)) j

th-ne← : ∀ {n fl xs ys} → Th {n} fl xs ys → ANE ys → ANE xs
th-ne← (keep e th) ne zero = let ⟨ d , d∈ ⟩ = ne zero in ⟨ d , proj₂ e d d∈ ⟩
th-ne← (keep e th) ne (suc i) = th-ne← th (λ j → ne (suc j)) i
th-ne← (drop x th) ne zero = x
th-ne← (drop x th) ne (suc i) = th-ne← th ne i

{- between nthD and the vector -}
to-vec : ∀ n {Xs} → (∀ i → nonempty (nthD Xs i)) → ANE (vec n Xs)
to-vec n ne i = subst nonempty (sym (vec-nth n _ i)) (ne i)

of-vec : ∀ n {Xs} → ANE (vec n Xs) → ∀ i → nonempty (nthD Xs i)
of-vec n ne i = subst nonempty (vec-nth n _ i) (ne i)

opt-ok : ∀ {k k' A} (M : Tm k A) {r : Fin k → Fin k'} {ρ ρ'} → NE k ρ → Agree (uses M) r ρ ρ' → ⟦ M ⟧ ρ ≃ ⟦ opt r M ⟧ ρ'
opts-ok : ∀ {k k' n} (Ms : Vec (Tm k Any) n) {r : Fin k → Fin k'} {ρ ρ'} → NE k ρ → Agree (usesV Ms) r ρ ρ'
  → ∀ i → nthD (⟦ Ms ⟧s ρ) i ≃ nthD (⟦ opts r Ms ⟧s ρ') i

th-ok : ∀ {k k' n} (fl : Vec Bool n) (Ms : Vec (Tm k Any) n) {u : Fin n → Bool} {r : Fin k → Fin k'} {ρ ρ'}
  → (∀ i → Fl (u i) (lookup fl i) (lookup Ms i)) → NE k ρ → Agree (usesV Ms) r ρ ρ'
  → Th fl (vec n (⟦ Ms ⟧s ρ)) (vec _ (⟦ select fl (opts r Ms) ⟧s ρ'))
th-ok [] [] s V ag = []
th-ok (b ∷ fl) (M ∷ Ms) s V ag with s zero
... | kept = keep (opt-ok M V (subL ag)) (th-ok fl Ms (λ i → s (suc i)) V (subR ag))
... | var {x = x} _ = drop (V x) (th-ok fl Ms (λ i → s (suc i)) V (subR ag))

opt-ok (` x) V ag = ag x (fromWitness refl)
opt-ok (clos {n} N Ms) {r} {ρ} {ρ'} V ag =
  guard-≃ n (count fl) (λ ne → of-vec (count fl) (th-ne→ th (to-vec n ne))) (λ ne → of-vec n (th-ne← th (to-vec (count fl) ne)))
    λ ne → Λ-≃ λ W neW _ →
      opt-ok N {squeeze fl}
        (ext-ne (E≢[]⇒nonempty-mem neW) λ i → subst nonempty (sym (fv-env-nth n Ds i)) (ne i))
        λ x u → subst₂ _≃_ (sym (code-env n Ds (mem W) x)) (sym (code-env _ Es (mem W) (squeeze fl x)))
                  (thin-lookup ≃-refl (th-thin th) x (covers {N = N} {Ms} s x u))
  where
  s = flags-ok (λ i → uses N (suc i)) Ms
  fl = keeps N Ms
  Ds = ⟦ Ms ⟧s ρ
  Es = ⟦ select fl (opts r Ms) ⟧s ρ'
  th = th-ok fl Ms s V ag
opt-ok (app L M) V ag = ⋆-≃ (opt-ok L V (subL ag)) (opt-ok M V (subR ag))
opt-ok (lit B c) V ag = ≃-refl
opt-ok (tuple {n = n} Ms) V ag = 𝒯-≃ n (opts-ok Ms V ag)
opt-ok (get i M) V ag = proj-≃ i (opt-ok M V ag)
opt-ok (inl M) V ag = inl-≃ (opt-ok M V ag)
opt-ok (inr M) V ag = inr-≃ (opt-ok M V ag)
opt-ok (case L M N) {r} {ρ} {ρ'} V ag =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) M ⟧ (X • ρ')} {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) N ⟧ (X • ρ')}
    (opt-ok L V (subL ag))
    (λ v W _ → opt-ok M (ext-ne ⟨ v , here refl ⟩ V) (ext-agree (subL (subR {u = uses L} ag))))
    (λ v W _ → opt-ok N (ext-ne ⟨ v , here refl ⟩ V) (ext-agree (subR (subR {u = uses L} ag))))
opt-ok (prim p L M) V ag = primD-≃ p (opt-ok L V (subL ag)) (opt-ok M V (subR ag))
opt-ok (let′ M N) {r} {ρ} {ρ'} V ag =
  letD-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ opt (ext r) N ⟧ (X • ρ')} (opt-ok M V (subL ag))
    (λ W neW _ → opt-ok N (ext-ne (E≢[]⇒nonempty-mem neW) V) (ext-agree (subR ag)))
opt-ok (inject G M) V ag = opt-ok M V ag
opt-ok (project t M) V ag = project-≃ _ t (opt-ok M V ag)

opts-ok (M ∷ Ms) V ag zero = opt-ok M V (subL ag)
opts-ok (M ∷ Ms) V ag (suc i) = opts-ok Ms V (subR ag) i

prune-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ prune-program M ⟧ ρ₀
prune-correct M = opt-ok M (λ ()) (λ ())
