{-

  Correctness of the enclose pass (ISWIM → Clos2).

  ISWIM and Clos2 use the same values, and enclose only changes where a
  function's body finds its free variables: in the surrounding environment
  in ISWIM, and among the values its closure captured in Clos2. So the
  pass preserves denotations exactly, ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂, when
  the environments agree on the variables M uses; this gives both the
  forward and the backward direction. The environment must be nonempty
  because Clos2 closures are strict in their free variables.

  A closure captures ` (m - 1) , ... , ` 0, where m is the bound of the
  body, so every surrounding variable the body uses is captured.

-}

open import NewSyntaxUtil
open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM
open import Compiler.Lang.Uses Op sig
open import Compiler.Model.Graph.Sem.ISWIM
open import Compiler.Model.Graph.Sem.Clos2Iswim as S2 renaming
  (⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧ₐ₂; ⟦_⟧₊ to ⟦_⟧₊₂)
open import Compiler.Compile.Optimize using (bind-n-ast)
open import Compiler.Compile.Enclose
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; ρ₀)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (init₀; push; apply-push; push-plus; ⋆-≃; 𝒯-≃; proj-≃; ℒ-≃; ℛ-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.OptimizeCorrect using (unbind-bind; push-ne)
open import NewEnv using (nonempty-env; extend-nonempty-env)

open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; _∸_; _⊔_)
open import Data.Nat.Properties
  using (+-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥; n<1+n; <-≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.EncloseCorrect where

{- Every variable a term uses is below its bound -------------------------------}

<-∸1 : ∀ {x b} → suc x < b → x < b ∸ 1
<-∸1 {x} {suc b} sx<sb = ≤-pred sx<sb

uses-bound : ∀ x (M : AST) → Uses x M → x < bound M
uses-bound-arg : ∀ {b} x (a : Arg b) → UsesArg x a → x < bound-arg a
uses-bound-args : ∀ {bs} x (args : Args bs) → UsesArgs x args → x < bound-args args

uses-bound x (` .x) refl = n<1+n x
uses-bound x (op ⦅ args ⦆) u = uses-bound-args x args u

uses-bound-arg x (ast M) u = uses-bound x M u
uses-bound-arg x (bind a) u = <-∸1 (uses-bound-arg (suc x) a u)

uses-bound-args x (cons a args) (inj₁ u) = <-≤-trans (uses-bound-arg x a u) (m≤m⊔n _ _)
uses-bound-args x (cons a args) (inj₂ u) =
  <-≤-trans (uses-bound-args x args u) (m≤n⊔m (bound-arg a) _)

{- The captured free variables ------------------------------------------------}

{- they are nonempty -}
fv-vars-ne : ∀ m (ρ : Env) → nonempty-env ρ → ∀ i → nonempty (nthD (⟦ fv-vars m ⟧₊₂ ρ) i)
fv-vars-ne (suc m) ρ NE zero = NE m
fv-vars-ne (suc m) ρ NE (suc i) = fv-vars-ne m ρ NE i

{- binding ` (n - 1) , ... , ` 0 one at a time puts ρ k at position k -}
push-vars : ∀ n (ρ σ : Env) k → k < n → push (⟦ fv-vars n ⟧₊₂ ρ) σ k ≡ ρ k
push-vars (suc n) ρ σ k k<sn with k <? n
... | yes k<n = push-vars n ρ (ρ n • σ) k k<n
... | no ¬k<n =
  trans (cong (push (⟦ fv-vars n ⟧₊₂ ρ) (ρ n • σ)) (trans k≡n (sym (+-identityʳ n))))
        (trans (push-plus n _ (ρ n • σ) 0) (cong ρ (sym k≡n)))
  where
  k≡n : k ≡ n
  k≡n = ≤-antisym (≤-pred k<sn) (≮⇒≥ ¬k<n)

{- The main lemma -------------------------------------------------------------}

enc-correct : ∀ (M : AST) ρ₁ ρ₂ → nonempty-env ρ₂ → (∀ x → Uses x M → ρ₁ x ≃ ρ₂ x)
  → ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂

enc-args-correct : ∀ {n} (args : Args (replicate n ■)) ρ₁ ρ₂ → nonempty-env ρ₂
  → (∀ x → UsesArgs x args → ρ₁ x ≃ ρ₂ x)
  → ∀ i → nthD (⟦ args ⟧₊ ρ₁) i ≃ nthD (⟦ enc-args args ⟧₊₂ ρ₂) i

enc-correct (` x) ρ₁ ρ₂ NE rel = rel x refl
enc-correct (lam ⦅ ⟩ N ,, Nil ⦆) ρ₁ ρ₂ NE rel = ⟨ G , H ⟩
  where
  m = bound N ∸ 1
  Ds = ⟦ fv-vars m ⟧₊₂ ρ₂
  ne = fv-vars-ne m ρ₂ NE

  {- the body finds its free variables where it found them before -}
  body≃ : ∀ U → U ≢ [] → ⟦ N ⟧ (mem U • ρ₁)
              ≃ apply-n m (⟦ bind-n-ast m (enclose N) ⟧ₐ₂ init₀) Ds (mem U)
  body≃ U neU rewrite apply-push m (bind-n-ast m (enclose N)) init₀ Ds (mem U)
                    | unbind-bind m (enclose N) =
    enc-correct N (mem U • ρ₁) (mem U • push Ds init₀)
      (extend-nonempty-env (push-ne m Ds init₀ ne (λ _ → ⟨ ω , refl ⟩)) (E≢[]⇒nonempty-mem neU))
      rel'
    where
    rel' : ∀ x → Uses x N → (mem U • ρ₁) x ≃ (mem U • push Ds init₀) x
    rel' zero _ = ≃-refl
    rel' (suc k) u =
      ≃-trans (rel k (inj₁ u))
              (≃-reflexive (sym (push-vars m ρ₂ init₀ k (<-∸1 (uses-bound (suc k) N u)))))

  G : ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ ρ₁ ⊆ ⟦ enclose (lam ⦅ ⟩ N ,, Nil ⦆) ⟧₂ ρ₂
  G ν tt = ⟨ ne , tt ⟩
  G (U ↦ x) ⟨ x∈ , neU ⟩ = ⟨ ne , ⟨ proj₁ (body≃ U neU) x x∈ , neU ⟩ ⟩

  H : ⟦ enclose (lam ⦅ ⟩ N ,, Nil ⦆) ⟧₂ ρ₂ ⊆ ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ ρ₁
  H ν ⟨ _ , tt ⟩ = tt
  H (U ↦ x) ⟨ _ , ⟨ x∈ , neU ⟩ ⟩ = ⟨ proj₂ (body≃ U neU) x x∈ , neU ⟩
enc-correct (app ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ⋆-≃ (enc-correct L ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
      (enc-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₂ (inj₁ u))))
enc-correct (lit B k ⦅ Nil ⦆) ρ₁ ρ₂ NE rel = ≃-refl
enc-correct (tuple n ⦅ args ⦆) ρ₁ ρ₂ NE rel = 𝒯-≃ n (enc-args-correct args ρ₁ ρ₂ NE rel)
enc-correct (get i ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  proj-≃ i (enc-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
enc-correct (inl-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ℒ-≃ (enc-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
enc-correct (inr-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ℛ-≃ (enc-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
enc-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ₁)} {λ X → ⟦ enclose M ⟧₂ (X • ρ₂)}
      {λ X → ⟦ N ⟧ (X • ρ₁)} {λ X → ⟦ enclose N ⟧₂ (X • ρ₂)}
      (enc-correct L ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
      (λ v V → enc-correct M _ _ (NE-ext v) (rel-ext M (λ x u → rel x (inj₂ (inj₁ u)))))
      (λ v V → enc-correct N _ _ (NE-ext v) (rel-ext N (λ x u → rel x (inj₂ (inj₂ (inj₁ u))))))
  where
  NE-ext : ∀ {V} v → nonempty-env (mem (v ∷ V) • ρ₂)
  NE-ext v = extend-nonempty-env NE ⟨ v , here refl ⟩
  rel-ext : ∀ B {X} → (∀ x → Uses (suc x) B → ρ₁ x ≃ ρ₂ x) → ∀ x → Uses x B → (X • ρ₁) x ≃ (X • ρ₂) x
  rel-ext B r zero _ = ≃-refl
  rel-ext B r (suc x) u = r x u

enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ NE rel zero =
  enc-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u))
enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ NE rel (suc i) =
  enc-args-correct args ρ₁ ρ₂ NE (λ x u → rel x (inj₂ u)) i

{- The end theorem ------------------------------------------------------------}

enclose-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct-closed M = enc-correct M ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) (λ x _ → ≃-refl)
