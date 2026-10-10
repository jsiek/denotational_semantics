{-

  Correctness of the enclose pass (Clos1 → Clos2).

  Clos1 and Clos2 use the same values, and enclose only changes where a
  closure's body finds its free variables: in the surrounding environment
  in Clos1, and among the values it captured in Clos2. So the pass
  preserves denotations exactly, ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂, when the
  environments agree on the variables M uses; this gives both the forward
  and the backward direction.

  The side condition (Enclosed) is the shape that the annotate pass gives
  closures: a closure lists the first n surrounding variables as its free
  variables, ` (n - 1) , ... , ` 0, and its body uses no other surrounding
  variable.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos1
open import Compiler.Lang.Uses Op sig
open import Compiler.Model.Graph.Sem.Clos1Iswim
open import Compiler.Model.Graph.Sem.Clos2Iswim as S2 renaming
  (⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧ₐ₂; ⟦_⟧₊ to ⟦_⟧₊₂)
open import Compiler.Compile.Optimize using (bind-n-ast)
open import Compiler.Compile.Enclose
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; ρ₀)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (init₀; push; apply-push; push-plus; ⋆-≃; 𝒯-≃; proj-≃; ℒ-≃; ℛ-≃)
open import Compiler.Model.Graph.Correctness.OptimizeCorrect using (unbind-bind)

open import Data.Nat using (ℕ; zero; suc; _<_; _<?_)
open import Data.Nat.Properties using (+-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.EncloseCorrect where

{- Programs in the shape that annotate produces ------------------------------}

data Enclosed : AST → Set
data EnclosedArgs : ∀ {n} → Args (replicate n ■) → Set

data Enclosed where
  enc-var : ∀ {x} → Enclosed (` x)
  enc-clos : ∀ {n N} → Enclosed N → (∀ k → Uses (suc k) N → k < n)
    → Enclosed (clos-op n ⦅ ! bind (ast N) ,, fv-vars n ⦆)
  enc-app : ∀ {L M} → Enclosed L → Enclosed M → Enclosed (app ⦅ L ,, M ,, Nil ⦆)
  enc-lit : ∀ {B k} → Enclosed (lit B k ⦅ Nil ⦆)
  enc-tuple : ∀ {n} {args : Args (replicate n ■)} → EnclosedArgs args
    → Enclosed (tuple n ⦅ args ⦆)
  enc-get : ∀ {n} {i : Fin n} {M} → Enclosed M → Enclosed (get i ⦅ M ,, Nil ⦆)
  enc-inl : ∀ {M} → Enclosed M → Enclosed (inl-op ⦅ M ,, Nil ⦆)
  enc-inr : ∀ {M} → Enclosed M → Enclosed (inr-op ⦅ M ,, Nil ⦆)
  enc-case : ∀ {L M N} → Enclosed L → Enclosed M → Enclosed N
    → Enclosed (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆)

data EnclosedArgs where
  enc-nil : EnclosedArgs {zero} Nil
  enc-cons : ∀ {n M} {args : Args (replicate n ■)} → Enclosed M → EnclosedArgs args
    → EnclosedArgs {suc n} (M ,, args)

{- binding ` (n - 1) , ... , ` 0 one at a time puts ρ k at position k -}
push-vars : ∀ n (ρ σ : Env) k → k < n → push (⟦ enc-args (fv-vars n) ⟧₊₂ ρ) σ k ≡ ρ k
push-vars (suc n) ρ σ k k<sn with k <? n
... | yes k<n = push-vars n ρ (ρ n • σ) k k<n
... | no ¬k<n =
  trans (cong (push (⟦ enc-args (fv-vars n) ⟧₊₂ ρ) (ρ n • σ)) (trans k≡n (sym (+-identityʳ n))))
        (trans (push-plus n _ (ρ n • σ) 0) (cong ρ (sym k≡n)))
  where
  k≡n : k ≡ n
  k≡n = ≤-antisym (≤-pred k<sn) (≮⇒≥ ¬k<n)

{- the free variables of an enclosed closure agree in both environments -}
fv-vars-correct : ∀ n ρ₁ ρ₂ → (∀ x → UsesArgs x (fv-vars n) → ρ₁ x ≃ ρ₂ x)
  → ∀ i → nthD (⟦ fv-vars n ⟧₊ ρ₁) i ≃ nthD (⟦ enc-args (fv-vars n) ⟧₊₂ ρ₂) i
fv-vars-correct (suc n) ρ₁ ρ₂ rel zero = rel n (inj₁ refl)
fv-vars-correct (suc n) ρ₁ ρ₂ rel (suc i) = fv-vars-correct n ρ₁ ρ₂ (λ x u → rel x (inj₂ u)) i

{- The main lemma -------------------------------------------------------------}

enc-correct : ∀ (M : AST) ρ₁ ρ₂ → Enclosed M → (∀ x → Uses x M → ρ₁ x ≃ ρ₂ x)
  → ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂

enc-args-correct : ∀ {n} (args : Args (replicate n ■)) ρ₁ ρ₂ → EnclosedArgs args
  → (∀ x → UsesArgs x args → ρ₁ x ≃ ρ₂ x)
  → ∀ i → nthD (⟦ args ⟧₊ ρ₁) i ≃ nthD (⟦ enc-args args ⟧₊₂ ρ₂) i

enc-correct (` x) ρ₁ ρ₂ e rel = rel x refl
enc-correct (clos-op n ⦅ ! bind (ast N) ,, fvs ⦆) ρ₁ ρ₂ (enc-clos eN up) rel = ⟨ G , H ⟩
  where
  Ds₁ = ⟦ fv-vars n ⟧₊ ρ₁
  Ds₂ = ⟦ enc-args (fv-vars n) ⟧₊₂ ρ₂
  Ds≃ = fv-vars-correct n ρ₁ ρ₂ (λ x u → rel x (inj₂ u))

  {- the body finds its free variables where it found them before -}
  body≃ : ∀ U → ⟦ N ⟧ (mem U • ρ₁)
              ≃ apply-n n (⟦ bind-n-ast n (enclose N) ⟧ₐ₂ init₀) Ds₂ (mem U)
  body≃ U rewrite apply-push n (bind-n-ast n (enclose N)) init₀ Ds₂ (mem U)
                | unbind-bind n (enclose N) =
    enc-correct N (mem U • ρ₁) (mem U • push Ds₂ init₀) eN rel'
    where
    rel' : ∀ x → Uses x N → (mem U • ρ₁) x ≃ (mem U • push Ds₂ init₀) x
    rel' zero _ = ≃-refl
    rel' (suc k) u =
      ≃-trans (rel k (inj₁ u)) (≃-reflexive (sym (push-vars n ρ₂ init₀ k (up k u))))

  G : ⟦ clos-op n ⦅ ! bind (ast N) ,, fv-vars n ⦆ ⟧ ρ₁
      ⊆ ⟦ enclose (clos-op n ⦅ ! bind (ast N) ,, fv-vars n ⦆) ⟧₂ ρ₂
  G ν ⟨ ne , tt ⟩ = ⟨ (λ i → ⟨ proj₁ (ne i) , proj₁ (Ds≃ i) _ (proj₂ (ne i)) ⟩) , tt ⟩
  G (U ↦ x) ⟨ ne , ⟨ x∈ , neU ⟩ ⟩ =
    ⟨ (λ i → ⟨ proj₁ (ne i) , proj₁ (Ds≃ i) _ (proj₂ (ne i)) ⟩)
    , ⟨ proj₁ (body≃ U) x x∈ , neU ⟩ ⟩

  H : ⟦ enclose (clos-op n ⦅ ! bind (ast N) ,, fv-vars n ⦆) ⟧₂ ρ₂
      ⊆ ⟦ clos-op n ⦅ ! bind (ast N) ,, fv-vars n ⦆ ⟧ ρ₁
  H ν ⟨ ne , tt ⟩ = ⟨ (λ i → ⟨ proj₁ (ne i) , proj₂ (Ds≃ i) _ (proj₂ (ne i)) ⟩) , tt ⟩
  H (U ↦ x) ⟨ ne , ⟨ x∈ , neU ⟩ ⟩ =
    ⟨ (λ i → ⟨ proj₁ (ne i) , proj₂ (Ds≃ i) _ (proj₂ (ne i)) ⟩)
    , ⟨ proj₂ (body≃ U) x x∈ , neU ⟩ ⟩
enc-correct (app ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ (enc-app eL eM) rel =
  ⋆-≃ (enc-correct L ρ₁ ρ₂ eL (λ x u → rel x (inj₁ u)))
      (enc-correct M ρ₁ ρ₂ eM (λ x u → rel x (inj₂ (inj₁ u))))
enc-correct (lit B k ⦅ Nil ⦆) ρ₁ ρ₂ e rel = ≃-refl
enc-correct (tuple n ⦅ args ⦆) ρ₁ ρ₂ (enc-tuple es) rel =
  𝒯-≃ n (enc-args-correct args ρ₁ ρ₂ es rel)
enc-correct (get i ⦅ M ,, Nil ⦆) ρ₁ ρ₂ (enc-get eM) rel =
  proj-≃ i (enc-correct M ρ₁ ρ₂ eM (λ x u → rel x (inj₁ u)))
enc-correct (inl-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ (enc-inl eM) rel =
  ℒ-≃ (enc-correct M ρ₁ ρ₂ eM (λ x u → rel x (inj₁ u)))
enc-correct (inr-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ (enc-inr eM) rel =
  ℛ-≃ (enc-correct M ρ₁ ρ₂ eM (λ x u → rel x (inj₁ u)))
enc-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ (enc-case eL eM eN) rel = ⟨ G , H ⟩
  where
  L≃ = enc-correct L ρ₁ ρ₂ eL (λ x u → rel x (inj₁ u))

  M≃ : ∀ X → ⟦ M ⟧ (X • ρ₁) ≃ ⟦ enclose M ⟧₂ (X • ρ₂)
  M≃ X = enc-correct M (X • ρ₁) (X • ρ₂) eM relM
    where
    relM : ∀ x → Uses x M → (X • ρ₁) x ≃ (X • ρ₂) x
    relM zero _ = ≃-refl
    relM (suc x) u = rel x (inj₂ (inj₁ u))

  N≃ : ∀ X → ⟦ N ⟧ (X • ρ₁) ≃ ⟦ enclose N ⟧₂ (X • ρ₂)
  N≃ X = enc-correct N (X • ρ₁) (X • ρ₂) eN relN
    where
    relN : ∀ x → Uses x N → (X • ρ₁) x ≃ (X • ρ₂) x
    relN zero _ = ≃-refl
    relN (suc x) u = rel x (inj₂ (inj₂ (inj₁ u)))

  G : ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₁
      ⊆ ⟦ enclose (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧₂ ρ₂
  G w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (left d) (allL d d∈))
                     , proj₁ (M≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (right d) (allR d d∈))
                     , proj₁ (N≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩

  H : ⟦ enclose (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧₂ ρ₂
      ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₁
  H w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (allL d d∈))
                     , proj₂ (M≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (allR d d∈))
                     , proj₂ (N≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩

enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ (enc-cons eM es) rel zero =
  enc-correct M ρ₁ ρ₂ eM (λ x u → rel x (inj₁ u))
enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ (enc-cons eM es) rel (suc i) =
  enc-args-correct args ρ₁ ρ₂ es (λ x u → rel x (inj₂ u)) i

{- The end theorem ------------------------------------------------------------}

enclose-correct-closed : ∀ (M : AST) → Enclosed M → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct-closed M e = enc-correct M ρ₀ ρ₀ e (λ x _ → ≃-refl)
