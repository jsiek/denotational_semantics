{-

  The Clos3 semantics is continuous: a ContinuousSemantics instance built
  from the per-operator lemmas in Domain.ISWIM.Continuity, and the
  resulting continuity of every term (from NewSemantics.⟦⟧-continuous).

-}

open import SetsAsPredicates
open import NewDOpSig
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Domain.ISWIM.Continuity
open import Compiler.Lang.Clos3
open import Compiler.Model.Graph.Sem.Clos3Iswim
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Compiler.Model.Graph.Sem.Clos3IswimContinuous where

term-mono : ∀ (M : AST) → Mono (λ ρ → ⟦ M ⟧ ρ)
term-mono M ρ⊆ = ⟦⟧-monotone M ρ⊆

args-nth-mono : ∀ {n} (args : Args (replicate n ■)) (i : Fin n)
  → Mono (λ ρ → nthD (⟦ args ⟧₊ ρ) i)
args-nth-mono {suc n} (cons (ast M) args) zero ρ⊆ = ⟦⟧-monotone M ρ⊆
args-nth-mono {suc n} (cons (ast M) args) (suc i) ρ⊆ = args-nth-mono args i ρ⊆

args-nth-cont : ∀ {n} (args : Args (replicate n ■)) {ρ : Env Value} {NE : nonempty-env ρ}
  → continuous-args ρ NE (replicate n ■) args
  → (i : Fin n) → Cont (λ ρ → nthD (⟦ args ⟧₊ ρ) i) ρ
args-nth-cont {suc n} (cons (ast M) args) ⟨ cM , cs ⟩ zero = cM
args-nth-cont {suc n} (cons (ast M) args) {ρ} {NE} ⟨ cM , cs ⟩ (suc i) =
  args-nth-cont args {ρ} {NE} cs i

Clos3-continuous-op : ∀ {op} {ρ : Env Value} {NE : nonempty-env ρ} {v} {args}
  → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → continuous-args ρ NE (sig op) args
  → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ′
Clos3-continuous-op {clos-op n} {ρ} {NE} {v} {cons (clear a) fvs} v∈ ⟨ _ , cs ⟩ =
  ⋆-cont {E₁ = λ _ → Fun} {E₂ = λ ρ → 𝒯 n (⟦ fvs ⟧₊ ρ)} NE
    (const-mono {D = Fun}) (𝒯-mono-env {Ds = λ ρ → ⟦ fvs ⟧₊ ρ} (args-nth-mono fvs))
    (const-cont {D = Fun} NE) (𝒯-cont {Ds = λ ρ → ⟦ fvs ⟧₊ ρ} NE (args-nth-mono fvs) (args-nth-cont fvs {ρ} {NE} cs))
    v v∈
  where
  {- the code of a closure does not depend on the environment -}
  Fun = Λ ⟨ (λ X → Λ ⟨ ⟦ clear a ⟧ₐ ρ X , ptt ⟩) , ptt ⟩
Clos3-continuous-op {app} {ρ} {NE} {v} {cons (ast L) (cons (ast N) nil)} v∈
    ⟨ cL , ⟨ cN , _ ⟩ ⟩ =
  ⋆-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ N ⟧ ρ} NE (term-mono L) (term-mono N) cL cN v v∈
Clos3-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
  const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧ ρ} NE v v∈
Clos3-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
  𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊ ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
Clos3-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  proj-cont i {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  ℒ-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  ℛ-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {case-op} {ρ} {NE} {v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  𝒞-cont {L = λ ρ → ⟦ L ⟧ ρ} {B₁ = λ ρ → ⟦ M ⟧ ρ} {B₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (term-mono L) cL (term-mono M) cM (term-mono N) cN v v∈

Clos3-Continuous : ContinuousSemantics
Clos3-Continuous = record
  { Sem = Clos3-Semantics
  ; continuous-op = λ {op} {ρ} {NE} {v} {args} → Clos3-continuous-op {op} {ρ} {NE} {v} {args}
  }

{- every element of a term's denotation is produced by finite parts of the
   environment -}
term-continuous : ∀ (M : AST) (ρ : Env Value) → nonempty-env ρ → ∀ v → v ∈ ⟦ M ⟧ ρ
  → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x)
                                 × v ∈ ⟦ M ⟧ (λ x → mem (Vs x))
term-continuous M ρ NE v v∈
    with ⟦⟧-continuous {{Clos3-Continuous}} {ρ} {NE} M v v∈
... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , v∈′ ⟩ ⟩ ⟩ =
  ⟨ (λ x → proj₁ (fin x))
  , ⟨ (λ x → ⟨ proj₂ (proj₂ (fin x))
             , (λ d d∈ → ρ′⊆ x d (proj₂ (proj₁ (proj₂ (fin x))) d d∈)) ⟩)
    , ⟦⟧-monotone M (λ x d d∈ → proj₁ (proj₁ (proj₂ (fin x))) d d∈) v v∈′ ⟩ ⟩
