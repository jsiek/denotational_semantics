{-# OPTIONS --safe #-}
{-

  The Clos4 semantics is continuous: a ContinuousSemantics instance built
  from the per-operator lemmas in Domain.ISWIM.Continuity, and the
  resulting continuity of every term (from NewSemantics.⟦⟧-continuous).

-}

open import SetsAsPredicates
open import NewDOpSig
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Domain.ISWIM.Continuity
open import Compiler.Lang.Clos4
open import Compiler.Model.Graph.Sem.Clos4Iswim
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Compiler.Model.Graph.Sem.Clos4IswimContinuous where

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

Clos4-continuous-op : ∀ {op} {ρ : Env Value} {NE : nonempty-env ρ} {v} {args}
  → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → continuous-args ρ NE (sig op) args
  → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ′
Clos4-continuous-op {fun-op} {ρ} {NE} {v} {cons (clear a) nil} v∈ _ =
  const-cont {D = ⟦ fun-op ⦅ cons (clear a) nil ⦆ ⟧ ρ} NE v v∈
Clos4-continuous-op {app} {ρ} {NE} {v} {cons (ast L) (cons (ast M) (cons (ast N) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  ⋆-cont {E₁ = λ ρ → ⋆ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩} {E₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (⋆-mono-env {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} (term-mono L) (term-mono M))
    (term-mono N)
    (⋆-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} NE (term-mono L) (term-mono M) cL cM)
    cN v v∈
Clos4-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
  const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧ ρ} NE v v∈
Clos4-continuous-op {pair-op} {ρ} {NE} {v} {cons (ast L) (cons (ast M) nil)} v∈
    ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
  pair-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} NE (term-mono L) (term-mono M) cL cM v v∈
Clos4-continuous-op {fst-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  car-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {snd-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  cdr-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
  𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊ ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
Clos4-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  proj-cont i {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  ℒ-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  ℛ-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {case-op} {ρ} {NE} {v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  𝒞-cont {L = λ ρ → ⟦ L ⟧ ρ} {B₁ = λ ρ → ⟦ M ⟧ ρ} {B₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (term-mono L) cL (term-mono M) cM (term-mono N) cN v v∈

Clos4-Continuous : ContinuousSemantics
Clos4-Continuous = record
  { Sem = Clos4-Semantics
  ; continuous-op = λ {op} {ρ} {NE} {v} {args} → Clos4-continuous-op {op} {ρ} {NE} {v} {args}
  }

{- every element of a term's denotation is produced by finite parts of the
   environment -}
term-continuous : ∀ (M : AST) (ρ : Env Value) → nonempty-env ρ → ∀ v → v ∈ ⟦ M ⟧ ρ
  → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x)
                                 × v ∈ ⟦ M ⟧ (λ x → mem (Vs x))
term-continuous M ρ NE v v∈
    with ⟦⟧-continuous {{Clos4-Continuous}} {ρ} {NE} M v v∈
... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , v∈′ ⟩ ⟩ ⟩ =
  ⟨ (λ x → proj₁ (fin x))
  , ⟨ (λ x → ⟨ proj₂ (proj₂ (fin x))
             , (λ d d∈ → ρ′⊆ x d (proj₂ (proj₁ (proj₂ (fin x))) d d∈)) ⟩)
    , ⟦⟧-monotone M (λ x d d∈ → proj₁ (proj₁ (proj₂ (fin x))) d d∈) v v∈′ ⟩ ⟩
