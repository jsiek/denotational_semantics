{-

  The Clos4 semantics is continuous: a ContinuousSemantics instance built
  from the per-operator lemmas in Domain.ISWIM.Continuity, and the
  resulting continuity of every term (from NewSemantics.⟦⟧-continuous).

-}

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Domain.ISWIM.Continuity
open import Compiler.Lang.Clos4
open import Compiler.Model.Graph.Sem.Continuous Op sig using (args-nth-mono; args-nth-cont)
import Compiler.Model.Graph.Sem.Continuous Op sig as G
open import Compiler.Model.Graph.Sem.Clos4Iswim
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)

open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

module Compiler.Model.Graph.Sem.Clos4IswimContinuous where

Clos4-continuous-op : ∀ {op} {ρ : Env Value} {NE : nonempty-env ρ} {v} {args}
  → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → continuous-args ρ NE (sig op) args
  → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ′
Clos4-continuous-op {fun-op} {ρ} {NE} {v} {cons (clear a) nil} v∈ _ =
  const-cont {D = ⟦ fun-op ⦅ cons (clear a) nil ⦆ ⟧ ρ} NE v v∈
Clos4-continuous-op {app} {ρ} {NE} {v} {cons (ast L) (cons (ast M) (cons (ast N) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  ⋆-cont {E₁ = λ ρ → ⋆ ⟨ ⟦ L ⟧ ρ , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩} {E₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (⋆-mono-env {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} (⟦⟧-monotone L) (⟦⟧-monotone M))
    (⟦⟧-monotone N)
    (⋆-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} NE (⟦⟧-monotone L) (⟦⟧-monotone M) cL cM)
    cN v v∈
Clos4-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
  const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧ ρ} NE v v∈
Clos4-continuous-op {pair-op} {ρ} {NE} {v} {cons (ast L) (cons (ast M) nil)} v∈
    ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
  pair-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} NE (⟦⟧-monotone L) (⟦⟧-monotone M) cL cM v v∈
Clos4-continuous-op {fst-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  car-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {snd-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  cdr-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
  𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊ ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
Clos4-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  proj-cont i {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inl-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inr-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos4-continuous-op {case-op} {ρ} {NE} {v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  𝒞-cont {L = λ ρ → ⟦ L ⟧ ρ} {B₁ = λ ρ → ⟦ M ⟧ ρ} {B₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (⟦⟧-monotone L) cL (⟦⟧-monotone M) cM (⟦⟧-monotone N) cN v v∈

Clos4-continuous-op {let-op} {ρ} {NE} {v} {cons (ast M) (cons (bind (ast N)) nil)} v∈
    ⟨ cM , ⟨ cN , _ ⟩ ⟩ =
  ⋆-cont {E₁ = λ ρ → Λ ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩} {E₂ = λ ρ → ⟦ M ⟧ ρ} NE
    (Λ-mono-env {B = λ ρ → ⟦ N ⟧ ρ} (⟦⟧-monotone N)) (⟦⟧-monotone M)
    (Λ-cont {B = λ ρ → ⟦ N ⟧ ρ} NE (⟦⟧-monotone N) cN) cM v v∈
Clos4-continuous-op {prim p} {ρ} {NE} {v}
    {cons (ast L) (cons (ast M) nil)} v∈ ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
  primD-cont p {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} (⟦⟧-monotone L) (⟦⟧-monotone M) cL cM v v∈

Clos4-Continuous : ContinuousSemantics
Clos4-Continuous = record
  { Sem = Clos4-Semantics
  ; continuous-op = λ {op} {ρ} {NE} {v} {args} → Clos4-continuous-op {op} {ρ} {NE} {v} {args}
  }

{- every element of a term's denotation is produced by finite parts of the
   environment -}
term-continuous : _
term-continuous = G.term-continuous {{Clos4-Continuous}}
