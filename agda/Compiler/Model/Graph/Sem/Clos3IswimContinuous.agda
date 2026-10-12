{-

  The Clos3 semantics is continuous: a ContinuousSemantics instance built
  from the per-operator lemmas in GraphModel.Continuity, and the
  resulting continuity of every term (from NewSemantics.⟦⟧-continuous).

-}

open import SetsAsPredicates
open import GraphModel.Domain
open import GraphModel.Ops
open import GraphModel.Continuity
open import Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos3
open import GraphModel.SemanticsUtil Op sig using (args-nth-mono; args-nth-cont)
import GraphModel.SemanticsUtil Op sig as G
open import Compiler.Model.Graph.Sem.Clos3Iswim
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)

open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

module Compiler.Model.Graph.Sem.Clos3IswimContinuous where

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
  ⋆-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ N ⟧ ρ} NE (⟦⟧-monotone L) (⟦⟧-monotone N) cL cN v v∈
Clos3-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
  const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧ ρ} NE v v∈
Clos3-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
  𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊ ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
Clos3-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  proj-cont i {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inl-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inr-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
Clos3-continuous-op {case-op} {ρ} {NE} {v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  𝒞-cont {L = λ ρ → ⟦ L ⟧ ρ} {B₁ = λ ρ → ⟦ M ⟧ ρ} {B₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (⟦⟧-monotone L) cL (⟦⟧-monotone M) cM (⟦⟧-monotone N) cN v v∈
Clos3-continuous-op {prim p} {ρ} {NE} {v}
    {cons (ast L) (cons (ast M) nil)} v∈ ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
  primD-cont p {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} (⟦⟧-monotone L) (⟦⟧-monotone M) cL cM v v∈

Clos3-Continuous : ContinuousSemantics
Clos3-Continuous = record
  { Sem = Clos3-Semantics
  ; continuous-op = λ {op} {ρ} {NE} {v} {args} → Clos3-continuous-op {op} {ρ} {NE} {v} {args}
  }

{- every element of a term's denotation is produced by finite parts of the
   environment -}
term-continuous : _
term-continuous = G.term-continuous {{Clos3-Continuous}}
