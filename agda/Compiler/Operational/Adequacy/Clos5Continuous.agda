{-

  The Clos5 semantics, for a fixed table T of global definitions, is
  monotone and continuous in the environment: a Semantics and a
  ContinuousSemantics instance built from the per-operator lemmas in
  Domain.ISWIM.Continuity, as for Clos4 (Sem/Clos4IswimContinuous.agda);
  a reference to a global definition is a constant.

  Used by the soundness of the Clos5 machine (Adequacy/Clos5Soundness.agda)
  for the steps that pass values to code (calls, case, let).

-}

module Compiler.Operational.Adequacy.Clos5Continuous where

open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Domain.ISWIM.Continuity
open import Compiler.Lang.Clos5
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; 𝕆-Clos5; ⟦_⟧[_]; ⟦_⟧₊[_])
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)
open import NewSemantics Op sig
  using (Semantics; ContinuousSemantics; continuous-args; ⟦⟧-monotone; ⟦⟧-continuous)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≢_)

𝕆-Clos5-mono : ∀ T → 𝕆-monotone sig (𝕆-Clos5 T)
𝕆-Clos5-mono T (fun-ref k) _ _ _ = lift (λ d d∈ → d∈)
𝕆-Clos5-mono T app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩
                   ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ =
  ⋆-mono ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
         ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
         ⟨ ⋆-mono ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩
         , ⟨ N~ , ptt ⟩ ⟩
𝕆-Clos5-mono T (lit B k) _ _ _ = lift (λ d d∈ → d∈)
𝕆-Clos5-mono T pair-op = pair-mono
𝕆-Clos5-mono T fst-op = car-mono
𝕆-Clos5-mono T snd-op = cdr-mono
𝕆-Clos5-mono T (tuple x) = 𝒯-mono x
𝕆-Clos5-mono T (get x) = proj-mono x
𝕆-Clos5-mono T inl-op = inl-mono
𝕆-Clos5-mono T inr-op = inr-mono
𝕆-Clos5-mono T case-op = 𝒞-mono
𝕆-Clos5-mono T let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-mono ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
         ⟨ Λ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

{- ⟦ M ⟧[ T ] is the meaning of M in this semantics -}
Clos5-Semantics : Table → Semantics
Clos5-Semantics T = record { interp-op = 𝕆-Clos5 T ; mono-op = 𝕆-Clos5-mono T ; error = ω }

module _ (T : Table) where

  instance
    S5 : Semantics
    S5 = Clos5-Semantics T

  term-mono : ∀ (M : AST) → Mono (λ ρ → ⟦ M ⟧[ T ] ρ)
  term-mono M ρ⊆ = ⟦⟧-monotone M ρ⊆

  args-nth-mono : ∀ {n} (args : Args (replicate n ■)) (i : Fin n)
    → Mono (λ ρ → nthD (⟦ args ⟧₊[ T ] ρ) i)
  args-nth-mono {suc n} (cons (ast M) args) zero ρ⊆ = ⟦⟧-monotone M ρ⊆
  args-nth-mono {suc n} (cons (ast M) args) (suc i) ρ⊆ = args-nth-mono args i ρ⊆

  args-nth-cont : ∀ {n} (args : Args (replicate n ■)) {ρ : Env Value} {NE : nonempty-env ρ}
    → continuous-args ρ NE (replicate n ■) args
    → (i : Fin n) → Cont (λ ρ → nthD (⟦ args ⟧₊[ T ] ρ) i) ρ
  args-nth-cont {suc n} (cons (ast M) args) ⟨ cM , cs ⟩ zero = cM
  args-nth-cont {suc n} (cons (ast M) args) {ρ} {NE} ⟨ cM , cs ⟩ (suc i) =
    args-nth-cont args {ρ} {NE} cs i

  Clos5-continuous-op : ∀ {op} {ρ : Env Value} {NE : nonempty-env ρ} {v} {args}
    → v ∈ ⟦ op ⦅ args ⦆ ⟧[ T ] ρ → continuous-args ρ NE (sig op) args
    → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ args ⦆ ⟧[ T ] ρ′
  Clos5-continuous-op {fun-ref k} {ρ} {NE} {v} {nil} v∈ _ =
    const-cont {D = T k} NE v v∈
  Clos5-continuous-op {app} {ρ} {NE} {v} {cons (ast L) (cons (ast M) (cons (ast N) nil))} v∈
      ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
    ⋆-cont {E₁ = λ ρ → ⋆ ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ M ⟧[ T ] ρ , ptt ⟩ ⟩} {E₂ = λ ρ → ⟦ N ⟧[ T ] ρ} NE
      (⋆-mono-env {E₁ = λ ρ → ⟦ L ⟧[ T ] ρ} {E₂ = λ ρ → ⟦ M ⟧[ T ] ρ} (term-mono L) (term-mono M))
      (term-mono N)
      (⋆-cont {E₁ = λ ρ → ⟦ L ⟧[ T ] ρ} {E₂ = λ ρ → ⟦ M ⟧[ T ] ρ} NE (term-mono L) (term-mono M) cL cM)
      cN v v∈
  Clos5-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
    const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧[ T ] ρ} NE v v∈
  Clos5-continuous-op {pair-op} {ρ} {NE} {v} {cons (ast L) (cons (ast M) nil)} v∈
      ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
    pair-cont {E₁ = λ ρ → ⟦ L ⟧[ T ] ρ} {E₂ = λ ρ → ⟦ M ⟧[ T ] ρ} NE (term-mono L) (term-mono M) cL cM v v∈
  Clos5-continuous-op {fst-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    car-cont {E = λ ρ → ⟦ M ⟧[ T ] ρ} cM v v∈
  Clos5-continuous-op {snd-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    cdr-cont {E = λ ρ → ⟦ M ⟧[ T ] ρ} cM v v∈
  Clos5-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
    𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊[ T ] ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
  Clos5-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    proj-cont i {E = λ ρ → ⟦ M ⟧[ T ] ρ} cM v v∈
  Clos5-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    inl-cont {E = λ ρ → ⟦ M ⟧[ T ] ρ} cM v v∈
  Clos5-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    inr-cont {E = λ ρ → ⟦ M ⟧[ T ] ρ} cM v v∈
  Clos5-continuous-op {case-op} {ρ} {NE} {v}
      {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
      ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
    𝒞-cont {L = λ ρ → ⟦ L ⟧[ T ] ρ} {B₁ = λ ρ → ⟦ M ⟧[ T ] ρ} {B₂ = λ ρ → ⟦ N ⟧[ T ] ρ} NE
      (term-mono L) cL (term-mono M) cM (term-mono N) cN v v∈
  Clos5-continuous-op {let-op} {ρ} {NE} {v} {cons (ast M) (cons (bind (ast N)) nil)} v∈
      ⟨ cM , ⟨ cN , _ ⟩ ⟩ =
    ⋆-cont {E₁ = λ ρ → Λ ⟨ (λ X → ⟦ N ⟧[ T ] (X • ρ)) , ptt ⟩} {E₂ = λ ρ → ⟦ M ⟧[ T ] ρ} NE
      (Λ-mono-env {B = λ ρ → ⟦ N ⟧[ T ] ρ} (term-mono N)) (term-mono M)
      (Λ-cont {B = λ ρ → ⟦ N ⟧[ T ] ρ} NE (term-mono N) cN) cM v v∈

  Clos5-Continuous : ContinuousSemantics
  Clos5-Continuous = record
    { Sem = S5
    ; continuous-op = λ {op} {ρ} {NE} {v} {args} → Clos5-continuous-op {op} {ρ} {NE} {v} {args}
    }

  ⟦⟧[]-monotone : ∀ (M : AST) {ρ ρ′} → ρ ⊆ₑ ρ′ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T ] ρ′
  ⟦⟧[]-monotone M ρ⊆ = ⟦⟧-monotone M ρ⊆

  {- every element of a term's denotation is produced by finite, nonempty
     parts of the environment -}
  term-continuous : ∀ (M : AST) (ρ : Env Value) → nonempty-env ρ → ∀ v → v ∈ ⟦ M ⟧[ T ] ρ
    → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x)
                                   × v ∈ ⟦ M ⟧[ T ] (λ x → mem (Vs x))
  term-continuous M ρ NE v v∈
      with ⟦⟧-continuous {{Clos5-Continuous}} {ρ} {NE} M v v∈
  ... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , v∈′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → proj₁ (fin x))
    , ⟨ (λ x → ⟨ proj₂ (proj₂ (fin x))
               , (λ d d∈ → ρ′⊆ x d (proj₂ (proj₁ (proj₂ (fin x))) d d∈)) ⟩)
      , ⟦⟧-monotone M (λ x d d∈ → proj₁ (proj₁ (proj₂ (fin x))) d d∈) v v∈′ ⟩ ⟩
