{-

  The Clos5 semantics, for a fixed table T of global definitions, is
  monotone and continuous in the environment: a Semantics and a
  ContinuousSemantics instance built from the per-operator lemmas in
  proof.Framework.GraphModel.Continuity, as for Clos4 (proof/Semantics/Graph/Clos4IswimContinuous.agda);
  a reference to a global definition is a constant.

  Used by the correctness of remove complex operands
  (Correctness/RCOCorrect.agda), for the let laws, and by the soundness
  of the Clos5 machine (proof/Adequacy/Clos5Soundness.agda), for
  the steps that pass values to code (calls, case, let).

-}

module proof.Semantics.Graph.Clos5IswimContinuous where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim
open import Language.Clos5
open import Semantics.Graph.Clos5Iswim using (Table; 𝕆-Clos5; ⟦_⟧[_]; ⟦_⟧₊[_]; table)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; finiteNE-env; _⊆ₑ_; _~ₑ[_]_; •-~)
open import proof.Framework.GraphModel.Semantics Op sig
  using (Semantics; ContinuousSemantics; continuous-args; ⟦⟧-monotone; ⟦⟧-continuous; ⟦⟧-pres)

open import Data.Nat using (suc; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.List using (_∷_; length)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
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
𝕆-Clos5-mono T (prim p) = primD-mono p

{- with a consistent table, the operators are consistent -}
𝕆-Clos5-consis : ∀ T → (∀ k → Con (T k)) → 𝕆-consistent _~_ sig (𝕆-Clos5 T)
𝕆-Clos5-consis T TC (fun-ref k) _ _ _ = lift (TC k)
𝕆-Clos5-consis T TC app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩
                   ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ =
  ⋆-consis ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
           ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
           ⟨ ⋆-consis ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩
           , ⟨ N~ , ptt ⟩ ⟩
𝕆-Clos5-consis T TC (lit B k) = ℬ-consis B k
𝕆-Clos5-consis T TC pair-op = pair-consis
𝕆-Clos5-consis T TC fst-op = car-consis
𝕆-Clos5-consis T TC snd-op = cdr-consis
𝕆-Clos5-consis T TC (tuple x) = 𝒯-consis x
𝕆-Clos5-consis T TC (get x) = proj-consis x
𝕆-Clos5-consis T TC inl-op = inl-consis
𝕆-Clos5-consis T TC inr-op = inr-consis
𝕆-Clos5-consis T TC case-op = 𝒞-consis
𝕆-Clos5-consis T TC let-op ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-consis ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
           ⟨ Λ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩
𝕆-Clos5-consis T TC (prim p) = primD-consis p

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
  Clos5-continuous-op {prim p} {ρ} {NE} {v} {cons (ast L) (cons (ast M) nil)} v∈
      ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
    primD-cont p {E₁ = λ ρ → ⟦ L ⟧[ T ] ρ} {E₂ = λ ρ → ⟦ M ⟧[ T ] ρ} (term-mono L) (term-mono M) cL cM v v∈

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

{- with a consistent table and environments, denotations are consistent -}
Clos5-con-env : ∀ T → (∀ k → Con (T k)) → ∀ M {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ'
  → Every _~_ (⟦ M ⟧[ T ] ρ) (⟦ M ⟧[ T ] ρ')
Clos5-con-env T TC M = ⟦⟧-pres {{Clos5-Semantics T}} (Every _~_) (𝕆-Clos5-consis T TC) (Con-⌈⌉ ω) M

Clos5-con : ∀ T → (∀ k → Con (T k)) → ∀ M {ρ} → Con-env ρ → Con (⟦ M ⟧[ T ] ρ)
Clos5-con T TC M = Clos5-con-env T TC M

{- the function Λ X. Λ Y. F X Y, for F consistent in X and Y -}
ΛΛ-con : ∀ {F : 𝒫 Value → 𝒫 Value → 𝒫 Value}
  → (∀ X X' Y Y' → Every _~_ X X' → Every _~_ Y Y' → Every _~_ (F X Y) (F X' Y'))
  → Con (Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩)
ΛΛ-con F~ = lower (Λ-consis _ _ ⟨ (λ X X' X~ → Λ-consis _ _
  ⟨ (λ Y Y' Y~ → lift (F~ X X' Y Y' X~ Y~)) , ptt ⟩) , ptt ⟩)

{- the tables of programs are consistent -}
table-con : ∀ ds k → Con (table ds k)
table-con [] k = λ _ _ ()
table-con (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ΛΛ-con (λ X X' Y Y' X~ Y~ →
                Clos5-con-env (table Ns) (table-con Ns) N (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
... | no _ = table-con Ns k
