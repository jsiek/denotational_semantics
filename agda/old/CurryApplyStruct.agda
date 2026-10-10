open import Data.Nat using (ℕ; zero; suc)

open import Values
import ValueStructAux
import OrderingAux
import WFDenotMod
import ConsistentAux


module CurryApplyStruct
  (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where

  open ValueStruct D
  open ValueOrdering V
  open Consistent C
  open ValueStructAux D
  open OrderingAux D V
  open ConsistentAux D V C
  open WFDenotMod D V C
  
  record CurryStruct
      (ℱ : Denotation → Denotation)
      : Set₁ where
    field
      ℱ-≲ : ∀{D : Denotation} {D′ : Denotation}
             {γ : Env}{δ : Env}
          → (∀{v : Value} → wf v → D (γ `, v) ≲ D′ (δ `, v))
          → ℱ D γ ≲ ℱ D′ δ
      ℱ-⊑ : ∀{D : Denotation}{γ : Env} {v w : Value}
          → WFDenot D → WFEnv γ → wf v → wf w
          → w ⊑ v
          → ℱ D γ v
          → ℱ D γ w
      ℱ-⊔ : ∀{D : Denotation}{γ : Env}{u v : Value}
          → ℱ D γ u → ℱ D γ v
          → ℱ D γ (u ⊔ v)
      ℱ-⊥ : ∀{D : Denotation}{γ : Env} → ℱ D γ ⊥
      ℱ-~ : ∀{D : Denotation}{γ : Env}{δ : Env} {u v : Value}
          → WFDenot D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
          → ℱ D γ u → ℱ D δ v
          → u ~ v

  {- was LambdaModelBasics -}
  record CurryApplyStruct
      (_●_ : Denotation → Denotation → Denotation)
      (ℱ : Denotation → Denotation)
      : Set₁ where
    field
      model_curry : CurryStruct ℱ
      ●-≲ : ∀{γ : Env}{δ : Env}{D₁ D₂ : Denotation}
              {D₁′ D₂′ : Denotation}
          → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
          → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
      ●-⊑ : ∀{D₁ D₂ : Denotation} {γ : Env} {v w : Value}
          → WFDenot D₁ → WFEnv γ → wf v → wf w
          → w ⊑ v → (D₁ ● D₂) γ v → (D₁ ● D₂) γ w
      ●-⊔ : ∀{D₁ D₂ : Denotation}{γ : Env}{u v : Value}
          → WFDenot D₁ → WFDenot D₂ → WFEnv γ → wf u → wf v
          → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
      ●-~ : ∀{D₁ D₂ : Denotation}{γ : Env}{δ : Env} {u v : Value}
          → WFDenot D₁ → WFDenot D₂
          → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
          → (D₁ ● D₂) γ u → (D₁ ● D₂) δ v → u ~ v

