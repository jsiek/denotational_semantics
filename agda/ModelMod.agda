open import Data.Nat using (ℕ; zero; suc)


open import Structures
import ValueStructAux
import OrderingAux
import WFDenotMod
import ConsistentAux


module ModelMod (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where

  open ValueStruct D
  open ValueOrdering V
  open Consistent C
  open ValueStructAux D
  open OrderingAux D V
  open ConsistentAux D V C
  open WFDenotMod D V C

  
  record CurryStruct
      (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
      : Set₁ where
    field
      ℱ-≲ : ∀{Γ Δ}{D : Denotation (suc Γ)} {D′ : Denotation (suc Δ)}
             {γ : Env Γ}{δ : Env Δ}
          → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
          → ℱ D γ ≲ ℱ D′ δ
      ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
          → WFDenot (suc Γ) D → WFEnv γ → wf v → wf w
          → w ⊑ v
          → ℱ D γ v
          → ℱ D γ w
      ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u v : Value}
          → ℱ D γ u → ℱ D γ v
          → ℱ D γ (u ⊔ v)
      ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} → ℱ D γ ⊥
      ℱ-~ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{δ : Env Γ} {u v : Value}
          → WFDenot (suc Γ) D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
          → ℱ D γ u → ℱ D δ v
          → u ~ v

  {- was LambdaModelBasics -}
  record CurryApplyStruct
      (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
      (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
      : Set₁ where
    field
      model_curry : CurryStruct ℱ
      ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
              {D₁′ D₂′ : Denotation Δ}
          → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
          → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
      ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
          → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v → (D₁ ● D₂) γ w
      ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {δ : Env Γ} {u v : Value}
          → WFDenot Γ D₁ → WFDenot Γ D₂ → γ ~′ δ → {c : u ~ v}
          → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
      ●-~ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ}{δ : Env Γ} {u v : Value}
          → WFDenot Γ D₁ → WFDenot Γ D₂ → γ ~′ δ
          → (D₁ ● D₂) γ u → (D₁ ● D₂) δ v → u ~ v

