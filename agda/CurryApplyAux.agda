open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import Structures
import ValueStructAux
import OrderingAux
import WFDenotMod
import CurryApplyStruct


module CurryApplyAux
  (D : ValueStruct)
  (V : ValueOrdering D) 
  (C : Consistent D V)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open Consistent C
  open import ConsistentAux D V C

  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry


  ℱ-cong : ∀{Γ}{D D′ : Denotation (suc Γ)}
         → D ≃ D′
           -----------
         → ℱ D ≃ ℱ D′
  ℱ-cong {Γ}{D}{D′} D≃D′ γ v wfγ wfv =
    ⟨ ℱ-≲ (λ {w} wfw {v'} wfv' Dv' → proj₁ (D≃D′ (γ `, w) v' (λ {x} → WFEnv-extend wfγ wfw {x}) wfv') Dv') wfv ,
      ℱ-≲ (λ {w} wfw {v'} wfv' Dv' → proj₂ (D≃D′ (γ `, w) v' (λ {x} → WFEnv-extend wfγ wfw {x}) wfv') Dv') wfv ⟩


  ●-cong : ∀{Γ}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
     → D₁ ≃ D₁′ → D₂ ≃ D₂′
     → (D₁ ● D₂) ≃ (D₁′ ● D₂′)
  ●-cong {Γ}{D₁}{D₁′}{D₂}{D₂′} d1 d2 γ v wfγ wfv =
     let to = ●-≲ {Γ}{Γ}{γ}{γ}{D₁}{D₂}{D₁′}{D₂′}
                 (λ {w} wfw D₁γw → proj₁ (d1 γ w wfγ wfw) D₁γw)
                 (λ {w} wfw D₂γw → proj₁ (d2 γ w wfγ wfw) D₂γw) wfv in
     let from = ●-≲ {Γ}{Γ}{γ}{γ}{D₁′}{D₂′}{D₁}{D₂}
                 (λ {w} wfw D₁γw → proj₂ (d1 γ w wfγ wfw) D₁γw)
                 (λ {w} wfw D₂γw → proj₂ (d2 γ w wfγ wfw) D₂γw) wfv in
     ⟨ to , from ⟩

