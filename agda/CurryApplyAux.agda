open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

open import Values
import ValueStructAux
import OrderingAux
import WFDenotMod
import CurryApplyStruct


module CurryApplyAux
  (D : ValueStruct)
  (V : ValueOrdering D) 
  (C : Consistent D V)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where
  open ValueStruct D
  open ValueStructAux D
  open OrderingAux D V
  open Consistent C
  open import ConsistentAux D V C

  open CurryApplyStruct.CurryApplyStruct MB
  open CurryApplyStruct.CurryStruct model_curry
  open import Utilities

  ℱ-cong : ∀{D D′ : Denotation}
         → D ≃ D′
           -----------
         → ℱ D ≃ ℱ D′
  ℱ-cong {D}{D′} D≃D′ γ v wfγ wfv =
    record { to = ℱ-≲ (λ {w} wfw {v'} wfv' Dv' → Iso.to (D≃D′ (γ `, w) v' (WFEnv-extend wfγ wfw) wfv') Dv') wfv ;
      from = ℱ-≲ (λ {w} wfw {v'} wfv' Dv' → Iso.from (D≃D′ (γ `, w) v' (WFEnv-extend wfγ wfw) wfv') Dv') wfv }


  ●-cong : ∀ {D₁ D₁′ D₂ D₂′ : Denotation}
     → D₁ ≃ D₁′ → D₂ ≃ D₂′
     → (D₁ ● D₂) ≃ (D₁′ ● D₂′)
  ●-cong {D₁}{D₁′}{D₂}{D₂′} d1 d2 γ v wfγ wfv =
     let to = ●-≲ {γ}{γ}{D₁}{D₂}{D₁′}{D₂′}
                 (λ {w} wfw D₁γw → Iso.to (d1 γ w wfγ wfw) D₁γw)
                 (λ {w} wfw D₂γw → Iso.to (d2 γ w wfγ wfw) D₂γw) wfv in
     let from = ●-≲ {γ}{γ}{D₁′}{D₂′}{D₁}{D₂}
                 (λ {w} wfw D₁γw → Iso.from (d1 γ w wfγ wfw) D₁γw)
                 (λ {w} wfw D₂γw → Iso.from (d2 γ w wfγ wfw) D₂γw) wfv in
     record { to = to ; from = from }

