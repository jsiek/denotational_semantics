{-# OPTIONS --allow-unsolved-metas #-}

module Compiler.Model.Graph.Sem.Clos3IswimConsistent where
{-

 Consistency of the Clos3 operators. The case for clos-op is still open,
 so this lives apart from Clos3Iswim to keep that module free of holes.

-}

open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3
open import Compiler.Model.Graph.Sem.Clos3Iswim

𝕆-Clos3-consis : 𝕆-consistent _~_ sig 𝕆-Clos3
𝕆-Clos3-consis (clos-op x) = {!   !}
  {- 𝒜-consis x ⟨ Λ ⟨ F (𝒯 x Ds) , ptt ⟩ , Ds ⟩ ⟨ Λ ⟨ F' (𝒯 x Ds') , ptt ⟩ , Ds' ⟩
    ⟨ Λ-consis ⟨ F (𝒯 x Ds) , ptt ⟩ ⟨ F' (𝒯 x Ds') , ptt ⟩
             ⟨ F~ (𝒯 x Ds) (𝒯 x Ds') (lower (𝒯-consis x Ds Ds' Ds~)) , ptt ⟩
    , Ds~ ⟩ -}
  {- DComp-rest-pres (Every _~_) (replicate x ■) ■ ■ (𝒯 x) (𝒯 x)
                  (λ T → 𝒜 x (Λ (F1 T))) ((λ T → 𝒜 x (Λ (F2 T))))
  (𝒯-consis x) (λ T T' T~ → 𝒜-consis x (Λ (F1 T)) (Λ (F2 T'))
                            (Λ-consis (F1 T) (F2 T') (F~ T T' (lower T~)))) -}
𝕆-Clos3-consis app = ⋆-consis
𝕆-Clos3-consis (lit B k) = ℬ-consis B k
𝕆-Clos3-consis (tuple x) = 𝒯-consis x
𝕆-Clos3-consis (get x) = proj-consis x
𝕆-Clos3-consis inl-op = ℒ-consis
𝕆-Clos3-consis inr-op = ℛ-consis
𝕆-Clos3-consis case-op = 𝒞-consis
