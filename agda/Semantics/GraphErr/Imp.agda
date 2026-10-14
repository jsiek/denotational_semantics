module Semantics.GraphErr.Imp where
{-

 What the semantics of Imp, CFG and X86 in the graph model with errors
 have in common: stores, slots, atoms and simple expressions, as in
 Semantics/Graph/Imp.agda, with the error-propagating operators.

 As in the machines (Semantics/CEK/{Imp,CFG}.agda): reading a slot beyond
 the frame errors (init, {ω}); assigning one errs once the value assigned
 has been computed (frameᵐ: ω if the value is anything, ∅ if it
 diverges); a call app f e a is the late-check call callᵐ, and the
 code of a definition runs its body in a fresh frame of max(2, n) slots,
 as the machines' frames have (e ∷ a ∷ zeros (n ∸ 2)). A reference to no
 definition is code whose call errs (errcode).

-}

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErr.Prim
open import Language.Imp
open import Semantics.GraphErr.Frames public

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<?_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

𝒜 : Table → ℕ → Store → Atm → 𝒫 Value
𝒜 T n σ (var x) = read n σ x
𝒜 T n σ (lit B k) = ℬ B k ptt
𝒜 T n σ (fun-ref k) = T k

𝒜s : Table → ℕ → Store → (as : List Atm) → Results (𝒫 Value) (replicate (length as) ■)
𝒜s T n σ [] = ptt
𝒜s T n σ (a ∷ as) = ⟨ 𝒜 T n σ a , 𝒜s T n σ as ⟩

{- the value of a simple expression in a frame of n slots -}
𝒮 : Table → ℕ → Store → Simple → 𝒫 Value
𝒮 T n σ (atm a) = 𝒜 T n σ a
𝒮 T n σ (app f e a) = callᵐ ⟨ 𝒜 T n σ f , ⟨ 𝒜 T n σ e , ⟨ 𝒜 T n σ a , ptt ⟩ ⟩ ⟩
𝒮 T n σ (pair a b) = pairᵐ ⟨ 𝒜 T n σ a , ⟨ 𝒜 T n σ b , ptt ⟩ ⟩
𝒮 T n σ (fst a) = carᵐ ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (snd a) = cdrᵐ ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (tuple as) = 𝒯ᵐ (length as) (𝒜s T n σ as)
𝒮 T n σ (get i a) = projᵐ i ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (inl a) = inlᵐ ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (inr a) = inrᵐ ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (prim p a b) = primᵐ p ⟨ 𝒜 T n σ a , ⟨ 𝒜 T n σ b , ptt ⟩ ⟩

frame : 𝒫 Value → 𝒫 Value → Store
frame X Y zero = X
frame X Y (suc zero) = Y
frame X Y (suc (suc y)) = zeros y
