{-

  Scott domains: the semantics of any signature, given the meaning of each
  operator as a continuous map. A term means a continuous map from
  environments to 𝔻; an argument under a binder means a continuous map to
  𝔻 ⟹ ..., so that a function of its bound variable is continuous; an
  argument under a clear sees only the default environment (every
  variable means init). As the graph model's semantics (the fold of the
  operators over a term, Framework/abt/Fold2.agda), but continuous by
  construction.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.List using (List; []; _∷_; replicate)
open import Data.Fin using (Fin; zero; suc)
open import Framework.abt.Sig using (Sig; ■; ν; ∁)

module Framework.Scott.Semantics
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe
open import Framework.Scott.Ops pt fe pe

{- the meaning of an argument with a given signature, and of a list of them -}
Res : Sig → DCPO₁
Res ■ = 𝔻
Res (ν b) = 𝔻 ⟹₁ Res b
Res (∁ b) = Res b

Ress : List Sig → DCPO₁
Ress [] = 𝟙ᵈ
Ress (b ∷ bs) = Res b ×₁ Ress bs

{- the meaning of an operator: a continuous map of the meanings of its arguments -}
SemOps : (Op : 𝓤₀ ̇ ) → (Op → List Sig) → 𝓤₁ ̇
SemOps Op sig = (op : Op) → DCPO[ Ress (sig op) , 𝔻 ]

{- The meanings of the operators common to the languages ---------------------}

{- an operator of one argument, of two (curried), a function (Λ of the
   meaning of its body), a case (the strict branches), a tuple -}
unary : DCPO[ 𝔻 , 𝔻 ] → DCPO[ Ress (■ ∷ []) , 𝔻 ]
unary f = ∘₁ (Ress (■ ∷ [])) 𝔻 𝔻 (fst₁ 𝔻 𝟙ᵈ) f

binary : DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ] → DCPO[ Ress (■ ∷ ■ ∷ []) , 𝔻 ]
binary f = ∘₁ (Ress (■ ∷ ■ ∷ [])) ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻
             (pair₁ (Ress (■ ∷ ■ ∷ [])) (𝔻 ⟹₁ 𝔻) 𝔻
                (∘₁ (Ress (■ ∷ ■ ∷ [])) 𝔻 (𝔻 ⟹₁ 𝔻) (fst₁ 𝔻 (Ress (■ ∷ []))) f)
                (∘₁ (Ress (■ ∷ ■ ∷ [])) (Ress (■ ∷ [])) 𝔻 (snd₁ 𝔻 (Ress (■ ∷ [])))
                   (fst₁ 𝔻 𝟙ᵈ)))
             (eval₁ 𝔻 𝔻)

lamᶜ : DCPO[ Ress (ν ■ ∷ []) , 𝔻 ]
lamᶜ = ∘₁ (Ress (ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻) 𝔻 (fst₁ (𝔻 ⟹₁ 𝔻) 𝟙ᵈ) Λ

caseᶜ : DCPO[ Ress (■ ∷ ν ■ ∷ ν ■ ∷ []) , 𝔻 ]
caseᶜ = ∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) ((Br ⟹₁ 𝔻) ×₁ Br) 𝔻
          (pair₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (Br ⟹₁ 𝔻) Br
             (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) 𝔻 (Br ⟹₁ 𝔻) (fst₁ 𝔻 (Ress (ν ■ ∷ ν ■ ∷ []))) cases)
             (pair₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻)
                (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻)
                   (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (Ress (ν ■ ∷ ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻) (snd₁ 𝔻 (Ress (ν ■ ∷ ν ■ ∷ []))) (fst₁ (𝔻 ⟹₁ 𝔻) (Ress (ν ■ ∷ []))))
                   strict)
                (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻)
                   (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (Ress (ν ■ ∷ [])) (𝔻 ⟹₁ 𝔻)
                      (∘₁ (Ress (■ ∷ ν ■ ∷ ν ■ ∷ [])) (Ress (ν ■ ∷ ν ■ ∷ [])) (Ress (ν ■ ∷ [])) (snd₁ 𝔻 (Ress (ν ■ ∷ ν ■ ∷ []))) (snd₁ (𝔻 ⟹₁ 𝔻) (Ress (ν ■ ∷ []))))
                      (fst₁ (𝔻 ⟹₁ 𝔻) 𝟙ᵈ))
                   strict)))
          (eval₁ Br 𝔻)


{- the i-th of n meanings, and all n -}
nthᶜ : (n : ℕ) → Fin n → DCPO[ Ress (replicate n ■) , 𝔻 ]
nthᶜ (succ n) zero = fst₁ 𝔻 (Ress (replicate n ■))
nthᶜ (succ n) (suc i) = ∘₁ (Ress (replicate (succ n) ■)) (Ress (replicate n ■)) 𝔻
                          (snd₁ 𝔻 (Ress (replicate n ■))) (nthᶜ n i)

toPow : (n : ℕ) → DCPO[ Ress (replicate n ■) , Pow (Fin n) 𝔻 ]
toPow n = (λ r i → nthᶜ n i · r) ,
          to-Pow-continuous (Fin n) 𝔻 (Ress (replicate n ■)) (λ r i → nthᶜ n i · r) (λ i → pr₂ (nthᶜ n i))

tupleᶜ : (n : ℕ) → DCPO[ Ress (replicate n ■) , 𝔻 ]
tupleᶜ n = ∘₁ (Ress (replicate n ■)) (Pow (Fin n) 𝔻) 𝔻 (toPow n) (tuple n)

{- The semantics of a signature --------------------------------------------}

module Semantics (Op : 𝓤₀ ̇ ) (sig : Op → List Sig) (init : ⟨ 𝔻 ⟩) (𝕆 : SemOps Op sig) where

 open import Framework.abt.AbstractBindingTree Op sig

 ⟦_⟧ : ABT → DCPO[ Env , 𝔻 ]
 ⟦_⟧ₐ : {b : Sig} → Arg b → DCPO[ Env , Res b ]
 ⟦_⟧₊ : {bs : List Sig} → Args bs → DCPO[ Env , Ress bs ]

 ⟦ ` x ⟧ = at ℕ 𝔻 x
 ⟦ op ⦅ args ⦆ ⟧ = ∘₁ Env (Ress (sig op)) 𝔻 ⟦ args ⟧₊ (𝕆 op)

 ⟦ ast M ⟧ₐ = ⟦ M ⟧
 ⟦ bind {b} a ⟧ₐ = curry₁ Env 𝔻 (Res b) (∘₁ (Env ×₁ 𝔻) Env (Res b) ext ⟦ a ⟧ₐ)
 ⟦ clear {b} a ⟧ₐ = ∘₁ Env Env (Res b) (const₁ Env Env (λ _ → init)) ⟦ a ⟧ₐ

 ⟦ nil ⟧₊ = const₁ Env 𝟙ᵈ ⋆
 ⟦ cons {b} {bs} a args ⟧₊ = pair₁ Env (Res b) (Ress bs) ⟦ a ⟧ₐ ⟦ args ⟧₊
