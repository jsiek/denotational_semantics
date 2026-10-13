module Semantics.GraphErrM.Clos5 where
{-

 The semantics of Clos5 (and of its monadic normal form, a sublanguage)
 in the graph model with errors: that of Semantics/Graph/Clos5Iswim.agda,
 with the error-propagating operators (Framework/GraphModel/ErrorMonad.agda),
 as the machine (Semantics/CEK/Clos5.agda) does: a call evaluates its
 code, environment and argument left to right and then checks the code
 (callᵐ, the late check); fst and snd are errors on a non-pair. A
 reference to a global definition is the code of that definition; a
 reference to none is code whose call errs (errcode), as the machine
 errs at the call.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErrM.Prim
open import Language.Clos5
open import Framework.abt.Fold2 Op sig using (fold; fold-arg; fold-args)
open import Framework.abt.ScopedTuple using (Tuple)
open import Framework.abt.Sig using (Result)
open import Framework.GraphModel.Env using (Env)

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the global definitions, by their references -}
Table : Set₁
Table = ℕ → 𝒫 Value

𝕆-Clos5ᵐ : Table → DOpSig (𝒫 Value) sig
𝕆-Clos5ᵐ T (fun-ref k) _ = T k
𝕆-Clos5ᵐ T app = callᵐ
𝕆-Clos5ᵐ T (lit B k) = ℬ B k
𝕆-Clos5ᵐ T pair-op = pairᵐ
𝕆-Clos5ᵐ T fst-op = carᵐ
𝕆-Clos5ᵐ T snd-op = cdrᵐ
𝕆-Clos5ᵐ T (tuple x) = 𝒯ᵐ x
𝕆-Clos5ᵐ T (get x) = projᵐ x
𝕆-Clos5ᵐ T inl-op = inlᵐ
𝕆-Clos5ᵐ T inr-op = inrᵐ
𝕆-Clos5ᵐ T case-op = 𝒞ᵐ
𝕆-Clos5ᵐ T (prim p) = primᵐ p
𝕆-Clos5ᵐ T let-op = letᵐ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧[_] : AST → Table → Env Value → 𝒫 Value
⟦ M ⟧[ T ] ρ = fold (𝕆-Clos5ᵐ T) init ρ M

⟦_⟧ₐ[_] : ∀ {b} → Arg b → Table → Env Value → Result (𝒫 Value) b
⟦ a ⟧ₐ[ T ] ρ = fold-arg (𝕆-Clos5ᵐ T) init ρ a

⟦_⟧₊[_] : ∀ {bs} → Args bs → Table → Env Value → Tuple bs (Result (𝒫 Value))
⟦ args ⟧₊[ T ] ρ = fold-args (𝕆-Clos5ᵐ T) init ρ args

{- the code N of a definition, given the table T of the older ones: it
   takes the tuple of free variables X and then the argument Y -}
code : Table → AST → 𝒫 Value
code T N = ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧[ T ] (Y • X • (λ _ → init))) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List AST → Table
table [] k = errcode
table (N ∷ Ns) k with k ≟ length Ns
... | yes _ = code (table Ns) N
... | no _ = table Ns k

⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] (λ _ → init)
