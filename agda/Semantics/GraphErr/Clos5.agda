module Semantics.GraphErr.Clos5 where
{-

 The semantics of Clos5 (and of its monadic normal form, a sublanguage)
 in the graph model with errors: that of Semantics/Graph/Clos5Iswim.agda,
 with the error-propagating operators (Framework/GraphModel/ErrorOps.agda),
 as the machine (Semantics/CEK/Clos5.agda) does: a call evaluates its
 code, environment and argument left to right and then checks the code
 (callᵉ, the late check); fst and snd are errors on a non-pair. A
 reference to a global definition is the code of that definition; a
 reference to none is code whose call errs (errcode), as the machine
 errs at the call.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorOps
open import Semantics.GraphErr.Prim
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

𝕆-Clos5ᵉ : Table → DOpSig (𝒫 Value) sig
𝕆-Clos5ᵉ T (fun-ref k) _ = T k
𝕆-Clos5ᵉ T app = callᵉ
𝕆-Clos5ᵉ T (lit B k) = ℬ B k
𝕆-Clos5ᵉ T pair-op = pairᵉ
𝕆-Clos5ᵉ T fst-op = carᵉ
𝕆-Clos5ᵉ T snd-op = cdrᵉ
𝕆-Clos5ᵉ T (tuple x) = 𝒯ᵉ x
𝕆-Clos5ᵉ T (get x) = projᵉ x
𝕆-Clos5ᵉ T inl-op = inlᵉ
𝕆-Clos5ᵉ T inr-op = inrᵉ
𝕆-Clos5ᵉ T case-op = 𝒞ᵉ
𝕆-Clos5ᵉ T (prim p) = primᵉ p
𝕆-Clos5ᵉ T let-op = letᵉ

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧[_] : AST → Table → Env Value → 𝒫 Value
⟦ M ⟧[ T ] ρ = fold (𝕆-Clos5ᵉ T) init ρ M

⟦_⟧ₐ[_] : ∀ {b} → Arg b → Table → Env Value → Result (𝒫 Value) b
⟦ a ⟧ₐ[ T ] ρ = fold-arg (𝕆-Clos5ᵉ T) init ρ a

⟦_⟧₊[_] : ∀ {bs} → Args bs → Table → Env Value → Tuple bs (Result (𝒫 Value))
⟦ args ⟧₊[ T ] ρ = fold-args (𝕆-Clos5ᵉ T) init ρ args

{- the code N of a definition, given the table T of the older ones: it
   takes the tuple of free variables X and then the argument Y -}
code : Table → AST → 𝒫 Value
code T N = ΛΛᵉ ⟨ (λ X Y → ⟦ N ⟧[ T ] (Y • X • (λ _ → init))) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List AST → Table
table [] k = errcode
table (N ∷ Ns) k with k ≟ length Ns
... | yes _ = code (table Ns) N
... | no _ = table Ns k

⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] (λ _ → init)
