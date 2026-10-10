module Compiler.Model.Graph.Sem.Clos5Iswim where
{-

 The semantics of Clos5, the language after the 'globalize' pass.

 The meaning of a term depends on a table T of the global definitions:
 a reference fun-ref k denotes T k. The definitions of a program are
 interpreted in order, the code of each one with the table of the older
 ones, and the main expression with the table of all of them.

-}

open import Primitives
open import SetsAsPredicates
open import NewDOpSig
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos5
open import abt.Fold2 Op sig using (fold; fold-arg; fold-args)
open import abt.ScopedTuple using (Tuple)
open import abt.Sig using (Result)
open import abt.GSubst using (_•_)
open import NewEnv using (Env)

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the global definitions, by their references -}
Table : Set₁
Table = ℕ → 𝒫 Value

𝕆-Clos5 : Table → DOpSig (𝒫 Value) sig
𝕆-Clos5 T (fun-ref k) _ = T k
𝕆-Clos5 T app ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ = ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩
𝕆-Clos5 T (lit B k) = ℬ B k
𝕆-Clos5 T pair-op = pair
𝕆-Clos5 T fst-op = car
𝕆-Clos5 T snd-op = cdr
𝕆-Clos5 T (tuple x) = 𝒯 x
𝕆-Clos5 T (get x) = proj x
𝕆-Clos5 T inl-op = ℒ
𝕆-Clos5 T inr-op = ℛ
𝕆-Clos5 T case-op = 𝒞

init : 𝒫 Value
init = ⌈ ω ⌉

⟦_⟧[_] : AST → Table → Env Value → 𝒫 Value
⟦ M ⟧[ T ] ρ = fold (𝕆-Clos5 T) init ρ M

⟦_⟧ₐ[_] : ∀ {b} → Arg b → Table → Env Value → Result (𝒫 Value) b
⟦ a ⟧ₐ[ T ] ρ = fold-arg (𝕆-Clos5 T) init ρ a

⟦_⟧₊[_] : ∀ {bs} → Args bs → Table → Env Value → Tuple bs (Result (𝒫 Value))
⟦ args ⟧₊[ T ] ρ = fold-args (𝕆-Clos5 T) init ρ args

{- the function whose code is N, given the table T of the older
   definitions: its code takes the tuple of free variables X and then the
   argument Y -}
code : Table → AST → 𝒫 Value
code T N = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧[ T ] (Y • X • (λ _ → init))) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List AST → Table
table [] k = ∅
table (N ∷ Ns) k with k ≟ length Ns
... | yes _ = code (table Ns) N
... | no _ = table Ns k

{- the meaning of a whole program -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds M ⟧ₚ = ⟦ M ⟧[ table ds ] (λ _ → init)
