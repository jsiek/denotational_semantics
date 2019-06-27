module ClosureConversion where

open import Variables public
open import Primitives
open import ISWIM

open import Data.Bool  
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; inspect; [_])

{-

  Target intermediate language of closure conversion

-}

data IROp : Set where
  fun : ℕ → IROp
  close : ℕ → IROp
  ir-app : IROp
  ir-lit : ∀{p : Prim} → rep p → IROp

IR-sig : IROp → List ℕ
IR-sig (fun n) = suc n ∷ []
IR-sig (close n) = L (suc n)
  where
  L : ℕ → List ℕ
  L 0 = []
  L (suc n) = 0 ∷ L n
IR-sig ir-app = 0 ∷ 0 ∷ []
IR-sig (ir-lit {p} k) = []

import Syntax3
module IRMod = Syntax3 IROp IR-sig
open IRMod renaming (AST to IR; `_ to var; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind) public
open IRMod using (_•_; _⨟_; ↑; exts-cons-shift)

FV : ∀{Γ} → Term Γ → Var Γ → Set
FV {Γ} (` x) y = (x ≡ y)
FV {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆) y = FV N (S y)
FV {Γ} (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) y = FV L y ⊎ FV M y
FV {Γ} (lit {p} k ⦅ nil ⦆) y = False


convert-clos : ∀{Γ} → Term Γ → IR Γ
convert-clos (` x) = var x
convert-clos {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆) =
  let n = num-FV (suc Γ) N in
  let f = node (fun {!!}) (ir-cons {!!} ir-nil) in
  {!node (close ?) f!}
  where
  num-FV : (Γ : ℕ) → AST Γ → ℕ
  num-FV zero N = 0
  num-FV (suc Γ) N =
    let fv = FV N (suc Γ) in
    {!!}

convert-clos (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = {!!}
convert-clos (lit {p} k ⦅ nil ⦆) =
   node (ir-lit {p} k) ir-nil 
