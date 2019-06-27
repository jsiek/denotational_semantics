module ClosureConversion where

open import Variables public
open import Primitives
open import ISWIM

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)

{-

  Target intermediate language of closure conversion

-}

data IROp : Set where
  fun : ℕ → IROp   {- number of parameters -}
  close : ℕ → IROp
  ir-app : IROp
  ir-lit : ∀{p : Prim} → rep p → IROp

IR-sig : IROp → List ℕ
IR-sig (fun n) = n ∷ []
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
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename) public
open IRMod using (_•_; _⨟_; ↑; exts-cons-shift)

FV : ∀{Γ} → Term Γ → Var Γ → Bool
FV {Γ} (` x) y
    with x var≟ y
... | yes _ = true
... | no _ = false
FV {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆) y = FV N (S y)
FV {Γ} (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) y = FV L y ∨ FV M y
FV {Γ} (lit {p} k ⦅ nil ⦆) y = false

FV′ : ∀{Γ} → Term Γ → Var Γ → List (Var Γ)
FV′ {Γ} M x
    with FV M x
... | true = x ∷ []
... | false = []

FVs : ∀{Γ} → (n : ℕ) → (lt : suc n ≤ Γ) → Term Γ → List (Var Γ)
FVs {Γ} zero lt M = FV′ M (ℕ→var zero lt)
FVs {Γ} (suc n) lt M =
  let ih = FVs n (≤-trans (n≤1+n (suc n)) lt) M in
  FV′ M (ℕ→var (suc n) lt) ++ ih

weaken : ∀{Δ} → Var Δ → Var (suc Δ)
weaken Z = Z
weaken (S x) = S (weaken x)



compressor : ∀{Γ} → (n : ℕ) → (lt : suc n ≤ Γ) → Term Γ
           → Σ[ Δ ∈ ℕ ] Rename Γ Δ
compressor {Γ} zero lt M = ⟨ suc zero , (λ x → Z) ⟩
compressor {Γ} (suc n) lt M
    with FV M (ℕ→var (suc n) lt)
... | false = compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | true
    with compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ρ ⟩ = ⟨ suc Δ , ρ′ ⟩
    where
    ρ′ : Rename Γ (suc Δ)
    ρ′ x
        with x var≟ (ℕ→var (suc n) lt)
    ... | yes eq = ℕ→var Δ ≤-refl
    ... | no neq = weaken (ρ x)


bind-ast : AST Γ → (n : ℕ) → Arg Γ n



convert-clos : ∀{Γ} → Term Γ → IR Γ
convert-clos (` x) = var x
convert-clos {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆)
    with compressor {suc Γ} Γ ≤-refl N
... | ⟨ Δ , ρ ⟩ =

  let N′ = ir-rename ρ (convert-clos N) in

  let f = node {Γ} (fun Δ) (ir-cons {!!} ir-nil) in
  {!node (close ?) f!}



convert-clos (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = {!!}
convert-clos (lit {p} k ⦅ nil ⦆) =
   node (ir-lit {p} k) ir-nil 
