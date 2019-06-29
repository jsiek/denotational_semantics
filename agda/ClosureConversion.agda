module ClosureConversion where

open import Variables public
open import Primitives
open import ISWIM

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≟_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; n≤1+n; +-identityʳ; ≤-step)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

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
IR-sig (close n) = replicate (suc n) 0
IR-sig ir-app = 0 ∷ 0 ∷ []
IR-sig (ir-lit {p} k) = []

import Syntax3
module IRMod = Syntax3 IROp IR-sig
open IRMod renaming (AST to IR; `_ to var; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename) public
open IRMod using (_•_; _⨟_; ↑; exts-cons-shift; bind-ast)

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

weaken-var : ∀{Δ} → Var Δ → Var (suc Δ)
weaken-var Z = Z
weaken-var (S x) = S (weaken-var x)

strengthen-var : ∀{Δ} → (x : Var (suc Δ)) → Var Δ ⊎ (x ≡ ℕ→var Δ ≤-refl )
strengthen-var {zero} Z = inj₂ refl
strengthen-var {zero} (S ())
strengthen-var {suc Δ} Z = inj₁ Z
strengthen-var {suc Δ} (S x)
    with strengthen-var {Δ} x
... | inj₁ x′ = inj₁ (S x′)
... | inj₂ eq rewrite eq = inj₂ refl

compressor′ : ∀{Γ} → (n : ℕ) → (lt : suc n ≤ Γ) → Term Γ
           → Σ[ Δ ∈ ℕ ] Rename Γ (suc Δ) × Rename (suc Δ) Γ
compressor′ {Γ} zero lt M = ⟨ zero , ⟨ (λ x → Z) , ρ-inv lt ⟩ ⟩
    where ρ-inv : 1 ≤ Γ → Rename 1 Γ
          ρ-inv (s≤s lt) x = Z
compressor′ {Γ} (suc n) lt M
    with FV M (ℕ→var (suc n) lt)
... | false = compressor′ {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | true
    with compressor′ {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ⟨ ρ , ρ-inv ⟩ ⟩ =
      ⟨ suc Δ , ⟨ ρ′ , ρ′-inv ⟩ ⟩
    where
    ρ′ : Rename Γ (suc (suc Δ))
    ρ′ x
        with x var≟ ℕ→var (suc n) lt
    ... | yes eq = ℕ→var (suc Δ) ≤-refl
    ... | no neq = weaken-var (ρ x)
    ρ′-inv : Rename (suc (suc Δ)) Γ
    ρ′-inv y
        with strengthen-var y
    ... | inj₁ y′ = ρ-inv y′
    ... | inj₂ eq rewrite eq = ℕ→var (suc n) lt
    

{-
compressor : ∀{Γ} → (n : ℕ) → (lt : suc n ≤ Γ) → Term Γ
           → Σ[ Δ ∈ ℕ ] Rename Γ Δ × Δ ≤ suc n
compressor {Γ} zero lt M =
  ⟨ suc zero , ⟨ (λ _ → Z) , ≤-refl ⟩ ⟩
compressor {Γ} (suc n) lt M
    with FV M (ℕ→var (suc n) lt)
... | false
    with compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ⟨ ρ , lt2 ⟩ ⟩ =    
      ⟨ Δ , ⟨ ρ , ≤-step lt2 ⟩ ⟩
compressor {Γ} (suc n) lt M | true
    with compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ⟨ ρ , lt2 ⟩ ⟩ =
      ⟨ suc Δ , ⟨ ρ′ , ≤-trans (_≤_.s≤s lt2) ≤-refl ⟩ ⟩
    where
    ρ′ : Rename Γ (suc Δ)
    ρ′ x
        with x var≟ (ℕ→var (suc n) lt)
    ... | yes eq = ℕ→var Δ ≤-refl
    ... | no neq = weaken-var (ρ x)
-}

convert-clos : ∀{Γ} → Term Γ → IR Γ
convert-clos (` x) = var x
convert-clos {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆)
    with compressor′ {suc Γ} Γ ≤-refl N
... | ⟨ Δ , ⟨ ρ , ρ-inv ⟩ ⟩
    with ir-rename ρ (convert-clos N)
... | N′ =
    let f = ir-rename ρ′ (node {0} (fun (suc Δ)) (ir-cons (N′′ N′) ir-nil)) in
    node {Γ} (close (suc Δ)) (ir-cons (ir-ast f)
                                      (free-vars {Δ} ρ-inv (suc Δ) {≤-refl}))
    where
    N′′ : IR (suc Δ) → Arg 0 (suc Δ)
    N′′ N′ rewrite sym (+-identityʳ Δ)        {- ugh! -}
        with bind-ast {0} (suc Δ) N′
    ... | x rewrite +-identityʳ Δ = x

    ρ′ : Rename 0 Γ
    ρ′ ()

    free-vars : ∀{Δ} → Rename (suc Δ) (suc Γ) → (n : ℕ) → {lt : n ≤ suc Δ}
              → Args Γ (replicate n 0)
    free-vars {Δ} ρ-inv zero {lt} = ir-nil
    free-vars {Δ} ρ-inv (suc n) {s≤s lt} =
       let x : Var (suc Δ)
           x = ℕ→var n (s≤s lt) in
       let x′ = ρ-inv x in
       ir-cons (ir-ast (var {!!})) (free-vars {Δ} ρ-inv n {≤-step lt})


convert-clos (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = {!!}
convert-clos (lit {p} k ⦅ nil ⦆) =
   node (ir-lit {p} k) ir-nil 
