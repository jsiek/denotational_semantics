module ClosureConversion where

open import Variables public
open import Primitives
open import ISWIM

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _≟_; _+_; ∣_-_∣)
open import Data.Nat.Properties
   using (≤-refl; ≤-trans; n≤1+n; +-comm; ≤-step; +-suc)
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

weaken : ∀{Δ} → Var Δ → Var (suc Δ)
weaken Z = Z
weaken (S x) = S (weaken x)

{-
n-0≡n : ∀{n : ℕ} → ∣ n - 0 ∣ ≡ n
n-0≡n {zero} = refl
n-0≡n {suc n} = refl
-}

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
    ... | no neq = weaken (ρ x)


n≤m→m≡k+n : ∀{n m} → n ≤ m → Σ[ k ∈ ℕ ] m ≡ k + n
n≤m→m≡k+n {.0} {m} _≤_.z≤n =
  ⟨ m , G ⟩
  where
  G : m ≡ m + 0
  G =
    begin
      m
    ≡⟨⟩
      0 + m
    ≡⟨ +-comm 0 m ⟩
      m + 0
    ∎
n≤m→m≡k+n {suc n} {suc m} (_≤_.s≤s n≤m)
    with n≤m→m≡k+n {n}{m} n≤m
... | ⟨ k , eq ⟩ rewrite eq =   
      ⟨ k , sym (+-suc k n) ⟩

convert-clos : ∀{Γ} → Term Γ → IR Γ
convert-clos (` x) = var x
convert-clos {Γ} (lam ⦅ cons (bind (ast N)) nil ⦆)
    with compressor {suc Γ} Γ ≤-refl N
... | ⟨ Δ , ⟨ ρ , lt ⟩ ⟩
    with n≤m→m≡k+n lt
... | ⟨ k , eq ⟩ rewrite eq =     

  let N′ = ir-rename ρ (convert-clos N) in
  let N′′ = bind-ast {0} Δ (G N′) in

  let f = node {Γ} (fun Δ) (ir-cons {!!} ir-nil) in
  {!node (close ?) f!}

  where
  G : IR Δ → IR (Δ + 0)
  G N = {!!}


convert-clos (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) = {!!}
convert-clos (lit {p} k ⦅ nil ⦆) =
   node (ir-lit {p} k) ir-nil 
