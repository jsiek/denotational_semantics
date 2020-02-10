module ClosureConversion where

open import Variables public
open import Primitives
open import ISWIM

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_; s≤s)
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
  ir-lit : (p : Prim) → rep p → IROp

IR-sig : IROp → List ℕ
IR-sig (fun n) = n ∷ []
IR-sig (close n) = replicate (suc n) 0
IR-sig ir-app = 0 ∷ 0 ∷ []
IR-sig (ir-lit p k) = []

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
FV {Γ} (ƛ N) y = FV N (S y)
FV {Γ} (L · M) y = FV L y ∨ FV M y
FV {Γ} ($ p k) y = false

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

pos-var : ∀{Γ} → Var Γ → Set
pos-var {.(suc _)} Z = False
pos-var {.(suc _)} (S x) = True

prev-var : ∀{Γ} → (x : Var (suc Γ)) → {nz : pos-var x} → Var Γ
prev-var {Γ} Z {()}
prev-var {Γ} (S x) {nz} = x

strengthen-var : ∀{Δ} → (x : Var (suc Δ)) → Var Δ ⊎ (x ≡ ℕ→var Δ ≤-refl )
strengthen-var {zero} Z = inj₂ refl
strengthen-var {zero} (S ())
strengthen-var {suc Δ} Z = inj₁ Z
strengthen-var {suc Δ} (S x)
    with strengthen-var {Δ} x
... | inj₁ x′ = inj₁ (S x′)
... | inj₂ eq rewrite eq = inj₂ refl


pos-var-suc : ∀{Γ n}{lt} → pos-var (ℕ→var {Γ} (suc n) lt)
pos-var-suc {zero} {n} {()}
pos-var-suc {suc Γ} {n} {lt} = tt

{-

  The compressor function produces a renaming for all the
  free variables in Γ, compressing them into suc Δ.
  (We write suc Δ instead of Δ because it is always greater than
  zero.)

-}
  
compressor : ∀{Γ} → (n : ℕ) → (lt : n < Γ) → Term Γ
           → Σ[ Δ ∈ ℕ ] Σ[ ρ ∈ Rename Γ (suc Δ) ]
             Σ[ ρ-inv ∈ Rename (suc Δ) Γ ] (∀{x} → pos-var (ρ-inv (S x)))
compressor {Γ} zero lt M = ⟨ zero , ⟨ (λ x → Z) , ⟨ ρ-inv lt , (λ {}) ⟩ ⟩ ⟩
    where ρ-inv : 1 ≤ Γ → Rename 1 Γ
          ρ-inv (s≤s lt) x = Z
compressor {Γ} (suc n) lt M
    with FV M (ℕ→var (suc n) lt)
... | false = compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | true
    with compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ⟨ ρ , ⟨ ρ-inv , nz ⟩ ⟩ ⟩ =
      ⟨ suc Δ , ⟨ ρ′ , ⟨ ρ′-inv , G ⟩ ⟩ ⟩
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

    G : ∀{x : Var (suc Δ)} → pos-var (ρ′-inv (S x))
    G {x}
        with strengthen-var x
    ... | inj₁ x′ = nz
    ... | inj₂ eq rewrite eq = pos-var-suc

{-

 Closure conversion 

 -}


convert-clos : ∀{Γ} → Term Γ → IR Γ
convert-clos (` x) = var x
convert-clos {Γ} (ƛ N)
    with compressor {suc Γ} Γ ≤-refl N
... | ⟨ Δ , ⟨ ρ , ⟨ ρ-inv , pos ⟩ ⟩ ⟩
    with ir-rename ρ (convert-clos N)
... | N′ =
    {-
    Δ is the number of free variables, not counting the 0 variable.
    If there are no free variables in N then Δ = 0.
    Those variables have index 1, 2, ..., Δ

    ρ maps from suc Γ to suc Δ
    ρ-inv maps from suc Δ to suc Γ
    -}
    let f = ir-rename ρ′ (node {0} (fun (suc Δ)) (ir-cons (N′′ N′) ir-nil)) in
    node {Γ} (close Δ) (ir-cons (ir-ast f)
                                (free-vars {Δ} {≤-refl}))
    where
    N′′ : IR (suc Δ) → Arg 0 (suc Δ)
    N′′ N′ rewrite sym (+-identityʳ Δ)        {- ugh! -}
        with bind-ast {0} (suc Δ) N′
    ... | x rewrite +-identityʳ Δ = x

    ρ′ : Rename 0 Γ
    ρ′ ()

    free-vars : ∀{n : ℕ}{lt : n ≤ Δ}
              → Args Γ (replicate n 0)
    free-vars {zero} {lt} = ir-nil
    free-vars {suc n} {s≤s {n = Δ′} lt} =     {- Δ = suc Δ′ -}
       let y : Var (suc Γ)
           y = ρ-inv (ℕ→var {suc Δ} (suc n) (s≤s (s≤s lt))) in
       ir-cons (ir-ast (var (prev-var y {pos}))) (free-vars {n} {≤-step lt})
convert-clos (L · M) =
   let L′ = convert-clos L in
   let M′ = convert-clos M in
   node ir-app (ir-cons (ir-ast L′) (ir-cons (ir-ast M′) ir-nil))
convert-clos ($ p k) =
   node (ir-lit p k) ir-nil 

{-

 Semantics of the target language

 -}


open import ValueConst
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import CurryConst
open import ModelCurryConst
open import ModelCallByValue value_struct ordering consistent ℱ model_curry


ℳ : ∀{Γ} → IR Γ → Denotation Γ
ℳ (node (ir-lit P k) ir-nil) γ v = ℘ {P} k v
ℳ {Γ} (var x) γ v =
    v ⊑ γ x
ℳ {Γ} (node (fun n) (ir-cons bN ir-nil)) =
    curry-n n bN
    where
    curry-n : ∀{Γ} → (n : ℕ) → Arg Γ n → Denotation Γ
    curry-n {Γ} 0 (ir-ast N) = ℳ N
    curry-n {Γ} (suc n) (ir-bind bN) =
      ℱ (curry-n {suc Γ} n bN)
ℳ {Γ} (node (close n) (ir-cons (ir-ast L) As)) =
    apply-n n (ℳ {Γ} L) As
    where
    apply-n : (n : ℕ) → Denotation Γ → Args Γ (replicate n 0) → Denotation Γ
    apply-n zero D ir-nil = D
    apply-n (suc n) D (ir-cons (ir-ast M) As) =
        let D′ = D ● ℳ {Γ} M in
        apply-n n D′ As
ℳ {Γ} (node ir-app (ir-cons (ir-ast L) (ir-cons (ir-ast M) ir-nil))) =
    (ℳ L) ● (ℳ M)
