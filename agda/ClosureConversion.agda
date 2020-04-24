module ClosureConversion where

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

import Syntax
open import ValueConst
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import CurryConst
open import ModelCurryConst
open import ModelCallByValue value_struct ordering consistent ℱ model_curry

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

open Syntax using (Rename; _•_; ↑)
module IRMod = Syntax.OpSig IROp IR-sig
open IRMod renaming (ABT to IR; `_ to ^_; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename) public
open IRMod using ( _⨟_; exts-cons-shift; bind-ast)

pattern # p k = node (ir-lit p k) ir-nil 
pattern Ƒ n N = node (fun n) (ir-cons N ir-nil)
pattern ⟪_,_,_⟫ f n fvs = node (close n) (ir-cons (ir-ast f) fvs)
pattern _˙_ L M = node ir-app (ir-cons (ir-ast L) (ir-cons (ir-ast M) ir-nil))

FV : Term → Var → Bool
FV (` x) y
    with x ≟ y
... | yes _ = true
... | no _ = false
FV (ƛ N) y = FV N (suc y)
FV (L · M) y = FV L y ∨ FV M y
FV ($ p k) y = false

FV′ : Term → Var → List Var
FV′ M x
    with FV M x
... | true = x ∷ []
... | false = []

FVs : (n : ℕ) → Term → List Var
FVs zero M = FV′ M zero
FVs (suc n) M =
  let ih = FVs n M in
  FV′ M (suc n) ++ ih

weaken-var : Var → Var
weaken-var 0 = 0
weaken-var (suc x) = suc (weaken-var x)

pos-var : Var → Set
pos-var 0 = False
pos-var (suc x) = True

prev-var : (x : Var) → {nz : pos-var x} → Var
prev-var 0 {()}
prev-var (suc x) {nz} = x

{-
strengthen-var : ∀{Δ} → (x : Var) → Var ⊎ (x ≡ Δ)
strengthen-var {zero} 0 = inj₂ refl
strengthen-var {zero} (suc ())
strengthen-var {suc Δ} 0 = inj₁ 0
strengthen-var {suc Δ} (suc x)
    with strengthen-var {Δ} x
... | inj₁ x′ = inj₁ (suc x′)
... | inj₂ eq rewrite eq = inj₂ refl
-}

{-
pos-var-suc : ∀{Γ n : ℕ}{lt} → pos-var (suc n)
pos-var-suc {zero} {n} {()}
pos-var-suc {suc Γ} {n} {lt} = tt
-}
{-

  The compressor function produces a renaming for all the
  free variables in Γ, compressing them into suc Δ.
  (We write suc Δ instead of Δ because it is always greater than
  zero.)

-}
{-  
compressor : ∀{Γ} → (n : ℕ) → (lt : n < Γ) → Term
           → Σ[ Δ ∈ ℕ ] Σ[ ρ ∈ Rename ]
             Σ[ ρ-inv ∈ Rename ] (∀{x} → pos-var (ρ-inv (suc x)))
compressor {Γ} zero lt M = ⟨ zero , ⟨ (λ x → 0) , ⟨ ρ-inv lt , (λ {}) ⟩ ⟩ ⟩
    where ρ-inv : 1 ≤ Γ → Rename 1 Γ
          ρ-inv (s≤s lt) x = 0
compressor {Γ} (suc n) lt M
    with FV M (suc n)
... | false = compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | true
    with compressor {Γ} n (≤-trans (n≤1+n (suc n)) lt) M
... | ⟨ Δ , ⟨ ρ , ⟨ ρ-inv , nz ⟩ ⟩ ⟩ =
      ⟨ suc Δ , ⟨ ρ′ , ⟨ ρ′-inv , G ⟩ ⟩ ⟩
    where
    ρ′ : Rename Γ (suc (suc Δ))
    ρ′ x
        with x ≟ (suc n)
    ... | yes eq = (suc Δ)
    ... | no neq = weaken-var (ρ x)
    
    ρ′-inv : Rename (suc (suc Δ)) Γ
    ρ′-inv y = ?
{-
        with strengthen-var y
    ... | inj₁ y′ = ρ-inv y′
    ... | inj₂ eq rewrite eq = (suc n)
-}
    G : ∀{x : Var (suc Δ)} → pos-var (ρ′-inv (suc x))
    G {x} = ?
{-
        with strengthen-var x
    ... | inj₁ x′ = nz
    ... | inj₂ eq rewrite eq = pos-var-suc
-}
-}

{-

 Closure conversion 

 -}


convert-clos : Term → IR
convert-clos (` x) = ^ x
convert-clos (ƛ N) = ?
{-
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
    let f = ir-rename ρ′ (Ƒ (suc Δ) (N′′ N′)) in
    ⟪ f , Δ , free-vars {Δ} {≤-refl} ⟫
    
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
           y = ρ-inv (suc n) in
       ir-cons (ir-ast (^ (prev-var y {pos}))) (free-vars {n} {≤-step lt})
-}
convert-clos (L · M) =
   let L′ = convert-clos L in
   let M′ = convert-clos M in
   L′ ˙ M′
convert-clos ($ p k) = # p k

{-

 Semantics of the target language

 -}


ℳ : IR → Denotation
ℳ (# P k) γ v = ℘ {P} k v
ℳ (^ x) γ v = v ⊑ γ x
ℳ (Ƒ n bN) =
    curry-n n bN
    where
    curry-n : (n : ℕ) → Arg n → Denotation
    curry-n 0 (ir-ast N) = ℳ N
    curry-n (suc n) (ir-bind bN) = ℱ (curry-n n bN)
ℳ ⟪ L , n , As ⟫ =
    apply-n n (ℳ L) As
    where
    apply-n : (n : ℕ) → Denotation → Args (replicate n 0) → Denotation
    apply-n zero D ir-nil = D
    apply-n (suc n) D (ir-cons (ir-ast M) As) =
        let D′ = D ● ℳ M in
        apply-n n D′ As
ℳ (L ˙ M) = (ℳ L) ● (ℳ M)

{-

  A lower-level intermediate language that represents
  closures as tuples.

-}

data IR2Op : Set where
  ir2-fun : ℕ → IR2Op
  tuple-nil : IR2Op
  tuple-cons : IR2Op
  ir2-car : IR2Op
  ir2-cdr : IR2Op
  ir2-app : IR2Op
  ir2-lit : (p : Prim) → rep p → IR2Op

IR2-sig : IR2Op → List ℕ
IR2-sig (ir2-fun n) = n ∷ []
IR2-sig tuple-nil = []
IR2-sig tuple-cons = 0 ∷ 0 ∷ []
IR2-sig ir2-car = 0 ∷ []
IR2-sig ir2-cdr = 0 ∷ []
IR2-sig ir2-app = 0 ∷ 0 ∷ []
IR2-sig (ir2-lit p k) = []

module IR2Mod = Syntax.OpSig IR2Op IR2-sig
open IR2Mod
   renaming (ABT to IR2; Arg to Arg2; `_ to ´_; _⦅_⦆ to ir2-node; cons to ir2-cons; nil to ir2-nil;
      ast to ir2-ast; bind to ir2-bind)

pattern ! p k = ir2-node (ir2-lit p k) ir2-nil
pattern 𝑓 n N = ir2-node (ir2-fun n) (ir2-cons N ir2-nil)
pattern _∙_ L M = ir2-node ir2-app (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern 〈〉 = ir2-node tuple-nil ir2-nil
pattern pair L M = ir2-node tuple-cons (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern car M = ir2-node ir2-car (ir2-cons (ir2-ast M) ir2-nil)
pattern cdr M = ir2-node ir2-cdr (ir2-cons (ir2-ast M) ir2-nil)

⟬_,_⟭ : Denotation → Denotation → Denotation
⟬_,_⟭ D₁ D₂ γ ⊥ = False
⟬_,_⟭ D₁ D₂ γ (const k) = False
⟬_,_⟭ D₁ D₂ γ (v₁ ↦ v₂) = const 0 ⊑ v₁ × D₁ γ v₂ ⊎ const 1 ⊑ v₁ × D₂ γ v₂
⟬_,_⟭ D₁ D₂ γ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ γ v₁ × ⟬ D₁ , D₂ ⟭ γ v₂

π₁ : Denotation → Denotation
π₁ D = D ● (λ γ v → ℘ {base Nat} 0 v)

π₂ : Denotation → Denotation
π₂ D = D ● (λ γ v → ℘ {base Nat} 1 v)

ℒ : IR2 → Denotation
ℒ (! P k) γ v = ℘ {P} k v
ℒ (´ x) γ v = (v ⊑ γ x)
ℒ (𝑓 n bN) = curry-n n bN
    where
    curry-n : (n : ℕ) → Arg2 n → Denotation
    curry-n 0 (ir2-ast N) = ℒ N
    curry-n (suc n) (ir2-bind bN) = ℱ (curry-n n bN)
ℒ (L ∙ M) = (ℒ L) ● (ℒ M)
ℒ 〈〉 γ v = v ⊑ ⊥
ℒ (pair L M) = ⟬ ℒ L , ℒ M ⟭
ℒ (car M) = π₁ (ℒ M)
ℒ (cdr M) = π₂ (ℒ M)
