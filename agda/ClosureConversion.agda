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

import Syntax3
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

module IRMod = Syntax3 IROp IR-sig
open IRMod renaming (AST to IR; `_ to ^_; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename) public
open IRMod using (_•_; _⨟_; ↑; exts-cons-shift; bind-ast)

pattern # p k = node (ir-lit p k) ir-nil 
pattern Ƒ n N = node (fun n) (ir-cons N ir-nil)
pattern ⟪_,_,_⟫ n f fvs = node (close n) (ir-cons (ir-ast f) fvs)
pattern _˙_ L M = node ir-app (ir-cons (ir-ast L) (ir-cons (ir-ast M) ir-nil))

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
convert-clos (` x) = ^ x
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
    let f = ir-rename ρ′ (Ƒ (suc Δ) (N′′ N′)) in
    ⟪ Δ , f , free-vars {Δ} {≤-refl} ⟫
    
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
       ir-cons (ir-ast (^ (prev-var y {pos}))) (free-vars {n} {≤-step lt})
convert-clos (L · M) =
   let L′ = convert-clos L in
   let M′ = convert-clos M in
   L′ ˙ M′
convert-clos ($ p k) = # p k

{-

 Semantics of the target language

 -}


ℳ : ∀{Γ} → IR Γ → Denotation Γ
ℳ (# P k) γ v = ℘ {P} k v
ℳ {Γ} (^ x) γ v = v ⊑ γ x
ℳ {Γ} (Ƒ n bN) =
    curry-n n bN
    where
    curry-n : ∀{Γ} → (n : ℕ) → Arg Γ n → Denotation Γ
    curry-n {Γ} 0 (ir-ast N) = ℳ N
    curry-n {Γ} (suc n) (ir-bind bN) =
      ℱ (curry-n {suc Γ} n bN)
ℳ {Γ} ⟪ n , L , As ⟫ =
    apply-n n (ℳ {Γ} L) As
    where
    apply-n : (n : ℕ) → Denotation Γ → Args Γ (replicate n 0) → Denotation Γ
    apply-n zero D ir-nil = D
    apply-n (suc n) D (ir-cons (ir-ast M) As) =
        let D′ = D ● ℳ {Γ} M in
        apply-n n D′ As
ℳ {Γ} (L ˙ M) = (ℳ L) ● (ℳ M)

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

module IR2Mod = Syntax3 IR2Op IR2-sig
open IR2Mod
   renaming (AST to IR2; Arg to Arg2; `_ to ´_; _⦅_⦆ to ir2-node; cons to ir2-cons; nil to ir2-nil;
      ast to ir2-ast; bind to ir2-bind)

pattern ! p k = ir2-node (ir2-lit p k) ir2-nil
pattern 𝑓 n N = ir2-node (ir2-fun n) (ir2-cons N ir2-nil)
pattern _∙_ L M = ir2-node ir2-app (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern 〈〉 = ir2-node tuple-nil ir2-nil
pattern pair L M = ir2-node tuple-cons (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern car M = ir2-node ir2-car (ir2-cons (ir2-ast M) ir2-nil)
pattern cdr M = ir2-node ir2-cdr (ir2-cons (ir2-ast M) ir2-nil)

⟬_,_⟭ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
⟬_,_⟭ {Γ} D₁ D₂ γ ⊥ = False
⟬_,_⟭ {Γ} D₁ D₂ γ (const k) = False
⟬_,_⟭ {Γ} D₁ D₂ γ (v₁ ↦ v₂) = const 0 ⊑ v₁ × D₁ γ v₂ ⊎ const 1 ⊑ v₁ × D₂ γ v₂
⟬_,_⟭ {Γ} D₁ D₂ γ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ γ v₁ × ⟬ D₁ , D₂ ⟭ γ v₂

π₁ : ∀{Γ} → Denotation Γ → Denotation Γ
π₁ {Γ} D = D ● (λ γ v → ℘ {base Nat} 0 v)

π₂ : ∀{Γ} → Denotation Γ → Denotation Γ
π₂ {Γ} D = D ● (λ γ v → ℘ {base Nat} 1 v)

ℒ : ∀{Γ} → IR2 Γ → Denotation Γ
ℒ (! P k) γ v = ℘ {P} k v
ℒ (´ x) γ v = (v ⊑ γ x)
ℒ (𝑓 n bN) = curry-n n bN
    where
    curry-n : ∀{Γ} → (n : ℕ) → Arg2 Γ n → Denotation Γ
    curry-n {Γ} 0 (ir2-ast N) = ℒ N
    curry-n {Γ} (suc n) (ir2-bind bN) =
      ℱ (curry-n {suc Γ} n bN)
ℒ (L ∙ M) = (ℒ L) ● (ℒ M)
ℒ 〈〉 γ v = v ⊑ ⊥
ℒ (pair L M) = ⟬ ℒ L , ℒ M ⟭
ℒ (car M) = π₁ (ℒ M)
ℒ (cdr M) = π₂ (ℒ M)
