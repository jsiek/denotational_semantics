module ClosureConversion where

import Syntax
open import Primitives
open import ISWIMLanguage

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_; _+_; s≤s)
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
IR-sig (fun n) = suc n ∷ []
IR-sig (close n) = replicate (suc n) 0
IR-sig ir-app = 0 ∷ 0 ∷ []
IR-sig (ir-lit p k) = []

open Syntax using (Rename; _•_; ↑; ⦉_⦊)
module IRMod = Syntax.OpSig IROp IR-sig
open IRMod renaming (ABT to IR; `_ to ^_; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename;
   WF to ir-WF; FV? to ir-FV?; WF-op to ir-WF-op; WF-cons to ir-WF-cons;
   WF-nil to ir-WF-nil; WF-ast to ir-WF-ast; WF-bind to ir-WF-bind;
   Arg to ir-Arg; Args to ir-Args) public
open IRMod using ( _⨟_; exts-cons-shift; bind-ast)

pattern # p k = node (ir-lit p k) ir-nil 
pattern Ƒ n N = node (fun n) (ir-cons N ir-nil)
pattern ⟪_,_,_⟫ f n fvs = node (close n) (ir-cons (ir-ast f) fvs)
pattern _˙_ L M = node ir-app (ir-cons (ir-ast L) (ir-cons (ir-ast M) ir-nil))

num-FV : (n i : ℕ) → IR → ℕ
num-FV n 0 M = 0
num-FV n (suc i) M
    with ir-FV? M n
... | true = suc (num-FV (suc n) i M )
... | false = num-FV (suc n) i M 

{-

  The compressor function produces a renaming that maps all the free
  variables above 0 in a term into a contiguous sequence of numbers
  starting at 1.

-}

compressor : (n i k : ℕ) → (M : Term) → Rename
compressor n 0 k M = ↑ k
compressor n (suc i) k M
    with FV? M n
... | true = k • compressor (suc n) i (suc k) M 
... | false = k • compressor (suc n) i k M 

test-M : Term
test-M = (` 2) · (` 5)

test-cmp : Rename
test-cmp = 0 • compressor 1 5 1 test-M

_ : rename test-cmp test-M ≡ (` 1 ) · (` 2)
_ = refl

add-binds : (n : ℕ) → IR → ir-Arg n
add-binds zero N = ir-ast N
add-binds (suc n) N = ir-bind (add-binds n N)

fv-refs : (n i k : ℕ) → (M : IR) → ir-Args (replicate (num-FV n i M) 0)
fv-refs n zero k M = ir-nil
fv-refs n (suc i) k M
    with ir-FV? M n
... | true = ir-cons (ir-ast (^ n)) (fv-refs (suc n) i (suc k) M)
... | false = fv-refs (suc n) i k M

{-

 Closure Conversion 

 -}

𝐶 : (M : Term) → ∀{Γ} → {wf : WF Γ M} → IR
𝐶 (` x) {Γ} {wfM} = ^ x
𝐶 (ƛ N) {Γ} {WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)} =
  let ρ = compressor 1 Γ 1 N in
  let N′ = ir-rename ρ (𝐶 N {suc Γ} {wfN}) in
  let nfv = num-FV 1 Γ N′ in
  let fun = Ƒ nfv (ir-bind (add-binds nfv N′)) in
  ⟪ fun , nfv , fv-refs 1 Γ 1 N′ ⟫
𝐶 (L · M) {Γ}
   {WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))} =
   let L′ = 𝐶 L {wf = wfL} in
   let M′ = 𝐶 M {wf = wfM} in
   L′ ˙ M′
𝐶 ($ p k) {Γ} {wf} = # p k

{-

 Semantics of the IR language

 -}

curry-n : (n : ℕ) → ir-Arg n → Denotation
apply-n : (n : ℕ) → Denotation → ir-Args (replicate n 0) → Denotation
    
ℳ : IR → Denotation
ℳ (# P k) γ v = ℘ {P} k v
ℳ (^ x) γ v = v ⊑ γ x
ℳ (Ƒ n bN) γ v =
    curry-n (suc n) bN `∅ v
ℳ ⟪ L , n , As ⟫ =
    apply-n n (ℳ L) As
ℳ (L ˙ M) = (ℳ L) ● (ℳ M)

curry-n 0 (ir-ast N) = ℳ N
curry-n (suc n) (ir-bind bN) = ℱ (curry-n n bN)

apply-n zero D ir-nil = D
apply-n (suc n) D (ir-cons (ir-ast M) As) =
    let D′ = D ● ℳ M in
    apply-n n D′ As

{-

Correctness of Closure Conversion

-}

apply-curry : ∀{Γ : ℕ} {N : Term} {wfN : WF (suc Γ) N} {wfλN : WF Γ (ƛ N)}
  → ℳ (𝐶 N {suc Γ}{wfN}) ≃ ℰ N
  → ℳ (𝐶 (ƛ N) {Γ} {wfλN}) ≃ ℱ (ℰ N)
apply-curry {Γ} {N} {wfN}{wfλN} ℳ𝐶N≃ℰN = {!!}

𝐶-correct : ∀ Γ (M : Term) (wf : WF Γ M)
   → (ℳ (𝐶 M {Γ}{wf})) ≃ (ℰ M)
𝐶-correct Γ ($ p k) wf = ≃-refl
𝐶-correct Γ (` x) wf = ≃-refl
𝐶-correct Γ (ƛ N) wf@(WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)) =
   let IH = 𝐶-correct (suc Γ) N wfN in
      ℳ (𝐶 (ƛ N) {Γ} {wf})
   ≃⟨ apply-curry {Γ}{N}{wfN}{wf} IH ⟩
      ℱ (ℰ N)
   ≃⟨⟩
      ℰ (ƛ N)
   ■
𝐶-correct Γ (L · M)
            (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))) =
  let IH1 = 𝐶-correct Γ L wfL in
  let IH2 = 𝐶-correct Γ M wfM in
  ●-cong IH1 IH2

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
   renaming (ABT to IR2; Arg to Arg2; `_ to ´_; _⦅_⦆ to ir2-node;
      cons to ir2-cons; nil to ir2-nil;
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
ℒ (𝑓 n bN) = curry-n' n bN
    where
    curry-n' : (n : ℕ) → Arg2 n → Denotation
    curry-n' 0 (ir2-ast N) = ℒ N
    curry-n' (suc n) (ir2-bind bN) = ℱ (curry-n' n bN)
ℒ (L ∙ M) = (ℒ L) ● (ℒ M)
ℒ 〈〉 γ v = v ⊑ ⊥
ℒ (pair L M) = ⟬ ℒ L , ℒ M ⟭
ℒ (car M) = π₁ (ℒ M)
ℒ (cdr M) = π₂ (ℒ M)
