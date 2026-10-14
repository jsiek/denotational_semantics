{-

  Typed select instructions (CFGᵀ → X86ᵀ), after Essentials of
  Compilation: the instructions of select into untyped X86
  (Compiler/SelectX86.agda), typed (Language/Typed/X86.agda). Without
  the types they are the same instructions
  (proof/Compiler/SelectErase.agda, Theorems/Erasure.agda).

  * A slot is the typed index of CFGᵀ; the frame of a body has as many
    slots as the deepest level its tails write (depth),
    and each write carries the proof that it is in the frame.
  * The code of a simple expression is selected in continuation-passing
    style (sel s o k): its value goes to %rax (ret) or to the next slot
    (to p), and then k runs, whatever the registers and the flag are.
  * callc f a: load fst f, %rax opens the closure f; load snd f, %rdi
    and movq a, %rsi give %rdi and %rsi the types callq needs.
  * project t a is chk t a, the check and the move.
  * The start of a definition moves %rdi and %rsi to slots 0 and 1.

-}

module Compiler.Select where

open import Language.Prim using (sub; eq)
open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Language.Typed.Imp as I
open import Language.Typed.X86

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All) renaming (map to All-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤m⊔n; m≤n⊔m)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

{- the number of slots a tail uses -}
depth : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → ℕ
depth {Δ = Δ} (return s) = length Δ
depth {Δ = Δ} (seq p s t) = length Δ ⊔ depth t
depth {Δ = Δ} (goto l) = length Δ
depth {Δ = Δ} (case {Δ'} a p l₁ l₂) = length Δ ⊔ suc (length Δ')

blocks-depth : ∀ {Σ Bs} → C.Blocks Σ Bs → ℕ
blocks-depth C.[] = 0
blocks-depth (bs ▷ t) = depth t ⊔ blocks-depth bs

depth-≥ : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) → length Δ ≤ depth t
depth-≥ (return s) = ≤-refl
depth-≥ (seq p s t) = m≤m⊔n _ _
depth-≥ (goto l) = ≤-refl
depth-≥ (case a p l₁ l₂) = m≤m⊔n _ _

atms : ∀ {Σ Δ m Γ O F} → Vec (Atm Σ Δ Any) m → Vec (Arg Σ (st Γ Δ O F) (ty Any)) m
atms [] = []
atms (a ∷ as) = atom a ∷ atms as

{- where the value of a simple expression goes: %rax, or the next slot -}
data Out (n : ℕ) (Δ : Ctx) (A : Ty) : Ctx → Set where
  ret : Out n Δ A Δ
  to : ∀ {Δ'} (p : Δ' ⊑ Δ) → .(suc (length Δ') ≤ n) → Out n Δ A (A ∷ Δ')

after : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → Regs → Maybe (Δ ∋ ⟪ fun ⟫) → Bool → St
after {Δ = Δ} {A} ret Γ O F = st (Γ [ rax ↦ just (ty A) ]) Δ O F
after {A = A} (to {Δ'} p _) Γ O F = st Γ (A ∷ Δ') nothing F

dst : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {Γ O F} → Dst n (st Γ Δ O F) (ty A) (after o Γ O F)
dst ret = reg rax
dst (to p lt) = slot p lt

{- the code of s into o, then k, with any registers and flag -}
sel : ∀ {Σ n Bs Δ A Δ''} → I.Simple Σ Δ A → (o : Out n Δ A Δ'')
  → (∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)) → ∀ {Γ O F} → Seq Σ n Bs (st Γ Δ O F)
sel (I.atm a) o k = movq (atom a) (dst o) ∷ k
sel (I.pack c e) o k = alloc (pair (atom c) (atom e)) (dst o) ∷ k
sel (I.callc (var x) a) o k =
  loadfst x rax ∷ loadsnd rdi ∷ movq (atom a) (reg rsi) ∷ callq (reg rax refl) refl refl ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.tuple as) o k = alloc (tuple (atms as)) (dst o) ∷ k
sel (I.get i a) o k = load (get i) (atom a) (dst o) ∷ k
sel (I.inl a) o k = alloc (inl (atom a)) (dst o) ∷ k
sel (I.inr a) o k = alloc (inr (atom a)) (dst o) ∷ k
sel (I.prim sub a b) o k = movq (atom a) (reg rax) ∷ subq (atom b) rax refl ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.prim eq a b) o k = cmpq (atom b) (atom a) ∷ sete (dst o) ∷ k
sel (I.inject G a) o k = movq (atom a ↑) (dst o) ∷ k
sel (I.project t (var x)) o k = chk t x (dst o) ∷ k

tail : ∀ {Σ n Bs Δ} (t : Tail Σ Bs Δ) → .(depth t ≤ n) → ∀ {Γ O F} → Seq Σ n Bs (st Γ Δ O F)
tail (return s) le = sel s ret (retq refl)
tail (seq p s t) le = sel s (to p (≤-trans (depth-≥ t) (≤-trans (m≤n⊔m _ _) le))) (tail t (≤-trans (m≤n⊔m _ _) le))
tail (goto l) le = jmp l
tail (case a p l₁ l₂) le = testinl (atom a) ∷ load payload (atom a) (slot p (≤-trans (m≤n⊔m _ _) le)) ∷ je l₁ l₂

blocks : ∀ {Σ n Bs} (bs : C.Blocks Σ Bs) → .(blocks-depth bs ≤ n) → Blocks Σ n Bs
blocks C.[] le = []
blocks (bs ▷ t) le = blocks bs (≤-trans (m≤n⊔m _ _) le) ▷ tail t (≤-trans (m≤m⊔n _ _) le)

{- main, in a frame of the slots its tails write -}
main-body : ∀ {Σ} → C.Body Σ [] → Body Σ (entry [])
main-body (C.body bs t) = body (blocks-depth bs ⊔ depth t) (blocks bs (m≤m⊔n _ _)) (tail t (m≤n⊔m _ _))

{- a definition: its start moves its environment and argument to slots 0 and 1 -}
def-body : ∀ {Σ m} → C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ []) → Body Σ (called m)
def-body (C.body bs t) =
  body (blocks-depth bs ⊔ depth t) (blocks bs (m≤m⊔n _ _))
    (movq (reg rdi refl) (slot here⊑ (≤-trans (s≤s z≤n) le)) ∷ movq (reg rsi refl) (slot here⊑ le) ∷ tail t (m≤n⊔m _ _))
  where le = ≤-trans (depth-≥ t) (m≤n⊔m _ _)

{- the pass, for a whole program -}
select : C.Program → Program
select (C.program ds b) = program (All-map def-body ds) (main-body b)
