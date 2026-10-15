{-

  Select instructions (CFGμ → X86μ), as typed select instructions
  (Compiler/Select.agda).

  * A slot is the typed index of CFGμ; the frame of a body has as many
    slots as the deepest level its tails write (depth), and each write
    carries the proof that it is in the frame.
  * The code of a simple expression is selected in continuation-passing
    style (sel s o k): its value goes to %rax (ret) or to the next slot
    (to p), and then k runs, whatever the registers and the flag are.
  * callc f a: load fst f, %rax opens the closure f; load snd f, %rdi
    and movq a, %rsi give %rdi and %rsi the types callq needs.
  * fold a and unfold a are moves (↑, ↓).
  * case a p l₁ l₂ is X86μ's case, the pseudo-instruction for testinl,
    the load of the payload and je.
  * The start of a definition moves %rdi and %rsi to slots 0 and 1.

-}

module Mu.Compiler.Select where

open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Framework.Membership using (_⊑_; here⊑)
import Mu.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Mu.Language.Imp as I
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤m⊔n; m≤n⊔m)
open import Relation.Binary.PropositionalEquality using (refl)

{- the number of slots a tail uses -}
depth : ∀ {Σ R Bs Δ} → Tail Σ R Bs Δ → ℕ
depth {Δ = Δ} (return s) = length Δ
depth {Δ = Δ} (seq p s t) = length Δ ⊔ depth t
depth {Δ = Δ} (goto l) = length Δ
depth {Δ = Δ} (case {Δ'} a p l₁ l₂) = length Δ ⊔ suc (length Δ')

blocks-depth : ∀ {Σ R Bs} → C.Blocks Σ R Bs → ℕ
blocks-depth C.[] = 0
blocks-depth (bs ▷ t) = depth t ⊔ blocks-depth bs

depth-≥ : ∀ {Σ R Bs Δ} (t : Tail Σ R Bs Δ) → length Δ ≤ depth t
depth-≥ (return s) = ≤-refl
depth-≥ (seq p s t) = m≤m⊔n _ _
depth-≥ (goto l) = ≤-refl
depth-≥ (case a p l₁ l₂) = m≤m⊔n _ _

atms : ∀ {Σ Δ Δs Γ O F} → All (Atm Σ Δ) Δs → All (λ A → Arg Σ (st Γ Δ O F) (ty A)) Δs
atms [] = []
atms (a ∷ as) = atom a ∷ atms as

{- where the value of a simple expression goes: %rax, or the next slot -}
data Out (n : ℕ) (Δ : Ctx) (A : Type) : Ctx → Set where
  ret : Out n Δ A Δ
  to : ∀ {Δ'} (p : Δ' ⊑ Δ) → .(suc (length Δ') ≤ n) → Out n Δ A (A ∷ Δ')

after : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → Regs → Maybe (Open Δ) → Bool → St
after {Δ = Δ} {A} ret Γ O F = st (Γ [ rax ↦ just (ty A) ]) Δ O F
after {A = A} (to {Δ'} p _) Γ O F = st Γ (A ∷ Δ') nothing F

dst : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {Γ O F} → Dst n (st Γ Δ O F) (ty A) (after o Γ O F)
dst ret = reg rax
dst (to p lt) = slot p lt

{- the code of s into o, then k, with any registers and flag -}
sel : ∀ {Σ n R Bs Δ A Δ''} → I.Simple Σ Δ A → (o : Out n Δ A Δ'')
  → (∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)) → ∀ {Γ O F} → Seq Σ n R Bs (st Γ Δ O F)
sel (I.atm a) o k = movq (atom a) (dst o) ∷ k
sel (I.pack c e) o k = alloc (pair (atom c) (atom e)) (dst o) ∷ k
sel (I.callc (var x) a) o k =
  loadfst x rax ∷ loadsnd rdi ∷ movq (atom a) (reg rsi) ∷ callq (reg rax refl) refl refl ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.tuple as) o k = alloc (tuple (atms as)) (dst o) ∷ k
sel (I.get i a) o k = load i (atom a) (dst o) ∷ k
sel (I.inl a) o k = alloc (inl (atom a)) (dst o) ∷ k
sel (I.inr a) o k = alloc (inr (atom a)) (dst o) ∷ k
sel (I.prim sub a b) o k = movq (atom a) (reg rax) ∷ subq (atom b) rax refl ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.prim eq a b) o k = cmpq (atom b) (atom a) ∷ sete (dst o) ∷ k
sel (I.fold a) o k = movq (atom a ↑) (dst o) ∷ k
sel (I.unfold a) o k = movq (atom a ↓) (dst o) ∷ k

tail : ∀ {Σ n R Bs Δ} (t : Tail Σ R Bs Δ) → .(depth t ≤ n) → ∀ {Γ O F} → Seq Σ n R Bs (st Γ Δ O F)
tail (return s) le = sel s ret (retq refl)
tail (seq p s t) le = sel s (to p (≤-trans (depth-≥ t) (≤-trans (m≤n⊔m _ _) le))) (tail t (≤-trans (m≤n⊔m _ _) le))
tail (goto l) le = jmp l
tail (case (var x) p l₁ l₂) le = case x p (≤-trans (m≤n⊔m _ _) le) l₁ l₂

blocks : ∀ {Σ n R Bs} (bs : C.Blocks Σ R Bs) → .(blocks-depth bs ≤ n) → Blocks Σ n R Bs
blocks C.[] le = []
blocks (bs ▷ t) le = blocks bs (≤-trans (m≤n⊔m _ _) le) ▷ tail t (≤-trans (m≤m⊔n _ _) le)

{- main, in a frame of the slots its tails write -}
main-body : ∀ {Σ R} → C.Body Σ R [] → Body Σ R (entry [])
main-body (C.body bs t) = body (blocks-depth bs ⊔ depth t) (blocks bs (m≤m⊔n _ _)) (tail t (m≤n⊔m _ _))

{- a definition: its start moves its environment and argument to slots 0 and 1 -}
def-body : ∀ {Σ s} → C.Body Σ (DSig.cod s) (Args s) → Body Σ (DSig.cod s) (called s)
def-body (C.body bs t) =
  body (blocks-depth bs ⊔ depth t) (blocks bs (m≤m⊔n _ _))
    (movq (reg rdi refl) (slot here⊑ (≤-trans (s≤s z≤n) le)) ∷ movq (reg rsi refl) (slot here⊑ le) ∷ tail t (m≤n⊔m _ _))
  where le = ≤-trans (depth-≥ t) (m≤n⊔m _ _)

{- the pass, for a whole program -}
select : ∀ {A} → C.Program A → Program A
select (C.program ds b) = program (All-map def-body ds) (main-body b)
