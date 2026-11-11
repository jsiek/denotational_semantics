{-

  Select instructions (CFGμ → X86μ), as typed select instructions
  (ISWIM/Compiler/Select.agda).

  * A slot is the typed index of CFGμ, in the same fixed frame, and an
    assignment to a slot becomes a write to that slot in place.
  * The code of a simple expression is selected in continuation-passing
    style (sel s o k): its value goes to %rax (ret) or to a slot (to x p),
    and then k runs, whatever the registers and the flag are.
  * callc f a: load fst f, %rax opens the closure f; load snd f, %rdi
    and movq a, %rsi give %rdi and %rsi the types callq needs.
  * fold a and unfold a are moves (↑, ↓).
  * case a x y l₁ l₂ is X86μ's case, the pseudo-instruction for testinl,
    the load of the payload and the jumps.
  * The start of a definition moves %rdi and %rsi to slots 0 and 1, the
    slots of its parameters.

-}

module FPC.Compiler.Select where

open import Language.Prim using (sub; eq)
open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; ⊑-∋)
import FPC.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import FPC.Language.Imp as I
open I using (⊆-refl)
open import FPC.Language.X86
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl)

atms : ∀ {Σ Δ Δs Γ I O F} → All (Atm Σ Δ I) Δs
  → All (λ A → Arg Σ (st Γ I O F) (ty A)) Δs
atms [] = []
atms (a ∷ as) = atom a ∷ atms as

{- where the value of a simple expression goes: %rax, or slot x, after
   which the rest starts with the initialized slots J -}
data Out {Δ : Ctx} (I : Inits Δ) (A : Type) : Inits Δ → Set where
  ret : Out I A I
  to : ∀ {J} (x : Δ ∋ A) → .(J ⊆ I ⊕ x) → Out I A J

after : ∀ {Δ} {I J : Inits Δ} {A} → Out I A J → Regs → Maybe (Open Δ) → Bool
  → St Δ
after {I = I} {A = A} ret Γ O F = st (Γ [ rax ↦ just (ty A) ]) I O F
after {J = J} (to x p) Γ O F = st Γ J nothing F

dst : ∀ {Δ} {I J : Inits Δ} {A} (o : Out I A J) {Γ O F}
  → Dst (st Γ I O F) (ty A) (after o Γ O F)
dst ret = reg rax
dst (to x p) = slot x p

{- the code of s into o, then k, with any registers and flag -}
sel : ∀ {Σ Δ R Bs A} {I J : Inits Δ} → I.Simple Σ Δ I A → (o : Out I A J)
  → (∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)) → ∀ {Γ O F}
    → Seq Σ Δ R Bs (st Γ I O F)
sel (I.atm a) o k = movq (atom a) (dst o) ∷ k
sel (I.pair c e) o k = alloc (pair (atom c) (atom e)) (dst o) ∷ k
sel (I.callc (var x i) a) o k =
  loadfst x i rax ∷ loadsnd rdi ∷ movq (atom a) (reg rsi)
    ∷ callq (reg rax refl) refl refl ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.tuple as) o k = alloc (tuple (atms as)) (dst o) ∷ k
sel (I.get i a) o k = load i (atom a) (dst o) ∷ k
sel (I.inl a) o k = alloc (inl (atom a)) (dst o) ∷ k
sel (I.inr a) o k = alloc (inr (atom a)) (dst o) ∷ k
sel (I.prim sub a b) o k =
  movq (atom a) (reg rax) ∷ subq (atom b) rax refl
  ∷ movq (reg rax refl) (dst o) ∷ k
sel (I.prim eq a b) o k = cmpq (atom b) (atom a) ∷ sete (dst o) ∷ k
sel (I.fold a) o k = movq (atom a ↑) (dst o) ∷ k
sel (I.unfold a) o k = movq (atom a ↓) (dst o) ∷ k

tail : ∀ {Σ Δ R Bs} {I : Inits Δ} (t : Tail Σ R Δ Bs I) → ∀ {Γ O F}
  → Seq Σ Δ R Bs (st Γ I O F)
tail (return s) = sel s ret (retq refl)
tail (seq x s p t) = sel s (to x p) (tail t)
tail (goto l) = jmp l
tail (case (var x i) y z l₁ l₂) = case x i y z l₁ l₂

blocks : ∀ {Σ Δ R Bs} (bs : C.Blocks Σ R Δ Bs) → Blocks Σ Δ R Bs
blocks C.[] = []
blocks (bs ▷ t) = blocks bs ▷ tail t

{- main, in its frame -}
main-body : ∀ {Σ R} → C.Body Σ R [] → Body Σ R begin
main-body (C.body Δ p bs t) = body Δ (blocks bs) (tail t)

{- a definition: its start moves its environment and argument to their
   slots, 0 and 1 -}
def-body : ∀ {Σ s} → C.Body Σ (DSig.cod s) (Args s)
  → Body Σ (DSig.cod s) (called s)
def-body (C.body Δ p bs t) =
  body Δ (blocks bs)
    (movq (reg rdi refl) (slot e (⊆-refl {I = none Δ ⊕ e}))
      ∷ movq (reg rsi refl) (slot a (⊆-refl {I = none Δ ⊕ e ⊕ a}))
      ∷ tail t)
  where
  e = ⊑-∋ p (S Z)
  a = ⊑-∋ p Z

{- the pass, for a whole program -}
select : ∀ {A} → C.Program A → Program A
select (C.program ds b) = program (All-map def-body ds) (main-body b)
