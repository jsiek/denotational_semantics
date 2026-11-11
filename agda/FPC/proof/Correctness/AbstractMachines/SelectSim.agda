{-

  Correctness of select instructions (CFGμ → X86μ, FPC/Compiler/Select.agda):
  a simulation of the CFGμ machine by the X86μ machine (Both,
  proof/Framework/Both.agda), as for typed select instructions
  (ISWIM/proof/Correctness/CEK/SelectSim.agda).

  Both machines hold the same values, and the X86μ frame is the CFGμ
  frame: both are fixed frames with the same slots, written in place.
  A state of CFGμ is matched by the code selected for its tail, in the
  same frame, with any registers and flag (Match); the X86μ call stack
  holds, for each CFGμ return frame, the caller's frame and the move of
  %rax where the caller wants it (_~_). One CFGμ step (a statement) is
  matched by the instructions selected for it: they write its value to
  its destination (xval), or call (xcall). A call starts the X86μ body
  in its frame with no slot initialized; its first two moves write the
  environment and the argument to their slots, which gives the frame
  that the CFGμ body starts with (start≡). Neither machine fails.

-}

module FPC.proof.Correctness.AbstractMachines.SelectSim where

open import Language.Prim using (sub; eq)
open import FPC.Language.Type
open import Framework.Membership using (_⊑_; ⊑-∋)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Framework.Slots using (read; write; restrict; empty; params)
open import FPC.proof.Framework.AllProp using (lookup-map)
open import FPC.proof.Framework.SlotsProp using (restrict-id)
import FPC.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import FPC.Language.Imp as I
open I using (none; ⊆-refl)
open import FPC.Language.X86
open import FPC.Compiler.Select
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; _◅◅_; Plus;
  plus; step⁺; star-plus; plus-star; plus→star)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
import FPC.Semantics.AbstractMachines.X86 as X
import FPC.Semantics.AbstractMachines.CFG as G
open G using (Res; value; call; pack; code; choose)
open X using (inl; inr; ⟨_,_,_,_⟩)

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

{- Jumps: label l of the selected blocks is the selected block l --------------}

block-sel : ∀ {Σ R Δ Bs I} (bs : C.Blocks Σ R Δ Bs) (l : Bs ∋ I)
  → block (blocks bs) l
      ≡ blk (blocks (C.Blk.blocks (C.block bs l)))
        (tail (C.Blk.tail (C.block bs l)))
block-sel (bs ▷ t) Z = refl
block-sel (bs ▷ t) (S l) = block-sel bs l

{- The start of a definition: the moves of %rdi and %rsi to their slots
   give the frame of its environment and argument -------------------------------}

start≡ : ∀ {V : Type → Set} {Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) (e : V B) (w : V A)
  → restrict (⊆-refl {I = none Δ I.⊕ ⊑-∋ p (S Z) I.⊕ ⊑-∋ p Z})
      (write (restrict (⊆-refl {I = none Δ I.⊕ ⊑-∋ p (S Z)})
        (write (empty Δ) (⊑-∋ p (S Z)) e)) (⊑-∋ p Z) w)
    ≡ params p e w
start≡ p e w =
  trans (restrict-id _ _) (cong (λ ψ → write ψ (⊑-∋ p Z) w) (restrict-id _ _))

{- The simulation, for a program with definitions ds and main body b₀ --------}

module Sim {Σ : List DSig} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) Σ)
  {T} (b₀ : C.Body Σ T []) where

  P = C.program ds b₀
  xds = map def-body ds
  L₁ = G.sem P
  L₂ = X.sem (select P)

  {- the CFGμ continuation, and the X86μ call stack -}
  infix 4 _~_
  data _~_ : ∀ {A} → G.Cont Σ A → X.Stack Σ A → Set where
    halt : ∀ {A} → G.halt {A = A} ~ X.halt
    seqK : ∀ {R Δ Bs I J A} {x : Δ ∋ A} .{p : J ⊆ I ⊕ x}
      {φ : G.Frame Σ Δ I} {t : Tail Σ R Δ Bs J} {bs κ σ}
      → κ ~ σ
      → G.seqK x p φ t bs κ
        ~ X.retK (movq (reg rax refl) (slot x p) ∷ tail t) (blocks bs) φ σ
    retK : ∀ {A} {κ : G.Cont Σ A} {σ Δ Bs I} {bs₂ : Blocks Σ Δ A Bs}
      {φ : G.Frame Σ Δ I}
      → κ ~ σ
      → G.retK κ ~ X.retK (movq (reg rax refl) (reg rax) ∷ retq refl) bs₂ φ σ

  data Match : G.State Σ → X.State Σ → Set where
    exec~ : ∀ {R Δ Bs I η Γ O F} {t : Tail Σ R Δ Bs I} {φ bs κ σ}
      {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F}
      → κ ~ σ
      → Match (G.exec t φ bs κ)
        (X.run (tail t) (blocks bs) σ η ⟨ ρ , φ , op , f ⟩)

  {- the same, in a frame equal to the CFGμ one -}
  exec≡ : ∀ {R Δ Bs I η Γ O F} {t : Tail Σ R Δ Bs I} {φ ψ bs κ σ}
    {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F}
    → ψ ≡ φ
    → κ ~ σ
    → Match (G.exec t φ bs κ)
      (X.run (tail t) (blocks bs) σ η ⟨ ρ , ψ , op , f ⟩)
  exec≡ refl k = exec~ k

  𝔅 = Both {L₁ = L₁} {L₂ = L₂} Match

  {- how the code selected for a simple expression into o, then k, runs -}
  data XOut {Δ R Bs I J} (bs : Blocks Σ Δ R Bs) (σ : X.Stack Σ R)
    (φ : G.Frame Σ Δ I)
    : ∀ {A} (o : Out I A J) → (∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F))
      → Res {Σ} A → X.State Σ → Set where
    xval : ∀ {A} {o : Out I A J}
      {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)} {v s η Γ O F}
      {ρ : X.RegVals Σ η Γ}
      {op : X.Opened Σ η O} {f : X.Flag Σ F}
      → Plus L₂ s (X.run k bs σ η (X.put (dst o) v ⟨ ρ , φ , op , f ⟩))
      → XOut bs σ φ o k (value v) s
    xcall : ∀ {Δg A B} {o : Out I B J}
      {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)}
      {g : Σ ∋ sig Δg A B} {e w s}
      → Plus L₂ s
        (X.run (Body.start (def-body (lookup ds g)))
          (Body.blocks (def-body (lookup ds g)))
          (X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ) Δg
          ⟨ X.rv tt e w , empty (C.Body.frame (lookup ds g)) , tt , tt ⟩)
      → XOut bs σ φ o k (call (pack (code g) e) w) s

  args~ : ∀ {Δ I Δs η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
    {f : X.Flag Σ F} {φ : G.Frame Σ Δ I}
    (as : All (Atm Σ Δ I) Δs)
    → X.args (atms as) ⟨ ρ , φ , op , f ⟩ ≡ map (G.atom φ) as
  args~ [] = refl
  args~ (a ∷ as) = cong (_ ∷_) (args~ as)

  module _ {Δ R Bs I J} {bs : Blocks Σ Δ R Bs} {σ : X.Stack Σ R} {η Γ O F}
    {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
    {f : X.Flag Σ F} where

    {- callc: open the closure in slot x, then call its code -}
    call~ : ∀ {A B} {φ : G.Frame Σ Δ I} (o : Out I B J)
      {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)}
      (x : Δ ∋ A ⇒ B) .(i : x ∈ I) (a : Atm Σ Δ I A) (v : G.Val Σ (A ⇒ B))
      → read φ x i ≡ v
      → XOut bs σ φ o k (call v (G.atom φ a))
        (X.run (sel (I.callc (var x i) a) o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    call~ {φ = φ} o {k} x i a (pack (code g) e) h =
      xcall
        (plus refl
          (refl ◅ refl
            ◅ trans (cong (λ v → X.enter xds (X.code-of v) (X.env-of v) w κ) h)
                (cong
                  (λ b →
                    next
                    (X.run (Body.start b) (Body.blocks b) κ _
                      ⟨ X.rv tt e w , empty (Body.frame b) , tt , tt ⟩))
                  (lookup-map def-body ds g))
            ◅ ε))
      where w = G.atom φ a
            κ = X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ

    {- the code selected for s -}
    sel~ : ∀ {A} {φ : G.Frame Σ Δ I} (o : Out I A J)
      {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)} (s : I.Simple Σ Δ I A)
      → XOut bs σ φ o k (G.run s φ)
        (X.run (sel s o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    sel~ o (I.atm a) = xval (step⁺ refl)
    sel~ o (I.pair c e) = xval (step⁺ refl)
    sel~ {φ = φ} o (I.callc (var x i) a) = call~ o x i a (read φ x i) refl
    sel~ o {k} (I.tuple as) =
      xval
      (step⁺
        (cong (λ vs → next (X.run k bs σ η (X.put (dst o) (X.tup vs) _)))
          (args~ as)))
    sel~ o (I.get i a) = xval (step⁺ refl)
    sel~ o (I.inl a) = xval (step⁺ refl)
    sel~ o (I.inr a) = xval (step⁺ refl)
    sel~ o (I.prim sub a b) = xval (plus refl (refl ◅ refl ◅ ε))
    sel~ o (I.prim eq a b) = xval (plus refl (refl ◅ ε))
    sel~ o (I.fold a) = xval (step⁺ refl)
    sel~ o (I.unfold a) = xval (step⁺ refl)

  private variable
    s₁ : G.State Σ
    s₂ : X.State Σ

  {- %rax returns to the stack, as the CFGμ value to the continuation -}
  back : ∀ {A} {κ : G.Cont Σ A} {σ Δ Bs I η Γ O F} {bs₂ : Blocks Σ Δ A Bs}
    {ρ : X.RegVals Σ η Γ} {φ : G.Frame Σ Δ I}
    {op : X.Opened Σ η O} {f : X.Flag Σ F} {v}
    → κ ~ σ
    → G.step ds s₁ ≡ G.cont ds v κ
    → Star L₂ s₂ (X.run (retq refl) bs₂ σ η ⟨ ρ X.[ rax ≔ v ] , φ , op , f ⟩)
    → 𝔅 s₁ s₂
  back halt e₀ τ = halt e₀ τ refl
  back (seqK k) e₀ τ =
    move (step⁺ e₀) (star-plus τ (plus refl (refl ◅ ε))) (exec~ k)
  back {v = v} (retK k) e₀ τ =
    back {Γ = rt (just (ty _)) nothing nothing} {ρ = X.rv v tt tt} k e₀
    (τ ◅◅ (refl ◅ refl ◅ ε))

  {- a call: the body starts after the moves of its parameters -}
  called~ : ∀ {Δ R Bs I J B} {bs : Blocks Σ Δ R Bs} {σ : X.Stack Σ R}
    {φ : G.Frame Σ Δ I} {o : Out I B J}
    {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)} {Δg A}
    {g : Σ ∋ sig Δg A B} {e w κ}
    → G.step ds s₁ ≡ next (G.start ds (lookup ds g) e w κ)
    → κ ~ X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ
    → Plus L₂ s₂
      (X.run (Body.start (def-body (lookup ds g)))
        (Body.blocks (def-body (lookup ds g)))
        (X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ) Δg
        ⟨ X.rv tt e w , empty (C.Body.frame (lookup ds g)) , tt , tt ⟩)
    → 𝔅 s₁ s₂
  called~ {g = g} {e = e} {w} e₀ k π =
    move (step⁺ e₀) (plus-star π (refl ◅ refl ◅ ε))
      (exec≡ (start≡ (C.Body.params (lookup ds g)) e w) k)

  {- return s -}
  retn~ : ∀ {R} {κ : G.Cont Σ R} {σ Δ Bs I} {bs : Blocks Σ Δ R Bs}
    {φ : G.Frame Σ Δ I} {r}
    → G.step ds s₁ ≡ G.retn ds κ r
    → κ ~ σ
    → XOut bs σ φ ret (retq refl) r s₂
    → 𝔅 s₁ s₂
  retn~ e₀ k (xval {ρ = ρ} π) = back {ρ = ρ} k e₀ (plus→star π)
  retn~ e₀ k (xcall π) = called~ {o = ret} {k = retq refl} e₀ (retK k) π

  {- seq x s p t -}
  assign~ : ∀ {R Δ Bs I J A} {x : Δ ∋ A} .{p : J ⊆ I ⊕ x}
    {φ : G.Frame Σ Δ I} {t : Tail Σ R Δ Bs J} {bs κ σ r}
    → G.step ds s₁ ≡ G.assign ds x p φ t bs κ r
    → κ ~ σ
    → XOut (blocks bs) σ φ (to x p) (tail t) r s₂
    → 𝔅 s₁ s₂
  assign~ e₀ k (xval π) = move (step⁺ e₀) π (exec~ k)
  assign~ {x = x} {p = p} {t = t} e₀ k (xcall π) =
    called~ {o = to x p} {k = tail t} e₀ (seqK k) π

  {- case x y z l₁ l₂: the payload, then the branch -}
  case~ : ∀ {R Δ Bs I A B η} {x : Δ ∋ A} {y : Δ ∋ B}
    {l₁ : Bs ∋ (I ⊕ x)} {l₂ : Bs ∋ (I ⊕ y)} {φ : G.Frame Σ Δ I}
    {bs : C.Blocks Σ R Δ Bs} {κ σ}
    → (v : G.Val Σ (A ⊹ B))
    → G.step ds s₁
      ≡ next
      (choose v (λ u → G.go ds (C.block bs l₁) (write φ x u) κ)
        (λ u → G.go ds (C.block bs l₂) (write φ y u) κ))
    → X.step xds s₂
      ≡ next
      (choose v (λ u → X.go xds (block (blocks bs) l₁) σ η (write φ x u))
        (λ u → X.go xds (block (blocks bs) l₂) σ η (write φ y u)))
    → κ ~ σ
    → 𝔅 s₁ s₂
  case~ {η = η} {l₁ = l₁} {bs = bs} {σ = σ} (inl u) e₀ e₁ k =
    move (step⁺ e₀)
      (step⁺
        (trans e₁ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₁))))
      (exec~ k)
  case~ {η = η} {l₂ = l₂} {bs = bs} {σ = σ} (inr u) e₀ e₁ k =
    move (step⁺ e₀)
      (step⁺
        (trans e₁ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₂))))
      (exec~ k)

  sim : ∀ {s₁ s₂}
    → Match s₁ s₂
    → 𝔅 s₁ s₂
  sim (exec~ {t = return s} k) = retn~ refl k (sel~ ret s)
  sim (exec~ {t = seq x s p t} k) = assign~ refl k (sel~ (to x p) s)
  sim (exec~ {η = η} {t = goto l} {bs = bs} {σ = σ} k) =
    move (step⁺ refl)
      (step⁺ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l)))
      (exec~ k)
  sim (exec~ {t = case (var x i) y z l₁ l₂} {φ = φ} {bs = bs} k) =
    case~ {x = y} {y = z} {l₁ = l₁} {l₂ = l₂} {φ = φ} {bs = bs}
      (read φ x i) refl refl k

  fsim = both-fsim Match (exec~ halt) sim

{- The end theorem ------------------------------------------------------------}

select-correct : ∀ {A} (P : C.Program A)
  → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds b) = equivalent (Sim.fsim ds b)
