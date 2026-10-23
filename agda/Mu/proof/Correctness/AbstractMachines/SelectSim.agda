{-

  Correctness of select instructions (CFGμ → X86μ, Mu/Compiler/Select.agda):
  a simulation of the CFGμ machine by the X86μ machine (Both,
  proof/Framework/Both.agda), as for typed select instructions
  (proof/Correctness/CEK/SelectSim.agda).

  Both machines hold the same values, and the X86μ frame is the CFGμ
  frame, so a state of CFGμ is matched by the code selected for its
  tail, in the same frame, with any registers and flag (Match); the
  X86μ call stack holds, for each CFGμ return frame, the caller's frame
  and the move of %rax where the caller wants it (_~_). One CFGμ step
  (a statement) is matched by the instructions selected for it: they
  write its value to its destination (xval), or call (xcall). Neither
  machine fails.

-}

module Mu.proof.Correctness.AbstractMachines.SelectSim where

open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Framework.Membership using (_⊑_)
open import Framework.Lookup using (forget)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import Mu.proof.Framework.AllProp using (lookup-map)
import Mu.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Mu.Language.Imp as I
open import Mu.Language.X86
open import Mu.Compiler.Select
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; _◅◅_; Plus; plus; step⁺; star-plus; plus-star; plus→star)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
import Mu.Semantics.AbstractMachines.X86 as X
import Mu.Semantics.AbstractMachines.CFG as G
open G using (Res; value; call; pack; code; choose)
open X using (inl; inr; ⟨_,_,_,_⟩)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

{- Jumps: label l of the selected blocks is the selected block l --------------}

blk-le : ∀ {Σ R Bs Δ n} (bs : C.Blocks Σ R Bs) (l : Bs ∋ Δ) → blocks-depth bs ≤ n → depth (C.Blk.tail (C.block bs l)) ≤ n
blk-le (bs ▷ t) Z le = ≤-trans (m≤m⊔n _ _) le
blk-le (bs ▷ t) (S l) le = blk-le bs l (≤-trans (m≤n⊔m _ _) le)

blk-le' : ∀ {Σ R Bs Δ n} (bs : C.Blocks Σ R Bs) (l : Bs ∋ Δ) → blocks-depth bs ≤ n
  → blocks-depth (C.Blk.blocks (C.block bs l)) ≤ n
blk-le' (bs ▷ t) Z le = ≤-trans (m≤n⊔m _ _) le
blk-le' (bs ▷ t) (S l) le = blk-le' bs l (≤-trans (m≤n⊔m _ _) le)

block-sel : ∀ {Σ R Bs Δ n} (bs : C.Blocks Σ R Bs) (l : Bs ∋ Δ) .(le : blocks-depth bs ≤ n)
  → block (blocks bs le) l
    ≡ blk (blocks (C.Blk.blocks (C.block bs l)) (blk-le' bs l le)) (tail (C.Blk.tail (C.block bs l)) (blk-le bs l le))
block-sel (bs ▷ t) Z le = refl
block-sel (bs ▷ t) (S l) le = block-sel bs l (≤-trans (m≤n⊔m _ _) le)

{- The simulation, for a program with definitions ds and main body b₀ --------}

module Sim {Σ : List DSig} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) Σ) {T} (b₀ : C.Body Σ T []) where

  P = C.program ds b₀
  xds = map def-body ds
  L₁ = G.sem P
  L₂ = X.sem (select P)

  {- the CFGμ continuation, and the X86μ call stack -}
  infix 4 _~_
  data _~_ : ∀ {A} → G.Cont Σ A → X.Stack Σ A → Set where
    halt : ∀ {A} → G.halt {A = A} ~ X.halt
    seqK : ∀ {R Bs Δ Δ' A n} {p : Δ' ⊑ Δ} {φ : G.Frame Σ Δ} {t : Tail Σ R Bs (A ∷ Δ')} {bs κ σ} .{lt le le'} → κ ~ σ
      → G.seqK p φ t bs κ ~ X.retK {n = n} (movq (reg rax refl) (slot p lt) ∷ tail t le) (blocks bs le') φ σ
    retK : ∀ {A} {κ : G.Cont Σ A} {σ n Bs Δ} {bs₂ : Blocks Σ n A Bs} {φ : G.Frame Σ Δ} → κ ~ σ
      → G.retK κ ~ X.retK (movq (reg rax refl) (reg rax) ∷ retq refl) bs₂ φ σ

  data Match : G.State Σ → X.State Σ → Set where
    exec~ : ∀ {R Bs Δ n η Γ O F} {t : Tail Σ R Bs Δ} {φ bs κ σ} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F}
      .{le le'} → κ ~ σ → Match (G.exec t φ bs κ) (X.run {n = n} (tail t le) (blocks bs le') σ η ⟨ ρ , φ , op , f ⟩)

  𝔅 = Both {L₁ = L₁} {L₂ = L₂} Match

  {- how the code selected for a simple expression into o, then k, runs -}
  data XOut {n R Bs Δ Δ''} (bs : Blocks Σ n R Bs) (σ : X.Stack Σ R) (φ : G.Frame Σ Δ)
    : ∀ {A} (o : Out n Δ A Δ'') → (∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)) → Res {Σ} A → X.State Σ → Set where
    xval : ∀ {A} {o : Out n Δ A Δ''} {k : ∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)} {v s η Γ O F} {ρ : X.RegVals Σ η Γ}
      {op : X.Opened Σ η O} {f : X.Flag Σ F}
      → Plus L₂ s (X.run k bs σ η (X.put (dst o) v ⟨ ρ , φ , op , f ⟩)) → XOut bs σ φ o k (value v) s
    xcall : ∀ {Δg A B} {o : Out n Δ B Δ''} {k : ∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)} {g : Σ ∋ sig Δg A B} {e w s}
      → Plus L₂ s (X.run (Body.start (def-body (lookup ds g))) (Body.blocks (def-body (lookup ds g)))
                         (X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ) Δg ⟨ X.rv tt e w , [] , tt , tt ⟩)
      → XOut bs σ φ o k (call (pack (code g) e) w) s

  args~ : ∀ {Δ Δs η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F} {φ : G.Frame Σ Δ}
    (as : All (Atm Σ Δ) Δs) → X.args (atms as) ⟨ ρ , φ , op , f ⟩ ≡ map (G.atom φ) as
  args~ [] = refl
  args~ (a ∷ as) = cong (_ ∷_) (args~ as)

  module _ {n R Bs Δ Δ''} {bs : Blocks Σ n R Bs} {σ : X.Stack Σ R} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
    {f : X.Flag Σ F} where

    {- callc: open the closure in slot x, then call its code -}
    call~ : ∀ {A B} {φ : G.Frame Σ Δ} (o : Out n Δ B Δ'') {k : ∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)}
      (x : Δ ∋ A ⇒ B) (a : Atm Σ Δ A) (v : G.Val Σ (A ⇒ B)) → lookup φ x ≡ v
      → XOut bs σ φ o k (call v (G.atom φ a)) (X.run (sel (I.callc (var x) a) o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    call~ {φ = φ} o {k} x a (pack (code g) e) h =
      xcall (plus refl (refl ◅ refl ◅ trans (cong (λ v → X.enter xds (X.code-of v) (X.env-of v) w κ) h)
                                            (cong (λ b → next (X.run (Body.start b) (Body.blocks b) κ _ ⟨ X.rv tt e w , [] , tt , tt ⟩))
                                                  (lookup-map def-body ds g)) ◅ ε))
      where w = G.atom φ a
            κ = X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ

    {- the code selected for s -}
    sel~ : ∀ {A} {φ : G.Frame Σ Δ} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)} (s : I.Simple Σ Δ A)
      → XOut bs σ φ o k (G.run s φ) (X.run (sel s o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    sel~ o (I.atm a) = xval (step⁺ refl)
    sel~ o (I.pack c e) = xval (step⁺ refl)
    sel~ {φ = φ} o (I.callc (var x) a) = call~ o x a (lookup φ x) refl
    sel~ o {k} (I.tuple as) = xval (step⁺ (cong (λ vs → next (X.run k bs σ η (X.put (dst o) (X.tup vs) _))) (args~ as)))
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
  back : ∀ {A} {κ : G.Cont Σ A} {σ n Bs Δ η Γ O F} {bs₂ : Blocks Σ n A Bs} {ρ : X.RegVals Σ η Γ} {φ : G.Frame Σ Δ}
    {op : X.Opened Σ η O} {f : X.Flag Σ F} {v}
    → κ ~ σ → G.step ds s₁ ≡ G.cont ds v κ → Star L₂ s₂ (X.run (retq refl) bs₂ σ η ⟨ ρ X.[ rax ≔ v ] , φ , op , f ⟩) → 𝔅 s₁ s₂
  back halt e₀ τ = halt e₀ τ refl
  back (seqK k) e₀ τ = move (step⁺ e₀) (star-plus τ (plus refl (refl ◅ ε))) (exec~ k)
  back {v = v} (retK k) e₀ τ = back {Γ = rt (just (ty _)) nothing nothing} {ρ = X.rv v tt tt} k e₀ (τ ◅◅ (refl ◅ refl ◅ ε))

  {- return s -}
  retn~ : ∀ {R} {κ : G.Cont Σ R} {σ n Bs Δ} {bs : Blocks Σ n R Bs} {φ : G.Frame Σ Δ} {r} → G.step ds s₁ ≡ G.retn ds κ r → κ ~ σ
    → XOut bs σ φ ret (retq refl) r s₂ → 𝔅 s₁ s₂
  retn~ e₀ k (xval {ρ = ρ} π) = back {ρ = ρ} k e₀ (plus→star π)
  retn~ e₀ k (xcall π) = move (step⁺ e₀) (plus-star π (refl ◅ refl ◅ ε)) (exec~ (retK k))

  {- seq p s t -}
  assign~ : ∀ {R Bs Δ Δ' A n} {p : Δ' ⊑ Δ} {φ : G.Frame Σ Δ} {t : Tail Σ R Bs (A ∷ Δ')} {bs κ σ r} .{lt le le'}
    → G.step ds s₁ ≡ G.assign ds p φ t bs κ r → κ ~ σ
    → XOut {n = n} (blocks bs le') σ φ (to p lt) (tail t le) r s₂ → 𝔅 s₁ s₂
  assign~ e₀ k (xval π) = move (step⁺ e₀) π (exec~ k)
  assign~ e₀ k (xcall π) = move (step⁺ e₀) (plus-star π (refl ◅ refl ◅ ε)) (exec~ (seqK k))

  {- case x p l₁ l₂: the payload, then the branch -}
  case~ : ∀ {R Bs Δ Δ' A B n η} {p : Δ' ⊑ Δ} {l₁ : Bs ∋ (A ∷ Δ')} {l₂ : Bs ∋ (B ∷ Δ')} {φ : G.Frame Σ Δ} {bs : C.Blocks Σ R Bs}
    {κ σ} .{le : blocks-depth bs ≤ n} (v : G.Val Σ (A ⊹ B))
    → G.step ds s₁ ≡ next (choose v (λ u → G.go ds (C.block bs l₁) (u ∷ forget p φ) κ) (λ u → G.go ds (C.block bs l₂) (u ∷ forget p φ) κ))
    → X.step xds s₂ ≡ next (choose v (λ u → X.go xds (block (blocks bs le) l₁) σ η (u ∷ forget p φ))
                                     (λ u → X.go xds (block (blocks bs le) l₂) σ η (u ∷ forget p φ)))
    → κ ~ σ → 𝔅 s₁ s₂
  case~ {η = η} {l₁ = l₁} {bs = bs} {σ = σ} {le = le} (inl u) e₀ e₁ k =
    move (step⁺ e₀) (step⁺ (trans e₁ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₁ le)))) (exec~ k)
  case~ {η = η} {l₂ = l₂} {bs = bs} {σ = σ} {le = le} (inr u) e₀ e₁ k =
    move (step⁺ e₀) (step⁺ (trans e₁ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₂ le)))) (exec~ k)

  sim : ∀ {s₁ s₂} → Match s₁ s₂ → 𝔅 s₁ s₂
  sim (exec~ {t = return s} k) = retn~ refl k (sel~ ret s)
  sim (exec~ {t = seq p s t} k) = assign~ refl k (sel~ (to p _) s)
  sim (exec~ {η = η} {t = goto l} {bs = bs} {σ = σ} {le' = le'} k) =
    move (step⁺ refl) (step⁺ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l le'))) (exec~ k)
  sim (exec~ {t = case (var x) p l₁ l₂} {φ = φ} {bs = bs} {le' = le'} k) =
    case~ {p = p} {l₁ = l₁} {l₂ = l₂} {φ = φ} {bs = bs} {le = le'} (lookup φ x) refl refl k

  fsim = both-fsim Match (exec~ halt) sim

{- The end theorem ---------------------------------------------------------------}

select-correct : ∀ {A} (P : C.Program A) → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds b) = equivalent (Sim.fsim ds b)
