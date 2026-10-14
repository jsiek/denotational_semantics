{-

  Correctness of typed select instructions into X86ᵀ (CFGᵀ → X86ᵀ,
  Compiler/SelectTAL.agda), a pilot (Theorems/TAL.agda): a simulation of
  the CFGᵀ machine by the X86ᵀ machine (Both, proof/Framework/Both.agda),
  and the compiler to X86ᵀ.

  Both machines hold the same values, and the X86ᵀ frame is the CFGᵀ
  frame, so a state of CFGᵀ is matched by the code selected for its
  tail, in the same frame, with any registers and flag (Match); the
  X86ᵀ call stack holds, for each CFGᵀ return frame, the caller's frame
  and the move of %rax where the caller wants it (_~_). One CFGᵀ step
  (a statement) is matched by the instructions selected for it: they
  write its value to its destination (xval), fail at chk where the
  project fails (xfail), or call (xcall). There is nothing else to
  rule out: X86ᵀ has no other error.

-}

module proof.Correctness.CEK.SelectTALSim where

open import Language.Prim using (sub; eq)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_)
open import Framework.Lookup using (_!_; forget)
open import proof.Framework.Lookup using (map-!)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Language.Typed.Imp as I
open import Language.Typed.X86
open import Compiler.SelectTAL
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile-cfg)
open import Semantics.Observation using (Obs; o-error)
open import proof.Semantics.CEK.Smallstep using (Machine; Next; next; stop; Star; ε; _◅_; _◅◅_; Plus; plus; step⁺; star-plus; plus-star; plus→star; Final)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent; equiv-trans)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
open import proof.Correctness.CEK.PipelineSim using (compile-cfg-correct)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.X86 as X
import Semantics.CEK.Typed.CFG as G
open G using (Res; value; fail; call; pack; code; choose)
open import Semantics.CEK.Typed.Imp using (ok?)
open X using (proj?; inl; inr; ⟨_,_,_,_⟩)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

{- Jumps: label l of the selected blocks is the selected block l --------------}

blk-le : ∀ {Σ Bs Δ n} (bs : C.Blocks Σ Bs) (l : Bs ∋ Δ) → blocks-depth bs ≤ n → depth (C.Blk.tail (C.block bs l)) ≤ n
blk-le (bs ▷ t) Z le = ≤-trans (m≤m⊔n _ _) le
blk-le (bs ▷ t) (S l) le = blk-le bs l (≤-trans (m≤n⊔m _ _) le)

blk-le' : ∀ {Σ Bs Δ n} (bs : C.Blocks Σ Bs) (l : Bs ∋ Δ) → blocks-depth bs ≤ n → blocks-depth (C.Blk.blocks (C.block bs l)) ≤ n
blk-le' (bs ▷ t) Z le = ≤-trans (m≤n⊔m _ _) le
blk-le' (bs ▷ t) (S l) le = blk-le' bs l (≤-trans (m≤n⊔m _ _) le)

block-sel : ∀ {Σ Bs Δ n} (bs : C.Blocks Σ Bs) (l : Bs ∋ Δ) .(le : blocks-depth bs ≤ n)
  → block (blocks bs le) l
    ≡ blk (blocks (C.Blk.blocks (C.block bs l)) (blk-le' bs l le)) (tail (C.Blk.tail (C.block bs l)) (blk-le bs l le))
block-sel (bs ▷ t) Z le = refl
block-sel (bs ▷ t) (S l) le = block-sel bs l (≤-trans (m≤n⊔m _ _) le)

{- The simulation, for a program with definitions ds and main body b₀ --------}

module Sim {Σ : List ℕ} (ds : All (λ n → C.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) (b₀ : C.Body Σ []) where

  P = C.program ds b₀
  xds = All-map def-body ds
  L₁ = G.sem P
  L₂ = X.sem (select P)

  {- the CFGᵀ continuation, and the X86ᵀ call stack -}
  infix 4 _~_
  data _~_ : G.Cont Σ → X.Stack Σ → Set where
    halt : G.halt ~ X.halt
    seqK : ∀ {Bs Δ Δ' n} {p : Δ' ⊑ Δ} {φ : G.Frame Σ Δ} {t : Tail Σ Bs (Any ∷ Δ')} {bs κ σ} .{lt le le'} → κ ~ σ
      → G.seqK p φ t bs κ ~ X.retK {n = n} (movq (reg rax refl) (slot p lt) ∷ tail t le) (blocks bs le') φ σ
    retK : ∀ {κ σ n Bs Δ} {bs₂ : Blocks Σ n Bs} {φ : G.Frame Σ Δ} → κ ~ σ
      → G.retK κ ~ X.retK (movq (reg rax refl) (reg rax) ∷ retq refl) bs₂ φ σ

  data Match : G.State Σ → X.State Σ → Set where
    exec~ : ∀ {Bs Δ n η Γ O F} {t : Tail Σ Bs Δ} {φ bs κ σ} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F}
      .{le le'} → κ ~ σ → Match (G.exec t φ bs κ) (X.run {n = n} (tail t le) (blocks bs le') σ η ⟨ ρ , φ , op , f ⟩)

  B = Both {L₁ = L₁} {L₂ = L₂} Match

  {- how the code selected for a simple expression into o, then k, runs -}
  data XOut {n Bs Δ Δ''} (bs : Blocks Σ n Bs) (σ : X.Stack Σ) (φ : G.Frame Σ Δ)
    : ∀ {A} (o : Out n Δ A Δ'') → (∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)) → Res {Σ} A → X.State Σ → Set where
    xval : ∀ {A} {o : Out n Δ A Δ''} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {v s η Γ O F} {ρ : X.RegVals Σ η Γ}
      {op : X.Opened Σ η O} {f : X.Flag Σ F}
      → Plus L₂ s (X.run k bs σ η (X.put (dst o) v ⟨ ρ , φ , op , f ⟩)) → XOut bs σ φ o k (value v) s
    xfail : ∀ {A} {o : Out n Δ A Δ''} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {s s'}
      → Star L₂ s s' → Final L₂ s' o-error → XOut bs σ φ o k fail s
    xcall : ∀ {o : Out n Δ Any Δ''} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {m} {g : Σ ∋ m} {e w s η}
      → Plus L₂ s (X.run (Body.start (def-body (ds ! g))) (Body.blocks (def-body (ds ! g)))
                         (X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ) η ⟨ X.rv tt e w , [] , tt , tt ⟩)
      → XOut bs σ φ o k (call (pack (code g) e) w) s

  args~ : ∀ {Δ j η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O} {f : X.Flag Σ F} {φ : G.Frame Σ Δ}
    (as : Vec (Atm Σ Δ Any) j) → X.args (atms as) ⟨ ρ , φ , op , f ⟩ ≡ map (G.atom φ) as
  args~ [] = refl
  args~ (a ∷ as) = cong (_ ∷_) (args~ as)

  module _ {n Bs Δ Δ''} {bs : Blocks Σ n Bs} {σ : X.Stack Σ} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
    {f : X.Flag Σ F} where

    {- callc: open the closure in slot x, then call its code -}
    call~ : ∀ {φ : G.Frame Σ Δ} (o : Out n Δ Any Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)}
      (x : Δ ∋ ⟪ fun ⟫) (a : Atm Σ Δ Any) (v : G.Val Σ ⟪ fun ⟫) → φ ! x ≡ v
      → XOut bs σ φ o k (call v (G.atom φ a)) (X.run (sel (I.callc (var x) a) o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    call~ {φ} o {k} x a (pack (code g) e) h =
      xcall (plus refl (refl ◅ refl ◅ trans (cong (λ v → X.enter xds (X.code-of v) (X.env-of v) w κ) h)
                                            (cong (λ b → next (X.run (Body.start b) (Body.blocks b) κ _ ⟨ X.rv tt e w , [] , tt , tt ⟩)) (map-! def-body ds g)) ◅ ε))
      where w = G.atom φ a
            κ = X.retK (movq (reg rax refl) (dst o) ∷ k) bs φ σ

    {- project: the check, then the move -}
    proj~ : ∀ {A} {φ : G.Frame Σ Δ} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {s}
      (r : Maybe (G.Val Σ A))
      → X.step xds s ≡ X.checked xds r (dst o) k bs σ ⟨ X._[_≔_] {τ = nothing} ρ rax tt , φ , op , tt ⟩ → XOut bs σ φ o k (ok? r) s
    proj~ o (just v) e = xval (plus e ε)
    proj~ o nothing e = xfail ε e

    {- the code selected for s -}
    sel~ : ∀ {A} {φ : G.Frame Σ Δ} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} (s : I.Simple Σ Δ A)
      → XOut bs σ φ o k (G.run s φ) (X.run (sel s o k) bs σ η ⟨ ρ , φ , op , f ⟩)
    sel~ o (I.atm a) = xval (step⁺ refl)
    sel~ o (I.pack c e) = xval (step⁺ refl)
    sel~ {φ = φ} o (I.callc (var x) a) = call~ o x a (φ ! x) refl
    sel~ o {k} (I.tuple as) = xval (step⁺ (cong (λ vs → next (X.run k bs σ η (X.put (dst o) (X.tup vs) _))) (args~ as)))
    sel~ o (I.get i a) = xval (step⁺ refl)
    sel~ o (I.inl a) = xval (step⁺ refl)
    sel~ o (I.inr a) = xval (step⁺ refl)
    sel~ o (I.prim sub a b) = xval (plus refl (refl ◅ refl ◅ ε))
    sel~ o (I.prim eq a b) = xval (plus refl (refl ◅ ε))
    sel~ o (I.inject G a) = xval (step⁺ refl)
    sel~ {φ = φ} o (I.project t (var x)) = proj~ o (proj? t (φ ! x)) refl

  private variable
    s₁ : G.State Σ
    s₂ : X.State Σ

  {- %rax returns to the stack, as the CFGᵀ value to the continuation -}
  back : ∀ {κ σ n Bs Δ η Γ O F} {bs₂ : Blocks Σ n Bs} {ρ : X.RegVals Σ η Γ} {φ : G.Frame Σ Δ} {op : X.Opened Σ η O} {f : X.Flag Σ F} {v}
    → κ ~ σ → G.step ds s₁ ≡ G.cont ds v κ → Star L₂ s₂ (X.run (retq refl) bs₂ σ η ⟨ ρ X.[ rax ≔ v ] , φ , op , f ⟩) → B s₁ s₂
  back halt e₀ τ = halt e₀ τ refl
  back (seqK k) e₀ τ = move (step⁺ e₀) (star-plus τ (plus refl (refl ◅ ε))) (exec~ k)
  back {v = v} (retK k) e₀ τ = back {Γ = returned [] .St.rs} {ρ = X.rv v tt tt} k e₀ (τ ◅◅ (refl ◅ refl ◅ ε))

  {- return s -}
  retn~ : ∀ {κ σ n Bs Δ} {bs : Blocks Σ n Bs} {φ : G.Frame Σ Δ} {r} → G.step ds s₁ ≡ G.retn ds κ r → κ ~ σ
    → XOut bs σ φ ret (retq refl) r s₂ → B s₁ s₂
  retn~ e₀ k (xval {ρ = ρ} π) = back {ρ = ρ} k e₀ (plus→star π)
  retn~ e₀ k (xfail τ fin) = halt e₀ τ fin
  retn~ e₀ k (xcall π) = move (step⁺ e₀) (plus-star π (refl ◅ refl ◅ ε)) (exec~ (retK k))

  {- seq p s t -}
  assign~ : ∀ {Bs Δ Δ' A n} {p : Δ' ⊑ Δ} {φ : G.Frame Σ Δ} {t : Tail Σ Bs (A ∷ Δ')} {bs κ σ r} .{lt le le'}
    → G.step ds s₁ ≡ G.assign ds p φ t bs κ r → κ ~ σ
    → XOut {n = n} (blocks bs le') σ φ (to p lt) (tail t le) r s₂ → B s₁ s₂
  assign~ e₀ k (xval π) = move (step⁺ e₀) π (exec~ k)
  assign~ e₀ k (xfail τ fin) = halt e₀ τ fin
  assign~ e₀ k (xcall π) = move (step⁺ e₀) (plus-star π (refl ◅ refl ◅ ε)) (exec~ (seqK k))

  {- case a p l₁ l₂: the test and the payload, then the branch -}
  case~ : ∀ {Bs Δ Δ' n η Γ O} {p : Δ' ⊑ Δ} {l₁ l₂ : Bs ∋ (Any ∷ Δ')} {φ : G.Frame Σ Δ} {bs κ σ} {ρ : X.RegVals Σ η Γ}
    {op : X.Opened Σ η O} .{le : blocks-depth bs ≤ n} (v : G.Val Σ ⟪ sum ⟫)
    → G.step ds s₁ ≡ next (choose v (λ u → G.go ds (C.block bs l₁) (u ∷ forget p φ) κ) (λ u → G.go ds (C.block bs l₂) (u ∷ forget p φ) κ))
    → κ ~ σ → Plus L₂ s₂ (X.run (je l₁ l₂) (blocks bs le) σ η ⟨ ρ , X.field′ payload v ∷ forget p φ , op , X.is-inl v ⟩)
    → B s₁ s₂
  case~ {η = η} {l₁ = l₁} {bs = bs} {σ = σ} {le = le} (inl u) e₀ k π =
    move (step⁺ e₀) (plus-star π (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₁ le) ◅ ε)) (exec~ k)
  case~ {η = η} {l₂ = l₂} {bs = bs} {σ = σ} {le = le} (inr u) e₀ k π =
    move (step⁺ e₀) (plus-star π (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l₂ le) ◅ ε)) (exec~ k)

  sim : ∀ {s₁ s₂} → Match s₁ s₂ → B s₁ s₂
  sim (exec~ {t = return s} k) = retn~ refl k (sel~ ret s)
  sim (exec~ {t = seq p s t} k) = assign~ refl k (sel~ (to p _) s)
  sim (exec~ {η = η} {t = goto l} {bs = bs} {σ = σ} {le' = le'} k) =
    move (step⁺ refl) (step⁺ (cong (λ b → next (X.go xds b σ η _)) (block-sel bs l le'))) (exec~ k)
  sim (exec~ {t = case (var x) p l₁ l₂} {φ = φ} k) = case~ {p = p} {φ = φ} (φ ! x) refl k (plus refl (refl ◅ ε))

  fsim = both-fsim Match (exec~ halt) sim

{- The end theorems ---------------------------------------------------------------}

select-correct : ∀ P → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds b) = equivalent (Sim.fsim ds b)

compile-tal-correct : ∀ M → Closed M → Equivalent (ISWIMₘ.sem M) (X.sem (compile-tal M))
compile-tal-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct _)
