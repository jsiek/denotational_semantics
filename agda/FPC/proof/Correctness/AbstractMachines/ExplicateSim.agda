{-

  Correctness of explicate control (Impμ → CFGμ,
  FPC/Compiler/Explicate.agda) by a forward simulation of the Impμ
  machine by the CFGμ machine, as for typed explicate control
  (ISWIM/proof/Correctness/CEK/ExplicateSim.agda).

  The machines share the values, the frames and the simple expressions,
  and an expression runs in the same frame on both. An expression e
  whose value is the body's result runs as explicate-tail e (tail~); one
  whose value is written to slot x before the tail k runs, as
  explicate-assign e x p k (asg~), where the Impμ continuation does
  what k does (Ctl x p φ): given the value v, it runs as k in the frame
  φ with v written to slot x and restricted to the slots that k starts
  with (restrict p). The Impμ continuation is x := □; e₂ for the tail
  made of e₂ (asgT, asgA), or a jump to a block that does (jmp). The
  continuation of a call is related to the CFGμ frames seqK and retK
  (_≈_).

  An assignment y := e₁ nested in the expression whose value goes to
  slot x writes y, which is not initialized where the expression starts.
  The tail k does not read y, so k runs in the same frame whether y was
  written or not (restrict-fresh, ctl-fresh).

  An Impμ step from x := e₁; e₂ is matched by no CFGμ step (the
  stutter, measured by the nesting of assignments, depth); any other
  Impμ step by one or more CFGμ steps. A tail made with some blocks runs
  with blocks that extend them (Ext), where the older labels find the
  same blocks (ext-block), because explicate only adds blocks (grows-t,
  grows-a).

-}

module FPC.proof.Correctness.AbstractMachines.ExplicateSim where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import FPC.Language.Imp as Imp
open Imp using (simple; assign; case; _∉_; ⊆-refl; ⊆-⊕⊕)
open import FPC.Language.CFG
open import FPC.Compiler.Explicate
open import FPC.Framework.AllUtil using (All; []; _∷_; map)
open import FPC.Framework.Slots using (write; restrict)
open import FPC.proof.Framework.SlotsProp using (restrict-id; restrict-fresh)
open import FPC.proof.Framework.AllProp using (lookup-map)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; Reach)
open import proof.Semantics.CEK.Simulation using (Answers≺; stops; steps;
  stutters; steps₁≺; after≺; answers-at; FSim; Equivalent; equivalent)
import FPC.Semantics.AbstractMachines.Imp as I
import FPC.Semantics.AbstractMachines.CFG as G

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong)

{- Blocks ---------------------------------------------------------------------}

{- bs' is bs with newer blocks, along g -}
data Ext {Σ R Δ} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ R Δ Bs
  → Blocks Σ R Δ Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ R Δ Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' I g} {bs : Blocks Σ R Δ Bs} {bs' : Blocks Σ R Δ Bs'}
    {t : Tail Σ R Δ Bs' I}
    → Ext g bs bs'
    → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ R Δ As Bs Cs}
  → {g : As ⊑ Bs}
  → {g' : Bs ⊑ Cs}
  → ∀ {as : Blocks Σ R Δ As} {bs cs}
  → Ext g as bs
  → Ext g' bs cs
  → Ext (⊑-trans g g') as cs
ext-trans x here = x
ext-trans x (there y) = there (ext-trans x y)

ext-block : ∀ {Σ R Δ Bs Bs' I}
  → {g : Bs ⊑ Bs'}
  → ∀ {bs : Blocks Σ R Δ Bs} {bs'}
  → Ext g bs bs'
  → (l : Bs ∋ I)
  → block bs' (⊑-∋ g l) ≡ block bs l
ext-block here l = refl
ext-block (there x) l = ext-block x l

grows-a : ∀ {Σ R Δ Bs A} {I J : Imp.Inits Δ} (e : Imp.Exp Σ Δ I A)
  → (x : Δ ∋ A)
  → (p : J ⊆ I ⊕ x)
  → ∀ (k : Tail Σ R Δ Bs J) bs
  → Ext (Out.grows (explicate-assign e x p k bs)) bs
    (Out.made (explicate-assign e x p k bs))
grows-a (simple s) x p k bs = here
grows-a {I = I} {J} (assign y _ e₁ e₂) x p k bs =
  ext-trans (grows-a e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs)
    (grows-a e₁ y (⊆-refl {I = I ⊕ y}) _ _)
grows-a {I = I} {J} (case a y _ z _ e₁ e₂) x p k bs =
  there
    (ext-trans
      (there
        (ext-trans (there here)
          (grows-a e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k))))
      (grows-a e₂ x (⊆-⊕⊕ {I = I} {J} x z p) _ _))

grows-t : ∀ {Σ R Δ Bs} {I : Imp.Inits Δ} (e : Imp.Exp Σ Δ I R)
  (bs : Blocks Σ R Δ Bs)
  → Ext (Out.grows (explicate-tail e bs)) bs (Out.made (explicate-tail e bs))
grows-t (simple s) bs = here
grows-t {I = I} (assign x _ e₁ e₂) bs =
  ext-trans (grows-t e₂ bs) (grows-a e₁ x (⊆-refl {I = I ⊕ x}) _ _)
grows-t (case a x _ y _ e₁ e₂) bs =
  there (ext-trans (there (grows-t e₁ bs)) (grows-t e₂ _))

{- the assignments the Impμ machine enters before e runs as a tail -}
depth : ∀ {Σ Δ I A} → Imp.Exp Σ Δ I A → ℕ
depth (assign x _ e₁ e₂) = suc (depth e₁)
depth _ = 0

{- The simulation, for a program with definitions ds and main b₀ --------------}

module Sim {Σ : List DSig}
  (ds : All (λ s → Imp.Body Σ (Args s) (DSig.cod s)) Σ)
  {T} (b₀ : Imp.Body Σ [] T) where

  ds₂ = map explicate-body ds
  L₂ = G.sem (explicate (Imp.program ds b₀))

  mutual
    {- κ₂ continues as κ₁, given the value -}
    infix 4 _≈_
    data _≈_ : ∀ {A} → I.Cont Σ A → G.Cont Σ A → Set where
      halt : ∀ {A} → I.halt {A = A} ≈ G.halt
      retK : ∀ {A} {κ₁ : I.Cont Σ A} {κ₂} → κ₁ ≈ κ₂ → κ₁ ≈ G.retK κ₂
      seqK : ∀ {R Δ Bs I J A} {x : Δ ∋ A} {p : J ⊆ I ⊕ x}
        {φ : I.Frame Σ Δ I} {k : Tail Σ R Δ Bs J} {bs} {κ₁ : I.Cont Σ A} {κ₂}
        → Ctl x p φ κ₁ k bs κ₂
        → κ₁ ≈ G.seqK x p φ k bs κ₂

    {- κ₁, given a value v, continues as the tail k in the frame φ with v
       in slot x, restricted to the slots that k starts with -}
    data Ctl : ∀ {R Δ Bs I J A} (x : Δ ∋ A) → J ⊆ I ⊕ x → I.Frame Σ Δ I
      → I.Cont Σ A → Tail Σ R Δ Bs J → Blocks Σ R Δ Bs → G.Cont Σ R
      → Set where
      asgT : ∀ {R Δ Bs I I₀ A} {x : Δ ∋ A} {p : I₀ ⊕ x ⊆ I ⊕ x}
        {e₂ : Imp.Exp Σ Δ (I₀ ⊕ x) R} {φ : I.Frame Σ Δ I}
        {φ₀ : I.Frame Σ Δ I₀} {κ κ₂} {bs : Blocks Σ R Δ Bs}
        → κ ≈ κ₂
        → (∀ v → restrict p (write φ x v) ≡ write φ₀ x v)
        → Ctl x p φ (I.assignK x φ₀ e₂ κ) (Out.tail (explicate-tail e₂ bs))
          (Out.made (explicate-tail e₂ bs)) κ₂
      asgA : ∀ {R Δ Bs I I₀ J A B} {y : Δ ∋ A} {x : Δ ∋ B}
        {q : I₀ ⊕ y ⊆ I ⊕ y} {p : J ⊆ I₀ ⊕ x}
        {e₂ : Imp.Exp Σ Δ (I₀ ⊕ y) B} {k : Tail Σ R Δ Bs J}
        {φ : I.Frame Σ Δ I} {φ₀ : I.Frame Σ Δ I₀} {κ κ₂ bs}
        → .(y ∉ I₀)
        → Ctl x p φ₀ κ k bs κ₂
        → (∀ v → restrict q (write φ y v) ≡ write φ₀ y v)
        → Ctl y q φ (I.assignK y φ₀ e₂ κ)
          (Out.tail (explicate-assign e₂ x (⊆-⊕⊕ {I = I₀} {J} x y p) k bs))
          (Out.made (explicate-assign e₂ x (⊆-⊕⊕ {I = I₀} {J} x y p) k bs))
          κ₂
      jmp : ∀ {R Δ Bs Bs' I J A} {x : Δ ∋ A} {p : J ⊆ I ⊕ x}
        {φ : I.Frame Σ Δ I} {κ κ₂} {k : Tail Σ R Δ Bs J}
        {bs : Blocks Σ R Δ Bs} {bs' : Blocks Σ R Δ Bs'} {l}
        → Ctl x p φ κ k bs κ₂
        → block bs' l ≡ blk bs k
        → Ctl x p φ κ (goto l) bs' κ₂

  data Match : ℕ → I.State Σ → G.State Σ → Set where
    tail~ : ∀ {R Δ Bs I} {e : Imp.Exp Σ Δ I R} {φ κ₁ κ₂}
      {bs : Blocks Σ R Δ Bs}
      → κ₁ ≈ κ₂
      → Match (depth e) (I.eval e φ κ₁)
        (G.exec (Out.tail (explicate-tail e bs)) φ
          (Out.made (explicate-tail e bs)) κ₂)
    asg~ : ∀ {R Δ Bs I J A} {e : Imp.Exp Σ Δ I A} {x : Δ ∋ A}
      {p : J ⊆ I ⊕ x} {k : Tail Σ R Δ Bs J} {bs φ κ₁ κ₂}
      → Ctl x p φ κ₁ k bs κ₂
      → Match (depth e) (I.eval e φ κ₁)
          (G.exec (Out.tail (explicate-assign e x p k bs)) φ
              (Out.made (explicate-assign e x p k bs)) κ₂)

  Ans = Answers≺ L₂ Match

  private variable
    i : ℕ
    A R : Type
    s₂ : G.State Σ
    κ₁ : I.Cont Σ A

  {- the tail k does not read the slot y, which was not initialized -}
  ctl-fresh : ∀ {Δ Bs I J C} {x : Δ ∋ A} {p : J ⊆ I ⊕ x}
    {φ : I.Frame Σ Δ I} {k : Tail Σ R Δ Bs J} {bs κ₂} (y : Δ ∋ C)
    (u : I.Val Σ C)
    → .(y ∉ I)
    → Ctl x p φ κ₁ k bs κ₂
    → Ctl x (⊆-⊕⊕ {I = I} {J} x y p) (write φ y u) κ₁ k bs κ₂
  ctl-fresh y u yn (asgT {x = x} {p = p} {φ = φ} r eq) =
    asgT r (λ v → trans (restrict-fresh φ y u x v yn p _) (eq v))
  ctl-fresh y u yn (asgA {y = x} {q = q} {φ = φ} xn c eq) =
    asgA xn c (λ v → trans (restrict-fresh φ y u x v yn q _) (eq v))
  ctl-fresh y u yn (jmp c eq) = jmp (ctl-fresh y u yn c) eq

  {- a CFGμ state in a frame equal to another -}
  at-frame : ∀ {j s₁ Δ Bs I} {k : Tail Σ R Δ Bs I} {bs κ₂}
    {ψ ψ' : I.Frame Σ Δ I}
    → ψ ≡ ψ'
    → Reach L₂ (Match j) s₁ (G.exec k ψ' bs κ₂)
    → Reach L₂ (Match j) s₁ (G.exec k ψ bs κ₂)
  at-frame refl r = r

  {- the tail k, run after the assignment, does what κ₁ does -}
  ctl : ∀ {Δ Bs I J} {x : Δ ∋ A} {p : J ⊆ I ⊕ x} {φ : I.Frame Σ Δ I}
    {k : Tail Σ R Δ Bs J} {bs} {κ₂}
    → Ctl x p φ κ₁ k bs κ₂
    → ∀ v
    → Σ[ s₁ ∈ I.State Σ ] I.cont ds v κ₁ ≡ next s₁ × Σ[ j
      ∈ ℕ ] Reach L₂ (Match j) s₁ (G.exec k (restrict p (write φ x v)) bs κ₂)
  ctl (asgT r eq) v = _ , refl , _ , at-frame (eq v) (_ , ε , tail~ r)
  ctl (asgA {y = y} {φ₀ = φ₀} yn c eq) v =
    _ , refl , _ , at-frame (eq v) (_ , ε , asg~ (ctl-fresh y v yn c))
  ctl (jmp {p = p} {φ = φ} {κ₂ = κ₂} c eq) v with ctl c v
  ... | s₁ , e , j , t , σ , m =
    s₁ , e , j , t ,
    cong (λ b → next (G.go ds₂ b (restrict p (write φ _ v)) κ₂)) eq ◅ σ , m

  cont≈ : ∀ {κ₂}
    → κ₁ ≈ κ₂
    → ∀ v
    → G.step ds₂ s₂ ≡ G.cont ds₂ v κ₂
    → Ans i (I.cont ds v κ₁) s₂
  cont≈ halt v st = stops st
  cont≈ (retK r) v st = cont≈ r v st
  cont≈ (seqK c) v st with ctl c v
  ... | _ , e , _ , rch = answers-at e (after≺ st rch)

  call≈ : ∀ {A'} (f : I.Val Σ (A' ⇒ A)) w {κ'}
    → G.step ds₂ s₂ ≡ G.enter ds₂ f w κ'
    → κ₁ ≈ κ'
    → Ans i (I.res ds (I.call f w) κ₁) s₂
  call≈ (I.pack (I.code g) e) w {κ'} st r =
    steps₁≺
      (trans st
        (cong (λ d → next (G.start ds₂ d e w κ'))
          (lookup-map explicate-body ds g))) (tail~ r)

  res-t : ∀ {κ₂}
    → κ₁ ≈ κ₂
    → ∀ r
    → G.step ds₂ s₂ ≡ G.retn ds₂ κ₂ r
    → Ans i (I.res ds r κ₁) s₂
  res-t r (I.value v) st = cont≈ r v st
  res-t r (I.call f w) st = call≈ f w st (retK r)

  res-a : ∀ {Δ Bs I J} {x : Δ ∋ A} {p : J ⊆ I ⊕ x} {φ : I.Frame Σ Δ I}
    {k : Tail Σ R Δ Bs J} {bs κ₂}
    → Ctl x p φ κ₁ k bs κ₂
    → ∀ r
    → G.step ds₂ s₂ ≡ G.assign ds₂ x p φ k bs κ₂ r
    → Ans i (I.res ds r κ₁) s₂
  res-a c (I.value v) st with ctl c v
  ... | _ , e , _ , rch = answers-at e (after≺ st rch)
  res-a c (I.call f w) st = call≈ f w st (seqK c)

  {- a case: both machines take the branch of the injection -}
  branch : ∀ {j₁ j₂ A' B'} (v : I.Val Σ (A' ⊹ B')) {f₁ : I.Val Σ A' → I.State Σ}
    {f₂ : I.Val Σ B' → I.State Σ}
      {g₁ : I.Val Σ A' → G.State Σ} {g₂ : I.Val Σ B' → G.State Σ}
    → G.step ds₂ s₂ ≡ next (I.choose v g₁ g₂)
    → (∀ u → Match j₁ (f₁ u) (g₁ u))
    → (∀ u → Match j₂ (f₂ u) (g₂ u))
    → Ans i (next (I.choose v f₁ f₂)) s₂
  branch (I.inl u) st m₁ m₂ = steps₁≺ st (m₁ u)
  branch (I.inr u) st m₁ m₂ = steps₁≺ st (m₂ u)

  at : ∀ {Δ I} {b b' : Blk Σ R Δ I} {j s₁ φ κ₂}
    → b ≡ b'
    → Match j s₁ (G.go ds₂ b' φ κ₂)
    → Match j s₁ (G.go ds₂ b φ κ₂)
  at refl m = m

  sim : ∀ {i s₁ s₂}
    → Match i s₁ s₂
    → Ans i (I.step ds s₁) s₂
  sim (tail~ {e = simple s} {φ = φ} r) = res-t r (I.run s φ) refl
  sim (asg~ {e = simple s} {φ = φ} c) = res-a c (I.run s φ) refl
  sim (tail~ {e = assign x _ e₁ e₂} r) =
    stutters ≤-refl (asg~ (asgT {p = ⊆-refl} r (λ v → restrict-id _ _)))
  sim (asg~ {e = assign y yn e₁ e₂} c) =
    stutters ≤-refl (asg~ (asgA {q = ⊆-refl} yn c (λ v → restrict-id _ _)))
  sim (tail~ {e = case a x _ y _ e₁ e₂} {φ = φ} {bs = bs} r) =
    branch (I.atom φ a) refl (λ u → at (ext-block (grows-t e₂ _) Z) (tail~ r))
      (λ u → tail~ r)
  sim (asg~ {I = I} {J} {e = case a y yn z zn e₁ e₂} {x = x} {p = p} {k = k}
      {bs = bs} {φ = φ} c) =
    branch (I.atom φ a) refl
      (λ u →
        at (ext-block (grows-a e₂ x (⊆-⊕⊕ {I = I} {J} x z p) _ _) Z)
          (asg~ (jmp (ctl-fresh y u yn c) refl)))
      (λ u →
        asg~
          (jmp (ctl-fresh z u zn c)
            (ext-block
              (grows-a e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)) Z)))

  fsim : FSim (I.sem (Imp.program ds b₀)) L₂
  fsim = record { match = Match ; init = _ , tail~ halt ; sim = sim }

{- The end theorem ------------------------------------------------------------}

explicate-correct : ∀ {A} (P : Imp.Program A)
  → Equivalent (I.sem P) (G.sem (explicate P))
explicate-correct (Imp.program ds b) = equivalent (Sim.fsim ds b)
