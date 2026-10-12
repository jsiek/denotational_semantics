{-

  Correctness of the explicate-control pass (Imp → CFG,
  Compile/Explicate.agda) by a forward simulation of the Imp machine by
  the CFG machine (see the design note in Smallstep.agda).

  The machines share the frame and the evaluation of simple expressions,
  and run in lock step except for the control flow that the pass makes
  explicit. An Imp expression e whose continuation κ₁ is in mode m runs
  as the tail explicate makes of it in that mode: explicate-tail e when
  its value is the body's result (tailM), explicate-assign e x k when it
  is assigned to x before the tail k runs (asgM x k). The stack of Imp
  continuations x := □; e₂ is so a CFG tail k (Ctl): either the tail made
  of e₂ (asg), or a goto to the join point that runs it (jmp).

  So an Imp step from x := e₁; e₂ is matched by no CFG step: e₁ runs as
  the tail that x := e₁; e₂ runs as (the stutter, measured by the
  nesting of assignments, depth). A value returned to x := □; e₂ is
  matched by the assignment of seq and the jumps to join points (join);
  a case, by its jump to a block, which runs the tail made of its branch
  (Br).

  A tail made at the blocks bs runs with any newer blocks bs' (bs ≼ bs'),
  where the blocks of bs keep their labels (block-≼): explicate only
  adds blocks (grows).

  There is no precondition.

-}

module Compiler.Operational.Correctness.ExplicateSim where

open import Compiler.Lang.Imp as Imp using (Atm; Exp; simple; atm; case; assign; body; program)
open import Compiler.Lang.CFG using (Tail; goto; block)
open import Compiler.Compile.Explicate
open import Compiler.Compile.Pipeline using (compile-imp; compile-cfg)
open import Compiler.Compile.EncloseScope using (Closed)
open import ListUtil using (_‼_)
open import Compiler.Operational.Smallstep using (Machine; next; plus; Star; ε; _◅_)
open import Compiler.Operational.Simulation
  using (Answers≺; stops; steps; stutters; FSim; Equivalent; equivalent; equiv-trans)
import Compiler.Operational.Machine.Imp as I
import Compiler.Operational.Machine.CFG as G
import Compiler.Operational.Machine.ISWIM as S
open import Compiler.Operational.Correctness.RCOSim using (‼-map)
open import Compiler.Operational.Correctness.LiftLocalsSim using (compile-imp-correct)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map; reverse)
open import Data.List.Properties using (reverse-map)
open import Data.Maybe using (just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; suc; _≤_; _≟_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; <-irrefl)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

{- Blocks ------------------------------------------------------------------------}

{- bs' is bs with newer blocks -}
infix 4 _≼_
data _≼_ (bs : List Tail) : List Tail → Set where
  here : bs ≼ bs
  there : ∀ {t bs'} → bs ≼ bs' → bs ≼ t ∷ bs'

≼-trans : ∀ {as bs cs} → as ≼ bs → bs ≼ cs → as ≼ cs
≼-trans p here = p
≼-trans p (there q) = there (≼-trans p q)

≼-len : ∀ {bs bs'} → bs ≼ bs' → length bs ≤ length bs'
≼-len here = ≤-refl
≼-len (there p) = m≤n⇒m≤1+n (≼-len p)

{- a block keeps its label, and its older blocks, among newer blocks -}
block-≼ : ∀ {t bs bs'} → t ∷ bs ≼ bs' → block bs' (length bs) ≡ just (t , bs)
block-≼ {bs = bs} here with length bs ≟ length bs
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)
block-≼ {bs = bs} (there {bs' = bs'} p) with length bs ≟ length bs'
... | yes eq = ⊥-elim (<-irrefl eq (≼-len p))
... | no _ = block-≼ p

{- the translation of an expression whose value is the result (tailM), or
   is assigned to x before k runs (asgM x k) -}
data Mode : Set where
  tailM : Mode
  asgM : ℕ → Tail → Mode

ex : Exp → Mode → List Tail → Tail × List Tail
ex e tailM = explicate-tail e
ex e (asgM x k) = explicate-assign e x k

grows : ∀ e m bs → bs ≼ proj₂ (ex e m bs)
grows (simple s) tailM bs = here
grows (simple s) (asgM x k) bs = here
grows (assign y e₁ e₂) tailM bs = ≼-trans (grows e₂ tailM bs) (grows e₁ (asgM y _) _)
grows (assign y e₁ e₂) (asgM x k) bs = ≼-trans (grows e₂ (asgM x k) bs) (grows e₁ (asgM y _) _)
grows (case a y e₁ e₂) tailM bs = there (≼-trans (there (grows e₁ tailM bs)) (grows e₂ tailM _))
grows (case a y e₁ e₂) (asgM x k) bs =
  there (≼-trans (there (≼-trans (there here) (grows e₁ (asgM x _) _))) (grows e₂ (asgM x _) _))

{- the assignments the Imp machine enters before e runs as a tail -}
depth : Exp → ℕ
depth (assign x e₁ e₂) = suc (depth e₁)
depth _ = 0

{- The simulation, for a program with table ds and main body n₀, e₀ ----------------}

module Sim (ds : List Imp.Body) (n₀ : ℕ) (e₀ : Exp) where

  ds₂ = map explicate-body ds
  L₂ = G.sem (explicate (program ds (body n₀ e₀)))

  private variable
    i x y l₁ l₂ : ℕ
    a : Atm
    e e₁ e₂ : Exp
    k : Tail
    bs bs' : List Tail
    m : Mode
    φ : I.Frame
    v : I.Val
    κ₁ : I.Cont
    κ₂ : G.Cont
    s₁ : I.State
    s₂ : G.State

  mutual
    {- κ₂ continues as κ₁, given a value -}
    infix 4 _≈_
    data _≈_ : I.Cont → G.Cont → Set where
      halt : I.halt ≈ G.halt
      frm : ∀ f → κ₁ ≈ κ₂ → I.frm f κ₁ ≈ G.frm f κ₂
      callK : κ₁ ≈ κ₂ → I.callK φ κ₁ ≈ G.callK φ κ₂
      seqK : Ctl bs κ₁ (asgM x k) κ₂ → bs ≼ bs' → κ₁ ≈ G.seqK x k bs' κ₂
      caseK : Br κ₁ e₁ κ₂ bs l₁ → Br κ₁ e₂ κ₂ bs l₂ → I.caseK x e₁ e₂ κ₁ ≈ G.caseK x l₁ l₂ bs κ₂

    {- κ₁ is the continuation of an expression that runs, made at the blocks
       bs in mode m, under κ₂ -}
    data Ctl : List Tail → I.Cont → Mode → G.Cont → Set where
      tl : κ₁ ≈ κ₂ → Ctl bs κ₁ tailM κ₂
      asg : Ctl bs κ₁ m κ₂ → proj₂ (ex e m bs) ≼ bs'
        → Ctl bs' (I.assignK x e κ₁) (asgM x (proj₁ (ex e m bs))) κ₂
      jmp : Ctl bs κ₁ (asgM x k) κ₂ → k ∷ bs ≼ bs' → Ctl bs' κ₁ (asgM x (goto (length bs))) κ₂

    {- block l of bs runs e under κ₁ -}
    data Br (κ₁ : I.Cont) (e : Exp) (κ₂ : G.Cont) (bs' : List Tail) (l : ℕ) : Set where
      br : Ctl bs κ₁ m κ₂ → block bs' l ≡ just (ex e m bs) → Br κ₁ e κ₂ bs' l

  data Match : ℕ → I.State → G.State → Set where
    exec~ : Ctl bs κ₁ m κ₂ → proj₂ (ex e m bs) ≼ bs'
      → Match (depth e) (I.eval e φ κ₁) (G.exec (proj₁ (ex e m bs)) φ bs' κ₂)
    eval~ : κ₁ ≈ κ₂ → Match 0 (I.eval (simple (atm a)) φ κ₁) (G.eval a φ κ₂)
    ret~ : κ₁ ≈ κ₂ → Match 0 (I.ret v φ κ₁) (G.ret v φ κ₂)

  Ans = Answers≺ L₂ Match

  go : ∀ {j s₁ s₂'} → G.step ds₂ s₂ ≡ next s₂' → Match j s₁ s₂' → Ans i (next s₁) s₂
  go st m = steps (plus st ε) m

  {- the tail k, run after the assignment to x, runs the rest of the
     assignment, after the jumps to join points -}
  join : Ctl bs κ₁ (asgM x k) κ₂ → bs ≼ bs'
    → Σ[ e ∈ Exp ] Σ[ κ ∈ I.Cont ] κ₁ ≡ I.assignK x e κ
       × (∀ φ → Σ[ s₂ ∈ G.State ] Star L₂ (G.exec k φ bs' κ₂) s₂ × Match (depth e) (I.eval e φ κ) s₂)
  join (asg c p) q = _ , _ , refl , λ φ → _ , ε , exec~ c (≼-trans p q)
  join (jmp c p) q with join c here
  ... | e , κ , refl , j = e , κ , refl , λ φ → let (s₂ , σ , m) = j φ in
    s₂ , cong (λ b → G.jump (just φ) b _) (block-≼ (≼-trans p q)) ◅ σ , m

  branch : ∀ {mφ bs} → G.step ds₂ s₂ ≡ G.jump mφ (just (k , bs)) κ₂
    → (∀ φ → Σ[ s₂' ∈ G.State ] Star L₂ (G.exec k φ bs κ₂) s₂' × Match (depth e) (I.eval e φ κ₁) s₂')
    → Ans i (I.goto mφ e κ₁) s₂
  branch {mφ = nothing} st j = stops st
  branch {mφ = just φ} st j with j φ
  ... | _ , σ , m = steps (plus st σ) m

  branch-br : ∀ {mφ l} → Br κ₁ e κ₂ bs l → G.step ds₂ s₂ ≡ G.jump mφ (block bs l) κ₂
    → Ans i (I.goto mφ e κ₁) s₂
  branch-br (br c eq) st = branch (trans st (cong (λ b → G.jump _ b _) eq)) λ φ → _ , ε , exec~ c here

  glob : ∀ n → G.global ds₂ n ≡ mmap explicate-body (Imp.global ds n)
  glob n = trans (cong (_‼ n) (sym (reverse-map explicate-body ds))) (‼-map explicate-body (reverse ds) n)

  call-ans : ∀ mb {u w} → κ₁ ≈ κ₂ → G.step ds₂ s₂ ≡ G.call (mmap explicate-body mb) u w φ κ₂
    → Ans i (I.call mb u w φ κ₁) s₂
  call-ans nothing r st = stops st
  call-ans (just (body n e)) r st = go st (exec~ {m = tailM} (tl (callK r)) here)

  res-ans : κ₁ ≈ κ₂ → ∀ r → G.step ds₂ s₂ ≡ G.res ds₂ r φ κ₂ → Ans i (I.res ds r φ κ₁) s₂
  res-ans r (I.operand a f) st = go st (eval~ (frm f r))
  res-ans r (I.value (just v)) st = go st (ret~ r)
  res-ans r (I.value nothing) st = stops st
  res-ans r (I.apply n u w) st = call-ans (Imp.global ds n) r (trans st (cong (λ mb → G.call mb u w _ _) (glob n)))

  sim : Match i s₁ s₂ → Ans i (I.step ds s₁) s₂
  sim (exec~ {e = simple s} (tl r) p) = res-ans r (I.first _ s) refl
  sim (exec~ {m = asgM x k} {e = simple s} c p) = res-ans (seqK c p) (I.first _ s) refl
  sim (exec~ {m = tailM} {e = assign y e₁ e₂} c p) = stutters ≤-refl (exec~ (asg c here) p)
  sim (exec~ {m = asgM x k} {e = assign y e₁ e₂} c p) = stutters ≤-refl (exec~ (asg c here) p)
  sim (exec~ {e = case a y e₁ e₂} (tl r) p) = go refl (eval~ (caseK
    (br (tl r) (block-≼ (≼-trans (there (grows e₂ tailM _)) p))) (br (tl r) (block-≼ p))))
  sim (exec~ {m = asgM x k} {e = case a y e₁ e₂} c p) = go refl (eval~ (caseK
    (br (jmp c here) (block-≼ (≼-trans (there (grows e₂ (asgM x _) _)) p)))
    (br (jmp c (there (grows e₁ (asgM x _) _))) (block-≼ p))))
  sim (eval~ {a = a} r) = res-ans r (I.value (I.atom _ a)) refl
  sim (ret~ halt) = stops refl
  sim (ret~ {v = v} (frm f r)) = res-ans r (I.resume v f) refl
  sim (ret~ (callK r)) = go refl (ret~ r)
  sim (ret~ (seqK c p)) with join c p
  ... | _ , _ , refl , j = branch refl j
  sim (ret~ {v = I.inl v} (caseK b₁ b₂)) = branch-br b₁ refl
  sim (ret~ {v = I.inr v} (caseK b₁ b₂)) = branch-br b₂ refl
  sim (ret~ {v = I.code _} (caseK _ _)) = stops refl
  sim (ret~ {v = I.pair _ _} (caseK _ _)) = stops refl
  sim (ret~ {v = I.const _ _} (caseK _ _)) = stops refl
  sim (ret~ {v = I.tup _} (caseK _ _)) = stops refl

  fsim : FSim (I.sem (program ds (body n₀ e₀))) L₂
  fsim = record { match = Match ; init = _ , exec~ {m = tailM} (tl halt) here ; sim = sim }

{- The end theorem ---------------------------------------------------------------}

explicate-correct : ∀ P → Equivalent (I.sem P) (G.sem (explicate P))
explicate-correct (program ds (body n e)) = equivalent (Sim.fsim ds n e)

{- The whole compiler, into CFG -------------------------------------------------}

compile-cfg-correct : ∀ M → Closed M → Equivalent (S.sem M) (G.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))
