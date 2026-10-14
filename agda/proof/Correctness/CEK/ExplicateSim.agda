{-

  Correctness of typed explicate control (Impᵀ → CFGᵀ,
  Compiler/Explicate.agda) by a forward simulation of the Impᵀ
  machine by the CFGᵀ machine (see the design note in
  Semantics/CEK/Smallstep.agda).

  The machines share the values, the frames and the simple expressions,
  and an expression runs in the same frame on both: a seq or case of
  CFGᵀ forgets exactly the slots that the Impᵀ continuation does not
  see. An expression e whose value is the body's result runs as
  explicate-tail e (tail~); one whose value is assigned to the next slot
  before the tail k runs, as explicate-assign e p k (asg~), where the
  Impᵀ continuation does what k does (Ctl): it is x := □; e₂ for the
  tail made of e₂ (asgT, asgA), or a jump to a block that does (jmp).
  The continuation of a call is related to the CFGᵀ frames seqK and retK
  (_≈_).

  So an Impᵀ step from x := e₁; e₂ is matched by no CFGᵀ step (the
  stutter, measured by the nesting of assignments, depth); any other
  Impᵀ step by one or more CFGᵀ steps (a statement, then the jumps to
  join points). A tail made with some blocks runs with blocks that
  extend them (Ext), where the older labels find the same blocks
  (ext-block): explicate only adds blocks (grows-t, grows-a).

  This proof, between the machines of Impᵀ and CFGᵀ, is shared by the
  CEK machine + simulation and the reduction semantics + simulation
  developments.

-}

module proof.Correctness.CEK.ExplicateSim where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Framework.Lookup using (forget)
import Language.Typed.Imp as Imp
open Imp using (simple; assign; case)
open import Language.Typed.CFG
open import Compiler.Explicate
open import proof.Framework.Lookup using (map-!)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; Reach)
open import proof.Semantics.CEK.Simulation
  using (Answers≺; stops; steps; stutters; steps₁≺; after≺; answers-at; FSim; Equivalent; equivalent)
import Semantics.CEK.Typed.Imp as I
import Semantics.CEK.Typed.CFG as G

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- Blocks ------------------------------------------------------------------------}

{- bs' is bs with newer blocks, along g -}
data Ext {Σ} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ Bs → Blocks Σ Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' Δ g} {bs : Blocks Σ Bs} {bs' : Blocks Σ Bs'} {t : Tail Σ Bs' Δ} → Ext g bs bs'
    → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ As Bs Cs} {g : As ⊑ Bs} {g' : Bs ⊑ Cs} {as : Blocks Σ As} {bs cs}
  → Ext g as bs → Ext g' bs cs → Ext (⊑-trans g g') as cs
ext-trans x here = x
ext-trans x (there y) = there (ext-trans x y)

ext-block : ∀ {Σ Bs Bs' Δ} {g : Bs ⊑ Bs'} {bs : Blocks Σ Bs} {bs'} → Ext g bs bs' → (l : Bs ∋ Δ)
  → block bs' (⊑-∋ g l) ≡ block bs l
ext-block here l = refl
ext-block (there x) l = ext-block x l

grows-a : ∀ {Σ Bs Δ Δ' A} (e : Imp.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ Bs (A ∷ Δ')) bs
  → Ext (Out.grows (explicate-assign e p k bs)) bs (Out.made (explicate-assign e p k bs))
grows-a (simple s) p k bs = here
grows-a (assign e₁ e₂) p k bs = ext-trans (grows-a e₂ (there⊑ p) k bs) (grows-a e₁ here⊑ _ _)
grows-a (case a e₁ e₂) p k bs =
  there (ext-trans (there (ext-trans (there here) (grows-a e₁ (there⊑ p) (goto Z) (bs ▷ k)))) (grows-a e₂ (there⊑ p) _ _))

grows-t : ∀ {Σ Bs Δ} (e : Imp.Exp Σ Δ Any) (bs : Blocks Σ Bs)
  → Ext (Out.grows (explicate-tail e bs)) bs (Out.made (explicate-tail e bs))
grows-t (simple s) bs = here
grows-t (assign e₁ e₂) bs = ext-trans (grows-t e₂ bs) (grows-a e₁ here⊑ _ _)
grows-t (case a e₁ e₂) bs = there (ext-trans (there (grows-t e₁ bs)) (grows-t e₂ _))

{- the assignments the Impᵀ machine enters before e runs as a tail -}
depth : ∀ {Σ Δ A} → Imp.Exp Σ Δ A → ℕ
depth (assign e₁ e₂) = suc (depth e₁)
depth _ = 0

{- The simulation, for a program with definitions ds and main e₀ ---------------}

module Sim {Σ : List ℕ} (ds : All (λ n → Imp.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) (e₀ : Imp.Exp Σ [] Any) where

  ds₂ = All-map explicate-body ds
  L₂ = G.sem (explicate (Imp.program ds e₀))

  mutual
    {- κ₂ continues as κ₁, given the value of the body -}
    infix 4 _≈_
    data _≈_ : I.Cont Σ Any → G.Cont Σ → Set where
      halt : I.halt ≈ G.halt
      retK : ∀ {κ₁ κ₂} → κ₁ ≈ κ₂ → κ₁ ≈ G.retK κ₂
      seqK : ∀ {Bs Δ Δ'} {p : Δ' ⊑ Δ} {φ k} {bs : Blocks Σ Bs} {κ₁ κ₂}
        → Ctl (forget p φ) κ₁ k bs κ₂ → κ₁ ≈ G.seqK p φ k bs κ₂

    {- κ₁, given a value v, continues as the tail k in the frame v ∷ φ -}
    data Ctl : ∀ {Bs Δ A} → I.Frame Σ Δ → I.Cont Σ A → Tail Σ Bs (A ∷ Δ) → Blocks Σ Bs → G.Cont Σ → Set where
      asgT : ∀ {Bs Δ A} {e₂ : Imp.Exp Σ (A ∷ Δ) Any} {φ κ κ₂} {bs : Blocks Σ Bs} → κ ≈ κ₂
        → Ctl φ (I.assignK e₂ φ κ) (Out.tail (explicate-tail e₂ bs)) (Out.made (explicate-tail e₂ bs)) κ₂
      asgA : ∀ {Bs Δ Δ'' A B} {e₂ : Imp.Exp Σ (A ∷ Δ) B} {p : Δ'' ⊑ Δ} {k : Tail Σ Bs (B ∷ Δ'')} {φ κ κ₂ bs}
        → Ctl (forget p φ) κ k bs κ₂
        → Ctl φ (I.assignK e₂ φ κ) (Out.tail (explicate-assign e₂ (there⊑ p) k bs))
              (Out.made (explicate-assign e₂ (there⊑ p) k bs)) κ₂
      jmp : ∀ {Bs Bs' Δ A} {φ κ κ₂} {k : Tail Σ Bs (A ∷ Δ)} {bs : Blocks Σ Bs} {bs' : Blocks Σ Bs'} {l}
        → Ctl φ κ k bs κ₂ → block bs' l ≡ blk bs k → Ctl φ κ (goto l) bs' κ₂

  data Match : ℕ → I.State Σ → G.State Σ → Set where
    tail~ : ∀ {Bs Δ} {e : Imp.Exp Σ Δ Any} {φ κ₁ κ₂} {bs : Blocks Σ Bs} → κ₁ ≈ κ₂
      → Match (depth e) (I.eval e φ κ₁) (G.exec (Out.tail (explicate-tail e bs)) φ (Out.made (explicate-tail e bs)) κ₂)
    asg~ : ∀ {Bs Δ Δ' A} {e : Imp.Exp Σ Δ A} {p : Δ' ⊑ Δ} {k : Tail Σ Bs (A ∷ Δ')} {bs φ κ₁ κ₂}
      → Ctl (forget p φ) κ₁ k bs κ₂
      → Match (depth e) (I.eval e φ κ₁)
          (G.exec (Out.tail (explicate-assign e p k bs)) φ (Out.made (explicate-assign e p k bs)) κ₂)

  Ans = Answers≺ L₂ Match

  private variable
    i : ℕ
    A : Ty
    s₂ : G.State Σ
    κ₁ : I.Cont Σ A
    κ₂ : G.Cont Σ

  {- the tail k, run after the assignment, does what κ₁ does -}
  ctl : ∀ {Bs Δ} {φ : I.Frame Σ Δ} {k : Tail Σ Bs (A ∷ Δ)} {bs} → Ctl φ κ₁ k bs κ₂ → ∀ v
    → Σ[ s₁ ∈ I.State Σ ] I.cont ds v κ₁ ≡ next s₁ × Σ[ j ∈ ℕ ] Reach L₂ (Match j) s₁ (G.exec k (v ∷ φ) bs κ₂)
  ctl (asgT r) v = _ , refl , _ , _ , ε , tail~ r
  ctl (asgA c) v = _ , refl , _ , _ , ε , asg~ c
  ctl (jmp {φ = φ} {κ₂ = κ₂} c eq) v with ctl c v
  ... | s₁ , e , j , t , σ , m = s₁ , e , j , t , cong (λ b → next (G.go ds₂ b (v ∷ φ) κ₂)) eq ◅ σ , m

  cont≈ : κ₁ ≈ κ₂ → ∀ v → G.step ds₂ s₂ ≡ G.cont ds₂ v κ₂ → Ans i (I.cont ds v κ₁) s₂
  cont≈ halt v st = stops st
  cont≈ (retK r) v st = cont≈ r v st
  cont≈ (seqK c) v st with ctl c v
  ... | _ , e , _ , rch = answers-at e (after≺ st rch)

  call≈ : ∀ f w {κ'} → G.step ds₂ s₂ ≡ G.enter ds₂ f w κ' → κ₁ ≈ κ' → Ans i (I.res ds (I.call f w) κ₁) s₂
  call≈ (I.pack (I.code g) e) w st r =
    steps₁≺ (trans st (cong (λ d → next (G.exec (Body.start d) _ (Body.blocks d) _)) (map-! explicate-body ds g))) (tail~ r)

  res-t : κ₁ ≈ κ₂ → ∀ r → G.step ds₂ s₂ ≡ G.retn ds₂ κ₂ r → Ans i (I.res ds r κ₁) s₂
  res-t r (I.value v) st = cont≈ r v st
  res-t r I.fail st = stops st
  res-t r (I.call f w) st = call≈ f w st (retK r)

  res-a : ∀ {Bs Δ Δ'} {p : Δ' ⊑ Δ} {φ} {k : Tail Σ Bs (A ∷ Δ')} {bs} → Ctl (forget p φ) κ₁ k bs κ₂
    → ∀ r → G.step ds₂ s₂ ≡ G.assign ds₂ p φ k bs κ₂ r → Ans i (I.res ds r κ₁) s₂
  res-a c (I.value v) st with ctl c v
  ... | _ , e , _ , rch = answers-at e (after≺ st rch)
  res-a c I.fail st = stops st
  res-a c (I.call f w) st = call≈ f w st (seqK c)

  {- a case: both machines take the branch of the injection -}
  branch : ∀ {j₁ j₂} (v : I.Val Σ ⟪ sum ⟫) {f₁ f₂ : I.Val Σ Any → I.State Σ} {g₁ g₂ : I.Val Σ Any → G.State Σ}
    → G.step ds₂ s₂ ≡ next (I.choose v g₁ g₂) → (∀ u → Match j₁ (f₁ u) (g₁ u)) → (∀ u → Match j₂ (f₂ u) (g₂ u))
    → Ans i (next (I.choose v f₁ f₂)) s₂
  branch (I.inl u) st m₁ m₂ = steps₁≺ st (m₁ u)
  branch (I.inr u) st m₁ m₂ = steps₁≺ st (m₂ u)

  at : ∀ {Δ} {b b' : Blk Σ Δ} {j s₁ φ} → b ≡ b' → Match j s₁ (G.go ds₂ b' φ κ₂) → Match j s₁ (G.go ds₂ b φ κ₂)
  at refl m = m

  sim : ∀ {i s₁ s₂} → Match i s₁ s₂ → Ans i (I.step ds s₁) s₂
  sim (tail~ {e = simple s} {φ = φ} r) = res-t r (I.run s φ) refl
  sim (asg~ {e = simple s} {φ = φ} c) = res-a c (I.run s φ) refl
  sim (tail~ {e = assign e₁ e₂} r) = stutters ≤-refl (asg~ (asgT r))
  sim (asg~ {e = assign e₁ e₂} c) = stutters ≤-refl (asg~ (asgA c))
  sim (tail~ {e = case a e₁ e₂} {φ = φ} {bs = bs} r) =
    branch (I.atom φ a) refl (λ u → at (ext-block (grows-t e₂ _) Z) (tail~ r)) (λ u → tail~ r)
  sim (asg~ {e = case a e₁ e₂} {p = p} {k = k} {bs = bs} {φ = φ} c) =
    branch (I.atom φ a) refl (λ u → at (ext-block (grows-a e₂ (there⊑ p) _ _) Z) (asg~ (jmp c refl)))
      (λ u → asg~ (jmp c (ext-block (grows-a e₁ (there⊑ p) (goto Z) (bs ▷ k)) Z)))

  fsim : FSim (I.sem (Imp.program ds e₀)) L₂
  fsim = record { match = Match ; init = _ , tail~ halt ; sim = sim }

{- The end theorem ---------------------------------------------------------------}

explicate-correct : ∀ P → Equivalent (I.sem P) (G.sem (explicate P))
explicate-correct (Imp.program ds e) = equivalent (Sim.fsim ds e)
