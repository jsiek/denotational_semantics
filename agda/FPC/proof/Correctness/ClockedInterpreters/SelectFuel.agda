{-

  Correctness of select instructions (CFGμ → X86μ) by clocked
  interpreters, clock for clock, with no value relation, as for typed
  select (ISWIM/proof/Correctness/Interp/SelectFuel.agda): the two
  interpreters hold the same values in the same frame, so for every
  clock the X86μ program gives exactly the result of the CFGμ one
  (clocked-≡).

  The code selected for a simple expression s into o, then k (sel s o k),
  gives the CFGμ result of s, bound to what k gives with the value in o,
  whatever the registers and the flag (sel-ok); a tail gives what it
  gives in CFGμ, with any registers and flag (tail-ok), and so does a
  jump (jump-ok), given that calls give the same results at that clock
  (Calls), which holds by induction on the clock (call-ok). The only
  steps that are not definitional are sete (equal-bit), tuple's operands
  (args-ok), the selected definitions (def-map) and the start of a
  definition, whose two writes restrict the frame to the slots it
  already has (restrict-id).

-}

module FPC.proof.Correctness.ClockedInterpreters.SelectFuel where

open import Language.Prim using (sub; eq)
open import FPC.Language.Type
import FPC.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import FPC.Language.Imp as I
open import FPC.Language.X86
open import FPC.Compiler.Select
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Semantics.Slots using (Slots; read; write; restrict; empty;
  params)
open import FPC.proof.Framework.SlotsProp using (restrict-id)
open import Framework.Membership using (⊑-∋)
open import proof.Semantics.Interp.Clock
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.Imp using (eval-simple) renaming
  (atom to value-of)
import FPC.Semantics.ClockedInterpreters.CFG as G
import FPC.Semantics.ClockedInterpreters.X86 as X
open X using (⟨_,_,_,_⟩; put)
open import FPC.proof.Semantics.ClockedInterpreters.GlobalFun using (def-map;
  either-cong)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong;
  trans)

module _ {Σ : List DSig}
  (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) Σ) where
  open Vals Σ

  xds = map def-body ds

  equal-bit : ∀ v w → δ eq v w ≡ X.bit (X.equal v w)
  equal-bit (const n) (const k) = refl

  args-ok : ∀ {Δ I Δs η Γ O F} {m : X.Mach Σ η (st {Δ} Γ I O F)}
    (as : All (Atm Σ Δ I) Δs)
    → X.args (atms as) m ≡ map (value-of (X.frame m)) as
  args-ok [] = refl
  args-ok (a ∷ as) = cong (_ ∷_) (args-ok as)

  {- calls give the same results at clock ck -}
  Calls : ℕ → Set
  Calls ck =
    ∀ {A B} (v : Val (A ⇒ B)) w
    → G.call ds ck v w ≡ X.call xds ck (X.code-of v) (X.env-of v) w

  module _ (ck : ℕ) (H : Calls ck) where

    sel-ok : ∀ {Δ R Bs A} {I J : I.Inits Δ} {bs : Blocks Σ Δ R Bs} {η Γ O F}
      {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
        {f : X.Flag Σ F} {φ : Slots Val Δ I} (o : Out I A J)
          {k : ∀ {Γ O F} → Seq Σ Δ R Bs (after o Γ O F)} {K}
      →
        (  ∀ {η Γ O F} (ρ : X.RegVals Σ η Γ) (op : X.Opened Σ η O)
          (f : X.Flag Σ F) v
         → K v ≡ X.run xds ck bs η (put (dst o) v ⟨ ρ , φ , op , f ⟩) k)
      → (s : I.Simple Σ Δ I A)
      → (eval-simple (G.call ds ck) φ s >>= K)
        ≡ X.run xds ck bs η ⟨ ρ , φ , op , f ⟩ (sel s o k)
    sel-ok o h (I.atm a) = h _ _ _ _
    sel-ok o h (I.pair a b) = h _ _ _ _
    sel-ok {φ = φ} o h (I.callc (var x i) a) =
      bind≡ (H (read φ x i) (value-of φ a)) λ v → h _ _ _ v
    sel-ok {ρ = ρ} {op} {f} {φ} o h (I.tuple as) rewrite args-ok
      {m = ⟨ ρ , φ , op , f ⟩} as = h _ _ _ _
    sel-ok o h (I.get i a) = h _ _ _ _
    sel-ok o h (I.inl a) = h _ _ _ _
    sel-ok o h (I.inr a) = h _ _ _ _
    sel-ok o h (I.prim sub a b) = h _ _ _ _
    sel-ok {φ = φ} o {K = K} h (I.prim eq a b) =
      trans (cong K (equal-bit (value-of φ a) (value-of φ b))) (h _ _ _ _)
    sel-ok o h (I.fold a) = h _ _ _ _
    sel-ok o h (I.unfold a) = h _ _ _ _

    tail-ok : ∀ {Δ R Bs I} {bs : C.Blocks Σ R Δ Bs} {η Γ O F}
      {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
      {f : X.Flag Σ F} {φ : Slots Val Δ I} (t : Tail Σ R Δ Bs I)
      → G.tail ds ck bs φ t
        ≡ X.run xds ck (blocks bs) η ⟨ ρ , φ , op , f ⟩ (tail t)
    jump-ok : ∀ {Δ R Bs I} (bs : C.Blocks Σ R Δ Bs) (l : Bs ∋ I) {η φ}
      → G.jump ds ck bs l φ ≡ X.jump xds ck (blocks bs) η l φ

    tail-ok (return s) =
      trans (sym (bind-ret _)) (sel-ok ret (λ _ _ _ _ → refl) s)
    tail-ok (seq x s p t) = sel-ok (to x p) (λ _ _ _ _ → tail-ok t) s
    tail-ok {bs = bs} (goto l) = jump-ok bs l
    tail-ok {bs = bs} {φ = φ} (case (var x i) y z l₁ l₂) =
      either-cong (read φ x i) (λ v → jump-ok bs l₁) (λ v → jump-ok bs l₂)

    jump-ok (bs ▷ t) Z = tail-ok t
    jump-ok (bs ▷ t) (S l) = jump-ok bs l

  call-ok : ∀ ck → Calls ck
  call-ok zero v w = refl
  call-ok (suc ck) (pack (code f) e) w rewrite def-map def-body ds f
    with lookup ds f
  ... | C.body Δ p bs t =
    trans (tail-ok ck (call-ok ck) t)
      (cong (λ ψ → X.run xds ck (blocks bs) _ ⟨ _ , ψ , _ , _ ⟩ (tail t))
        (sym
          (trans
            (cong
              (λ ψ →
                restrict (I.⊆-refl {I = I.initial p}) (write ψ (⊑-∋ p Z) w))
              (restrict-id (write (empty Δ) (⊑-∋ p (S Z)) e) _))
            (restrict-id (params p e w) _))))

select-correct : ∀ {A} (P : C.Program A)
  → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds (C.body Δ p bs t)) =
  clocked-≡ λ ck → tail-ok ds ck (call-ok ds ck) t
