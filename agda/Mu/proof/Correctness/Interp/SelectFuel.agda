{-

  Correctness of select instructions (CFGμ → X86μ) by clocked
  interpreters, clock for clock, with no value relation, as for typed
  select (proof/Correctness/Interp/SelectFuel.agda): the two
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
  (args-ok) and the selected definitions (def-map).

-}

module Mu.proof.Correctness.Interp.SelectFuel where

open import Language.Prim using (sub; eq)
open import Mu.Language.Type
import Mu.Language.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Mu.Language.Imp as I
open import Mu.Language.X86
open import Mu.Compiler.Select
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import proof.Semantics.Interp.Clock
open import Mu.Semantics.Interp.Clos5 using (module Vals)
open import Mu.Semantics.Interp.Imp using (eval-simple) renaming (atom to value-of)
import Mu.Semantics.Interp.CFG as G
import Mu.Semantics.Interp.X86 as X
open X using (⟨_,_,_,_⟩; put)
open import Mu.proof.Semantics.Interp.Clos5 using (def-map; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

module _ {Σ : List Sig} (ds : All (λ s → C.Body Σ (Sig.cod s) (Args s)) Σ) where
  open Vals Σ

  xds = map def-body ds

  equal-bit : ∀ v w → δ eq v w ≡ X.bit (X.equal v w)
  equal-bit (const n) (const k) = refl

  args-ok : ∀ {Δ Δs η Γ O F} {m : X.Mach Σ η (st Γ Δ O F)} (as : All (Atm Σ Δ) Δs) → X.args (atms as) m ≡ map (value-of (X.frame m)) as
  args-ok [] = refl
  args-ok (a ∷ as) = cong (_ ∷_) (args-ok as)

  {- calls give the same results at clock ck -}
  Calls : ℕ → Set
  Calls ck = ∀ {A B} (v : Val (A ⇒ B)) w → G.call ds ck v w ≡ X.call xds ck (X.code-of v) (X.env-of v) w

  module _ (ck : ℕ) (H : Calls ck) where

    sel-ok : ∀ {n R Bs Δ A Δ''} {bs : Blocks Σ n R Bs} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
      {f : X.Flag Σ F} {φ : Env Δ} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n R Bs (after o Γ O F)} {K}
      → (∀ {η Γ O F} (ρ : X.RegVals Σ η Γ) (op : X.Opened Σ η O) (f : X.Flag Σ F) v
           → K v ≡ X.run xds ck bs η (put (dst o) v ⟨ ρ , φ , op , f ⟩) k)
      → (s : I.Simple Σ Δ A) → (eval-simple (G.call ds ck) φ s >>= K) ≡ X.run xds ck bs η ⟨ ρ , φ , op , f ⟩ (sel s o k)
    sel-ok o h (I.atm a) = h _ _ _ _
    sel-ok o h (I.pack a b) = h _ _ _ _
    sel-ok {φ = φ} o h (I.callc (var x) a) = bind≡ (H (lookup φ x) (value-of φ a)) λ v → h _ _ _ v
    sel-ok {ρ = ρ} {op} {f} {φ} o h (I.tuple as) rewrite args-ok {m = ⟨ ρ , φ , op , f ⟩} as = h _ _ _ _
    sel-ok o h (I.get i a) = h _ _ _ _
    sel-ok o h (I.inl a) = h _ _ _ _
    sel-ok o h (I.inr a) = h _ _ _ _
    sel-ok o h (I.prim sub a b) = h _ _ _ _
    sel-ok {φ = φ} o {K = K} h (I.prim eq a b) = trans (cong K (equal-bit (value-of φ a) (value-of φ b))) (h _ _ _ _)
    sel-ok o h (I.fold a) = h _ _ _ _
    sel-ok o h (I.unfold a) = h _ _ _ _

    tail-ok : ∀ {n R Bs Δ} {bs : C.Blocks Σ R Bs} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
      {f : X.Flag Σ F} {φ : Env Δ} (t : Tail Σ R Bs Δ) .{le le'}
      → G.tail ds ck bs φ t ≡ X.run xds ck (blocks {n = n} bs le') η ⟨ ρ , φ , op , f ⟩ (tail t le)
    jump-ok : ∀ {n R Bs Δ} (bs : C.Blocks Σ R Bs) (l : Bs ∋ Δ) .{le} {η φ}
      → G.jump ds ck bs l φ ≡ X.jump xds ck (blocks {n = n} bs le) η l φ

    tail-ok (return s) = trans (sym (bind-ret _)) (sel-ok ret (λ _ _ _ _ → refl) s)
    tail-ok (seq p s t) = sel-ok (to p _) (λ _ _ _ _ → tail-ok t) s
    tail-ok {bs = bs} (goto l) = jump-ok bs l
    tail-ok {bs = bs} {φ = φ} (case (var x) p l₁ l₂) =
      either-cong (lookup φ x) (λ v → jump-ok bs l₁) (λ v → jump-ok bs l₂)

    jump-ok (bs ▷ t) Z = tail-ok t
    jump-ok (bs ▷ t) (S l) = jump-ok bs l

  call-ok : ∀ ck → Calls ck
  call-ok zero v w = refl
  call-ok (suc ck) (pack (code f) e) w rewrite def-map def-body ds f with lookup ds f
  ... | C.body bs t = tail-ok ck (call-ok ck) t

select-correct : ∀ {A} (P : C.Program A) → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds (C.body bs t)) = clocked-≡ λ ck → tail-ok ds ck (call-ok ds ck) t
