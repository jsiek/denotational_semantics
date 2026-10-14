{-

  Correctness of select instructions (CFGᵀ → X86ᵀ, Compiler/Select.agda)
  by clocked interpreters, clock for clock, with no value relation: the
  two interpreters hold the same values in the same frame, so for every
  clock the X86ᵀ program gives exactly the result of the CFGᵀ one
  (clocked-≡).

  The code selected for a simple expression s into o, then k (sel s o k),
  gives the CFGᵀ result of s, bound to what k gives with the value in o,
  whatever the registers and the flag (sel-ok); a tail gives what it
  gives in CFGᵀ, with any registers and flag (tail-ok), and so does a
  jump (jump-ok), given that calls give the same results at that clock
  (Calls), which holds by induction on the clock (call-ok). The only
  steps that are not definitional are sete (equal-bit), tuple's operands
  (args-ok) and the selected definitions (map-!).

-}

module proof.Correctness.Interp.SelectFuel where

open import Language.Prim using (sub; eq)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Lookup using (_!_)
open import proof.Framework.Lookup using (map-!)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Language.Typed.Imp as I
open import Language.Typed.X86
open import Compiler.Select
open import proof.Semantics.Interp.Clock
open import Semantics.Interp.Typed.Clos5 using (module Vals)
open import Semantics.Interp.Typed.Imp using (eval-simple) renaming (atom to value-of)
import Semantics.Interp.Typed.CFG as G
import Semantics.Interp.Typed.X86 as X
open X using (⟨_,_,_,_⟩; put)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

module _ {Σ : List ℕ} (ds : All (λ n → C.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) where
  open Vals Σ

  xds = All-map def-body ds

  equal-bit : ∀ v w → X.bit (X.equal v w) ≡ δ eq v w
  equal-bit (const n) (const k) = refl

  args-ok : ∀ {Δ j η Γ O F} {m : X.Mach Σ η (st Γ Δ O F)} (as : Vec (Atm Σ Δ Any) j) → X.args (atms as) m ≡ map (value-of (X.frame m)) as
  args-ok [] = refl
  args-ok (a ∷ as) = cong (_ ∷_) (args-ok as)

  {- calls give the same results at clock ck -}
  Calls : ℕ → Set
  Calls ck = ∀ v w → X.call xds ck (X.code-of v) (X.env-of v) w ≡ G.call ds ck v w

  module _ (ck : ℕ) (H : Calls ck) where

    sel-ok : ∀ {n Bs Δ A Δ''} {bs : Blocks Σ n Bs} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
      {f : X.Flag Σ F} {φ : Env Δ} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {K}
      → (∀ {η Γ O F} (ρ : X.RegVals Σ η Γ) (op : X.Opened Σ η O) (f : X.Flag Σ F) v
           → X.run xds ck bs η (put (dst o) v ⟨ ρ , φ , op , f ⟩) k ≡ K v)
      → (s : I.Simple Σ Δ A) → X.run xds ck bs η ⟨ ρ , φ , op , f ⟩ (sel s o k) ≡ (eval-simple (G.call ds ck) φ s >>= K)
    sel-ok o h (I.atm a) = h _ _ _ _
    sel-ok o h (I.pack a b) = h _ _ _ _
    sel-ok {φ = φ} o h (I.callc (var x) a) = bind≡ (H (φ ! x) (value-of φ a)) λ v → h _ _ _ v
    sel-ok {ρ = ρ} {op} {f} {φ} o h (I.tuple as) rewrite args-ok {m = ⟨ ρ , φ , op , f ⟩} as = h _ _ _ _
    sel-ok o h (I.get i a) = h _ _ _ _
    sel-ok o h (I.inl a) = h _ _ _ _
    sel-ok o h (I.inr a) = h _ _ _ _
    sel-ok o h (I.prim sub a b) = h _ _ _ _
    sel-ok {φ = φ} o {K = K} h (I.prim eq a b) = trans (h _ _ _ _) (cong K (equal-bit (value-of φ a) (value-of φ b)))
    sel-ok o h (I.inject G a) = h _ _ _ _
    sel-ok {φ = φ} o h (I.project t (var x)) = bind-cong (project? t (φ ! x)) λ v → h _ _ _ v

    tail-ok : ∀ {n Bs Δ} {bs : C.Blocks Σ Bs} {η Γ O F} {ρ : X.RegVals Σ η Γ} {op : X.Opened Σ η O}
      {f : X.Flag Σ F} {φ : Env Δ} (t : Tail Σ Bs Δ) .{le le'}
      → X.run xds ck (blocks {n = n} bs le') η ⟨ ρ , φ , op , f ⟩ (tail t le) ≡ G.tail ds ck bs φ t
    jump-ok : ∀ {n Bs Δ} (bs : C.Blocks Σ Bs) (l : Bs ∋ Δ) .{le} {η φ}
      → X.jump xds ck (blocks {n = n} bs le) η l φ ≡ G.jump ds ck bs l φ
    case-ok : ∀ {n Bs Δ'} {bs : C.Blocks Σ Bs} {l₁ l₂ : Bs ∋ (Any ∷ Δ')} .{le} {η} {φ : Env Δ'} (v : Val ⟪ sum ⟫)
      → X.jump xds ck (blocks {n = n} bs le) η (if either v (λ _ → true) (λ _ → false) then l₁ else l₂) (X.field′ payload v ∷ φ)
        ≡ either v (λ u → G.jump ds ck bs l₁ (u ∷ φ)) (λ u → G.jump ds ck bs l₂ (u ∷ φ))

    tail-ok (return s) = trans (sel-ok ret (λ _ _ _ _ → refl) s) (bind-ret _)
    tail-ok (seq p s t) = sel-ok (to p _) (λ _ _ _ _ → tail-ok t) s
    tail-ok {bs = bs} (goto l) = jump-ok bs l
    tail-ok {bs = bs} {φ = φ} (case a p l₁ l₂) = case-ok {bs = bs} (value-of φ a)

    jump-ok (bs ▷ t) Z = tail-ok t
    jump-ok (bs ▷ t) (S l) = jump-ok bs l

    case-ok {bs = bs} {l₁} (inl u) = jump-ok bs l₁
    case-ok {bs = bs} {l₂ = l₂} (inr u) = jump-ok bs l₂

  call-ok : ∀ ck → Calls ck
  call-ok zero v w = refl
  call-ok (suc ck) (pack (code f) e) w rewrite map-! def-body ds f with ds ! f
  ... | C.body bs t = tail-ok ck (call-ok ck) t

select-correct : ∀ (P : C.Program) → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds (C.body bs t)) = clocked-≡ λ ck → sym (tail-ok ds ck (call-ok ds ck) t)
