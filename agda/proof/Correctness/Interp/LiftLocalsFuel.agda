{-

  Correctness of typed lift locals (Monᵀ → Impᵀ), clock for clock (see
  the design note in Semantics/Interp/Clock.agda). A Monᵀ program means
  its embedding into Clos5ᵀ; the Impᵀ frame of a body is the Clos5ᵀ
  environment of its embedding, and the values are the same, so the two
  programs give the same result for every clock: where the calls agree
  (calls), an expression and its lifting agree (lift-ok), and so the
  calls agree at the next clock (calls≡).

-}

module proof.Correctness.Interp.LiftLocalsFuel where

open import Language.Typed.Type
open import Language.Typed.Mon
import Language.Typed.Imp as Imp
open import Compiler.LiftLocals
open import proof.Semantics.Interp.Clock
open import Framework.Lookup using (_!_)
import Semantics.Interp.Typed.Clos5 as C
import Semantics.Interp.Typed.Imp as I
open import Semantics.Interp.Typed.Imp using (atom)
open import proof.Semantics.Interp.Typed.Clos5 using (def-map; atm-bind; eval-atom; atoms-bind; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

module _ {Σ : List ℕ} (ds : All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) where
  open C.Vals Σ
  private
    dsC = All-map ⌜_⌝ ds
    dsI = All-map lift ds

  module _ (ck : ℕ) (calls : ∀ f w → I.call dsI ck f w ≡ C.call dsC ck f w) where
    lift-ok : ∀ {Δ A} (e : Exp Σ Δ A) (φ : Env Δ) → I.eval dsI ck φ (lift e) ≡ C.eval dsC ck φ ⌜ e ⌝
    lift-ok (atm a) φ = sym (eval-atom a)
    lift-ok (pack a b) φ = sym (trans (atm-bind a) (atm-bind b))
    lift-ok (callc a b) φ = trans (calls _ _) (sym (trans (atm-bind a) (atm-bind b)))
    lift-ok (tuple as) φ = sym (atoms-bind as)
    lift-ok (get i a) φ = sym (atm-bind a)
    lift-ok (inl a) φ = sym (atm-bind a)
    lift-ok (inr a) φ = sym (atm-bind a)
    lift-ok (case a e₁ e₂) φ =
      trans (either-cong (atom φ a) (λ v → lift-ok e₁ (v ∷ φ)) (λ v → lift-ok e₂ (v ∷ φ))) (sym (atm-bind a))
    lift-ok (prim p a b) φ = sym (trans (atm-bind a) (atm-bind b))
    lift-ok (let′ e₁ e₂) φ = bind≡ (lift-ok e₁ φ) λ v → lift-ok e₂ (v ∷ φ)
    lift-ok (inject G a) φ = sym (atm-bind a)
    lift-ok (project t a) φ = sym (atm-bind a)

  calls≡ : ∀ ck f w → I.call dsI ck f w ≡ C.call dsC ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w rewrite def-map lift ds f | def-map ⌜_⌝ ds f =
    lift-ok ck (calls≡ ck) (ds ! f) _

lift-locals-correct : ∀ (P : Program) → Equivalent (C.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (program {Σ} ds e) = clocked-≡ λ ck → sym (lift-ok ds ck (calls≡ ds ck) e [])
