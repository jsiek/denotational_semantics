{-

  Correctness of lift locals (Monμ → Impμ), clock for clock, as for
  typed lift locals (proof/Correctness/Interp/LiftLocalsFuel.agda). A
  Monμ program means its embedding into GlobalFunμ; the Impμ frame of a body
  is the GlobalFunμ environment of its embedding, and the values are the
  same, so the two programs give the same result for every clock: where
  the calls agree (calls), an expression and its lifting agree
  (lift-ok), and so the calls agree at the next clock (calls≡).

-}

module Mu.proof.Correctness.ClockedInterpreters.LiftLocalsFuel where

open import Mu.Language.Type
open import Mu.Language.Mon
open import Mu.Compiler.LiftLocals
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.GlobalFun as C
import Mu.Semantics.ClockedInterpreters.Imp as I
open import Mu.Semantics.ClockedInterpreters.Imp using (atom)
open import Mu.proof.Semantics.ClockedInterpreters.GlobalFun using (def-map; atm-bind; eval-atom; atoms-bind; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

module _ {Σ : List DSig} (ds : All (λ s → Exp Σ (Args s) (DSig.cod s)) Σ) where
  open C.Vals Σ
  private
    dsC = map ⌜_⌝ ds
    dsI = map lift ds

  module _ (ck : ℕ) (calls : ∀ {A B} (f : Val (A ⇒ B)) w → C.call dsC ck f w ≡ I.call dsI ck f w) where
    lift-ok : ∀ {Δ A} (e : Exp Σ Δ A) (φ : Env Δ) → C.eval dsC ck φ ⌜ e ⌝ ≡ I.eval dsI ck φ (lift e)
    lift-ok (atm a) φ = eval-atom a
    lift-ok (pack a b) φ = trans (atm-bind a) (atm-bind b)
    lift-ok (callc a b) φ = trans (trans (atm-bind a) (atm-bind b)) (calls _ _)
    lift-ok (tuple as) φ = atoms-bind as
    lift-ok (get i a) φ = atm-bind a
    lift-ok (inl a) φ = atm-bind a
    lift-ok (inr a) φ = atm-bind a
    lift-ok (case a e₁ e₂) φ =
      trans (atm-bind a) (either-cong (atom φ a) (λ v → lift-ok e₁ (v ∷ φ)) (λ v → lift-ok e₂ (v ∷ φ)))
    lift-ok (prim p a b) φ = trans (atm-bind a) (atm-bind b)
    lift-ok (let′ e₁ e₂) φ = bind≡ (lift-ok e₁ φ) λ v → lift-ok e₂ (v ∷ φ)
    lift-ok (fold a) φ = atm-bind a
    lift-ok (unfold a) φ = atm-bind a

  calls≡ : ∀ ck {A B} (f : Val (A ⇒ B)) w → C.call dsC ck f w ≡ I.call dsI ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w rewrite def-map lift ds f | def-map ⌜_⌝ ds f =
    lift-ok ck (calls≡ ck) (lookup ds f) _

lift-locals-correct : ∀ {A} (P : Program A) → Equivalent (C.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (program {Σ} ds e) = clocked-≡ λ ck → lift-ok ds ck (calls≡ ds ck) e []
