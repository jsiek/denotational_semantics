{-

  Correctness of explicate control (Impμ → CFGμ), clock for clock, as
  for typed explicate control
  (ISWIM/proof/Correctness/Interp/ExplicateFuel.agda). The pass keeps every
  call, the values are the same, and so the two programs give the same result
  for every clock.

  The pass threads the blocks made so far and only adds blocks (Ext), so
  a jump to a block made earlier finds it (jump-at). A tail means K when
  it gives K φ in every frame φ (Ok bs K o). The CPS lemma (assign-ok)
  says that if k means K, then explicate-assign e x p k means running e,
  writing its value to slot x and running K in the frame restricted to
  the slots that k starts with; explicate-tail e means the value of e
  (tail-ok). An assignment nested in e writes a slot y that is not
  initialized where e starts, so k, which does not read y, runs in the
  same frame as in Impμ (restrict-fresh).

-}

module FPC.proof.Correctness.ClockedInterpreters.ExplicateFuel where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import FPC.Language.Imp as Imp
open Imp using (⊆-refl; ⊆-⊕⊕)
open import FPC.Language.CFG
open import FPC.Compiler.Explicate
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Semantics.Slots using (write; restrict; params)
open import FPC.proof.Framework.SlotsProp using (restrict-id; restrict-fresh)
open import proof.Semantics.Interp.Clock
import FPC.Semantics.ClockedInterpreters.GlobalFun as C
import FPC.Semantics.ClockedInterpreters.Imp as Ip
import FPC.Semantics.ClockedInterpreters.CFG as G
open import FPC.Semantics.ClockedInterpreters.Imp using (Fr; atom; eval-simple)
open import FPC.proof.Semantics.ClockedInterpreters.GlobalFun using (def-map;
  either-cong)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong)

{- the blocks bs' are bs and more -}
data Ext {Σ R Δ} : ∀ {Bs Bs'} → Blocks Σ R Δ Bs → Bs ⊑ Bs'
  → Blocks Σ R Δ Bs' → Set where
  same : ∀ {Bs} {bs : Blocks Σ R Δ Bs} → Ext bs here⊑ bs
  more : ∀ {Bs Bs' I} {bs : Blocks Σ R Δ Bs} {g} {bs' : Blocks Σ R Δ Bs'}
    {t : Tail Σ R Δ Bs' I} → Ext bs g bs' → Ext bs (there⊑ g) (bs' ▷ t)

ext-trans : ∀ {Σ R Δ Bs₀ Bs₁ Bs₂} {bs₀ : Blocks Σ R Δ Bs₀}
  {bs₁ : Blocks Σ R Δ Bs₁} {bs₂ : Blocks Σ R Δ Bs₂} {g₁ g₂}
  → Ext bs₀ g₁ bs₁
  → Ext bs₁ g₂ bs₂
  → Ext bs₀ (⊑-trans g₁ g₂) bs₂
ext-trans e₁ same = e₁
ext-trans e₁ (more e₂) = more (ext-trans e₁ e₂)

module _ {Σ : List DSig}
  (ds : All (λ s → Imp.Body Σ (Args s) (DSig.cod s)) Σ) where
  open C.Vals Σ
  private ds' = map explicate-body ds

  module _ (ck : ℕ)
    (calls : ∀ {A B} (f : Val (A ⇒ B)) w
      → Ip.call ds ck f w ≡ G.call ds' ck f w)
    where

    simple≡ : ∀ {Δ I A} (φ : Fr Δ I) (s : Simple Σ Δ I A)
      → eval-simple (Ip.call ds ck) φ s ≡ eval-simple (G.call ds' ck) φ s
    simple≡ φ (Imp.atm a) = refl
    simple≡ φ (Imp.pair a b) = refl
    simple≡ φ (Imp.callc a b) = calls _ _
    simple≡ φ (Imp.tuple as) = refl
    simple≡ φ (Imp.get i a) = refl
    simple≡ φ (Imp.inl a) = refl
    simple≡ φ (Imp.inr a) = refl
    simple≡ φ (Imp.prim p a b) = refl
    simple≡ φ (Imp.fold a) = refl
    simple≡ φ (Imp.unfold a) = refl

    module _ {R : Type} {Δ : Ctx} where

      jump-at : ∀ {Bs Bs' I} {bs : Blocks Σ R Δ Bs} {g}
        {bs' : Blocks Σ R Δ Bs'} (l : Bs ∋ I) φ
        → Ext bs g bs'
        → G.jump ds' ck bs l φ ≡ G.jump ds' ck bs' (⊑-∋ g l) φ
      jump-at l φ same = refl
      jump-at l φ (more e) = jump-at l φ e

      {- K is what the output o of the pass from bs means -}
      record Ok {Bs I} (bs : Blocks Σ R Δ Bs) (K : Fr Δ I → Result (Val R))
        (o : Out Σ R Δ Bs I) : Set where
        constructor ok
        field
          exts : Ext bs (Out.grows o) (Out.made o)
          means : ∀ φ → K φ ≡ G.tail ds' ck (Out.made o) φ (Out.tail o)

      after-ok : ∀ {Bs Bs₁ I} {bs : Blocks Σ R Δ Bs}
        {bs₁ : Blocks Σ R Δ Bs₁} {g} (o : Out Σ R Δ Bs₁ I) {K}
        → Ext bs g bs₁
        → Ok bs₁ K o
        → Ok bs K (after g o)
      after-ok (out g' bs' t) e (ok e' m) = ok (ext-trans e e') m

      either-bind : ∀ {A B C} (u : Val (A ⊹ B)) {f : Val A → Result (Val C)}
        {g : Val B → Result (Val C)}
        {h : Val C → Result (Val R)}
        → (either u f g >>= h) ≡ either u (λ v → f v >>= h) (λ v → g v >>= h)
      either-bind (inl v) = refl
      either-bind (inr v) = refl

      assign-ok : ∀ {Bs A} {I J} (e : Imp.Exp Σ Δ I A) (x : Δ ∋ A)
        (p : J ⊆ I ⊕ x) (k : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs)
        {K : Fr Δ J → Result (Val R)}
        → (∀ φ → K φ ≡ G.tail ds' ck bs φ k)
        → Ok bs (λ φ → Ip.eval ds ck φ e >>= λ v → K (restrict p (write φ x v)))
          (explicate-assign e x p k bs)
      assign-ok (Imp.simple s) x p k bs h =
        ok same λ φ → bind≡ (simple≡ φ s) λ v → h _
      assign-ok {I = I} {J} (Imp.assign y yn e₁ e₂) x p k bs {K} h
        with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
        | assign-ok e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs h
      ... | out g bs₁ t | ok e m
        with explicate-assign e₁ y (⊆-refl {I = I ⊕ y}) t bs₁
        | assign-ok e₁ y (⊆-refl {I = I ⊕ y}) t bs₁ m
      ...   | o | ok e' m' =
        after-ok o e (ok e' λ φ →
          trans (bind-assoc (Ip.eval ds ck φ e₁))
            (trans (bind-cong (Ip.eval ds ck φ e₁) λ u →
              trans
                (bind-cong (Ip.eval ds ck (write φ y u) e₂) λ v →
                  cong K (sym (restrict-fresh φ y u x v yn p _)))
                (cong (λ ψ → Ip.eval ds ck ψ e₂ >>= λ v →
                         K (restrict (⊆-⊕⊕ {I = I} {J} x y p) (write ψ x v)))
                  (sym (restrict-id (write φ y u) _))))
              (m' φ)))
      assign-ok {I = I} {J} (Imp.case a y yn z zn e₁ e₂) x p k bs {K} h
        with explicate-assign e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
          | assign-ok e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k) h
      ... | out g₁ bs₁ t₁ | ok e₁' m₁
        with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
          (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
           | assign-ok e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
               (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
             (λ φ → trans (h φ) (jump-at Z φ e₁'))
      ...   | out g₂ bs₂ t₂ | ok e₂' m₂ =
        ok (more (ext-trans (more (ext-trans (more same) e₁')) e₂'))
        λ φ → trans (either-bind (atom φ a))
                    (either-cong (atom φ a)
                        (λ u →
                          trans
                            (bind-cong (Ip.eval ds ck (write φ y u) e₁) λ v →
                              cong K (sym (restrict-fresh φ y u x v yn p _)))
                            (trans (m₁ _) (jump-at Z _ e₂')))
                        (λ u →
                          trans
                            (bind-cong (Ip.eval ds ck (write φ z u) e₂) λ v →
                              cong K (sym (restrict-fresh φ z u x v zn p _)))
                            (m₂ _)))

      tail-ok : ∀ {Bs I} (e : Imp.Exp Σ Δ I R) (bs : Blocks Σ R Δ Bs)
        → Ok bs (λ φ → Ip.eval ds ck φ e) (explicate-tail e bs)
      tail-ok (Imp.simple s) bs = ok same λ φ → simple≡ φ s
      tail-ok {I = I} (Imp.assign x xn e₁ e₂) bs
        with explicate-tail e₂ bs | tail-ok e₂ bs
      ... | out g bs₁ t | ok e m
        with explicate-assign e₁ x (⊆-refl {I = I ⊕ x}) t bs₁
        | assign-ok e₁ x (⊆-refl {I = I ⊕ x}) t bs₁ m
      ...   | o | ok e' m' =
        after-ok o e (ok e' λ φ →
          trans
            (bind-cong (Ip.eval ds ck φ e₁) λ v →
              cong (λ ψ → Ip.eval ds ck ψ e₂)
                (sym (restrict-id (write φ x v) _)))
            (m' φ))
      tail-ok (Imp.case a x xn y yn e₁ e₂) bs
        with explicate-tail e₁ bs | tail-ok e₁ bs
      ... | out g₁ bs₁ t₁ | ok e₁' m₁
        with explicate-tail e₂ (bs₁ ▷ t₁) | tail-ok e₂ (bs₁ ▷ t₁)
      ...   | out g₂ bs₂ t₂ | ok e₂' m₂ =
        ok (more (ext-trans (more e₁') e₂'))
        λ φ →
          either-cong (atom φ a) (λ v → trans (m₁ _) (jump-at Z _ e₂'))
          (λ v → m₂ _)

    body-ok : ∀ {Δ' A B} (b : Imp.Body Σ (A ∷ tup Δ' ∷ []) B) v w
      → Ip.run ds ck b v w ≡ G.run ds' ck (explicate-body b) v w
    body-ok (Imp.body Δ p e) v w = Ok.means (tail-ok e []) (params p v w)

  calls≡ : ∀ ck {A B} (f : Val (A ⇒ B)) w
    → Ip.call ds ck f w ≡ G.call ds' ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w rewrite def-map explicate-body ds f =
    body-ok ck (calls≡ ck) (lookup ds f) e w

explicate-correct : ∀ {A} (P : Imp.Program A)
  → Equivalent (Ip.sem P) (G.sem (explicate P))
explicate-correct (Imp.program ds (Imp.body Δ p e)) =
  clocked-≡ λ ck → Ok.means (tail-ok ds ck (calls≡ ds ck) e []) _
