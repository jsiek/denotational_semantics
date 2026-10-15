{-

  Correctness of typed explicate control (Impᵀ → CFGᵀ), clock for clock
  (see the design note in Semantics/Interp/Clock.agda). The pass keeps
  every call, the values are the same, and so the two programs give the
  same result for every clock.

  The pass threads the blocks made so far and only adds blocks (Ext), so
  a jump to a block made earlier finds it (jump-at). A tail means K when
  it gives K φ in every frame φ (Ok bs K o); the CPS lemma (assign-ok): if k
  means K, explicate-assign e p k means running e, assigning its value
  to the slot after Δ' and running K; explicate-tail e means the value
  of e (tail-ok).

-}

module proof.Correctness.Interp.ExplicateFuel where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Language.Typed.Imp as Imp
open import Language.Typed.CFG
open import Compiler.Explicate
open import proof.Semantics.Interp.Clock
import Semantics.Interp.Typed.Clos5 as C
import Semantics.Interp.Typed.Imp as I
import Semantics.Interp.Typed.CFG as G
open import Semantics.Interp.Typed.Imp using (atom; eval-simple)
open import Framework.Lookup using (_!_; forget)
open import proof.Semantics.Interp.Typed.Clos5 using (def-map; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

{- the blocks bs' are bs and more -}
data Ext {Σ} : ∀ {Bs Bs'} → Blocks Σ Bs → Bs ⊑ Bs' → Blocks Σ Bs' → Set where
  same : ∀ {Bs} {bs : Blocks Σ Bs} → Ext bs here⊑ bs
  more : ∀ {Bs Bs' Δ} {bs : Blocks Σ Bs} {g} {bs' : Blocks Σ Bs'} {t : Tail Σ Bs' Δ} → Ext bs g bs' → Ext bs (there⊑ g) (bs' ▷ t)

ext-trans : ∀ {Σ Bs₀ Bs₁ Bs₂} {bs₀ : Blocks Σ Bs₀} {bs₁ : Blocks Σ Bs₁} {bs₂ : Blocks Σ Bs₂} {g₁ g₂}
  → Ext bs₀ g₁ bs₁ → Ext bs₁ g₂ bs₂ → Ext bs₀ (⊑-trans g₁ g₂) bs₂
ext-trans e₁ same = e₁
ext-trans e₁ (more e₂) = more (ext-trans e₁ e₂)

module _ {Σ : List ℕ} (ds : All (λ n → Imp.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) where
  open C.Vals Σ
  private ds' = All-map explicate-body ds

  module _ (ck : ℕ) (calls : ∀ f w → I.call ds ck f w ≡ G.call ds' ck f w) where

    simple≡ : ∀ {Δ A} (φ : Env Δ) (s : Simple Σ Δ A) → eval-simple (I.call ds ck) φ s ≡ eval-simple (G.call ds' ck) φ s
    simple≡ φ (Imp.atm a) = refl
    simple≡ φ (Imp.pack a b) = refl
    simple≡ φ (Imp.callc a b) = calls _ _
    simple≡ φ (Imp.tuple as) = refl
    simple≡ φ (Imp.get i a) = refl
    simple≡ φ (Imp.inl a) = refl
    simple≡ φ (Imp.inr a) = refl
    simple≡ φ (Imp.prim p a b) = refl
    simple≡ φ (Imp.inject G a) = refl
    simple≡ φ (Imp.project t a) = refl

    jump-at : ∀ {Bs Bs' Δ} {bs : Blocks Σ Bs} {g} {bs' : Blocks Σ Bs'} (l : Bs ∋ Δ) φ
      → Ext bs g bs' → G.jump ds' ck bs l φ ≡ G.jump ds' ck bs' (⊑-∋ g l) φ
    jump-at l φ same = refl
    jump-at l φ (more e) = jump-at l φ e

    {- K is what the output o of the pass from bs means -}
    record Ok {Bs Δ} (bs : Blocks Σ Bs) (K : Env Δ → Result (Val Any)) (o : Out Σ Bs Δ) : Set where
      constructor ok
      field
        exts : Ext bs (Out.grows o) (Out.made o)
        means : ∀ φ → K φ ≡ G.tail ds' ck (Out.made o) φ (Out.tail o)

    after-ok : ∀ {Bs Bs₁ Δ} {bs : Blocks Σ Bs} {bs₁ : Blocks Σ Bs₁} {g} (o : Out Σ Bs₁ Δ) {K}
      → Ext bs g bs₁ → Ok bs₁ K o → Ok bs K (after g o)
    after-ok (out g' bs' t) e (ok e' m) = ok (ext-trans e e') m

    either-bind : ∀ {B} (u : Val ⟪ sum ⟫) {f g : Val Any → Result (Val B)} {h : Val B → Result (Val Any)}
      → (either u f g >>= h) ≡ either u (λ v → f v >>= h) (λ v → g v >>= h)
    either-bind (inl v) = refl
    either-bind (inr v) = refl

    assign-ok : ∀ {Bs Δ Δ' A} (e : Imp.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ Bs (A ∷ Δ')) (bs : Blocks Σ Bs) {K : Env (A ∷ Δ') → Result (Val Any)}
      → (∀ φ → K φ ≡ G.tail ds' ck bs φ k)
      → Ok bs (λ φ → I.eval ds ck φ e >>= λ v → K (v ∷ forget p φ)) (explicate-assign e p k bs)
    assign-ok (Imp.simple s) p k bs h = ok same λ φ → bind≡ (simple≡ φ s) λ v → h (v ∷ forget p φ)
    assign-ok (Imp.assign e₁ e₂) p k bs h with explicate-assign e₂ (there⊑ p) k bs | assign-ok e₂ (there⊑ p) k bs h
    ... | out g bs₁ t | ok e m with explicate-assign e₁ here⊑ t bs₁ | assign-ok e₁ here⊑ t bs₁ m
    ...   | o | ok e' m' = after-ok o e (ok e' λ φ → trans (bind-assoc (I.eval ds ck φ e₁)) (m' φ))
    assign-ok (Imp.case a e₁ e₂) p k bs {K} h
      with explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k) | assign-ok e₁ (there⊑ p) (goto Z) (bs ▷ k) h
    ... | out g₁ bs₁ t₁ | ok e₁' m₁
      with explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
         | assign-ok e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁) (λ φ → trans (h φ) (jump-at Z φ e₁'))
    ...   | out g₂ bs₂ t₂ | ok e₂' m₂ =
      ok (more (ext-trans (more (ext-trans (more same) e₁')) e₂'))
      λ φ → trans (either-bind (atom φ a))
                  (either-cong (atom φ a) (λ v → trans (m₁ _) (jump-at Z _ e₂')) (λ v → m₂ _))

    tail-ok : ∀ {Bs Δ} (e : Imp.Exp Σ Δ Any) (bs : Blocks Σ Bs) → Ok bs (λ φ → I.eval ds ck φ e) (explicate-tail e bs)
    tail-ok (Imp.simple s) bs = ok same λ φ → simple≡ φ s
    tail-ok (Imp.assign e₁ e₂) bs with explicate-tail e₂ bs | tail-ok e₂ bs
    ... | out g bs₁ t | ok e m = after-ok (explicate-assign e₁ here⊑ t bs₁) e (assign-ok e₁ here⊑ t bs₁ m)
    tail-ok (Imp.case a e₁ e₂) bs with explicate-tail e₁ bs | tail-ok e₁ bs
    ... | out g₁ bs₁ t₁ | ok e₁' m₁ with explicate-tail e₂ (bs₁ ▷ t₁) | tail-ok e₂ (bs₁ ▷ t₁)
    ...   | out g₂ bs₂ t₂ | ok e₂' m₂ =
      ok (more (ext-trans (more e₁') e₂'))
      λ φ → either-cong (atom φ a) (λ v → trans (m₁ _) (jump-at Z _ e₂')) (λ v → m₂ _)

    body-ok : ∀ {Δ} (e : Imp.Exp Σ Δ Any) φ → I.eval ds ck φ e ≡ G.run ds' ck (explicate-body e) φ
    body-ok e φ with explicate-tail e [] | tail-ok e []
    ... | out g bs t | ok _ m = m φ

  calls≡ : ∀ ck f w → I.call ds ck f w ≡ G.call ds' ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w rewrite def-map explicate-body ds f = body-ok ck (calls≡ ck) (ds ! f) _

explicate-correct : ∀ (P : Imp.Program) → Equivalent (I.sem P) (G.sem (explicate P))
explicate-correct (Imp.program ds e) = clocked-≡ λ ck → body-ok ds ck (calls≡ ds ck) e []
