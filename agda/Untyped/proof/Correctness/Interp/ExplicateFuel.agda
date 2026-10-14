{-

  Correctness of explicate control (Imp → CFG, Compiler/Explicate.agda),
  clock for clock (see the design note in Clock.agda). The pass keeps
  every call, so the interpreters tick in lock step, and the two
  programs return the same results: the values are those of Clos5 in
  both, and code k names definition k of either program, the second
  being the first explicated. There is no precondition.

  The pass threads the list of blocks, newest first, and only adds
  blocks, so the list a tail is made with is a suffix of the final one
  (bs ⊑ cs). A tail made with bs jumps only to blocks of bs, which keep
  their labels when newer blocks are added (jump-at), so what it means
  does not depend on the newer blocks: Means bs t K says that t, run
  with any cs ⊒ bs in the frame φ, returns K φ. The CPS lemma
  (assign-ok): if k means K, explicate-assign e x k means running e,
  assigning its value to x and then K; explicate-tail e means the value
  of e (tail-ok). The join point k of a case gets the label length bs,
  and the jumps to it run k with bs (jump-at).

-}

module Untyped.proof.Correctness.Interp.ExplicateFuel where

open import Untyped.Language.Imp as Imp using (simple; assign)
open import Untyped.Language.CFG using (Body; Tail; goto; case)
open import Untyped.Compiler.Explicate
open import Untyped.Compiler.Pipeline using (compile-imp; compile-cfg)
open import Untyped.proof.Compiler.EncloseScope using (Closed)
open import proof.Semantics.Interp.Clock
import Untyped.Semantics.Interp.Imp as I
import Untyped.Semantics.Interp.CFG as G
open import Untyped.Semantics.Interp.Imp using (Frame; _[_]≔_; set; eval-simple; value; here)
open import Untyped.Semantics.Interp.Clos5 using (Val; code; pair; const; tup; inl; inr)
import Semantics.Interp.ISWIM as ISWIM
open import proof.Framework.ListUtil using (‼-pw)
open import Untyped.proof.Correctness.Interp.LiftLocalsFuel using (compile-imp-correct)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _≤_; _≟_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; <-irrefl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

private variable A B : Set

{- x := the value of r, then h, then g -}
assoc-set : ∀ (r : Result (Val × Frame)) x (h : Frame → Result A) {g : A → Result B}
  → ((r >>= λ p → set (proj₂ p) x (proj₁ p) h) >>= g) ≡ (r >>= λ p → set (proj₂ p) x (proj₁ p) λ φ → h φ >>= g)
assoc-set r x h = trans (bind-assoc r) (bind-cong r λ p → bind-assoc (from-maybe (proj₂ p [ x ]≔ proj₁ p)))

value-here : ∀ {φ} (r : Result Val) → value (here φ r) ≡ r
value-here timeout = refl
value-here error = refl
value-here (ret v) = refl

{- Block lists ---------------------------------------------------------------------}

{- cs is bs with newer blocks -}
data _⊑_ (bs : List Tail) : List Tail → Set where
  ⊑-refl : bs ⊑ bs
  ⊑-step : ∀ {t cs} → bs ⊑ cs → bs ⊑ (t ∷ cs)

⊑-trans : ∀ {bs cs es} → bs ⊑ cs → cs ⊑ es → bs ⊑ es
⊑-trans p ⊑-refl = p
⊑-trans p (⊑-step q) = ⊑-step (⊑-trans p q)

⊑-length : ∀ {bs cs} → bs ⊑ cs → length bs ≤ length cs
⊑-length ⊑-refl = ≤-refl
⊑-length (⊑-step p) = m≤n⇒m≤1+n (⊑-length p)

{- Clock for clock ------------------------------------------------------------------}

module _ (ds : List Imp.Body) where
  private ds' = map explicate-body ds

  {- at clock ck, where calls agree -}
  module _ (ck : ℕ) (calls : ∀ f e w → I.call ds ck (I.code? ds f) e w ≡ G.call ds' ck (G.code? ds' f) e w) where

    simple≡ : ∀ φ s → eval-simple (λ f → I.call ds ck (I.code? ds f)) φ s ≡ eval-simple (λ f → G.call ds' ck (G.code? ds' f)) φ s
    simple≡ φ (Imp.atm a) = refl
    simple≡ φ (Imp.app f e a) =
      bind-cong (I.atom φ f) λ f → bind-cong (I.atom φ e) λ e → bind-cong (I.atom φ a) λ w → calls f e w
    simple≡ φ (Imp.pair a b) = refl
    simple≡ φ (Imp.fst a) = refl
    simple≡ φ (Imp.snd a) = refl
    simple≡ φ (Imp.tuple as) = refl
    simple≡ φ (Imp.get i a) = refl
    simple≡ φ (Imp.inl a) = refl
    simple≡ φ (Imp.inr a) = refl
    simple≡ φ (Imp.prim p a b) = refl

    {- block length bs, with the blocks older than it -}
    jump-at : ∀ {t bs cs φ} → (t ∷ bs) ⊑ cs → G.jump ds' ck cs φ (length bs) ≡ G.tail ds' ck bs φ t
    jump-at {bs = bs} ⊑-refl with length bs ≟ length bs
    ... | yes _ = refl
    ... | no ne = ⊥-elim (ne refl)
    jump-at {bs = bs} (⊑-step {cs = cs} p) with length bs ≟ length cs
    ... | yes e = ⊥-elim (<-irrefl e (⊑-length p))
    ... | no _ = jump-at p

    {- t, made with the blocks bs, returns K φ -}
    Means : List Tail → Tail → (Frame → Result Val) → Set
    Means bs t K = ∀ {cs} → bs ⊑ cs → ∀ φ → G.tail ds' ck cs φ t ≡ K φ

    {- the output of the pass from bs means K -}
    Ok : List Tail → Tail × List Tail → (Frame → Result Val) → Set
    Ok bs r K = bs ⊑ proj₂ r × Means (proj₂ r) (proj₁ r) K

    case-ok : ∀ a y e₁ e₂ cs {l₁ l₂ φ} {g : Val × Frame → Result Val}
      → (∀ φ' → G.jump ds' ck cs φ' l₁ ≡ (I.eval ds ck φ' e₁ >>= g))
      → (∀ φ' → G.jump ds' ck cs φ' l₂ ≡ (I.eval ds ck φ' e₂ >>= g))
      → G.tail ds' ck cs φ (case a y l₁ l₂) ≡ (I.eval ds ck φ (Imp.case a y e₁ e₂) >>= g)
    case-ok a y e₁ e₂ cs {φ = φ} h₁ h₂ =
      trans (bind-cong (I.atom φ a) λ v → bind-cong (I.inj? v) λ
               { (inj₁ w) → trans (bind-cong (from-maybe (φ [ y ]≔ w)) h₁) (sym (bind-assoc (from-maybe (φ [ y ]≔ w))))
               ; (inj₂ w) → trans (bind-cong (from-maybe (φ [ y ]≔ w)) h₂) (sym (bind-assoc (from-maybe (φ [ y ]≔ w)))) })
            (sym (trans (bind-assoc (I.atom φ a)) (bind-cong (I.atom φ a) λ v → bind-assoc (I.inj? v))))

    {- the CPS lemma: x := e, then k -}
    assign-ok : ∀ e x k bs {K} → Means bs k K
      → Ok bs (explicate-assign e x k bs) (λ φ → I.eval ds ck φ e >>= λ p → set (proj₂ p) x (proj₁ p) K)
    assign-ok (simple s) x k bs M =
      ⊑-refl , λ p φ → trans (bind≡ (sym (simple≡ φ s)) λ v → bind-cong (from-maybe (φ [ x ]≔ v)) λ φ' → M p φ')
                             (sym (bind-assoc (eval-simple _ φ s)))
    assign-ok (assign y e₁ e₂) x k bs M =
      ⊑-trans (proj₁ Ok₂) (proj₁ Ok₁) , λ p φ → trans (proj₂ Ok₁ p φ) (sym (assoc-set (I.eval ds ck φ e₁) y _))
      where
      Ok₂ = assign-ok e₂ x k bs M
      Ok₁ = assign-ok e₁ y (proj₁ (explicate-assign e₂ x k bs)) (proj₂ (explicate-assign e₂ x k bs)) (proj₂ Ok₂)
    assign-ok (Imp.case a y e₁ e₂) x k bs {K} M =
      ⊑-step (⊑-trans (⊑-step (⊑-trans (⊑-step ⊑-refl) p₁)) p₂) ,
      λ {cs} p φ → case-ok a y e₁ e₂ cs (λ φ' → trans (jump-at (⊑-trans (⊑-step p₂) p)) (M₁ ⊑-refl φ'))
                      (λ φ' → trans (jump-at p) (M₂ ⊑-refl φ'))
      where
      J : Means (k ∷ bs) (goto (length bs)) K
      J p φ = trans (jump-at p) (M ⊑-refl φ)
      r₁ = explicate-assign e₁ x (goto (length bs)) (k ∷ bs)
      Ok₁ = assign-ok e₁ x (goto (length bs)) (k ∷ bs) J
      Ok₂ = assign-ok e₂ x (goto (length bs)) (proj₁ r₁ ∷ proj₂ r₁) λ p → J (⊑-trans (⊑-step (proj₁ Ok₁)) p)
      p₁ = proj₁ Ok₁
      p₂ = proj₁ Ok₂
      M₁ = proj₂ Ok₁
      M₂ = proj₂ Ok₂

    {- e in tail position -}
    tail-ok : ∀ e bs → Ok bs (explicate-tail e bs) (λ φ → value (I.eval ds ck φ e))
    tail-ok (simple s) bs = ⊑-refl , λ p φ → trans (sym (simple≡ φ s)) (sym (value-here _))
    tail-ok (assign x e₁ e₂) bs =
      ⊑-trans (proj₁ Ok₂) (proj₁ Ok₁) , λ p φ → trans (proj₂ Ok₁ p φ) (sym (assoc-set (I.eval ds ck φ e₁) x _))
      where
      Ok₂ = tail-ok e₂ bs
      Ok₁ = assign-ok e₁ x (proj₁ (explicate-tail e₂ bs)) (proj₂ (explicate-tail e₂ bs)) (proj₂ Ok₂)
    tail-ok (Imp.case a x e₁ e₂) bs =
      ⊑-step (⊑-trans (⊑-step p₁) p₂) ,
      λ {cs} p φ → case-ok a x e₁ e₂ cs (λ φ' → trans (jump-at (⊑-trans (⊑-step p₂) p)) (M₁ ⊑-refl φ'))
                      (λ φ' → trans (jump-at p) (M₂ ⊑-refl φ'))
      where
      r₁ = explicate-tail e₁ bs
      Ok₂ = tail-ok e₂ (proj₁ r₁ ∷ proj₂ r₁)
      p₁ = proj₁ (tail-ok e₁ bs)
      p₂ = proj₁ Ok₂
      M₁ = proj₂ (tail-ok e₁ bs)
      M₂ = proj₂ Ok₂

  {- definition k of the CFG program is definition k of the Imp program, explicated -}
  Def : Imp.Body → Body → Set
  Def b b' = b' ≡ explicate-body b

  code-pw : ∀ f → M.Pointwise Def (I.code? ds f) (G.code? ds' f)
  code-pw (code k) = ‼-pw (reverse⁺ (pw ds)) k
    where pw : ∀ ds → Pointwise Def ds (map explicate-body ds)
          pw [] = []
          pw (d ∷ ds) = refl ∷ pw ds
  code-pw (pair _ _) = M.nothing
  code-pw (const B k) = M.nothing
  code-pw (tup _) = M.nothing
  code-pw (inl _) = M.nothing
  code-pw (inr _) = M.nothing

  calls≡ : ∀ ck f e w → I.call ds ck (I.code? ds f) e w ≡ G.call ds' ck (G.code? ds' f) e w
  call-pw : ∀ ck {mb mb'} → M.Pointwise Def mb mb' → ∀ e w → I.call ds ck mb e w ≡ G.call ds' ck mb' e w

  calls≡ ck f = call-pw ck (code-pw f)

  call-pw ck M.nothing e w = refl
  call-pw zero (M.just _) e w = refl
  call-pw (suc ck) (M.just {Imp.body n x} refl) e w = sym (proj₂ (tail-ok ck (calls≡ ck) x []) ⊑-refl _)

{- The end theorem -----------------------------------------------------------------}

explicate-correct : ∀ P → Equivalent (I.sem P) (G.sem (explicate P))
explicate-correct (Imp.program ds (Imp.body n e)) = clocked-≡ λ ck →
  sym (proj₂ (tail-ok ds ck (calls≡ ds ck) e []) ⊑-refl _)

{- The whole compiler, into CFG ---------------------------------------------------}

compile-cfg-correct : ∀ M → Closed M → Equivalent (ISWIM.sem M) (G.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))
