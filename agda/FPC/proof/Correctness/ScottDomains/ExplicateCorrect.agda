{-

  Correctness of explicate control (Impμ → CFGμ,
  FPC/Compiler/Explicate.agda) in Scott domains
  (FPC/Semantics/ScottDomains/{Imp,CFG}.agda), as in the graph model
  (FPC/proof/Correctness/GraphModel/ExplicateCorrect.agda), with equality of
  values in place of equality of sets.

  explicate-assign e x p k bs is e in continuation-passing style, as
  the semantics of Impμ is: its tail, with its blocks, means e run with
  the continuation that writes slot x and runs k with the blocks bs
  (asg); explicate-tail e means e run with the continuation that
  returns the value (idK). Each case is a congruence; a case passes its
  continuation to its branches, which in CFGμ reach it through the join
  point, the block that holds k. A label made earlier means the same
  with the blocks added after it (Ext, ext-at).

  In Impμ the continuation of an assignment nested in e keeps the frame
  where e starts, while in CFGμ k runs after the nested writes too. These
  write slots that are not initialized where e starts, and k reads only
  slots that are initialized there or slot x (p : J ⊆ I ⊕ x). A tail, and
  a block, means the same in two frames that agree on the slots it
  starts with (Agree, tail-agree, blocks-resp), so the extra writes
  change nothing (asg-write).

  The continuations are continuous maps, so the graph model's κ-≃ is
  just a congruence (ap). The compiler takes apart the output of a
  recursive call with `with`; Out is a record, so the proof uses its
  projections instead (a `with` while meanings are in scope is slow to
  check: tl by `with`, as in the graph model, does not check in 6
  minutes).

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import FPC.Language.Type
import FPC.Language.Imp as I
open I using (_∈_; _∉_; _⊕_; _⊆_; ⊆-refl; ⊆-⊕⊕; ∈-⊆; ∈∉-idx)
open import FPC.Language.CFG
open import FPC.Compiler.Explicate
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)
open import FPC.Framework.AllUtil using (lookup; pos)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Fin using (zero; suc)
open import Data.Empty using (⊥-elim)
import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≢_)

module FPC.proof.Correctness.ScottDomains.ExplicateCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to
  inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import FPC.Semantics.ScottDomains.Ops pt fe pe
open import FPC.Semantics.ScottDomains.Imp pt fe pe using (⟦_⟧ᴷ; K; idK; underK)
  renaming (code′ to codeᵢ; ⟦_⟧ₚ to ⟦_⟧ᵢ)
open import FPC.Semantics.ScottDomains.CFG pt fe pe using (⟦_⟧ᵗ; blocks; run;
  Meanings) renaming (code′ to codeᶜ′; ⟦_⟧ₚ to ⟦_⟧ᶜ)
open import FPC.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using
  (codeᶠ-cong; tables-cons; write-cong; 𝒜; 𝒜s; 𝒮; 𝒜-＝; 𝒮-＝)
open import Semantics.Scott.Prim pt fe pe using (primD)

{- frames that agree ----------------------------------------------------------}

{- a proof of b from an irrelevant one -}
recover : (b : Bool) → .(T b) → T b
recover true _ = tt
recover false ()

{- a slot initialized after a write to x, at another position, was
   initialized before -}
∈-⊕-other : ∀ {Δ A B} {I : I.Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → y ∈ I ⊕ x
  → idx x ≢ idx y
  → y ∈ I
∈-⊕-other {I = b ∷ I} Z Z i ne = ⊥-elim (ne Eq.refl)
∈-⊕-other {I = b ∷ I} Z (S y) i ne = i
∈-⊕-other {I = b ∷ I} (S x) Z i ne = i
∈-⊕-other {I = b ∷ I} (S x) (S y) i ne =
  ∈-⊕-other {I = I} x y i (λ e → ne (Eq.cong Data.Nat.suc e))

{- the frames σ and σ' agree on the slots initialized in I -}
record Agree {Δ} (I : I.Inits Δ) (σ σ' : ⟨ Env ⟩) : 𝓤₁ ̇ where
  constructor mk-agree
  field agree : ∀ {A} (x : Δ ∋ A) → x ∈ I → σ (idx x) ＝ σ' (idx x)
open Agree

{- after the same write to slot x, the frames agree on the slots J
   (J ⊆ I ⊕ x) -}
agree-write : ∀ {Δ A} {I J : I.Inits Δ} (x : Δ ∋ A) {σ σ'} (X : ⟨ 𝔻 ⟩)
  → .(J ⊆ I ⊕ x)
  → Agree I σ σ'
  → Agree J (write (idx x) σ X) (write (idx x) σ' X)
agree-write {I = I} {J} x {σ} {σ'} X p ag = mk-agree λ y i →
  write-cong (idx x) (idx y) σ σ' X
    (λ ne →
      agree ag y
        (∈-⊕-other {I = I} x y
          (recover (lookup (I ⊕ x) y) (∈-⊆ {I = I ⊕ x} {J} y i p)) ne))

{- a write to a slot that is not initialized in I keeps the slots of I -}
agree-fresh : ∀ {Δ B} {I : I.Inits Δ} (y : Δ ∋ B) (σ : ⟨ Env ⟩)
  (X : ⟨ 𝔻 ⟩)
  → .(y ∉ I)
  → Agree I (write (idx y) σ X) σ
agree-fresh {I = I} y σ X n = mk-agree λ z i →
  write-other (idx y) (idx z) σ X
    (λ e → ∈∉-idx {I = I} z y i (recover _ n) (Eq.sym e))

{- the meanings of the blocks Bs depend only on the slots each starts
   with -}
module _ {Σ R} (T : Table Σ) where

  Resp : ∀ {Δ} {Bs : List (I.Inits Δ)} → Meanings Bs → 𝓤₁ ̇
  Resp {Δ} {Bs} B =
    ∀ {I} (l : Bs ∋ I) σ σ' → Agree I σ σ' → B l · σ ＝ B l · σ'

  𝒜-agree : ∀ {Δ I A} (a : I.Atm Σ Δ I A) {σ σ'}
    → Agree I σ σ'
    → 𝒜 a T · σ ＝ 𝒜 a T · σ'
  𝒜-agree (I.var x i) ag = agree ag x (recover _ i)
  𝒜-agree (I.lit B c) ag = refl
  𝒜-agree (I.ref f) ag = refl

  𝒜s-agree : ∀ {Δ I Δs} (as : All (I.Atm Σ Δ I) Δs) {σ σ'}
    → Agree I σ σ'
    → 𝒜s as T · σ ＝ 𝒜s as T · σ'
  𝒜s-agree [] ag = refl
  𝒜s-agree (a ∷ as) ag =
    dfunext fe λ
      { zero → 𝒜-agree a ag ; (suc i) → happly (𝒜s-agree as ag) i }

  𝒮-agree : ∀ {Δ I A} (s : I.Simple Σ Δ I A) {σ σ'}
    → Agree I σ σ'
    → 𝒮 s T · σ ＝ 𝒮 s T · σ'
  𝒮-agree (I.atm a) ag = 𝒜-agree a ag
  𝒮-agree (I.pair a b) ag =
    ap₂ (λ x y → pair · x · y) (𝒜-agree a ag) (𝒜-agree b ag)
  𝒮-agree (I.callc a b) ag =
    ap₂ (λ x y → appᵈ · (appᵈ · (car · x) · (cdr · x)) · y) (𝒜-agree a ag)
      (𝒜-agree b ag)
  𝒮-agree (I.tuple {Δs} as) ag = ap (tupleᵈ (length Δs) ·_) (𝒜s-agree as ag)
  𝒮-agree (I.get i a) ag = ap (proj (pos i) ·_) (𝒜-agree a ag)
  𝒮-agree (I.inl a) ag = ap (inlᵈ ·_) (𝒜-agree a ag)
  𝒮-agree (I.inr a) ag = ap (inrᵈ ·_) (𝒜-agree a ag)
  𝒮-agree (I.prim p a b) ag =
    ap₂ (λ x y → primD p · x · y) (𝒜-agree a ag) (𝒜-agree b ag)
  𝒮-agree (I.fold a) ag = 𝒜-agree a ag
  𝒮-agree (I.unfold a) ag = 𝒜-agree a ag

  {- a tail means the same in frames that agree on the slots it starts
     with -}
  tail-agree : ∀ {Δ Bs I} (t : Tail Σ R Δ Bs I) {B : Meanings Bs}
    → Resp B
    → ∀ σ σ'
    → Agree I σ σ'
    → ⟦ t ⟧ᵗ T B · σ ＝ ⟦ t ⟧ᵗ T B · σ'
  tail-agree (return s) r σ σ' ag = 𝒮-agree s ag
  tail-agree (seq x s p t) {B} r σ σ' ag =
    ap₂ (λ f d → appᵈ · (Λ · f) · d)
      (to-continuous-function-＝ 𝔻 𝔻
         {absAt (idx x) (⟦ t ⟧ᵗ T B) · σ} {absAt (idx x) (⟦ t ⟧ᵗ T B) · σ'}
         (λ X → tail-agree t r _ _ (agree-write x X p ag)))
      (𝒮-agree s ag)
  tail-agree (goto l) r σ σ' ag = r l σ σ' ag
  tail-agree {I = I} (case a x y l₁ l₂) {B} r σ σ' ag =
    ap₂ (λ v w → cases · v · w) (𝒜-agree a ag)
      (ap₂ _,_
         (ap (strict ·_)
            (to-continuous-function-＝ 𝔻 𝔻
               {absAt (idx x) (B l₁) · σ} {absAt (idx x) (B l₁) · σ'}
               (λ X → r l₁ _ _ (agree-write x X (⊆-refl {I = I ⊕ x}) ag))))
         (ap (strict ·_)
            (to-continuous-function-＝ 𝔻 𝔻
               {absAt (idx y) (B l₂) · σ} {absAt (idx y) (B l₂) · σ'}
               (λ X → r l₂ _ _ (agree-write y X (⊆-refl {I = I ⊕ y}) ag)))))

  blocks-resp : ∀ {Δ Bs} (bs : Blocks Σ R Δ Bs) → Resp (blocks bs T)
  blocks-resp (bs ▷ t) Z = tail-agree t (blocks-resp bs)
  blocks-resp (bs ▷ t) (S l) = blocks-resp bs l

{- blocks that extend others --------------------------------------------------}

data Ext {Σ R Δ} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ R Δ Bs
  → Blocks Σ R Δ Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ R Δ Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' I g bs bs'} {t : Tail Σ R Δ Bs' I}
    → Ext {Bs = Bs} g bs bs'
    → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ R Δ Bs Bs' Bs''}
  → {g : Bs ⊑ Bs'}
  → {g' : Bs' ⊑ Bs''}
  → ∀ {bs bs' bs''}
  → Ext {Σ} {R} {Δ} g bs bs'
  → Ext g' bs' bs''
  → Ext (⊑-trans g g') bs bs''
ext-trans e here = e
ext-trans e (there e') = there (ext-trans e e')

ext-at : ∀ {Σ R Δ Bs Bs'}
  → {g : Bs ⊑ Bs'}
  → {bs : Blocks Σ R Δ Bs} {bs' : Blocks Σ R Δ Bs'} (T : Table Σ)
  → Ext g bs bs'
  → ∀ {I} (l : Bs ∋ I)
  → blocks bs T l ＝ blocks bs' T (⊑-∋ g l)
ext-at T here l = refl
ext-at T (there e) l = ext-at T e l

{- The pass preserves meanings ------------------------------------------------}

module _ {Σ R} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  {- write slot x, then k with the blocks bs -}
  asg : ∀ {Δ Bs A} {J : I.Inits Δ} → Δ ∋ A → Tail Σ R Δ Bs J
    → Blocks Σ R Δ Bs → ⟨ Env ⟩ → ⟨ K ⟩
  asg x k bs σ = appᵈ · (lamAt (idx x) (⟦ k ⟧ᵗ T' (blocks bs T')) · σ)

  {- a write to a slot y that is not initialized where the assignment
     to x starts does not change what k reads -}
  asg-write : ∀ {Δ Bs A B} {I J : I.Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
    (k : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs)
    → .(J ⊆ I ⊕ x)
    → .(y ∉ I)
    → ∀ σ X
    → asg x k bs (write (idx y) σ X) ＝ asg x k bs σ
  asg-write {I = I} x y k bs p n σ X =
    ap (λ f → appᵈ · (Λ · f))
      (to-continuous-function-＝ 𝔻 𝔻
        {absAt (idx x) (⟦ k ⟧ᵗ T' (blocks bs T')) · write (idx y) σ X}
        {absAt (idx x) (⟦ k ⟧ᵗ T' (blocks bs T')) · σ}
        (λ Y →
          tail-agree T' k (blocks-resp T' bs) _ _
            (agree-write {I = I} x Y p (agree-fresh {I = I} y σ X n))))

  Good : ∀ {Δ Bs} {I : I.Inits Δ} → (⟨ Env ⟩ → ⟨ 𝔻 ⟩) → Blocks Σ R Δ Bs
    → Out Σ R Δ Bs I → 𝓤₁ ̇
  Good F bs (out g bs' t) =
    Ext g bs bs' × ((σ : ⟨ Env ⟩) → F σ ＝ ⟦ t ⟧ᵗ T' (blocks bs' T') · σ)

  {- the continuation of the right-hand side of an assignment to x, when
     its body e₂ runs as the tail t -}
  bind : ∀ {Δ Bs A B} {I J : I.Inits Δ} (x : Δ ∋ A) (e₂ : I.Exp Σ Δ I B)
    (κ : ⟨ K ⟩) (t : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs) σ
    → (  (X : ⟨ 𝔻 ⟩)
       → ⟦ e₂ ⟧ᴷ T · write (idx x) σ X · κ
         ＝ ⟦ t ⟧ᵗ T' (blocks bs T') · write (idx x) σ X)
    → appᵈ · (Λ · (underK (idx x) (⟦ e₂ ⟧ᴷ T) · (σ , κ))) ＝ asg x t bs σ
  bind x e₂ κ t bs σ h =
    ap (appᵈ ·_)
      (Λ-cong (underK (idx x) (⟦ e₂ ⟧ᴷ T) · (σ , κ))
        (absAt (idx x) (⟦ t ⟧ᵗ T' (blocks bs T')) · σ) (λ X _ → h X))

  {- the two branches of a case -}
  branches : ∀ {Δ I A B} (a : I.Atm Σ Δ I (A ⊹ B)) (F₁ F₂ G₁ G₂ : DCPO[ 𝔻 , 𝔻 ])
    σ
    → ((X : ⟨ 𝔻 ⟩) → F₁ · X ＝ G₁ · X)
    → ((X : ⟨ 𝔻 ⟩) → F₂ · X ＝ G₂ · X)
    → cases · (𝒜 a T · σ) · (strict · F₁ , strict · F₂)
      ＝ cases · (𝒜 a T' · σ) · (strict · G₁ , strict · G₂)
  branches a F₁ F₂ G₁ G₂ σ h₁ h₂ =
    ap₂ (λ x y → cases · x · y) (𝒜-＝ TT a σ)
      (ap₂ _,_ (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {F₁} {G₁} h₁))
               (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {F₂} {G₂} h₂)))

  cps : ∀ {Δ Bs A} {I J : I.Inits Δ} (e : I.Exp Σ Δ I A)
    → (x : Δ ∋ A)
    → .(p : J ⊆ I ⊕ x)
    → (k : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T · σ · asg x k bs σ) bs (explicate-assign e x p k bs)
  cps (I.simple s) x p k bs =
    here , λ σ → ap (asg x k bs σ ·_) (𝒮-＝ TT s σ)
  cps {I = I} {J} (I.assign y n e₁ e₂) x p k bs =
    ext-trans (pr₁ c₂) (pr₁ c₁) ,
    λ σ →
      ap (⟦ e₁ ⟧ᴷ T · σ ·_)
        (bind y e₂ (asg x k bs σ) (Out.tail o₂) (Out.made o₂) σ
          (λ X →
            ap (⟦ e₂ ⟧ᴷ T · write (idx y) σ X ·_)
              (asg-write {I = I} x y k bs p n σ X ⁻¹)
            ∙ pr₂ c₂ (write (idx y) σ X)))
      ∙ pr₂ c₁ σ
   where
    o₂ = explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
    c₂ = cps e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
    c₁ = cps e₁ y (⊆-refl {I = I ⊕ y}) (Out.tail o₂) (Out.made o₂)
  cps {I = I} {J} (I.case a y n₁ z n₂ e₁ e₂) x p k bs =
    there (ext-trans (there (ext-trans (there here) (pr₁ c₁))) (pr₁ c₂)) ,
    λ σ →
      branches a (underK (idx y) (⟦ e₁ ⟧ᴷ T) · (σ , asg x k bs σ))
        (underK (idx z) (⟦ e₂ ⟧ᴷ T) · (σ , asg x k bs σ))
        (absAt (idx y) (blocks (Out.made o₂) T' (⊑-∋ (Out.grows o₂) Z)) · σ)
        (absAt (idx z) (⟦ Out.tail o₂ ⟧ᵗ T' (blocks (Out.made o₂) T')) · σ) σ
        (λ X →
          ap (⟦ e₁ ⟧ᴷ T · write (idx y) σ X ·_)
            (asg-write {I = I} x y k bs p n₁ σ X ⁻¹)
          ∙ pr₂ c₁ (write (idx y) σ X)
          ∙ ap (λ N → N · write (idx y) σ X) (ext-at T' (pr₁ c₂) Z))
        (λ X →
          ap (⟦ e₂ ⟧ᴷ T · write (idx z) σ X ·_)
            (asg-write {I = I} x z k bs p n₂ σ X ⁻¹)
          ∙ ap
              (λ N →
                ⟦ e₂ ⟧ᴷ T · write (idx z) σ X
                · (appᵈ · (Λ · (absAt (idx x) N · write (idx z) σ X))))
              (ext-at T' (pr₁ c₁) Z)
          ∙ pr₂ c₂ (write (idx z) σ X))
   where
    o₁ = explicate-assign e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
    c₁ = cps e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
    o₂ =
      explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
        (goto (⊑-∋ (there⊑ (Out.grows o₁)) Z)) (Out.made o₁ ▷ Out.tail o₁)
    c₂ =
      cps e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
        (goto (⊑-∋ (there⊑ (Out.grows o₁)) Z)) (Out.made o₁ ▷ Out.tail o₁)

  tl : ∀ {Δ Bs} {I : I.Inits Δ} (e : I.Exp Σ Δ I R) (bs : Blocks Σ R Δ Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T · σ · idK) bs (explicate-tail e bs)
  tl (I.simple s) bs = here , 𝒮-＝ TT s
  tl {I = I} (I.assign x n e₁ e₂) bs =
    ext-trans (pr₁ c₂) (pr₁ c₁) ,
    λ σ →
      ap (⟦ e₁ ⟧ᴷ T · σ ·_)
        (bind x e₂ idK (Out.tail o₂) (Out.made o₂) σ
          (λ X → pr₂ c₂ (write (idx x) σ X)))
      ∙ pr₂ c₁ σ
   where
    o₂ = explicate-tail e₂ bs
    c₂ = tl e₂ bs
    c₁ = cps e₁ x (⊆-refl {I = I ⊕ x}) (Out.tail o₂) (Out.made o₂)
  tl (I.case a x n₁ y n₂ e₁ e₂) bs =
    there (ext-trans (there (pr₁ c₁)) (pr₁ c₂)) ,
    λ σ →
      branches a (underK (idx x) (⟦ e₁ ⟧ᴷ T) · (σ , idK))
        (underK (idx y) (⟦ e₂ ⟧ᴷ T) · (σ , idK))
        (absAt (idx x) (blocks (Out.made o₂) T' (⊑-∋ (Out.grows o₂) Z)) · σ)
        (absAt (idx y) (⟦ Out.tail o₂ ⟧ᵗ T' (blocks (Out.made o₂) T')) · σ) σ
        (λ X →
          pr₂ c₁ (write (idx x) σ X)
          ∙ ap (λ N → N · write (idx x) σ X) (ext-at T' (pr₁ c₂) Z))
        (λ X → pr₂ c₂ (write (idx y) σ X))
   where
    o₁ = explicate-tail e₁ bs
    c₁ = tl e₁ bs
    o₂ = explicate-tail e₂ (Out.made o₁ ▷ Out.tail o₁)
    c₂ = tl e₂ (Out.made o₁ ▷ Out.tail o₁)

  body-＝ : ∀ {Γ} (b : I.Body Σ Γ R) σ
    → ⟦ I.Body.exp b ⟧ᴷ T · σ · idK ＝ run (explicate-body b) T' · σ
  body-＝ (I.body Δ p e) σ = pr₂ (tl e []) σ

{- Programs -------------------------------------------------------------------}

{- the code of a definition means the code of its output -}
code-explicate : ∀ {Σ} {T T' : Table Σ}
  (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) {s}
  (b : I.Body Σ (Args s) (DSig.cod s))
  → codeᵢ T b ＝ codeᶜ′ T' (explicate-body b)
code-explicate {T = T} {T'} TT b@(I.body Δ p e) =
  codeᶠ-cong p (∘₁ Env (K ⟹₁ 𝔻) 𝔻 (⟦ e ⟧ᴷ T) (at-point₁ K 𝔻 idK))
    (run (explicate-body b) T')
    (λ X Y _ _ → body-＝ TT b _)

table-explicate : ∀ {Σ ss}
  (ds : All (λ s → I.Body Σ (Args s) (DSig.cod s)) ss) {s} (f : Σ ∋ s)
  → tables codeᵢ ds f ＝ tables codeᶜ′ (All-map explicate-body ds) f
table-explicate [] f = refl
table-explicate (d ∷ ds) f =
  tables-cons codeᵢ codeᶜ′ d ds (explicate-body d) (All-map explicate-body ds) f
    (code-explicate (table-explicate ds) d)
    (table-explicate ds f)

explicate-correct : ∀ {A} (P : I.Program A) → ⟦ P ⟧ᵢ ＝ ⟦ explicate P ⟧ᶜ
explicate-correct (I.program ds b@(I.body Δ p e)) =
  body-＝ (table-explicate ds) b ρ₀
