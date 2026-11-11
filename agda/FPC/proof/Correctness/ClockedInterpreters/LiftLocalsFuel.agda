{-

  Correctness of lift locals (Monμ → Impμ), clock for clock, as for
  typed lift locals (ISWIM/proof/Correctness/Interp/LiftLocalsFuel.agda). A
  Monμ program means its embedding into GlobalFunμ. The Impμ frame holds
  the value of each variable in scope in the variable's slot (Holds), and
  the values are the same, so the two programs give the same result for
  every clock: where the calls agree (calls), an expression and its
  lifting agree (lift-ok), and so the calls agree at the next clock
  (calls≡). A let or a case writes a slot that is not initialized, while
  the slots of the variables in scope are, so the write keeps the values
  of those variables (read-write-other).

-}

module FPC.proof.Correctness.ClockedInterpreters.LiftLocalsFuel where

open import FPC.Language.Type
open import FPC.Language.Mon
import FPC.Language.Imp as Imp
open Imp using (Inits; _∈_; _⊕_; Only; fill-∈; only-initial)
open import Framework.Membership using (_⊑_; here⊑; ⊑-∋; ⊑-trans)
open import FPC.Compiler.LiftLocals renaming (atom to lift-atom)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Framework.Slots using (read; write; empty; params)
open import FPC.proof.Framework.SlotsProp using (read-write; read-write-other;
  params-arg; params-env)
open import proof.Semantics.Interp.Clock
import FPC.Semantics.ClockedInterpreters.GlobalFun as C
import FPC.Semantics.ClockedInterpreters.Imp as Ip
open Ip using (Fr)
open import FPC.proof.Semantics.ClockedInterpreters.GlobalFun using (def-map;
  atom; atm-bind; eval-atom; atoms-bind; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; cong₂)

module _ {Σ : List DSig} {Γ Δ : Ctx} where
  open C.Vals Σ

  {- the frame φ holds the values γ of the variables of Γ in their slots
     ρ -}
  record Holds {I : Inits Δ} (ρ : Slots Γ Δ) (ok : Inited ρ I) (γ : Env Γ)
    (φ : Fr Δ I) : Set where
    constructor holds
    field at : ∀ {B} (x : Γ ∋ B) → read φ (ρ x) (ok x) ≡ lookup γ x

  atom-ok : ∀ {I : Inits Δ} {A} {ρ : Slots Γ Δ} {ok : Inited ρ I} {γ φ}
    (a : Atm Σ Γ A)
    → Holds ρ ok γ φ
    → atom γ a ≡ Ip.atom φ (lift-atom {I = I} ρ ok a)
  atom-ok (var x) h = sym (Holds.at h x)
  atom-ok (lit B c) h = refl
  atom-ok (ref f) h = refl

  atoms-ok : ∀ {I : Inits Δ} {Δs} {ρ : Slots Γ Δ} {ok : Inited ρ I} {γ φ}
    (as : All (Atm Σ Γ) Δs)
    → Holds ρ ok γ φ
    → map (atom γ) as ≡ map (Ip.atom φ) (atoms {I = I} ρ ok as)
  atoms-ok [] h = refl
  atoms-ok {ρ = ρ} {ok} (a ∷ as) h =
    cong₂ _∷_ (atom-ok {ρ = ρ} {ok} a h) (atoms-ok {ρ = ρ} {ok} as h)

{- a write to a fresh slot x, holding the value of the new variable -}
holds-ext : ∀ {Σ Γ Δ A} {I : Inits Δ} {ρ : Slots Γ Δ} {ok : Inited ρ I}
  {γ : C.Vals.Env Σ Γ} {φ : Fr Δ I} (x : Δ ∋ A) (v : C.Vals.Val Σ A)
  → Imp._∉_ x I
  → Holds ρ ok γ φ
  → Holds (ext x ρ) (inited-ext {I = I} x ρ ok) (v ∷ γ) (write φ x v)
holds-ext {ρ = ρ} {ok} {φ = φ} x v xn h = holds at
  where
  at : ∀ {B} (y : _ ∋ B) → _
  at Z = read-write φ x v _
  at (S y) = trans (read-write-other φ x v (ρ y) (ok y) xn _) (Holds.at h y)

module _ {Σ : List DSig}
  (ds : All (λ s → Exp Σ (Args s) (DSig.cod s)) Σ) where
  open C.Vals Σ
  private
    dsC = map ⌜_⌝ ds
    dsI = map lift-body ds

  module _ (ck : ℕ)
    (calls : ∀ {A B} (f : Val (A ⇒ B)) w
      → C.call dsC ck f w ≡ Ip.call dsI ck f w) where

    lift-ok : ∀ {Γ Δ D A} {I : Inits Δ} (e : Exp Σ Γ A)
      (q : binds e D ⊑ Δ) (ρ : Slots Γ Δ) (ok : Inited ρ I)
      (o : Only (⊑-trans (binds-⊒ e D) q) I) (γ : Env Γ) (φ : Fr Δ I)
      → Holds ρ ok γ φ
      → C.eval dsC ck γ ⌜ e ⌝ ≡ Ip.eval dsI ck φ (lift e q ρ ok o)
    lift-ok (atm a) q ρ ok o γ φ h = trans (eval-atom a) (cong ret (atom-ok {ρ = ρ} {ok} a h))
    lift-ok (pair a b) q ρ ok o γ φ h =
      trans (trans (atm-bind a) (atm-bind b))
        (cong ret (cong₂ pack (atom-ok {ρ = ρ} {ok} a h) (atom-ok {ρ = ρ} {ok} b h)))
    lift-ok (callc a b) q ρ ok o γ φ h =
      trans (trans (atm-bind a) (atm-bind b))
        (trans (calls _ _) (cong₂ (Ip.call dsI ck) (atom-ok {ρ = ρ} {ok} a h) (atom-ok {ρ = ρ} {ok} b h)))
    lift-ok (tuple as) q ρ ok o γ φ h =
      trans (atoms-bind as) (cong (λ vs → ret (tup vs)) (atoms-ok {ρ = ρ} {ok} as h))
    lift-ok (get i a) q ρ ok o γ φ h =
      trans (atm-bind a) (cong (λ v → ret (nth i v)) (atom-ok {ρ = ρ} {ok} a h))
    lift-ok (inl a) q ρ ok o γ φ h =
      trans (atm-bind a) (cong (λ v → ret (inl v)) (atom-ok {ρ = ρ} {ok} a h))
    lift-ok (inr a) q ρ ok o γ φ h =
      trans (atm-bind a) (cong (λ v → ret (inr v)) (atom-ok {ρ = ρ} {ok} a h))
    lift-ok (prim p a b) q ρ ok o γ φ h =
      trans (trans (atm-bind a) (atm-bind b))
        (cong₂ (λ u v → ret (δ p u v)) (atom-ok {ρ = ρ} {ok} a h) (atom-ok {ρ = ρ} {ok} b h))
    lift-ok (fold a) q ρ ok o γ φ h =
      trans (atm-bind a) (cong (λ v → ret (fold v)) (atom-ok {ρ = ρ} {ok} a h))
    lift-ok (unfold a) q ρ ok o γ φ h =
      trans (atm-bind a) (cong (λ v → ret (unfold-v v)) (atom-ok {ρ = ρ} {ok} a h))
    lift-ok {I = I} (let′ e₁ e₂) q ρ ok o γ φ h =
      bind≡ (lift-ok e₁ q₁ ρ ok (only₁ o) γ φ h) λ v →
        lift-ok e₂ q (ext x ρ) (inited-ext {I = I} x ρ ok) (only₂ o) (v ∷ γ)
          (write φ x v) (holds-ext x v (fresh o) h)
      where open Let {I = I} e₁ e₂ q
    lift-ok {I = I} (case a e₁ e₂) q ρ ok o γ φ h =
      trans (atm-bind a)
        (trans
          (either-cong (atom γ a)
            (λ v → lift-ok e₁ q₁ (ext x ρ) (inited-ext {I = I} x ρ ok)
              (only₁ o) (v ∷ γ) (write φ x v) (holds-ext x v (fresh₁ o) h))
            (λ v → lift-ok e₂ q (ext y ρ) (inited-ext {I = I} y ρ ok)
              (only₂ o) (v ∷ γ) (write φ y v) (holds-ext y v (fresh₂ o) h)))
          (cong (λ u → either u _ _) (atom-ok {ρ = ρ} {ok} a h)))
      where open Case {I = I} a e₁ e₂ q

  calls≡ : ∀ ck {A B} (f : Val (A ⇒ B)) w
    → C.call dsC ck f w ≡ Ip.call dsI ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w rewrite def-map lift-body ds f
    | def-map ⌜_⌝ ds f =
    lift-ok ck (calls≡ ck) d here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p)
      (w ∷ e ∷ []) (params p e w) (holds at)
    where
    d = lookup ds f
    p = binds-⊒ d _
    at : ∀ {B} (x : _ ∋ B)
      → read (params p e w) (⊑-∋ p x) _ ≡ lookup (w ∷ e ∷ []) x
    at Z = params-arg p e w _
    at (S Z) = params-env p e w _

lift-locals-correct : ∀ {A} (P : Program A)
  → Equivalent (C.sem ⌜ P ⌝ₚ) (Ip.sem (lift-program P))
lift-locals-correct (program {Σ} ds e) =
  clocked-≡ λ ck →
    lift-ok ds ck (calls≡ ds ck) e here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p))
      (only-initial p) [] (empty _) (holds λ ())
  where p = binds-⊒ e []
