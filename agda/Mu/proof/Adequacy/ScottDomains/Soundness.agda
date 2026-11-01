{-

  Soundness of the clocked interpreter of FPC
  (Mu/Semantics/ClockedInterpreters/FPC.agda) with respect to its
  Scott-domain semantics (Mu/Semantics/ScottDomains/FPC.agda): what the
  interpreter returns, at any clock, means what the program means, and
  the interpreter never errs.

  As for the graph model (Mu/proof/Adequacy/Soundness.agda), through the
  meanings of values (𝒱; a closure means the function value of its body
  in the meaning of its environment, 𝓔), by induction on the clock and
  the term. In Scott domains the meanings are elements of 𝔻, so a
  result is sound (Sound r d) when it is a value whose meaning is d, or
  a timeout. Every value means a defined element (𝒱-defined), which is
  what the strict operators need at a call, a let and a case.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Framework.Primitives using (Base; base-rep; Int)
open import Framework.abt.GSubst using (_•_)
open import Language.Prim using (sub; eq; bool) renaming (δ to δᴾ)
open import Mu.Language.Type using (Type; Ctx; _⇒_; tup; out-ty; _∋_; Z; S; idx)
open import Mu.Language.FPC
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.Semantics.ClockedInterpreters.FPC
  renaming (Val to Value; Env to Envᵢ; const to cv; δ to δᵥ)
open import Semantics.Observation using (Obs; o-const)
open import Semantics.Interp.Clock using (Result; timeout; error; ret; _>>=_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (length; [])
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary using (does)

module Mu.proof.Adequacy.ScottDomains.Soundness
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import proof.Framework.Scott.Ops pt fe pe
  renaming (Env to Envᵈ; app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Values pt fe pe using (view; view-inj)
open import proof.Framework.Scott.Semantics pt fe pe using (lamᶜ; abs; _∷ᶠ_; init; lamᶜ-β; letᶜ-β; caseᶜ-inl; caseᶜ-inr)
open import Semantics.Scott.Prim pt fe pe using (primD; out)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧; ⟦_⟧s)

{- Meanings of values and environments ------------------------------------------}

𝒱 : ∀ {A} → Value A → ⟨ 𝔻 ⟩
𝒱s : ∀ {Δ} → All Value Δ → Fin (length Δ) → ⟨ 𝔻 ⟩
𝓔 : ∀ {Γ} → Envᵢ Γ → ⟨ Envᵈ ⟩

{- no FPC program has a value of a code type -}
𝒱 (code N) = unit
𝒱 (pack (code N) (tup γ)) = lamᶜ ⟦ N ⟧ · 𝓔 γ
𝒱 (cv {B} k) = const B k
𝒱 (tup {Δ} vs) = tupleᵈ (length Δ) · 𝒱s vs
𝒱 (inl v) = inlᵈ · 𝒱 v
𝒱 (inr v) = inrᵈ · 𝒱 v
𝒱 (fold v) = 𝒱 v

𝒱s [] = λ ()
𝒱s (v ∷ vs) = 𝒱 v ∷ᶠ 𝒱s vs

𝓔 [] = λ _ → init
𝓔 (v ∷ γ) = 𝒱 v • 𝓔 γ

{- values mean defined elements -}
𝒱-defined : ∀ {A} (v : Value A) → defined (𝒱 v)
𝒱s-defined : ∀ {Δ} (vs : All Value Δ) (i : Fin (length Δ)) → defined (𝒱s vs i)
𝒱-defined (code N) = unit-defined
𝒱-defined (pack (code N) (tup γ)) = Λ-defined (abs ⟦ N ⟧ · 𝓔 γ)
𝒱-defined (cv {B} k) = const-defined B k
𝒱-defined (tup {Δ} vs) = tuple-defined (length Δ) (𝒱s vs) (𝒱s-defined vs)
𝒱-defined (inl v) = inl-defined (𝒱 v) (𝒱-defined v)
𝒱-defined (inr v) = inr-defined (𝒱 v) (𝒱-defined v)
𝒱-defined (fold v) = 𝒱-defined v
𝒱s-defined (v ∷ vs) zero = 𝒱-defined v
𝒱s-defined (v ∷ vs) (suc i) = 𝒱s-defined vs i

𝓔-lookup : ∀ {Γ A} (γ : Envᵢ Γ) (x : Γ ∋ A) → 𝒱 (lookup γ x) ＝ 𝓔 γ (idx x)
𝓔-lookup (v ∷ γ) Z = refl
𝓔-lookup (v ∷ γ) (S x) = 𝓔-lookup γ x

𝒱s-lookup : ∀ {Δ A} (vs : All Value Δ) (i : Δ ∋ A) → 𝒱s vs (pos i) ＝ 𝒱 (lookup vs i)
𝒱s-lookup (v ∷ vs) Z = refl
𝒱s-lookup (v ∷ vs) (S i) = 𝒱s-lookup vs i

{- the meaning of a primitive's result -}
𝒱-δ : ∀ p n m → 𝒱 (δᵥ p (cv n) (cv m)) ＝ out (δᴾ p n m)
𝒱-δ sub n m = refl
𝒱-δ eq n m = 𝒱-bool (does (n ≟ℤ m))
 where
  𝒱-unit : 𝒱 {tup []} (tup []) ＝ unit
  𝒱-unit = ap (tupleᵈ 0 ·_) (dfunext fe (λ ()))
  𝒱-bool : (b : Bool) → 𝒱 {out-ty eq} (if b then inl (tup []) else inr (tup [])) ＝ out (bool b)
  𝒱-bool true = ap (inlᵈ ·_) 𝒱-unit
  𝒱-bool false = ap (inrᵈ ·_) 𝒱-unit

{- Observations of constants ------------------------------------------------------}

private
 view-＝ : (a b : ⟨ 𝔻 ⟩) (e : a ＝ b) (q : defined a) → view a q ＝ view b (transport defined e q)
 view-＝ a .a refl q = refl

 {- values made with different tags differ -}
 inj-tag : (t t' : Tag) (x : _) (y : _) → inj t · x ＝ inj t' · y → t ＝ t'
 inj-tag t t' x y e =
  ap pr₁ (view-inj t x (defined-inj t x) ⁻¹ ∙ view-＝ _ _ e (defined-inj t x) ∙ view-inj t' y _)

 con-inj : ∀ {B B' k k'} → con B k ＝ con B' k' → o-const B k ≡ o-const B' k'
 con-inj refl = ≡-refl

 not-con : (t : Tag) (x : _) {B : Base} {k : base-rep B} → ((B' : Base) (k' : base-rep B') → ¬ (t ＝ con B' k'))
   → ¬ (inj t · x ＝ const B k)
 not-con t x {B} {k} h e = h B k (inj-tag t (con B k) x ⋆ e)

{- a value means a constant exactly when it is observed as that constant -}
𝒱-const : ∀ {A B} {k : base-rep B} (v : Value A) → 𝒱 v ＝ const B k → obs v ≡ o-const B k
𝒱-const (cv k') e = con-inj (inj-tag _ _ ⋆ ⋆ e)
𝒱-const (fold v) e = 𝒱-const v e
𝒱-const (code N) e = 𝟘-elim (not-con (tup 0) _ (λ _ _ ()) e)
𝒱-const (pack (code N) (tup γ)) e = 𝟘-elim (not-con fun _ (λ _ _ ()) e)
𝒱-const (tup {Δ} vs) e =
 𝟘-elim (not-con (tup (length Δ)) (𝒱s vs) (λ _ _ ())
           (guard-defined (length Δ) (𝒱s vs) (𝒱s-defined vs) _ ⁻¹ ∙ e))
𝒱-const (inl v) e = 𝟘-elim (not-con left (𝒱 v) (λ _ _ ()) (seq-defined (𝒱 v) _ (𝒱-defined v) ⁻¹ ∙ e))
𝒱-const (inr v) e = 𝟘-elim (not-con right (𝒱 v) (λ _ _ ()) (seq-defined (𝒱 v) _ (𝒱-defined v) ⁻¹ ∙ e))

const-𝒱 : ∀ {A B} {k : base-rep B} (v : Value A) → obs v ≡ o-const B k → 𝒱 v ＝ const B k
const-𝒱 (cv k) ≡-refl = refl
const-𝒱 (fold v) e = const-𝒱 v e
const-𝒱 (code N) ()
const-𝒱 (pack c γ) ()
const-𝒱 (tup vs) ()
const-𝒱 (inl v) ()
const-𝒱 (inr v) ()

{- Results that hold ---------------------------------------------------------------}

{- a value with P, or a timeout; never an error -}
data Holds {X : 𝓤₀ ̇ } (P : X → 𝓤₁ ̇ ) : Result X → 𝓤₁ ̇ where
  timeout : Holds P timeout
  ret : ∀ {v} → P v → Holds P (ret v)

bind-holds : {X Y : 𝓤₀ ̇ } {P : X → 𝓤₁ ̇ } {Q : Y → 𝓤₁ ̇ } {r : Result X} {f : X → Result Y}
  → Holds P r → ((v : X) → P v → Holds Q (f v)) → Holds Q (r >>= f)
bind-holds timeout k = timeout
bind-holds (ret {v} h) k = k v h

Sound : ∀ {A} → Result (Value A) → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Sound r d = Holds (λ v → 𝒱 v ＝ d) r

sound-＝ : ∀ {A} {r : Result (Value A)} {d d'} → d ＝ d' → Sound r d → Sound r d'
sound-＝ refl s = s

{- Soundness ------------------------------------------------------------------------}

sound : ∀ {Γ A} ck (γ : Envᵢ Γ) (M : Tm Γ A) → Sound (eval ck γ M) (⟦ M ⟧ · 𝓔 γ)
sounds : ∀ {Γ Δ} ck (γ : Envᵢ Γ) (Ms : All (Tm Γ) Δ)
  → Holds (λ vs → (i : Fin (length Δ)) → 𝒱s vs i ＝ (⟦ Ms ⟧s · 𝓔 γ) i) (evals ck γ Ms)
sound-call : ∀ {A B} ck (f : Value (A ⇒ B)) (w : Value A) → Sound (call ck f w) (appᵈ · 𝒱 f · 𝒱 w)

sound ck γ (` x) = ret (𝓔-lookup γ x)
sound ck γ (lam N) = ret refl
sound ck γ (app L M) =
  bind-holds (sound ck γ L) λ f eL → bind-holds (sound ck γ M) λ w eM →
    sound-＝ (ap₂ (λ a b → appᵈ · a · b) eL eM) (sound-call ck f w)
sound ck γ (lit B c) = ret refl
sound ck γ (tuple {Δ} Ms) =
  bind-holds (sounds ck γ Ms) λ vs e → ret (ap (tupleᵈ (length Δ) ·_) (dfunext fe e))
sound ck γ (get {Δ} i M) =
  bind-holds (sound ck γ M) λ { (tup vs) e →
    ret ((proj-tuple (length Δ) (𝒱s vs) (𝒱s-defined vs) (pos i) ∙ 𝒱s-lookup vs i) ⁻¹ ∙ ap (proj (pos i) ·_) e) }
sound ck γ (inl M) = bind-holds (sound ck γ M) λ v e → ret (ap (inlᵈ ·_) e)
sound ck γ (inr M) = bind-holds (sound ck γ M) λ v e → ret (ap (inrᵈ ·_) e)
sound ck γ (case L M N) = bind-holds (sound ck γ L) λ
  { (inl v) e → sound-＝ (caseᶜ-inl ⟦ L ⟧ ⟦ M ⟧ ⟦ N ⟧ (𝓔 γ) (𝒱 v) (e ⁻¹) (𝒱-defined v) ⁻¹) (sound ck (v ∷ γ) M)
  ; (inr v) e → sound-＝ (caseᶜ-inr ⟦ L ⟧ ⟦ M ⟧ ⟦ N ⟧ (𝓔 γ) (𝒱 v) (e ⁻¹) (𝒱-defined v) ⁻¹) (sound ck (v ∷ γ) N) }
sound ck γ (prim p L M) = bind-holds (sound ck γ L) λ
  { (cv n) eL → bind-holds (sound ck γ M) λ
    { (cv m) eM → ret (𝒱-δ p n m ∙ primD-const p n m ⁻¹ ∙ ap₂ (λ a b → primD p · a · b) eL eM) } }
sound ck γ (let′ M N) = bind-holds (sound ck γ M) λ v e →
  sound-＝ ((letᶜ-β ⟦ M ⟧ ⟦ N ⟧ (𝓔 γ) ∙ ap (λ a → seq · a · (⟦ N ⟧ · (a • 𝓔 γ))) (e ⁻¹)
              ∙ seq-defined (𝒱 v) _ (𝒱-defined v)) ⁻¹)
           (sound ck (v ∷ γ) N)
sound ck γ (fold M) = bind-holds (sound ck γ M) λ v e → ret e
sound ck γ (unfold M) = bind-holds (sound ck γ M) λ { (fold v) e → ret e }

sounds ck γ [] = ret (λ ())
sounds ck γ (M ∷ Ms) =
  bind-holds (sound ck γ M) λ v e → bind-holds (sounds ck γ Ms) λ vs es →
    ret (λ { zero → e ; (suc i) → es i })

sound-call zero f w = timeout
sound-call (succ ck) (pack (code N) (tup γ)) w =
  sound-＝ ((lamᶜ-β ⟦ N ⟧ (𝓔 γ) (𝒱 w) ∙ seq-defined (𝒱 w) _ (𝒱-defined w)) ⁻¹) (sound ck (w ∷ γ) N)
