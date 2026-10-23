{-

  Correctness of remove complex operands (GlobalFunμ → Monμ,
  Mu/Compiler/RCO.agda): the GlobalFunμ machine on P and on the embedding of
  rco-program P are Equivalent, for every program P, as for typed rco
  (proof/Correctness/CEK/RCOSim.agda).

  The two runs compute the same values. The target's environment has the
  values of the lets in front: a source term M in φ₁ is related to the
  target term rco M r in φ₂ when φ₂ holds at r x the value of x (ER).

  The machines move between related states (Both,
  proof/Framework/Both.agda), with one or more steps each. An operation
  with complex operands becomes lets for them, then the operation on
  atoms. The source evaluates the operands in order, through its
  continuation frames; the target evaluates a complex operand under the
  let of atomize, with the rest of the translation (the Kripke
  continuation k of atomize) as the let's body. So a source frame κ₁ is
  related to that let (pend) when, given the value of an atom a, the
  source continuing with κ₁ and the target running k applied to a are
  related (KRel); KRel is shown for each kind of frame (sim-eval). A tuple's
  components are collected newest first by both machines, in front of
  the values still to come (_<><ᵃ_), so the source's tuple is the values
  so far followed by those of the atoms, with no equation about lengths.

-}

module Mu.proof.Correctness.AbstractMachines.RCOSim where

open import Mu.Language.Type
open import Framework.Primitives using (Int)
open import Mu.Language.GlobalFun
import Mu.Language.Mon as M
open M using (Atm; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.RCO
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map; _<><_; _<><ᵃ_)
open import Mu.proof.Framework.AllProp using (lookup-map)
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (next; ε; _◅_; plus; step⁺)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim; pre₁; pre₂)
open import Mu.proof.Correctness.AbstractMachines.GlobalFunCommon using (atm-step; tuple-atoms)
open import Mu.Semantics.AbstractMachines.GlobalFun
open import Mu.Semantics.AbstractMachines.Imp using (atom)

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- φ₂ holds at r x the value of x in φ₁ -}
record ER {Σ Γ Δ} (r : Ren Γ Δ) (φ₁ : Env Σ Γ) (φ₂ : Env Σ Δ) : Set where
  constructor er
  field at : ∀ {A} (x : Γ ∋ A) → lookup φ₂ (r x) ≡ lookup φ₁ x
open ER

er-id : ∀ {Σ Γ} {φ : Env Σ Γ} → ER (λ x → x) φ φ
er-id = er λ x → refl

er-S : ∀ {Σ Γ B} {φ : Env Σ Γ} {v : Val Σ B} → ER S φ (v ∷ φ)
er-S = er λ x → refl

er-ext : ∀ {Σ Γ Δ B} {r : Ren Γ Δ} {φ₁ φ₂} {v : Val Σ B} → ER r φ₁ φ₂ → ER (ext r) (v ∷ φ₁) (v ∷ φ₂)
er-ext e = er λ { Z → refl ; (S x) → at e x }

er-∘ : ∀ {Σ Γ Δ Δ'} {r : Ren Γ Δ} {r' : Ren Δ Δ'} {φ₁ : Env Σ Γ} {φ₂ φ₃} → ER r φ₁ φ₂ → ER r' φ₂ φ₃
  → ER (λ x → r' (r x)) φ₁ φ₃
er-∘ e e' = er λ x → trans (at e' _) (at e x)

atom-ren : ∀ {Σ Δ Δ' A} {r : Ren Δ Δ'} {φ φ'} → ER r φ φ' → (a : Atm Σ Δ A) → atom φ' (ren r a) ≡ atom φ a
atom-ren e (var x) = at e x
atom-ren e (lit B c) = refl
atom-ren e (ref f) = refl

{- The simulation, for a program with definitions ds and main M₀ ---------------}

module Sim {Σ : List DSig} (ds : All (Code Σ) Σ) {T} (M₀ : Tm Σ [] T) where

  ds₂ = map ⌜_⌝ (map (λ D → rco D (λ x → x)) ds)
  L₁ = sem (program ds M₀)
  L₂ = sem ⌜ rco-program (program ds M₀) ⌝ₚ

  at₂ = atm-step ds₂ ⌜ rco M₀ (λ x → x) ⌝

  mutual
    infix 4 _≈_ _~_
    data _≈_ : ∀ {A} → Cont Σ A → Cont Σ A → Set where
      halt : ∀ {A} → halt {A = A} ≈ halt
      letK : ∀ {Γ Δ A B} {r : Ren Γ Δ} {N : Tm Σ (A ∷ Γ) B} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
        → letK N φ₁ κ₁ ≈ letK ⌜ rco N (ext r) ⌝ φ₂ κ₂
      {- a source frame, and the let of atomize -}
      pend : ∀ {Δ A B} {k : K Σ Δ A B} {φ₂ κ₁ κ₂}
        → (∀ {Δ'} (r' : Ren Δ Δ') φ₂' (a : Atm Σ Δ' A) → ER r' φ₂ φ₂'
             → Both {L₁ = L₁} {L₂ = L₂} _~_ (ret (atom φ₂' a) κ₁) (eval ⌜ k r' a ⌝ φ₂' κ₂))
        → κ₁ ≈ letK ⌜ k S (var Z) ⌝ φ₂ κ₂

    data _~_ : State Σ → State Σ → Set where
      eval~ : ∀ {Γ Δ A} {M : Tm Σ Γ A} {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
        → eval M φ₁ κ₁ ~ eval ⌜ rco M r ⌝ φ₂ κ₂
      ret~ : ∀ {A} {v : Val Σ A} {κ₁ κ₂} → κ₁ ≈ κ₂ → ret v κ₁ ~ ret v κ₂

  𝔅 = Both {L₁ = L₁} {L₂ = L₂} _~_

  KRel : ∀ {Δ A B} → Cont Σ A → K Σ Δ A B → Env Σ Δ → Cont Σ B → Set
  KRel κ₁ k φ₂ κ₂ = ∀ {Δ'} (r' : Ren _ Δ') φ₂' (a : Atm Σ Δ' _) → ER r' φ₂ φ₂' → 𝔅 (ret (atom φ₂' a) κ₁) (eval ⌜ k r' a ⌝ φ₂' κ₂)

  ret≡ : ∀ {A} {u u' : Val Σ A} {κ₁ κ₂} → u ≡ u' → κ₁ ≈ κ₂ → ret u κ₁ ~ ret u' κ₂
  ret≡ refl k = ret~ k

  {- the same frame, given the same value -}
  same : ∀ {A} {s₁ s₂} {u : Val Σ A} {κ₁ κ₂} → step ds s₁ ≡ next (ret u κ₁) → step ds₂ s₂ ≡ next (ret u κ₂) → κ₁ ≈ κ₂ → 𝔅 s₁ s₂
  same st₁ st₂ k = move (step⁺ st₁) (step⁺ st₂) (ret~ k)

  {- a call -}
  call~ : ∀ {A B} (f : Val Σ (A ⇒ B)) {f'} w {κ₁ κ₂} → f' ≡ f → κ₁ ≈ κ₂ → call ds f w κ₁ ~ call ds₂ f' w κ₂
  call~ (pack (code g) e) w refl k =
    subst (λ N → eval (lookup ds g) _ _ ~ eval N _ _)
      (sym (trans (lookup-map ⌜_⌝ (map (λ D → rco D (λ x → x)) ds) g) (cong ⌜_⌝ (lookup-map (λ D → rco D (λ x → x)) ds g))))
      (eval~ er-id k)

  ret-both : ∀ {A} {κ₁ κ₂ : Cont Σ A} → κ₁ ≈ κ₂ → ∀ v → 𝔅 (ret v κ₁) (ret v κ₂)
  ret-both halt v = halt refl ε refl
  ret-both (letK e k) v = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)
  ret-both (pend kr) v = pre₂ _~_ refl (kr S _ (var Z) er-S)

  case-both : ∀ {Γ Δ A B C} {N₁ : Tm Σ (A ∷ Γ) C} {N₂ : Tm Σ (B ∷ Γ) C} {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} (v : Val Σ (A ⊹ B))
    → ER r φ₁ φ₂ → κ₁ ≈ κ₂ → 𝔅 (ret v (caseK N₁ N₂ φ₁ κ₁)) (ret v (caseK ⌜ rco N₁ (ext r) ⌝ ⌜ rco N₂ (ext r) ⌝ φ₂ κ₂))
  case-both (inl u) e k = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)
  case-both (inr u) e k = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)

  {- the second operand of pack, callc and prim, after an atom a for the first -}
  krel-packR : ∀ {Δ Δ' A B} {φ₂ : Env Σ Δ} (a : Atm Σ Δ (code Δ' A B)) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (packR (atom φ₂ a) κ₁) (λ r₂ b → M.pack (ren r₂ a) b) φ₂ κ₂
  krel-packR a k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε))
    (ret≡ (cong (λ u → pack u (atom φ₂'' b)) (sym (atom-ren e₂ a))) k)

  krel-callR : ∀ {Δ A B} {φ₂ : Env Σ Δ} (a : Atm Σ Δ (A ⇒ B)) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (callR (atom φ₂ a) κ₁) (λ r₂ b → M.callc (ren r₂ a) b) φ₂ κ₂
  krel-callR a k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε)) (call~ _ _ (atom-ren e₂ a) k)

  krel-primR : ∀ {Δ p} {φ₂ : Env Σ Δ} (a : Atm Σ Δ (base Int)) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (primR p (int (atom φ₂ a)) κ₁) (λ r₂ b → M.prim p (ren r₂ a) b) φ₂ κ₂
  krel-primR {p = p} a k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε))
    (ret≡ (cong (λ u → δᵀ p (int u) (int (atom φ₂'' b))) (sym (atom-ren e₂ a))) k)

  sim-eval : ∀ {Γ Δ A} (M : Tm Σ Γ A) {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → 𝔅 (eval M φ₁ κ₁) (eval ⌜ rco M r ⌝ φ₂ κ₂)
  atz : ∀ {Γ Δ A B'} (N : Tm Σ Γ A) {r : Ren Γ Δ} {k : K Σ Δ A B'} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → KRel κ₁ k φ₂ κ₂
    → 𝔅 (eval N φ₁ κ₁) (eval ⌜ atomize N r k ⌝ φ₂ κ₂)
  atzs : ∀ {Γ Δ B' Δ' Δs} (Ns : All (Tm Σ Γ) Δs) {r : Ren Γ Δ} {k : ∀ {Δ''} → Ren Δ Δ'' → All (Atm Σ Δ'') Δs → M.Exp Σ Δ'' B'}
    {φ₁ φ₂} {vs : All (Val Σ) Δ'} {κ₁ : Cont Σ (tup (Δ' <>< Δs))} {κ₂ : Cont Σ B'} {s₁}
    → ER r φ₁ φ₂
    → (∀ {Δ''} (r' : Ren Δ Δ'') φ₂' (as : All (Atm Σ Δ'') Δs) → ER r' φ₂ φ₂' → ∀ {s}
        → step ds s ≡ next (ret (tup (vs <><ᵃ map (atom φ₂') as)) κ₁) → 𝔅 s (eval ⌜ k r' as ⌝ φ₂' κ₂))
    → step ds s₁ ≡ next (tuple-next vs Ns φ₁ κ₁) → 𝔅 s₁ (eval ⌜ atomizes Ns r k ⌝ φ₂ κ₂)

  sim-eval (` x) e k = move (step⁺ refl) (step⁺ refl) (ret≡ (sym (at e x)) k)
  sim-eval (fun-ref f) e k = move (step⁺ refl) (step⁺ refl) (ret~ k)
  sim-eval (pack L N) e k = pre₁ _~_ refl refl (atz L e λ _ _ a e₁ → pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-packR a k)))
  sim-eval (callc L N) e k = pre₁ _~_ refl refl (atz L e λ _ _ a e₁ → pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-callR a k)))
  sim-eval (lit B c) e k = move (step⁺ refl) (step⁺ refl) (ret~ k)
  sim-eval (tuple Ms) e k = atzs Ms e (λ _ _ as _ st → move (step⁺ st) (plus refl (tuple-atoms ds₂ ⌜ rco M₀ (λ x → x) ⌝ [] as)) (ret~ k)) refl
  sim-eval (get i N) e k = pre₁ _~_ refl refl (atz N e λ _ _ a _ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k)))
  sim-eval (inl N) e k = pre₁ _~_ refl refl (atz N e λ _ _ a _ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k)))
  sim-eval (inr N) e k = pre₁ _~_ refl refl (atz N e λ _ _ a _ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k)))
  sim-eval (case L N₁ N₂) e k = pre₁ _~_ refl refl (atz L e λ _ φ₂' a e₁ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (case-both (atom φ₂' a) (er-∘ e e₁) k)))
  sim-eval (prim p L N) e k = pre₁ _~_ refl refl (atz L e λ _ _ a e₁ → pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-primR a k)))
  sim-eval (let′ N₁ N₂) e k = move (step⁺ refl) (step⁺ refl) (eval~ e (letK e k))
  sim-eval (fold N) e k = pre₁ _~_ refl refl (atz N e λ _ _ a _ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k)))
  sim-eval (unfold N) e k = pre₁ _~_ refl refl (atz N e λ _ _ a _ → pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k)))

  atz (` x) {r} {k} {φ₂ = φ₂} {κ₁} e kr =
    pre₁ _~_ refl refl (subst (λ v → 𝔅 (ret v κ₁) (eval ⌜ k (λ y → y) (var (r x)) ⌝ φ₂ _)) (at e x) (kr (λ y → y) φ₂ (var (r x)) er-id))
  atz (fun-ref f) e kr = pre₁ _~_ refl refl (kr (λ y → y) _ (ref f) er-id)
  atz (lit B c) e kr = pre₁ _~_ refl refl (kr (λ y → y) _ (lit B c) er-id)
  atz N@(pack _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(callc _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(tuple _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(get _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(inl _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(inr _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(case _ _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(prim _ _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(let′ _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(fold _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(unfold _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))

  atzs [] e kv st = kv (λ y → y) _ [] er-id st
  atzs (N ∷ Ns) {vs = vs} {κ₁} e kv st =
    pre₁ _~_ st refl (atz N e λ r₁ φ₂' a e₁ →
      atzs Ns (er-∘ e e₁) (λ r₂ φ₂'' as e₂ st' →
        kv _ φ₂'' (ren r₂ a ∷ as) (er-∘ e₁ e₂)
          (trans st' (cong (λ u → next (ret (tup (vs <><ᵃ (u ∷ map (atom φ₂'') as))) κ₁)) (sym (atom-ren e₂ a))))) refl)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → 𝔅 s₁ s₂
  sim (eval~ {M = M} e k) = sim-eval M e k
  sim (ret~ k) = ret-both k _

{- The end theorem ---------------------------------------------------------------}

rco-correct : ∀ {A} (P : Program A) → Equivalent (sem P) (sem ⌜ rco-program P ⌝ₚ)
rco-correct (program ds M) = equivalent (both-fsim _~_ (eval~ er-id halt) sim)
  where open Sim ds M
