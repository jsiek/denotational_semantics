{-

  Correctness of typed remove complex operands (Clos5ᵀ → Monᵀ,
  Compiler/RCO.agda): the Clos5ᵀ machine on P and on the embedding
  of rco-program P are Equivalent, for every program P.

  The two runs compute the same values (a code pointer is a typed index
  into the same table, and definition g of the target is rco of
  definition g of the source). The target's environment has the values
  of the lets in front: a source term M in φ₁ is related to the target
  term rco M r in φ₂ when φ₂ holds at r x the value of x (ER).

  The machines move between related states (Both,
  proof/Framework/Both.agda), with one or more steps each. An operation
  with complex operands becomes lets for them, then the operation on
  atoms. The source evaluates the operands in order, through its
  continuation frames; the target evaluates a complex operand under the
  let of atomize, with the rest of the translation (the Kripke
  continuation k of atomize) as the let's body. So a source frame κ₁ is
  related to that let (pend) when, given the value of an atom a, the
  source continuing with κ₁ and the target running k applied to a are
  related (KRel); KRel is shown for each kind of frame (the operations
  on one operand, the two operands of pack, callc and prim, the
  components of a tuple, and case). An atom evaluates to its value in one
  step and cannot fail, so the time at which each side evaluates it
  does not matter.

-}

module proof.Correctness.CEK.RCOSim where

open import Language.Typed.Type
open import Framework.Primitives using (Int)
open import Language.Typed.Clos5
import Language.Typed.Mon as M
open M using (Atm; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Compiler.RCO
open import Framework.Lookup using (_!_)
open import proof.Framework.Lookup using (map-!)
open import Semantics.Observation using (Obs; o-error)
open import proof.Semantics.CEK.Smallstep using (next; stop; next?; Star; ε; _◅_; Plus; plus; step⁺; star-plus)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim; pre₁; pre₂)
open import proof.Correctness.CEK.Clos5Common using (atm-step; tuple-atoms)
open import Framework.VecUtil using (_+ʳ_; _<><_)
open import Semantics.CEK.Typed.Clos5
open import Semantics.CEK.Typed.Imp using (atom)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- φ₂ holds at r x the value of x in φ₁ -}
record ER {Σ Γ Δ} (r : Ren Γ Δ) (φ₁ : Env Σ Γ) (φ₂ : Env Σ Δ) : Set where
  constructor er
  field at : ∀ {A} (x : Γ ∋ A) → φ₂ ! r x ≡ φ₁ ! x
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

module Sim {Σ : List ℕ} (ds : All (Code Σ) Σ) (M₀ : Tm Σ [] Any) where

  ds₂ = All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)
  L₁ = sem (program ds M₀)
  L₂ = sem ⌜ rco-program (program ds M₀) ⌝ₚ

  at₂ = atm-step ds₂ ⌜ rco M₀ (λ x → x) ⌝

  mutual
    infix 4 _≈_ _~_
    data _≈_ : ∀ {A} → Cont Σ A → Cont Σ A → Set where
      halt : halt ≈ halt
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

  B = Both {L₁ = L₁} {L₂ = L₂} _~_

  KRel : ∀ {Δ A B} → Cont Σ A → K Σ Δ A B → Env Σ Δ → Cont Σ B → Set
  KRel κ₁ k φ₂ κ₂ = ∀ {Δ'} (r' : Ren _ Δ') φ₂' (a : Atm Σ Δ' _) → ER r' φ₂ φ₂' → B (ret (atom φ₂' a) κ₁) (eval ⌜ k r' a ⌝ φ₂' κ₂)

  ret≡ : ∀ {A} {u u' : Val Σ A} {κ₁ κ₂} → u ≡ u' → κ₁ ≈ κ₂ → ret u κ₁ ~ ret u' κ₂
  ret≡ refl k = ret~ k

  {- the same frame, given the same value -}
  same : ∀ {A} {s₁ s₂} {u : Val Σ A} {κ₁ κ₂} → step ds s₁ ≡ next (ret u κ₁) → step ds₂ s₂ ≡ next (ret u κ₂) → κ₁ ≈ κ₂ → B s₁ s₂
  same st₁ st₂ k = move (step⁺ st₁) (step⁺ st₂) (ret~ k)

  {- a call -}
  call~ : ∀ (f : Val Σ ⟪ fun ⟫) w {κ₁ κ₂} → κ₁ ≈ κ₂ → call ds f w κ₁ ~ call ds₂ f w κ₂
  call~ (pack (code g) e) w k =
    subst (λ N → eval (ds ! g) _ _ ~ eval N _ _)
      (sym (trans (map-! ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds) g) (cong ⌜_⌝ (map-! (λ D → rco D (λ x → x)) ds g)))) (eval~ er-id k)

  ret-both : ∀ {A} {κ₁ κ₂ : Cont Σ A} → κ₁ ≈ κ₂ → ∀ v → B (ret v κ₁) (ret v κ₂)
  ret-both halt v = halt refl ε refl
  ret-both (letK e k) v = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)
  ret-both (pend kr) v = pre₂ _~_ refl (kr S _ (var Z) er-S)

  proj-both : ∀ {t} (v : Val Σ Any) {κ₁ κ₂} → κ₁ ≈ κ₂ → B (ret v (projK t κ₁)) (ret v (projK t κ₂))
  proj-both {t} v k with proj? t v in e
  ... | just w = move (step⁺ (cong (next? o-error _) e)) (step⁺ (cong (next? o-error _) e)) (ret~ k)
  ... | nothing = halt (cong (next? o-error _) e) ε (cong (next? o-error _) e)

  case-both : ∀ {Γ Δ} {N₁ N₂ : Tm Σ (Any ∷ Γ) Any} {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} (v : Val Σ ⟪ sum ⟫) → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → B (ret v (caseK N₁ N₂ φ₁ κ₁)) (ret v (caseK ⌜ rco N₁ (ext r) ⌝ ⌜ rco N₂ (ext r) ⌝ φ₂ κ₂))
  case-both (inl u) e k = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)
  case-both (inr u) e k = move (step⁺ refl) (step⁺ refl) (eval~ (er-ext e) k)

  {- the frames of the operations on one operand -}
  krel-get : ∀ {Δ n i} {φ₂ : Env Σ Δ} {κ₁ κ₂ : Cont Σ Any} → κ₁ ≈ κ₂ → KRel (getK {n = n} i κ₁) (λ _ a → M.get i a) φ₂ κ₂
  krel-get k r' φ₂' a e' = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k))

  krel-inl : ∀ {Δ} {φ₂ : Env Σ Δ} {κ₁ κ₂} → κ₁ ≈ κ₂ → KRel (inlK κ₁) (λ _ a → M.inl a) φ₂ κ₂
  krel-inl k r' φ₂' a e' = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k))

  krel-inr : ∀ {Δ} {φ₂ : Env Σ Δ} {κ₁ κ₂} → κ₁ ≈ κ₂ → KRel (inrK κ₁) (λ _ a → M.inr a) φ₂ κ₂
  krel-inr k r' φ₂' a e' = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k))

  krel-inj : ∀ {Δ G} {φ₂ : Env Σ Δ} {κ₁ κ₂} → κ₁ ≈ κ₂ → KRel (injK G κ₁) (λ _ a → M.inject G a) φ₂ κ₂
  krel-inj k r' φ₂' a e' = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (same refl refl k))

  krel-proj : ∀ {Δ t} {φ₂ : Env Σ Δ} {κ₁ κ₂} → κ₁ ≈ κ₂ → KRel (projK t κ₁) (λ _ a → M.project t a) φ₂ κ₂
  krel-proj k r' φ₂' a e' = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (proj-both (atom φ₂' a) k))

  krel-case : ∀ {Γ Δ} {N₁ N₂ : Tm Σ (Any ∷ Γ) Any} {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → KRel (caseK N₁ N₂ φ₁ κ₁) (λ r₁ a → M.case a (rco N₁ (ext λ x → r₁ (r x))) (rco N₂ (ext λ x → r₁ (r x)))) φ₂ κ₂
  krel-case e k r₁ φ₂' a e₁ = pre₂ _~_ refl (pre₂ _~_ (at₂ a) (case-both (atom φ₂' a) (er-∘ e e₁) k))

  {- the second operand of pack, callc and prim, after an atom a for the first -}
  krel-packR : ∀ {Δ n} {φ₂ : Env Σ Δ} (a : Atm Σ Δ (code n)) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (packR (atom φ₂ a) κ₁) (λ r₂ b → M.pack (ren r₂ a) b) φ₂ κ₂
  krel-packR a k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε))
    (ret≡ (cong (λ u → pack u (atom φ₂'' b)) (sym (atom-ren e₂ a))) k)

  krel-callR : ∀ {Δ} {φ₂ : Env Σ Δ} (a : Atm Σ Δ ⟪ fun ⟫) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (callR (atom φ₂ a) κ₁) (λ r₂ b → M.callc (ren r₂ a) b) φ₂ κ₂
  krel-callR {φ₂ = φ₂} a {κ₁} {κ₂} k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε))
    (subst (λ F → call ds (atom φ₂ a) (atom φ₂'' b) κ₁ ~ call ds₂ F (atom φ₂'' b) κ₂) (sym (atom-ren e₂ a)) (call~ _ _ k))

  krel-primR : ∀ {Δ p} {φ₂ : Env Σ Δ} (a : Atm Σ Δ ⟪ base Int ⟫) {κ₁ κ₂} → κ₁ ≈ κ₂
    → KRel (primR p (int (atom φ₂ a)) κ₁) (λ r₂ b → M.prim p (ren r₂ a) b) φ₂ κ₂
  krel-primR {p = p} a k r₂ φ₂'' b e₂ = move (step⁺ refl) (plus refl (at₂ (ren r₂ a) ◅ refl ◅ at₂ b ◅ refl ◅ ε))
    (ret≡ (cong (λ u → δᵀ p (int u) (int (atom φ₂'' b))) (sym (atom-ren e₂ a))) k)

  sim-eval : ∀ {Γ Δ A} (M : Tm Σ Γ A) {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → B (eval M φ₁ κ₁) (eval ⌜ rco M r ⌝ φ₂ κ₂)
  atz : ∀ {Γ Δ A B'} (N : Tm Σ Γ A) {r : Ren Γ Δ} {k : K Σ Δ A B'} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → KRel κ₁ k φ₂ κ₂
    → B (eval N φ₁ κ₁) (eval ⌜ atomize N r k ⌝ φ₂ κ₂)
  atzs : ∀ {Γ Δ B' m j} (Ns : Vec (Tm Σ Γ Any) j) {r : Ren Γ Δ} {k : ∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) j → M.Exp Σ Δ' B'}
    {φ₁ φ₂} {vs : Vec _ m} {κ₁ : Cont Σ ⟪ tup (m +ʳ j) ⟫} {κ₂ : Cont Σ B'} {s₁}
    → ER r φ₁ φ₂
    → (∀ {Δ'} (r' : Ren Δ Δ') φ₂' (as : Vec (Atm Σ Δ' Any) j) → ER r' φ₂ φ₂' → ∀ {s V} → V ≡ vs <>< map (atom φ₂') as
        → step ds s ≡ next (ret (tup V) κ₁) → B s (eval ⌜ k r' as ⌝ φ₂' κ₂))
    → step ds s₁ ≡ next (tuple-next vs Ns φ₁ κ₁) → B s₁ (eval ⌜ atomizes Ns r k ⌝ φ₂ κ₂)

  {- the first operand of pack, callc and prim -}
  krel-packL : ∀ {Γ Δ n} (N : Tm Σ Γ ⟪ tup n ⟫) {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → KRel (packL N φ₁ κ₁) (λ r₁ a → atomize N (λ x → r₁ (r x)) (λ r₂ b → M.pack (ren r₂ a) b)) φ₂ κ₂
  krel-packL N e k r₁ φ₂' a e₁ = pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-packR a k))

  krel-callL : ∀ {Γ Δ} (N : Tm Σ Γ Any) {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → KRel (callL N φ₁ κ₁) (λ r₁ a → atomize N (λ x → r₁ (r x)) (λ r₂ b → M.callc (ren r₂ a) b)) φ₂ κ₂
  krel-callL N e k r₁ φ₂' a e₁ = pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-callR a k))

  krel-primL : ∀ {Γ Δ p} (N : Tm Σ Γ ⟪ base Int ⟫) {r : Ren Γ Δ} {φ₁ φ₂ κ₁ κ₂} → ER r φ₁ φ₂ → κ₁ ≈ κ₂
    → KRel (primL p N φ₁ κ₁) (λ r₁ a → atomize N (λ x → r₁ (r x)) (λ r₂ b → M.prim p (ren r₂ a) b)) φ₂ κ₂
  krel-primL N e k r₁ φ₂' a e₁ = pre₁ _~_ refl refl (atz N (er-∘ e e₁) (krel-primR a k))

  {- a tuple of atoms -}
  kv-tuple : ∀ {Δ j} {φ₂ : Env Σ Δ} {κ₁ κ₂} → κ₁ ≈ κ₂ → ∀ {Δ'} (r' : Ren Δ Δ') φ₂' (as : Vec (Atm Σ Δ' Any) j)
    → ER r' φ₂ φ₂' → ∀ {s V} → V ≡ map (atom φ₂') as → step ds s ≡ next (ret (tup V) κ₁)
    → B s (eval ⌜ M.tuple as ⌝ φ₂' κ₂)
  kv-tuple k r' φ₂' as e' refl st = move (step⁺ st) (plus refl (tuple-atoms ds₂ ⌜ rco M₀ (λ x → x) ⌝ [] as)) (ret~ k)

  sim-eval (` x) e k = move (step⁺ refl) (step⁺ refl) (ret≡ (sym (at e x)) k)
  sim-eval (fun-ref f) e k = move (step⁺ refl) (step⁺ refl) (ret~ k)
  sim-eval (pack L N) e k = pre₁ _~_ refl refl (atz L e (krel-packL N e k))
  sim-eval (callc L N) e k = pre₁ _~_ refl refl (atz L e (krel-callL N e k))
  sim-eval (lit B c) e k = move (step⁺ refl) (step⁺ refl) (ret~ k)
  sim-eval (tuple Ms) e k = atzs Ms e (kv-tuple k) refl
  sim-eval (get i N) e k = pre₁ _~_ refl refl (atz N e (krel-get k))
  sim-eval (inl N) e k = pre₁ _~_ refl refl (atz N e (krel-inl k))
  sim-eval (inr N) e k = pre₁ _~_ refl refl (atz N e (krel-inr k))
  sim-eval (case L N₁ N₂) e k = pre₁ _~_ refl refl (atz L e (krel-case e k))
  sim-eval (prim p L N) e k = pre₁ _~_ refl refl (atz L e (krel-primL N e k))
  sim-eval (let′ N₁ N₂) e k = move (step⁺ refl) (step⁺ refl) (eval~ e (letK e k))
  sim-eval (inject G N) e k = pre₁ _~_ refl refl (atz N e (krel-inj k))
  sim-eval (project t N) e k = pre₁ _~_ refl refl (atz N e (krel-proj k))

  atz (` x) {r} {k} {φ₂ = φ₂} {κ₁} e kr =
    pre₁ _~_ refl refl (subst (λ v → B (ret v κ₁) (eval ⌜ k (λ y → y) (var (r x)) ⌝ φ₂ _)) (at e x) (kr (λ y → y) φ₂ (var (r x)) er-id))
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
  atz N@(inject _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))
  atz N@(project _ _) {k = k} e kr = pre₂ _~_ refl (sim-eval N e (pend {k = k} kr))

  atzs [] e kv st = kv (λ y → y) _ [] er-id refl st
  atzs (N ∷ Ns) {vs = vs} e kv st =
    pre₁ _~_ st refl (atz N e λ r₁ φ₂' a e₁ →
      atzs Ns (er-∘ e e₁) (λ r₂ φ₂'' as e₂ eqL st' →
        kv _ φ₂'' (ren r₂ a ∷ as) (er-∘ e₁ e₂) (trans eqL (cong (λ u → (u ∷ vs) <>< map (atom φ₂'') as) (sym (atom-ren e₂ a)))) st') refl)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → B s₁ s₂
  sim (eval~ {M = M} e k) = sim-eval M e k
  sim (ret~ k) = ret-both k _

{- The end theorem ---------------------------------------------------------------}

rco-correct : ∀ (P : Program) → Equivalent (sem P) (sem ⌜ rco-program P ⌝ₚ)
rco-correct (program ds M) = equivalent (both-fsim _~_ (eval~ er-id halt) sim)
  where open Sim ds M
