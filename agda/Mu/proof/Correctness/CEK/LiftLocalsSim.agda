{-

  Correctness of lift locals (Monμ → Impμ, Mu/Compiler/LiftLocals.agda):
  the Impμ machine on lift-program P and the Clos5μ machine on the
  embedding ⌜ P ⌝ₚ (the meaning of a Monμ program) are Equivalent, as
  for typed lift locals (proof/Correctness/CEK/LiftLocalsSim.agda).

  The pass is structural, and the frame of the Impμ machine is the
  environment of the Clos5μ machine, so the two run on the same values
  and frames. The Impμ machine is simulated by the Clos5μ one (Both,
  proof/Framework/Both.agda): one Impμ step runs a simple expression on
  its atoms, which the Clos5μ machine evaluates one by one, through
  continuation frames, in a few steps (atm-step); then both continue
  with related continuations (x := □; e₂ and let □ in e₂), or both stop
  with the same observation (the end).

-}

module Mu.proof.Correctness.CEK.LiftLocalsSim where

open import Mu.Language.Type
import Mu.Language.Mon as M
open M using (DSig; Args; atm; pack; callc; tuple; get; inl; inr; case; prim; let′; fold; unfold; ⌜_⌝; ⌜_⌝ₚ)
open import Mu.Compiler.LiftLocals using (lift; lift-program)
open import Mu.Framework.AllUtil using (All; []; _∷_; map)
open import Mu.Framework.AllProp using (lookup-map)
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; Plus; plus; plus-star; star-plus; step⁺; plus→star)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent; equiv-sym)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
open import Mu.proof.Correctness.CEK.Clos5Common using (atm-step; tuple-atoms)
import Mu.Semantics.CEK.Clos5 as C
import Mu.Semantics.CEK.Imp as I

open import Data.List using (List; []; _∷_)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

module Sim {Σ : List DSig} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) Σ) {T} (e₀ : M.Exp Σ [] T) where

  ds₁ = map lift ds
  ds₂ = map ⌜_⌝ ds
  L₁ = I.sem (lift-program (M.program ds e₀))
  L₂ = C.sem ⌜ M.program ds e₀ ⌝ₚ

  at = atm-step ds₂ ⌜ e₀ ⌝

  infix 4 _≈_ _~_
  {- the source's (Clos5μ) on the left, the target's (Impμ) on the right -}
  data _≈_ : ∀ {A} → C.Cont Σ A → I.Cont Σ A → Set where
    halt : ∀ {A} → C.halt {A = A} ≈ I.halt
    assignK : ∀ {Δ A B} {e : M.Exp Σ (A ∷ Δ) B} {φ κ₁ κ₂} → κ₂ ≈ κ₁ → C.letK ⌜ e ⌝ φ κ₂ ≈ I.assignK (lift e) φ κ₁

  data _~_ : C.State Σ → I.State Σ → Set where
    eval~ : ∀ {Δ A} {e : M.Exp Σ Δ A} {φ κ₁ κ₂} → κ₂ ≈ κ₁ → C.eval ⌜ e ⌝ φ κ₂ ~ I.eval (lift e) φ κ₁

  {- the Impμ machine (L₁) is the one simulated, so Both takes the
     converse of _~_ -}
  𝔅 = Both {L₁ = L₁} {L₂ = L₂} (flip _~_)

  private variable
    A : Type
    s₁ : I.State Σ
    s₂ t : C.State Σ
    κ₁ : I.Cont Σ A
    κ₂ : C.Cont Σ A

  {- a value goes to related continuations -}
  val : ∀ {v : C.Val Σ A} → I.step ds₁ s₁ ≡ I.cont ds₁ v κ₁ → κ₂ ≈ κ₁ → Plus L₂ s₂ (C.ret v κ₂) → 𝔅 s₁ s₂
  val st halt π = halt st (plus→star π) refl
  val st (assignK k) π = move (step⁺ st) (plus-star π (refl ◅ ε)) (eval~ k)

  call : ∀ {A'} (f : C.Val Σ (A' ⇒ A)) w → I.step ds₁ s₁ ≡ I.res ds₁ (I.call f w) κ₁ → κ₂ ≈ κ₁
    → Plus L₂ s₂ (C.ret w (C.callR f κ₂)) → 𝔅 s₁ s₂
  call (C.pack (C.code g) e) w st k π =
    move (step⁺ (trans st (cong (λ d → next (I.eval d _ _)) (lookup-map lift ds g))))
         (plus-star π (cong (λ d → next (C.eval d _ _)) (lookup-map ⌜_⌝ ds g) ◅ ε)) (eval~ k)

  choose : ∀ {Δ A' B'} (v : C.Val Σ (A' ⊹ B')) {e₁ : M.Exp Σ (A' ∷ Δ) A} {e₂ : M.Exp Σ (B' ∷ Δ) A} {φ} → κ₂ ≈ κ₁
    → I.step ds₁ s₁ ≡ next (C.choose v (λ u → I.eval (lift e₁) (u ∷ φ) κ₁) (λ u → I.eval (lift e₂) (u ∷ φ) κ₁))
    → Star L₂ s₂ t → C.step ds₂ t ≡ next (C.choose v (λ u → C.eval ⌜ e₁ ⌝ (u ∷ φ) κ₂) (λ u → C.eval ⌜ e₂ ⌝ (u ∷ φ) κ₂))
    → 𝔅 s₁ s₂
  choose (C.inl u) k st σ st₂ = move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ k)
  choose (C.inr u) k st σ st₂ = move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ k)

  sim : s₂ ~ s₁ → 𝔅 s₁ s₂
  sim (eval~ {e = atm a} k) = val refl k (step⁺ (at a))
  sim (eval~ {e = pack a b} k) = val refl k (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {e = callc f a} k) = call _ _ refl k (plus refl (at f ◅ refl ◅ at a ◅ ε))
  sim (eval~ {e = tuple as} k) = val refl k (plus refl (tuple-atoms ds₂ ⌜ e₀ ⌝ [] as))
  sim (eval~ {e = get i a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inl a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inr a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = case a e₁ e₂} {φ = φ} k) = choose (I.atom φ a) {e₁} {e₂} {φ} k refl (refl ◅ at a ◅ ε) refl
  sim (eval~ {e = prim p a b} k) = val refl k (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {e = let′ e₁ e₂} k) = move (step⁺ refl) (step⁺ refl) (eval~ (assignK k))
  sim (eval~ {e = fold a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = unfold a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))

{- The end theorem -------------------------------------------------------------}

lift-locals-correct : ∀ {A} (P : M.Program A) → Equivalent (C.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (M.program ds e) = equiv-sym (equivalent (both-fsim (flip _~_) (eval~ halt) sim))
  where open Sim ds e
