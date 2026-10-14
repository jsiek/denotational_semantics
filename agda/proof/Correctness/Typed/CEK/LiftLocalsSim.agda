{-

  Correctness of typed lift locals (Monᵀ → Impᵀ,
  Compiler/Typed/LiftLocals.agda): the Impᵀ machine on lift-program P
  and the Clos5ᵀ machine on the embedding ⌜ P ⌝ₚ (the meaning of a Monᵀ
  program) are Equivalent.

  The pass is structural, and the frame of the Impᵀ machine is the
  environment of the Clos5ᵀ machine, so the two run on the same values
  and frames. The Impᵀ machine is simulated by the Clos5ᵀ one (Both,
  proof/Framework/Both.agda): one Impᵀ step runs a simple expression
  on its atoms, which the Clos5ᵀ machine evaluates one by one, through
  continuation frames, in a few steps (atm-step); then both continue
  with related continuations (x := □; e₂ and let □ in e₂), or both stop
  with the same observation (the end, or a failed project).

-}

module proof.Correctness.Typed.CEK.LiftLocalsSim where

open import Language.Typed.Type
import Language.Typed.Mon as M
open M using (atm; pack; callc; tuple; get; inl; inr; case; prim; let′; inject; project; ⌜_⌝; ⌜_⌝ₚ)
open import Language.Typed.Imp using (Program)
open import Compiler.Typed.LiftLocals using (lift; lift-program)
open import proof.Framework.Membership using (map-!)
open import Semantics.Observation using (Obs; o-error)
open import proof.Semantics.CEK.Smallstep using (Machine; Next; next; stop; next?; Star; ε; _◅_; Plus; plus; plus-star; star-plus; step⁺; plus→star)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent; equiv-sym)
open import proof.Framework.Both Obs using (Both; halt; move; ends; both-fsim)
open import proof.Correctness.Typed.CEK.Clos5Common using (atm-step; tuple-atoms; collected-push)
import Semantics.CEK.Typed.Clos5 as C
import Semantics.CEK.Typed.Imp as I

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

module Sim {Σ : List ℕ} (ds : All (λ n → M.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) (e₀ : M.Exp Σ [] Any) where

  ds₁ = All-map lift ds
  ds₂ = All-map ⌜_⌝ ds
  L₁ = I.sem (lift-program (M.program ds e₀))
  L₂ = C.sem ⌜ M.program ds e₀ ⌝ₚ

  at = atm-step ds₂ ⌜ e₀ ⌝

  infix 4 _≈_ _~_
  data _≈_ : ∀ {A} → I.Cont Σ A → C.Cont Σ A → Set where
    halt : I.halt ≈ C.halt
    assignK : ∀ {Δ A B} {e : M.Exp Σ (A ∷ Δ) B} {φ κ₁ κ₂} → κ₁ ≈ κ₂ → I.assignK (lift e) φ κ₁ ≈ C.letK ⌜ e ⌝ φ κ₂

  data _~_ : I.State Σ → C.State Σ → Set where
    eval~ : ∀ {Δ A} {e : M.Exp Σ Δ A} {φ κ₁ κ₂} → κ₁ ≈ κ₂ → I.eval (lift e) φ κ₁ ~ C.eval ⌜ e ⌝ φ κ₂

  B = Both {L₁ = L₁} {L₂ = L₂} _~_

  private variable
    A : Ty
    s₁ : I.State Σ
    s₂ t : C.State Σ
    κ₁ : I.Cont Σ A
    κ₂ : C.Cont Σ A

  {- a value goes to related continuations -}
  val : ∀ {v : C.Val Σ A} → I.step ds₁ s₁ ≡ I.cont ds₁ v κ₁ → κ₁ ≈ κ₂ → Plus L₂ s₂ (C.ret v κ₂) → B s₁ s₂
  val st halt π = halt st (plus→star π) refl
  val st (assignK k) π = move (step⁺ st) (plus-star π (refl ◅ ε)) (eval~ k)

  call : ∀ f w → I.step ds₁ s₁ ≡ I.res ds₁ (I.call f w) κ₁ → κ₁ ≈ κ₂ → Plus L₂ s₂ (C.ret w (C.callR f κ₂))
    → B s₁ s₂
  call (C.pack (C.code g) e) w st k π =
    move (step⁺ (trans st (cong (λ d → next (I.eval d _ _)) (map-! lift ds g))))
         (plus-star π (cong (λ d → next (C.eval d _ _)) (map-! ⌜_⌝ ds g) ◅ ε)) (eval~ k)

  proj : ∀ {t' : Tag} (m : Maybe (C.Val Σ ⟪ flat t' ⟫)) {κ₁ : I.Cont Σ ⟪ flat t' ⟫} {κ₂ : C.Cont Σ ⟪ flat t' ⟫} → I.step ds₁ s₁ ≡ I.res ds₁ (I.ok? m) κ₁ → κ₁ ≈ κ₂
    → Star L₂ s₂ t → C.step ds₂ t ≡ next? o-error (λ w → C.ret w κ₂) m → B s₁ s₂
  proj (just w) st k σ st₂ = val st k (star-plus σ (step⁺ st₂))
  proj nothing st k σ st₂ = halt st σ st₂

  choose : ∀ {Δ} (v : C.Val Σ ⟪ sum ⟫) {e₁ e₂ : M.Exp Σ (Any ∷ Δ) Any} {φ} → κ₁ ≈ κ₂
    → I.step ds₁ s₁ ≡ next (C.choose v (λ u → I.eval (lift e₁) (u ∷ φ) κ₁) (λ u → I.eval (lift e₂) (u ∷ φ) κ₁))
    → Star L₂ s₂ t → C.step ds₂ t ≡ next (C.choose v (λ u → C.eval ⌜ e₁ ⌝ (u ∷ φ) κ₂) (λ u → C.eval ⌜ e₂ ⌝ (u ∷ φ) κ₂))
    → B s₁ s₂
  choose (C.inl u) k st σ st₂ = move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ k)
  choose (C.inr u) k st σ st₂ = move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ k)

  sim : s₁ ~ s₂ → B s₁ s₂
  sim (eval~ {e = atm a} k) = val refl k (step⁺ (at a))
  sim (eval~ {e = pack a b} k) = val refl k (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {e = callc f a} k) = call _ _ refl k (plus refl (at f ◅ refl ◅ at a ◅ ε))
  sim (eval~ {e = tuple as} {φ = φ} k) with tuple-atoms ds₂ ⌜ e₀ ⌝ [] as refl
  ... | e' , σ = val refl k (subst (λ V → Plus L₂ (C.eval ⌜ tuple as ⌝ φ _) (C.ret (C.tup V) _)) (collected-push φ as e') (plus refl σ))
  sim (eval~ {e = get i a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inl a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inr a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = case a e₁ e₂} {φ = φ} k) = choose (I.atom φ a) {e₁} {e₂} {φ} k refl (refl ◅ at a ◅ ε) refl
  sim (eval~ {e = prim p a b} k) = val refl k (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {e = let′ e₁ e₂} k) = move (step⁺ refl) (step⁺ refl) (eval~ (assignK k))
  sim (eval~ {e = inject G a} k) = val refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = project t' a} k) = proj _ refl k (refl ◅ at a ◅ ε) refl

{- The end theorem -------------------------------------------------------------}

lift-locals-correct : ∀ (P : M.Program) → Equivalent (C.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (M.program ds e) = equiv-sym (equivalent (both-fsim _~_ (eval~ halt) sim))
  where open Sim ds e
