{-

  Correctness of lift locals (Monμ → Impμ, FPC/Compiler/LiftLocals.agda):
  the Impμ machine on lift-program P and the GlobalFunμ machine on the
  embedding ⌜ P ⌝ₚ (the meaning of a Monμ program) are Equivalent, as
  for typed lift locals (ISWIM/proof/Correctness/CEK/LiftLocalsSim.agda).

  The pass is structural, and the two machines run on the same values.
  The frame of the Impμ machine holds, in the slot ρ x of each variable
  x in scope, the value of x in the environment of the GlobalFunμ
  machine (Rel). A let or a case writes a slot that is not initialized,
  while the slots of the variables in scope are, so the write keeps the
  values of those variables (rel-ext, by read-write-other); an atom
  therefore has the same value in both machines (atom-rel). A call
  starts in a frame of the argument and environment (params-arg,
  params-env).

  The Impμ machine is simulated by the GlobalFunμ one (Both,
  proof/Framework/Both.agda): one Impμ step runs a simple expression on
  its atoms, which the GlobalFunμ machine evaluates one by one, through
  continuation frames, in a few steps (atm-step); then both continue
  with related continuations (x := □; e₂ and let □ in e₂), or both stop
  with the same observation (the end).

-}

module FPC.proof.Correctness.AbstractMachines.LiftLocalsSim where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; ⊑-∋)
import FPC.Language.Mon as M
open M using (DSig; Args; atm; pair; callc; tuple; get; inl; inr; case; prim;
  let′; fold; unfold; ⌜_⌝; ⌜_⌝ₚ)
open import FPC.Language.Imp using (Inits; _∈_; _∉_; _⊕_)
import FPC.Compiler.LiftLocals as LL
open LL using (lift; lift-body; lift-program; binds; Inited; ext)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Framework.Slots using (read; write; params; empty)
open import FPC.proof.Framework.AllProp using (lookup-map)
open import FPC.proof.Framework.SlotsProp using (read-write; read-write-other;
  params-arg; params-env)
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_; Plus; plus;
  plus-star; star-plus; step⁺; plus→star)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent;
  equiv-sym)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
open import FPC.proof.Correctness.AbstractMachines.GlobalFunCommon using
  (atom; atm-step; tuple-atoms)
import FPC.Semantics.AbstractMachines.GlobalFun as C
import FPC.Semantics.AbstractMachines.Imp as I

open import Data.List using (List; []; _∷_)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; cong₂)

{- The frame and the environment ---------------------------------------------}

{- the slot ρ x of the frame φ holds the value of x in γ -}
record Rel {Σ Γ Δ} {I : Inits Δ} (ρ : LL.Slots Γ Δ) (γ : C.Env Σ Γ)
  (φ : I.Frame Σ Δ I) : Set where
  constructor rel
  field
    holds : ∀ {B} (x : Γ ∋ B) .(i : ρ x ∈ I) → read φ (ρ x) i ≡ lookup γ x
open Rel

{- a write to a slot that is not initialized, for the bound variable -}
rel-ext : ∀ {Σ Γ Δ A} {I : Inits Δ} {ρ : LL.Slots Γ Δ} {γ : C.Env Σ Γ}
  {φ : I.Frame Σ Δ I} (x : Δ ∋ A) (v : C.Val Σ A)
  → .(Inited ρ I)
  → .(x ∉ I)
  → Rel ρ γ φ
  → Rel (ext x ρ) (v ∷ γ) (write φ x v)
rel-ext {ρ = ρ} {φ = φ} x v ok xn r = rel λ
  { Z i → read-write φ x v i
  ; (S y) i →
      trans (read-write-other φ x v (ρ y) (ok y) xn i) (holds r y (ok y)) }

atom-rel : ∀ {Σ Γ Δ A} {I : Inits Δ} {ρ : LL.Slots Γ Δ} {γ : C.Env Σ Γ}
  {φ : I.Frame Σ Δ I} .(ok : Inited ρ I)
  → Rel ρ γ φ
  → (a : M.Atm Σ Γ A)
  → I.atom φ (LL.atom ρ ok a) ≡ atom γ a
atom-rel ok r (M.var x) = holds r x (ok x)
atom-rel ok r (M.lit B c) = refl
atom-rel ok r (M.ref f) = refl

atoms-rel : ∀ {Σ Γ Δ Δs} {I : Inits Δ} {ρ : LL.Slots Γ Δ} {γ : C.Env Σ Γ}
  {φ : I.Frame Σ Δ I} .(ok : Inited ρ I)
  → Rel ρ γ φ
  → (as : All (M.Atm Σ Γ) Δs)
  → map (I.atom φ) (LL.atoms ρ ok as) ≡ map (atom γ) as
atoms-rel ok r [] = refl
atoms-rel ok r (a ∷ as) = cong₂ _∷_ (atom-rel ok r a) (atoms-rel ok r as)

{- the start of a body: its argument and environment, in their slots -}
rel-params : ∀ {Σ Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) (e : C.Val Σ B)
  (w : C.Val Σ A)
  → Rel (⊑-∋ p) (w ∷ e ∷ []) (params p e w)
rel-params p e w = rel λ
  { Z i → params-arg p e w i
  ; (S Z) i → params-env p e w i }

{- The simulation, for a program with definitions ds and main e₀ -------------}

module Sim {Σ : List DSig} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) Σ)
  {T} (e₀ : M.Exp Σ [] T) where

  ds₁ = map lift-body ds
  ds₂ = map ⌜_⌝ ds
  L₁ = I.sem (lift-program (M.program ds e₀))
  L₂ = C.sem ⌜ M.program ds e₀ ⌝ₚ

  at = atm-step ds₂ ⌜ e₀ ⌝

  infix 4 _≈_ _~_
  {- the source's (GlobalFunμ) on the left, the target's (Impμ) on the right -}
  data _≈_ : ∀ {A} → C.Cont Σ A → I.Cont Σ A → Set where
    halt : ∀ {A} → C.halt {A = A} ≈ I.halt
    assignK : ∀ {Γ Δ D A B} {I : Inits Δ} {e : M.Exp Σ (A ∷ Γ) B}
      {q : binds e D ⊑ Δ} {x : Δ ∋ A} {ρ : LL.Slots Γ Δ}
      .{ok : Inited (ext x ρ) (I ⊕ x)} .{o} {γ} {φ : I.Frame Σ Δ I} {κ₁ κ₂}
      → .(Inited ρ I)
      → .(x ∉ I)
      → Rel ρ γ φ
      → κ₂ ≈ κ₁
      → C.letK ⌜ e ⌝ γ κ₂ ≈ I.assignK x φ (lift e q (ext x ρ) ok o) κ₁

  data _~_ : C.State Σ → I.State Σ → Set where
    eval~ : ∀ {Γ Δ D A} {I : Inits Δ} {e : M.Exp Σ Γ A} {q : binds e D ⊑ Δ}
      {ρ : LL.Slots Γ Δ} .{ok : Inited ρ I} .{o} {γ} {φ : I.Frame Σ Δ I}
      {κ₁ κ₂}
      → Rel ρ γ φ
      → κ₂ ≈ κ₁
      → C.eval ⌜ e ⌝ γ κ₂ ~ I.eval (lift e q ρ ok o) φ κ₁

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
  val : ∀ {v₁ v : C.Val Σ A}
    → v₁ ≡ v
    → I.step ds₁ s₁ ≡ I.cont ds₁ v₁ κ₁
    → κ₂ ≈ κ₁
    → Plus L₂ s₂ (C.ret v κ₂)
    → 𝔅 s₁ s₂
  val refl st halt π = halt st (plus→star π) refl
  val {v₁ = v} refl st (assignK {x = x} ok xn r k) π =
    move (step⁺ st) (plus-star π (refl ◅ ε)) (eval~ (rel-ext x v ok xn r) k)

  call : ∀ {A'} {f₁ : C.Val Σ (A' ⇒ A)} {w₁} (f : C.Val Σ (A' ⇒ A)) w
    → f₁ ≡ f
    → w₁ ≡ w
    → I.step ds₁ s₁ ≡ I.res ds₁ (I.call f₁ w₁) κ₁
    → κ₂ ≈ κ₁
    → Plus L₂ s₂ (C.ret w (C.callR f κ₂))
    → 𝔅 s₁ s₂
  call {κ₁ = κ₁} (C.pack (C.code g) e) w refl refl st k π =
    move
      (step⁺
        (trans st
          (cong (λ d → next (I.enter ds₁ d e w κ₁))
            (lookup-map lift-body ds g))))
      (plus-star π
        (cong (λ d → next (C.eval d _ _)) (lookup-map ⌜_⌝ ds g) ◅ ε))
      (eval~ (rel-params _ e w) k)

  choose : ∀ {Γ Δ A' B'} {I : Inits Δ} {v₁ : C.Val Σ (A' ⊹ B')}
    (v : C.Val Σ (A' ⊹ B')) {e₁ : M.Exp Σ (A' ∷ Γ) A} {e₂ : M.Exp Σ (B' ∷ Γ) A}
    {x y} {ρ : LL.Slots Γ Δ} {D₁ D₂} {q₁ : binds e₁ D₁ ⊑ Δ}
    {q₂ : binds e₂ D₂ ⊑ Δ}
    .{ok₁ : Inited (ext x ρ) (I ⊕ x)} .{ok₂ : Inited (ext y ρ) (I ⊕ y)}
    .{o₁ o₂} {γ} {φ : I.Frame Σ Δ I}
    → v₁ ≡ v
    → .(Inited ρ I)
    → .(x ∉ I)
    → .(y ∉ I)
    → Rel ρ γ φ
    → κ₂ ≈ κ₁
    → I.step ds₁ s₁
      ≡ next
      (C.choose v₁ (λ u → I.eval (lift e₁ q₁ (ext x ρ) ok₁ o₁) (write φ x u) κ₁)
        (λ u → I.eval (lift e₂ q₂ (ext y ρ) ok₂ o₂) (write φ y u) κ₁))
    → Star L₂ s₂ t
    → C.step ds₂ t
      ≡ next
      (C.choose v (λ u → C.eval ⌜ e₁ ⌝ (u ∷ γ) κ₂)
        (λ u → C.eval ⌜ e₂ ⌝ (u ∷ γ) κ₂))
    → 𝔅 s₁ s₂
  choose (C.inl u) {x = x} refl ok xn yn r k st σ st₂ =
    move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ (rel-ext x u ok xn r) k)
  choose (C.inr u) {y = y} refl ok xn yn r k st σ st₂ =
    move (step⁺ st) (star-plus σ (step⁺ st₂)) (eval~ (rel-ext y u ok yn r) k)

  sim : s₂ ~ s₁
    → 𝔅 s₁ s₂
  sim (eval~ {e = atm a} {ok = ok} r k) =
    val (atom-rel ok r a) refl k (step⁺ (at a))
  sim (eval~ {e = pair a b} {ok = ok} r k) =
    val (cong₂ C.pack (atom-rel ok r a) (atom-rel ok r b)) refl k
      (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {e = callc f a} {ok = ok} r k) =
    call _ _ (atom-rel ok r f) (atom-rel ok r a) refl k
      (plus refl (at f ◅ refl ◅ at a ◅ ε))
  sim (eval~ {e = tuple as} {ok = ok} r k) =
    val (cong C.tup (atoms-rel ok r as)) refl k
      (plus refl (tuple-atoms ds₂ ⌜ e₀ ⌝ [] as))
  sim (eval~ {e = get i a} {ok = ok} r k) =
    val (cong (λ u → lookup (C.elems u) i) (atom-rel ok r a)) refl k
      (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inl a} {ok = ok} r k) =
    val (cong C.inl (atom-rel ok r a)) refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = inr a} {ok = ok} r k) =
    val (cong C.inr (atom-rel ok r a)) refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {I = I} {e = case a e₁ e₂} {q = q} {ok = ok} {o} {φ = φ} r k) =
    choose (atom _ a) (atom-rel ok r a) ok (fresh₁ o) (fresh₂ o) r k refl
      (refl ◅ at a ◅ ε) refl
    where open LL.Case {I = I} a e₁ e₂ q
  sim (eval~ {e = prim p a b} {ok = ok} r k) =
    val
      (cong₂ (λ u w → C.δᵀ p (C.int u) (C.int w)) (atom-rel ok r a)
        (atom-rel ok r b)) refl k
      (plus refl (at a ◅ refl ◅ at b ◅ refl ◅ ε))
  sim (eval~ {I = I} {e = let′ e₁ e₂} {q = q} {ok = ok} {o} r k) =
    move (step⁺ refl) (step⁺ refl) (eval~ r (assignK ok (fresh o) r k))
    where open LL.Let {I = I} e₁ e₂ q
  sim (eval~ {e = fold a} {ok = ok} r k) =
    val (cong C.fold (atom-rel ok r a)) refl k (plus refl (at a ◅ refl ◅ ε))
  sim (eval~ {e = unfold a} {ok = ok} r k) =
    val (cong C.unfoldᵥ (atom-rel ok r a)) refl k
      (plus refl (at a ◅ refl ◅ ε))

{- The end theorem ------------------------------------------------------------}

lift-locals-correct : ∀ {A} (P : M.Program A)
  → Equivalent (C.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (M.program ds e) =
  equiv-sym (equivalent (both-fsim (flip _~_) (eval~ (rel λ ()) halt) sim))
  where open Sim ds e
