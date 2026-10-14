{-

  Correctness of typed lift locals (Monᵀ → Impᵀ) by a forward simulation
  of the Clos5ᵀ reduction semantics of the Monᵀ program (its embedding,
  ⌜_⌝ₚ) by the Impᵀ machine (Semantics/CEK/Typed/Imp.agda).

  A machine state decodes to a term (D): its expression, with the values
  of its frame substituted for the slots (env), in the stack of lets of
  its continuation (plug). The source is that term, or one step before
  it (Lag): a simple expression that computes a value (a component, a
  primitive, a project) does so in the step that hands the value to the
  continuation, so a state whose expression is one decodes to its value,
  which the source reaches in one step (catch). The target also enters a
  let in a step of its own, which decodes to the same term.

-}

module proof.Correctness.Typed.Reduction.LiftLocalsRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Framework.Lookup using (_!_)
open import proof.Framework.Lookup using (map-!)
import Language.Typed.Clos5 as C
open C using (Tm; Code)
import Language.Typed.Mon as Mon
open Mon using (Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ₚ)
open import Language.Typed.Imp
open import Compiler.Typed.LiftLocals using (lift; lift-program)
open import Semantics.Observation
open import Framework.Smallstep Obs using (Machine; Next; next; stop; Step; Steps; zero; suc; ε; _◅_)
open import proof.Framework.Smallstep Obs using (plus; step⁺)
open import proof.Framework.Simulation Obs using (Answers≺; stops; steps; stutters; runs; Lag; lag; lag-fsim; equivalent; answers-at)
open import proof.Framework.Reduction Obs o-error using (Red; val; error; to; step-in; toNext; Frame; frame; frame-id; frame-∘; val-in; step-in-to; error-in)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.Clos5 as T
open T using (Value; value-red; sub; exts; tmK; _•_; ∅; _[_])
import Semantics.CEK.Typed.Imp as I
import Semantics.CEK.Typed.Clos5 as C5ₘ
open I using (Val; code; pack; const; tup; inl; inr; dyn; Env; Res; value; fail; call; Cont; halt; assignK; State; eval)
import Language.Prim as P
import Data.Fin as Fin

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
import Data.Vec as V
open import Data.Vec.Relation.Unary.All using () renaming (All to Allᵥ; [] to []ᵥ; _∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)
open import Data.Empty using (⊥-elim)

module _ {Σ : List ℕ} where

  {- Decoding -----------------------------------------------------------------------}

  {- a machine value as a value term -}
  ⌞_⌟ : ∀ {A} → Val Σ A → Tm Σ [] A
  ⌞_⌟ᵛ : ∀ {n} → Vec (Val Σ Any) n → Vec (Tm Σ [] Any) n
  ⌞ code f ⌟ = C.fun-ref f
  ⌞ pack v w ⌟ = C.pack ⌞ v ⌟ ⌞ w ⌟
  ⌞ const {B} c ⌟ = C.lit B c
  ⌞ tup vs ⌟ = C.tuple ⌞ vs ⌟ᵛ
  ⌞ inl v ⌟ = C.inl ⌞ v ⌟
  ⌞ inr v ⌟ = C.inr ⌞ v ⌟
  ⌞ dyn G v ⌟ = C.inject G ⌞ v ⌟
  ⌞ [] ⌟ᵛ = []
  ⌞ v ∷ vs ⌟ᵛ = ⌞ v ⌟ ∷ ⌞ vs ⌟ᵛ

  value-⌞⌟ : ∀ {A} (v : Val Σ A) → Value ⌞ v ⌟
  values-⌞⌟ : ∀ {n} (vs : Vec (Val Σ Any) n) → Allᵥ Value ⌞ vs ⌟ᵛ
  value-⌞⌟ (code f) = T.fun-ref
  value-⌞⌟ (pack v w) = T.pack (value-⌞⌟ v) (value-⌞⌟ w)
  value-⌞⌟ (const c) = T.lit
  value-⌞⌟ (tup vs) = T.tuple (values-⌞⌟ vs)
  value-⌞⌟ (inl v) = T.inl (value-⌞⌟ v)
  value-⌞⌟ (inr v) = T.inr (value-⌞⌟ v)
  value-⌞⌟ (dyn G v) = T.inject (value-⌞⌟ v)
  values-⌞⌟ [] = []ᵥ
  values-⌞⌟ (v ∷ vs) = value-⌞⌟ v ∷ᵥ values-⌞⌟ vs

  obs-⌞⌟ : (v : Val Σ Any) → T.obs ⌞ v ⌟ ≡ I.obs v
  obsG-⌞⌟ : ∀ {G} (v : Val Σ ⟪ G ⟫) → T.obs ⌞ v ⌟ ≡ I.obs v
  obss-⌞⌟ : ∀ {n} (vs : Vec (Val Σ Any) n) → T.obss ⌞ vs ⌟ᵛ ≡ C5ₘ.obs-vec vs
  obs-⌞⌟ (dyn G v) = obsG-⌞⌟ v
  obsG-⌞⌟ (pack v w) = refl
  obsG-⌞⌟ (const c) = refl
  obsG-⌞⌟ (tup vs) = cong o-tuple (obss-⌞⌟ vs)
  obsG-⌞⌟ (inl v) = cong o-inl (obs-⌞⌟ v)
  obsG-⌞⌟ (inr v) = cong o-inr (obs-⌞⌟ v)
  obss-⌞⌟ [] = refl
  obss-⌞⌟ (v ∷ vs) = cong₂ _∷_ (obs-⌞⌟ v) (obss-⌞⌟ vs)

  {- a frame as a closing substitution -}
  env : ∀ {Δ} → Env Σ Δ → ∀ {B} → Δ ∋ B → Tm Σ [] B
  env [] = ∅
  env (v ∷ φ) = ⌞ v ⌟ • env φ

  env-! : ∀ {Δ B} (φ : Env Σ Δ) (x : Δ ∋ B) → env φ x ≡ ⌞ φ ! x ⌟
  env-! (v ∷ φ) Z = refl
  env-! (v ∷ φ) (S x) = env-! φ x

  {- Impᵀ in Clos5ᵀ -}
  ⌜_⌝ˢ : ∀ {Δ A} → Simple Σ Δ A → Tm Σ Δ A
  ⌜ atm a ⌝ˢ = ⌜ a ⌝ᵃ
  ⌜ pack a b ⌝ˢ = C.pack ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
  ⌜ callc a b ⌝ˢ = C.callc ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
  ⌜ tuple as ⌝ˢ = C.tuple Mon.⌜ as ⌝ᵛ
  ⌜ get i a ⌝ˢ = C.get i ⌜ a ⌝ᵃ
  ⌜ inl a ⌝ˢ = C.inl ⌜ a ⌝ᵃ
  ⌜ inr a ⌝ˢ = C.inr ⌜ a ⌝ᵃ
  ⌜ prim p a b ⌝ˢ = C.prim p ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
  ⌜ inject G a ⌝ˢ = C.inject G ⌜ a ⌝ᵃ
  ⌜ project t a ⌝ˢ = C.project t ⌜ a ⌝ᵃ

  ⌜_⌝ⁱ : ∀ {Δ A} → Exp Σ Δ A → Tm Σ Δ A
  ⌜ simple s ⌝ⁱ = ⌜ s ⌝ˢ
  ⌜ assign e₁ e₂ ⌝ⁱ = C.let′ ⌜ e₁ ⌝ⁱ ⌜ e₂ ⌝ⁱ
  ⌜ case a e₁ e₂ ⌝ⁱ = C.case ⌜ a ⌝ᵃ ⌜ e₁ ⌝ⁱ ⌜ e₂ ⌝ⁱ

  ⌜lift⌝ : ∀ {Δ A} (e : Mon.Exp Σ Δ A) → ⌜ lift e ⌝ⁱ ≡ Mon.⌜ e ⌝
  ⌜lift⌝ (Mon.atm a) = refl
  ⌜lift⌝ (Mon.pack a b) = refl
  ⌜lift⌝ (Mon.callc a b) = refl
  ⌜lift⌝ (Mon.tuple as) = refl
  ⌜lift⌝ (Mon.get i a) = refl
  ⌜lift⌝ (Mon.inl a) = refl
  ⌜lift⌝ (Mon.inr a) = refl
  ⌜lift⌝ (Mon.case a e₁ e₂) = cong₂ (C.case ⌜ a ⌝ᵃ) (⌜lift⌝ e₁) (⌜lift⌝ e₂)
  ⌜lift⌝ (Mon.prim p a b) = refl
  ⌜lift⌝ (Mon.let′ e₁ e₂) = cong₂ C.let′ (⌜lift⌝ e₁) (⌜lift⌝ e₂)
  ⌜lift⌝ (Mon.inject G a) = refl
  ⌜lift⌝ (Mon.project t a) = refl

  {- an atom, and atoms -}
  atom-⌞⌟ : ∀ {Δ A} (φ : Env Σ Δ) (a : Atm Σ Δ A) → sub (env φ) ⌜ a ⌝ᵃ ≡ ⌞ I.atom φ a ⌟
  atom-⌞⌟ φ (var x) = env-! φ x
  atom-⌞⌟ φ (lit B c) = refl
  atom-⌞⌟ φ (ref f) = refl

  atoms-⌞⌟ : ∀ {Δ n} (φ : Env Σ Δ) (as : Vec (Atm Σ Δ Any) n) → T.travs tmK (env φ) Mon.⌜ as ⌝ᵛ ≡ ⌞ V.map (I.atom φ) as ⌟ᵛ
  atoms-⌞⌟ φ [] = refl
  atoms-⌞⌟ φ (a ∷ as) = cong₂ _∷_ (atom-⌞⌟ φ a) (atoms-⌞⌟ φ as)

  lookup-⌞⌟ : ∀ {n} (vs : Vec (Val Σ Any) n) i → lookup ⌞ vs ⌟ᵛ i ≡ ⌞ lookup vs i ⌟
  lookup-⌞⌟ (v ∷ vs) Fin.zero = refl
  lookup-⌞⌟ (v ∷ vs) (Fin.suc i) = lookup-⌞⌟ vs i

  out-⌞⌟ : ∀ p n m → T.out {Σ} {[]} p n m ≡ ⌞ I.δᵀ p n m ⌟
  out-⌞⌟ P.sub n m = refl
  out-⌞⌟ P.eq n m with does (n Z.≟ m)
  ... | true = refl
  ... | false = refl

  {- The machine ---------------------------------------------------------------------------}

  module _ (ds : All (λ n → Mon.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) (e₀ : Mon.Exp Σ [] Any) where

    ds₁ : All (Code Σ) Σ
    ds₁ = All-map Mon.⌜_⌝ ds

    ds₂ : All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ
    ds₂ = All-map lift ds

    red₁ = T.red ds₁

    {- what a simple expression does, in both -}
    data SV {Δ} (φ : Env Σ Δ) : ∀ {A} → Simple Σ Δ A → Res A → Set where
      val0 : ∀ {A} {s : Simple Σ Δ A} {v} → sub (env φ) ⌜ s ⌝ˢ ≡ ⌞ v ⌟ → SV φ s (value v)
      val1 : ∀ {A} {s : Simple Σ Δ A} {v} → red₁ (sub (env φ) ⌜ s ⌝ˢ) ≡ to ⌞ v ⌟ → SV φ s (value v)
      err : ∀ {A} {s : Simple Σ Δ A} → red₁ (sub (env φ) ⌜ s ⌝ˢ) ≡ error → SV φ s fail
      cal : ∀ {s : Simple Σ Δ Any} {n} {f : Σ ∋ n} {e w} → sub (env φ) ⌜ s ⌝ˢ ≡ C.callc (C.pack (C.fun-ref f) ⌞ e ⌟) ⌞ w ⌟
        → SV φ s (call (pack (code f) e) w)

    sv : ∀ {Δ A} (s : Simple Σ Δ A) (φ : Env Σ Δ) → SV φ s (I.run s φ)
    sv (atm a) φ = val0 (atom-⌞⌟ φ a)
    sv (pack a b) φ = val0 (cong₂ C.pack (atom-⌞⌟ φ a) (atom-⌞⌟ φ b))
    sv (callc a b) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | pack (code f) e | ea = cal (cong₂ C.callc ea (atom-⌞⌟ φ b))
    sv (tuple as) φ = val0 (cong C.tuple (atoms-⌞⌟ φ as))
    sv (get i a) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | tup vs | ea = val1 (trans (cong (λ X → red₁ (C.get i X)) ea)
                               (trans (val-in (value-red (T.tuple (values-⌞⌟ vs)))) (cong to (lookup-⌞⌟ vs i))))
    sv (inl a) φ = val0 (cong C.inl (atom-⌞⌟ φ a))
    sv (inr a) φ = val0 (cong C.inr (atom-⌞⌟ φ a))
    sv (prim p a b) φ with I.atom φ a | atom-⌞⌟ φ a | I.atom φ b | atom-⌞⌟ φ b
    ... | const n | ea | const m | eb = val1 (trans (cong₂ (λ X Y → red₁ (C.prim p X Y)) ea eb) (cong to (out-⌞⌟ p n m)))
    sv (inject G a) φ = val0 (cong (C.inject G) (atom-⌞⌟ φ a))
    sv (project t a) φ with I.atom φ a | atom-⌞⌟ φ a
    ... | dyn H v | ea with H ≟F flat t
    ...   | yes refl = val1 (trans (cong (λ X → red₁ (C.project t X)) ea) (trans (val-in (value-red (T.inject (value-⌞⌟ v)))) (pd-yes (flat t ≟F flat t))))
      where pd-yes : (d : Dec (flat t ≡ flat t)) → T.proj-dec d ⌞ v ⌟ ≡ to ⌞ v ⌟
            pd-yes (yes refl) = refl
            pd-yes (no ne) = ⊥-elim (ne refl)
    ...   | no ne = err (trans (cong (λ X → red₁ (C.project t X)) ea) (trans (val-in (value-red (T.inject (value-⌞⌟ v)))) (pd-no (H ≟F flat t))))
      where pd-no : (d : Dec (H ≡ flat t)) → T.proj-dec d ⌞ v ⌟ ≡ error
            pd-no (yes e) = ⊥-elim (ne e)
            pd-no (no _) = refl

    {- the stack of lets of a continuation -}
    plug : ∀ {A} → Cont Σ A → Tm Σ [] A → Tm Σ [] Any
    plug halt M = M
    plug (assignK e φ κ) M = plug κ (C.let′ M (sub (exts tmK (env φ)) ⌜ e ⌝ⁱ))

    plug-frame : ∀ {A} (κ : Cont Σ A) → Frame red₁ red₁ (plug κ)
    plug-frame halt = frame-id
    plug-frame (assignK e φ κ) = frame-∘ (frame _ λ _ → refl) (plug-frame κ)

    {- the decoding of a state, and its value or result when it is a simple expression -}
    Dsyn : State Σ → Tm Σ [] Any
    Dsyn (eval e φ κ) = plug κ (sub (env φ) ⌜ e ⌝ⁱ)

    res-tm : ∀ {A} → Res A → Tm Σ [] A → Tm Σ [] A
    res-tm (value v) X = ⌞ v ⌟
    res-tm fail X = X
    res-tm (call f w) X = X

    D : State Σ → Tm Σ [] Any
    D (eval (simple s) φ κ) = plug κ (res-tm (I.run s φ) (sub (env φ) ⌜ s ⌝ˢ))
    D s = Dsyn s

    L₁ L₂ : Machine
    L₁ = T.sem (C.program ds₁ Mon.⌜ e₀ ⌝)
    L₂ = I.sem (program ds₂ (lift e₀))

    {- the source reaches the decoding in at most one step -}
    catch : ∀ s → (D s ≡ Dsyn s) ⊎ Step L₁ (Dsyn s) (D s)
    catch (eval (simple s) φ κ) with I.run s φ | sv s φ
    ... | value v | val0 e = inj₁ (cong (plug κ) (sym e))
    ... | value v | val1 e = inj₂ (cong (toNext _) (step-in-to (plug-frame κ) e))
    ... | fail | err e = inj₁ refl
    ... | call _ _ | cal e = inj₁ refl
    catch (eval (assign e₁ e₂) φ κ) = inj₁ refl
    catch (eval (case a e₁ e₂) φ κ) = inj₁ refl

    R : Tm Σ [] Any → State Σ → Set
    R M s = M ≡ D s

    lag-of : ∀ s → Σ[ i ∈ ℕ ] Lag L₁ R i (Dsyn s) s
    lag-of s with catch s
    ... | inj₁ e = 0 , lag zero (sym e)
    ... | inj₂ st = 1 , lag (suc st zero) refl

    {- a target step before an answer -}
    pre : ∀ {i a s s'} → Step L₂ s s' → Answers≺ L₂ (Lag L₁ R) i a s' → Answers≺ L₂ (Lag L₁ R) i a s
    pre st (stops fin) = runs (step⁺ st) fin
    pre st (steps (plus st' σ) m) = steps (plus st (st' ◅ σ)) m
    pre st (stutters _ m) = steps (step⁺ st) m
    pre st (runs (plus st' σ) fin) = runs (plus st (st' ◅ σ)) fin

    Ans : State Σ → Set
    Ans s = ∀ {i} → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ (D s)) s

    {- the source reaches what the target reaches -}
    to-lag : ∀ {i} M {s s'} → Machine.step L₁ M ≡ next (Dsyn s') → Step L₂ s s'
      → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ M) s
    to-lag M e st = answers-at e (steps (step⁺ st) (proj₂ (lag-of _)))

    {- a value to the continuation -}
    value-ans : ∀ {Δ A} (s : Simple Σ Δ A) (φ : Env Σ Δ) (κ : Cont Σ A) (v : Val Σ A) → I.run s φ ≡ value v
      → ∀ {i} → Answers≺ L₂ (Lag L₁ R) i (Machine.step L₁ (plug κ ⌞ v ⌟)) (eval (simple s) φ κ)
    value-ans s φ halt v e =
      answers-at (cong (toNext _) (value-red (value-⌞⌟ v))) (stops (trans (cong (λ r → I.res ds₂ r halt) e) (cong stop (sym (obs-⌞⌟ v)))))
    value-ans s φ (assignK e₂ φ' κ) v e =
      to-lag (plug κ (C.let′ ⌞ v ⌟ (sub (exts tmK (env φ')) ⌜ e₂ ⌝ⁱ))) (cong (toNext _) (step-in-to (plug-frame κ)
                (trans (val-in (value-red (value-⌞⌟ v))) (cong to (T.exts-[] (env φ') ⌞ v ⌟ ⌜ e₂ ⌝ⁱ)))))
        (cong (λ r → I.res ds₂ r (assignK e₂ φ' κ)) e)

    inl-β : ∀ {W M N} → Value W → red₁ (C.case (C.inl W) M N) ≡ to (M [ W ])
    inl-β w = val-in (value-red (T.inl w))
    inr-β : ∀ {W M N} → Value W → red₁ (C.case (C.inr W) M N) ≡ to (N [ W ])
    inr-β w = val-in (value-red (T.inr w))

    sim : ∀ {Δ A} (e : Exp Σ Δ A) (φ : Env Σ Δ) (κ : Cont Σ A) → Ans (eval e φ κ)
    sim (simple s) φ κ with I.run s φ in e | sv s φ
    ... | value v | _ = value-ans s φ κ v e
    ... | fail | err r = answers-at (cong (toNext _) (error-in (plug-frame κ) r)) (stops (cong (λ x → I.res ds₂ x κ) e))
    ... | call (pack (code f) e') w | cal r rewrite r =
      to-lag (plug κ (C.callc (C.pack (C.fun-ref f) ⌞ e' ⌟) ⌞ w ⌟)) (cong (toNext _) (step-in-to (plug-frame κ)
        (trans (val-in (value-red (T.pack T.fun-ref (value-⌞⌟ e')))) (trans (val-in (value-red (value-⌞⌟ w)))
          (cong (λ X → to (sub (env (w ∷ e' ∷ [])) X))
            (trans (map-! Mon.⌜_⌝ ds f) (sym (trans (cong ⌜_⌝ⁱ (map-! lift ds f)) (⌜lift⌝ (ds ! f))))))))))
        (cong (λ x → I.res ds₂ x κ) e)
    sim (assign e₁ e₂) φ κ with catch (eval e₁ φ (assignK e₂ φ κ))
    ... | inj₁ eq = pre refl (subst (λ X → Answers≺ L₂ (Lag L₁ R) _ (Machine.step L₁ X) _) eq (sim e₁ φ (assignK e₂ φ κ)))
    ... | inj₂ st = answers-at st (steps (step⁺ refl) (lag zero refl))
    sim (case a e₁ e₂) φ κ with I.atom φ a in eq | atom-⌞⌟ φ a
    ... | inl w | ea rewrite ea =
      to-lag (plug κ (C.case (C.inl ⌞ w ⌟) (sub (exts tmK (env φ)) ⌜ e₁ ⌝ⁱ) (sub (exts tmK (env φ)) ⌜ e₂ ⌝ⁱ))) (cong (toNext _) (step-in-to (plug-frame κ)
        (trans (inl-β {M = sub (exts tmK (env φ)) ⌜ e₁ ⌝ⁱ} {N = sub (exts tmK (env φ)) ⌜ e₂ ⌝ⁱ} (value-⌞⌟ w)) (cong to (T.exts-[] (env φ) ⌞ w ⌟ ⌜ e₁ ⌝ⁱ))))) (cong (λ x → next (C5ₘ.choose x (λ v → eval e₁ (v ∷ φ) κ) (λ v → eval e₂ (v ∷ φ) κ))) eq)
    ... | inr w | ea rewrite ea =
      to-lag (plug κ (C.case (C.inr ⌞ w ⌟) (sub (exts tmK (env φ)) ⌜ e₁ ⌝ⁱ) (sub (exts tmK (env φ)) ⌜ e₂ ⌝ⁱ))) (cong (toNext _) (step-in-to (plug-frame κ)
        (trans (inr-β {M = sub (exts tmK (env φ)) ⌜ e₁ ⌝ⁱ} {N = sub (exts tmK (env φ)) ⌜ e₂ ⌝ⁱ} (value-⌞⌟ w)) (cong to (T.exts-[] (env φ) ⌞ w ⌟ ⌜ e₂ ⌝ⁱ))))) (cong (λ x → next (C5ₘ.choose x (λ v → eval e₁ (v ∷ φ) κ) (λ v → eval e₂ (v ∷ φ) κ))) eq)

    correct : Equivalent L₁ L₂
    correct = equivalent (lag-fsim (subst (λ X → Σ[ i ∈ ℕ ] Lag L₁ R i X (Machine.start L₂)) start-eq (lag-of (Machine.start L₂)))
                                   λ { {s₂ = eval e φ κ} refl → sim e φ κ })
      where start-eq : Dsyn (eval (lift e₀) [] halt) ≡ Mon.⌜ e₀ ⌝
            start-eq = trans (T.sub-id (λ ()) ⌜ lift e₀ ⌝ⁱ) (⌜lift⌝ e₀)

{- The end theorem -------------------------------------------------------------------------------}

lift-locals-correct : ∀ (P : Mon.Program) → Equivalent (T.sem ⌜ P ⌝ₚ) (I.sem (lift-program P))
lift-locals-correct (Mon.program ds e₀) = correct ds e₀
