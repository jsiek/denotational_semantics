{-

  Continuity in the graph model, for any operators: finite
  approximations of an environment, the operands of an operator as
  functions of the environment, what it means for an operator to
  preserve continuity (Continuous), and what a language needs of each
  of its operators (Good: monotone, consistent and continuous); with the
  operators shared by the graph model and the graph model with errors
  (constants, the components of a tuple). The continuity of the
  operators of the graph model is in Continuity.agda, that of the
  error-propagating ones in ErrorContinuity.agda.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; finiteNE-env; _⊆ₑ_; _⊔ₑ_; join-finiteNE-env; •-~)
open import proof.Framework.GraphModel.DenotProperties
open import Framework.abt.ScopedTuple using (Tuple)
open import Framework.abt.Sig using (Sig; Result; ∁)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Level using (lift; lower)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module proof.Framework.GraphModel.ContinuityBase where

open import proof.Framework.GraphModel.Env using () renaming (monotone-env to Mono; continuous-env to Cont) public

VEnv : Set₁
VEnv = Env Value

{- Finite approximations of an environment ----------------------------------}

record Approx (ρ : VEnv) : Set₁ where
  constructor approx
  field
    env : VEnv
    fin : finiteNE-env env
    sub : env ⊆ₑ ρ
open Approx public

approx-init : ∀ {ρ} → nonempty-env ρ → Approx ρ
approx-init NE = approx (λ x → ⌈ proj₁ (NE x) ⌉)
  (λ x → ⟨ proj₁ (NE x) ∷ [] , ⟨ ⟨ (λ { _ refl → here refl }) , (λ { _ (here refl) → refl }) ⟩ , (λ ()) ⟩ ⟩)
  (λ { x _ refl → proj₂ (NE x) })

approx-join : ∀ {ρ} → Approx ρ → Approx ρ → Approx ρ
approx-join (approx ρ₁ f₁ s₁) (approx ρ₂ f₂ s₂) =
  approx (ρ₁ ⊔ₑ ρ₂) (join-finiteNE-env f₁ f₂) (λ { x v (inj₁ v∈) → s₁ x v v∈ ; x v (inj₂ v∈) → s₂ x v v∈ })

join-l : ∀ {ρ} (a b : Approx ρ) → env a ⊆ₑ env (approx-join a b)
join-l (approx ρ₁ f₁ s₁) (approx ρ₂ f₂ s₂) x d d∈ = inj₁ d∈

join-r : ∀ {ρ} (a b : Approx ρ) → env b ⊆ₑ env (approx-join a b)
join-r (approx ρ₁ f₁ s₁) (approx ρ₂ f₂ s₂) x d d∈ = inj₂ d∈

{- the approximation of the rest of an extended environment -}
approx-tail : ∀ {X ρ} → Approx (X • ρ) → Approx ρ
approx-tail (approx ρ′ f s) = approx (λ x → ρ′ (suc x)) (λ x → f (suc x)) (λ x → s (suc x))

done : ∀ (E : VEnv → 𝒫 Value) {ρ} (a : Approx ρ) v → v ∈ E (env a)
  → Σ[ ρ′ ∈ VEnv ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ E ρ′
done E (approx ρ′ f s) v v∈ = ⟨ ρ′ , ⟨ f , ⟨ s , v∈ ⟩ ⟩ ⟩

one : ∀ (E : VEnv → 𝒫 Value) {ρ v} → Cont E ρ → v ∈ E ρ → Σ[ a ∈ Approx ρ ] v ∈ E (env a)
one E {v = v} c v∈ with c v v∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , v∈′ ⟩ ⟩ ⟩ = ⟨ approx ρ′ f s , v∈′ ⟩

many : ∀ (E : VEnv → 𝒫 Value) {ρ} → nonempty-env ρ → Mono E → Cont E ρ
  → ∀ V → mem V ⊆ E ρ → Σ[ a ∈ Approx ρ ] mem V ⊆ E (env a)
many E NE m c [] _ = ⟨ approx-init NE , (λ _ ()) ⟩
many E NE m c (v ∷ V) V⊆ with one E c (V⊆ v (here refl)) | many E NE m c V (λ d d∈ → V⊆ d (there d∈))
... | ⟨ a , v∈ ⟩ | ⟨ b , V⊆′ ⟩ = ⟨ approx-join a b , G ⟩
  where
  G : mem (v ∷ V) ⊆ _
  G _ (here refl) = m (join-l a b) v v∈
  G d (there d∈) = m (join-r a b) d (V⊆′ d d∈)

{- The operands of an operator, as functions of the environment ---------------}

{- the operand of sort b whose body means E: a binder extends the
   environment, and a clear replaces it by the one of a closed term -}
⟪_⟫ : ∀ b → (VEnv → 𝒫 Value) → VEnv → Result (𝒫 Value) b
⟪ ■ ⟫ E ρ = E ρ
⟪ ν b ⟫ E ρ X = ⟪ b ⟫ E (X • ρ)
⟪ ∁ b ⟫ E ρ = ⟪ b ⟫ E (λ _ → ⌈ ω ⌉)

Bodies : List Sig → Set₁
Bodies bs = Tuple bs (λ _ → VEnv → 𝒫 Value)

⟪_⟫₊ : ∀ bs → Bodies bs → VEnv → Results (𝒫 Value) bs
⟪ [] ⟫₊ _ _ = ptt
⟪ b ∷ bs ⟫₊ ⟨ E , Es ⟩ ρ = ⟨ ⟪ b ⟫ E ρ , ⟪ bs ⟫₊ Es ρ ⟩

{- the body E is continuous wherever the operand puts it -}
BodyCont : Sig → (VEnv → 𝒫 Value) → VEnv → Set₁
BodyCont ■ E ρ = Cont E ρ
BodyCont (ν b) E ρ = ∀ V → V ≢ [] → BodyCont b E (mem V • ρ)
BodyCont (∁ b) E ρ = BodyCont b E (λ _ → ⌈ ω ⌉)

OK : ∀ bs → Bodies bs → VEnv → Set₁
OK [] _ _ = ⊤
OK (b ∷ bs) ⟨ E , Es ⟩ ρ = (Mono E × BodyCont b E ρ) × OK bs Es ρ

Continuous : ∀ bs → DOp (𝒫 Value) bs → Set₁
Continuous bs f = ∀ Es {ρ} → nonempty-env ρ → OK bs Es ρ → Cont (λ ρ → f (⟪ bs ⟫₊ Es ρ)) ρ

⟪⟫-mono : ∀ b {E} → Mono E → ∀ {ρ ρ′ : VEnv} → ρ ⊆ₑ ρ′
  → result-rel-pres _⊆_ b (⟪ b ⟫ E ρ) (⟪ b ⟫ E ρ′)
⟪⟫-mono ■ m ρ⊆ = lift (m ρ⊆)
⟪⟫-mono (ν b) m ρ⊆ X Y X⊆ = ⟪⟫-mono b m (•-~ _⊆_ ρ⊆ X⊆)
⟪⟫-mono (∁ b) m ρ⊆ = ⟪⟫-mono b m (λ _ _ d∈ → d∈)

{- a monotone operator on monotone bodies is monotone in the environment -}
mono-env : ∀ bs {f : DOp (𝒫 Value) bs} → monotone bs ■ f → ∀ Es {ρ₁} → OK bs Es ρ₁
  → Mono (λ ρ → f (⟪ bs ⟫₊ Es ρ))
mono-env bs {f} m Es ok {ρ} {ρ′} ρ⊆ = lower (m (⟪ bs ⟫₊ Es ρ) (⟪ bs ⟫₊ Es ρ′) (ms bs Es ok))
  where
  ms : ∀ bs Es {ρ₁} → OK bs Es ρ₁ → results-rel-pres _⊆_ bs (⟪ bs ⟫₊ Es ρ) (⟪ bs ⟫₊ Es ρ′)
  ms [] _ _ = ptt
  ms (b ∷ bs) ⟨ E , Es ⟩ ⟨ ⟨ m , _ ⟩ , ok ⟩ = ⟨ ⟪⟫-mono b m ρ⊆ , ms bs Es ok ⟩

{- Operators that do not depend on the environment ---------------------------}

const-cont : ∀ {D : 𝒫 Value}{ρ} → nonempty-env ρ → Cont (λ _ → D) ρ
const-cont {D} NE v v∈ = done (λ _ → D) (approx-init NE) v v∈

ℬ-cont : ∀ B k → Continuous [] (ℬ B k)
ℬ-cont B k _ NE _ = const-cont NE


{- Tuples ---------------------------------------------------------------------}

{- one finite approximation in which each of finitely many sets is nonempty -}
cover : ∀ {m} (Es : Fin m → VEnv → 𝒫 Value) {ρ} → nonempty-env ρ
  → (∀ j → Mono (Es j)) → (∀ j → Cont (Es j) ρ) → (∀ j → nonempty (Es j ρ))
  → Σ[ a ∈ Approx ρ ] (∀ j → nonempty (Es j (env a)))
cover {zero} Es NE ms cs nes = ⟨ approx-init NE , (λ ()) ⟩
cover {suc m} Es NE ms cs nes
    with one (Es zero) (cs zero) (proj₂ (nes zero))
       | cover (λ j → Es (suc j)) NE (λ j → ms (suc j)) (λ j → cs (suc j)) (λ j → nes (suc j))
... | ⟨ a , e∈ ⟩ | ⟨ b , f ⟩ = ⟨ approx-join a b , G ⟩
  where
  G : ∀ j → nonempty (Es j (env (approx-join a b)))
  G zero = ⟨ _ , ms zero (join-l a b) _ e∈ ⟩
  G (suc j) = ⟨ proj₁ (f j) , ms (suc j) (join-r a b) _ (proj₂ (f j)) ⟩

nth-ok : ∀ {n} Es {ρ} → OK (replicate n ■) Es ρ → ∀ i
  → Mono (λ ρ → nthD (⟪ replicate n ■ ⟫₊ Es ρ) i) × Cont (λ ρ → nthD (⟪ replicate n ■ ⟫₊ Es ρ) i) ρ
nth-ok {suc n} ⟨ E , Es ⟩ ⟨ ok , _ ⟩ zero = ok
nth-ok {suc n} ⟨ E , Es ⟩ ⟨ _ , oks ⟩ (suc i) = nth-ok Es oks i


{- What a language needs of each of its operators ---------------------------------}

{- monotone, continuous, and consistent under the language's assumption P
   (on the meanings of the global definitions, for Clos5) -}
record Good (P : Set) bs (f : DOp (𝒫 Value) bs) : Set₁ where
  field
    mono : monotone bs ■ f
    consis : P → consistent _~_ bs ■ f
    cont : Continuous bs f
open Good public

mk-good : ∀ {P bs} {f : DOp (𝒫 Value) bs} → monotone bs ■ f → consistent _~_ bs ■ f
  → Continuous bs f → Good P bs f
mk-good m c k = record { mono = m ; consis = λ _ → c ; cont = k }

ℬ-good : ∀ {P} B k → Good P [] (ℬ B k)
ℬ-good B k = mk-good (ℬ-mono B k) (ℬ-consis B k) (ℬ-cont B k)

