{-

  Forward (preserve) direction of the correctness of the delay pass
  (Clos3 → Clos4), using the finite-observation logical relation of
  DelayFiniteRel (see issue #1), and the end theorem that combines it
  with the backward direction (DelayReflectFinite).

  Here R k V D' relates a finite list V of source values to a target set
  D'. The function clause applies the functions in V to a list of
  arguments U, and relates the results to the target application
  (car D' ⋆ cdr D') ⋆ E'. Source application cannot pair a function with
  a foreign environment, so unlike the backward direction no consistency
  is needed. In exchange, the case for case-op needs R-++, because a
  source scrutinee may contain both left and right elements.

  Assumptions (postulates):
  - tgt-continuous : target denotations are continuous.
-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3 as L3
open import Compiler.Lang.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Compiler.Model.Graph.Sem.Clos3Iswim as S3
open import Compiler.Model.Graph.Sem.Clos4Iswim as S4 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv using (nonempty-env; extend-nonempty-env)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon
import Compiler.Model.Graph.Correctness.DelayReflectFinite as Reflect

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module Compiler.Model.Graph.Correctness.DelayPreserveFinite where

{- Observations of a finite list of source values ----------------------------}

{- the arguments that the functions in V are prepared to accept -}
record SArgWit (V : List Value) (u : Value) : Set where
  constructor sargwit
  field
    U₀ : List Value
    w : Value
    entry∈ : (U₀ ↦ w) ⋵ V
    u∈U₀ : u ⋵ U₀

SArgs : List Value → 𝒫 Value
SArgs V = SArgWit V

{- the results of applying the functions in V to the arguments U -}
record SAppWit (V U : List Value) (w : Value) : Set where
  constructor sappwit
  field
    U₀ : List Value
    entry∈ : (U₀ ↦ w) ⋵ V
    U₀≢[] : U₀ ≢ []
    U₀⊆ : mem U₀ ⊆ mem U

SApps : List Value → List Value → 𝒫 Value
SApps V U = SAppWit V U

d-sarg : ∀ {u U₀ w} → u ⋵ U₀ → suc (depth u) ≤ depth (U₀ ↦ w)
d-sarg {u}{U₀}{w} u∈ = s≤s (≤-trans (depth-⋵ u∈) (m≤m⊔n (depths U₀) (depth w)))

d-sapp : ∀ {U₀ w} → suc (depth w) ≤ depth (U₀ ↦ w)
d-sapp {U₀}{w} = s≤s (m≤n⊔m (depths U₀) (depth w))

Bnd-SArgs : ∀ {k V U} → Bnd (suc k) V → mem U ⊆ SArgs V → Bnd k U
Bnd-SArgs bV U⊆ u u∈ with U⊆ u u∈
... | sargwit U₀ w e∈ u∈U₀ = <-shrink (d-sarg {w = w} u∈U₀) (bV _ e∈)

Bnd-SApps : ∀ {k V U W} → Bnd (suc k) V → mem W ⊆ SApps V U → Bnd k W
Bnd-SApps bV W⊆ w w∈ with W⊆ w w∈
... | sappwit U₀ e∈ _ _ = <-shrink (d-sapp {U₀}{w}) (bV _ e∈)

SArgs-⊆ : ∀ {V₁ V₂} → mem V₁ ⊆ mem V₂ → SArgs V₁ ⊆ SArgs V₂
SArgs-⊆ s u (sargwit U₀ w e∈ u∈) = sargwit U₀ w (s _ e∈) u∈

SApps-⊆ : ∀ {V₁ V₂ U₁ U₂} → mem V₁ ⊆ mem V₂ → mem U₁ ⊆ mem U₂
        → SApps V₁ U₁ ⊆ SApps V₂ U₂
SApps-⊆ s t w (sappwit U₀ e∈ ne U₀⊆) = sappwit U₀ (s _ e∈) ne (λ d d∈ → t d (U₀⊆ d d∈))

SApps-flat : ∀ {V U} → (∀ v → v ⋵ V → Flat v) → SApps V U ⊆ ∅
SApps-flat fl w (sappwit U₀ e∈ _ _) = flat-fun (fl _ e∈)

{- The relation ---------------------------------------------------------------}

open import Compiler.Model.Graph.Correctness.DelayFiniteRel
  SArgs SApps _⊙_ (λ _ → True)
  SArgs-⊆ (λ s → SApps-⊆ s (λ d z → z)) SApps-flat ⊙-mono-l Bnd-SArgs Bnd-SApps
  public

{- Unions of source observations ---------------------------------------------}

partition : ∀ {P Q : 𝒫 Value} W → mem W ⊆ (P ∪ Q)
  → Σ[ W₁ ∈ List Value ] Σ[ W₂ ∈ List Value ]
      mem W₁ ⊆ P × mem W₂ ⊆ Q × mem W ⊆ mem (W₁ ++ W₂) × mem (W₁ ++ W₂) ⊆ mem W
partition [] _ = ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩ ⟩ ⟩ ⟩
partition {P}{Q} (w ∷ W) W⊆
    with partition W (λ d d∈ → W⊆ d (there d∈)) | W⊆ w (here refl)
... | ⟨ W₁ , ⟨ W₂ , ⟨ W₁⊆ , ⟨ W₂⊆ , ⟨ W⊆' , W⊇' ⟩ ⟩ ⟩ ⟩ ⟩ | inj₁ p =
  ⟨ w ∷ W₁ , ⟨ W₂ , ⟨ G , ⟨ W₂⊆ , ⟨ H , K ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G : mem (w ∷ W₁) ⊆ P
  G _ (here refl) = p
  G d (there d∈) = W₁⊆ d d∈
  H : mem (w ∷ W) ⊆ mem (w ∷ (W₁ ++ W₂))
  H _ (here refl) = here refl
  H d (there d∈) = there (W⊆' d d∈)
  K : mem (w ∷ (W₁ ++ W₂)) ⊆ mem (w ∷ W)
  K _ (here refl) = here refl
  K d (there d∈) = there (W⊇' d d∈)
... | ⟨ W₁ , ⟨ W₂ , ⟨ W₁⊆ , ⟨ W₂⊆ , ⟨ W⊆' , W⊇' ⟩ ⟩ ⟩ ⟩ ⟩ | inj₂ q =
  ⟨ W₁ , ⟨ w ∷ W₂ , ⟨ W₁⊆ , ⟨ G , ⟨ H , K ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G : mem (w ∷ W₂) ⊆ Q
  G _ (here refl) = q
  G d (there d∈) = W₂⊆ d d∈
  H : mem (w ∷ W) ⊆ mem (W₁ ++ (w ∷ W₂))
  H _ (here refl) = ∈-++⁺ʳ W₁ (here refl)
  H d (there d∈) with ∈-++⁻ W₁ (W⊆' d d∈)
  ... | inj₁ d∈W₁ = ∈-++⁺ˡ d∈W₁
  ... | inj₂ d∈W₂ = ∈-++⁺ʳ W₁ (there d∈W₂)
  K : mem (W₁ ++ (w ∷ W₂)) ⊆ mem (w ∷ W)
  K d d∈ with ∈-++⁻ W₁ d∈
  ... | inj₁ d∈W₁ = there (W⊇' d (∈-++⁺ˡ d∈W₁))
  ... | inj₂ (here refl) = here refl
  ... | inj₂ (there d∈W₂) = there (W⊇' d (∈-++⁺ʳ W₁ d∈W₂))

{- the arguments actually used by a list of application results -}
restrict : ∀ {V U} W → mem W ⊆ SApps V U
  → Σ[ U₁ ∈ List Value ] mem U₁ ⊆ mem U × mem U₁ ⊆ SArgs V × mem W ⊆ SApps V U₁
restrict [] _ = ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩ ⟩
restrict {V}{U} (w ∷ W) W⊆
    with W⊆ w (here refl) | restrict W (λ d d∈ → W⊆ d (there d∈))
... | sappwit U₀ e∈ ne U₀⊆ | ⟨ U₁ , ⟨ U₁⊆U , ⟨ U₁⊆A , W⊆' ⟩ ⟩ ⟩ =
  ⟨ U₀ ++ U₁ , ⟨ G , ⟨ H , K ⟩ ⟩ ⟩
  where
  G : mem (U₀ ++ U₁) ⊆ mem U
  G d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆ d d∈U₀
  ... | inj₂ d∈U₁ = U₁⊆U d d∈U₁
  H : mem (U₀ ++ U₁) ⊆ SArgs V
  H d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = sargwit U₀ w e∈ d∈U₀
  ... | inj₂ d∈U₁ = U₁⊆A d d∈U₁
  K : mem (w ∷ W) ⊆ SApps V (U₀ ++ U₁)
  K _ (here refl) = sappwit U₀ e∈ ne (λ d d∈ → ∈-++⁺ˡ d∈)
  K d (there d∈) = SApps-⊆ (λ _ z → z) (λ _ z → ∈-++⁺ʳ U₀ z) d (W⊆' d d∈)

ne-++ : ∀ (V₁ V₂ : List Value) → V₁ ++ V₂ ≢ [] → V₁ ≢ [] ⊎ V₂ ≢ []
ne-++ [] V₂ ne = inj₂ ne
ne-++ (x ∷ V₁) V₂ _ = inj₁ (λ ())

R-++ : ∀ k {V₁ V₂ D} → R k V₁ D → R k V₂ D → R k (V₁ ++ V₂) D
R-++ zero _ _ = ptt
R-++ (suc k) {V₁}{V₂}{D} r₁ r₂ = record
  { const-obs = λ c c∈ → [ O₁.const-obs c , O₂.const-obs c ] (∈-++⁻ V₁ c∈)
  ; ω-obs = λ ω∈ → [ O₁.ω-obs , O₂.ω-obs ] (∈-++⁻ V₁ ω∈)
  ; nonempty-obs = λ ne → [ O₁.nonempty-obs , O₂.nonempty-obs ] (ne-++ V₁ V₂ ne)
  ; app-obs = app-++
  ; nth-obs = λ i W W⊆ →
      split (Nths i V₁) (Nths i V₂) (Nth i D) (O₁.nth-obs i) (O₂.nth-obs i) W
        (λ d d∈ → ∈-++⁻ V₁ (W⊆ d d∈))
  ; left-obs = λ W W⊆ →
      split (Lefts' V₁) (Lefts' V₂) (Lefts D) O₁.left-obs O₂.left-obs W
        (λ d d∈ → ∈-++⁻ V₁ (W⊆ d d∈))
  ; right-obs = λ W W⊆ →
      split (Rights' V₁) (Rights' V₂) (Rights D) O₁.right-obs O₂.right-obs W
        (λ d d∈ → ∈-++⁻ V₁ (W⊆ d d∈))
  }
  where
  module O₁ = Obs r₁
  module O₂ = Obs r₂

  split : ∀ (P Q D' : 𝒫 Value) → (∀ W → mem W ⊆ P → R k W D')
    → (∀ W → mem W ⊆ Q → R k W D') → ∀ W → mem W ⊆ (P ∪ Q) → R k W D'
  split P Q D' f g W W⊆ with partition W W⊆
  ... | ⟨ W₁ , ⟨ W₂ , ⟨ W₁⊆ , ⟨ W₂⊆ , ⟨ W⊆' , _ ⟩ ⟩ ⟩ ⟩ ⟩ =
    R-⊆ k W⊆' (R-++ k (f W₁ W₁⊆) (g W₂ W₂⊆))

  side : ∀ {U w} → SAppWit (V₁ ++ V₂) U w → (SApps V₁ U ∪ SApps V₂ U) w
  side (sappwit U₀ e∈ ne U₀⊆) with ∈-++⁻ V₁ e∈
  ... | inj₁ e∈₁ = inj₁ (sappwit U₀ e∈₁ ne U₀⊆)
  ... | inj₂ e∈₂ = inj₂ (sappwit U₀ e∈₂ ne U₀⊆)

  app-++ : ∀ U E → mem U ⊆ SArgs (V₁ ++ V₂) → True → R k U E
    → ∀ W → mem W ⊆ SApps (V₁ ++ V₂) U → R k W (D ⊙ E)
  app-++ U E _ _ rU W W⊆ =
    split (SApps V₁ U) (SApps V₂ U) (D ⊙ E) f₁ f₂ W (λ w w∈ → side (W⊆ w w∈))
    where
    f₁ : ∀ W → mem W ⊆ SApps V₁ U → R k W (D ⊙ E)
    f₁ W W⊆ with restrict W W⊆
    ... | ⟨ U₁ , ⟨ U₁⊆U , ⟨ U₁⊆A , W⊆' ⟩ ⟩ ⟩ =
      O₁.app-obs U₁ E U₁⊆A tt (R-⊆ k U₁⊆U rU) W W⊆'
    f₂ : ∀ W → mem W ⊆ SApps V₂ U → R k W (D ⊙ E)
    f₂ W W⊆ with restrict W W⊆
    ... | ⟨ U₁ , ⟨ U₁⊆U , ⟨ U₁⊆A , W⊆' ⟩ ⟩ ⟩ =
      O₂.app-obs U₁ E U₁⊆A tt (R-⊆ k U₁⊆U rU) W W⊆'

{- Assumptions ----------------------------------------------------------------}

postulate
  tgt-continuous : ∀ (M' : AST') (ρ' : Env) → nonempty-env ρ' → ∀ v → v ∈ ⟦ M' ⟧' ρ'
    → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ' x)
                                   × v ∈ ⟦ M' ⟧' (λ x → mem (Vs x))

cont-1' : ∀ (M' : AST') (ρ' : Env) (X : 𝒫 Value) → nonempty-env ρ' → nonempty X
  → ∀ x → x ∈ ⟦ M' ⟧' (X • ρ')
  → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M' ⟧' (mem (u ∷ U) • ρ')
cont-1' M' ρ' X NE NE-X x x∈ = go (tgt-continuous M' (X • ρ') (extend-nonempty-env NE NE-X) x x∈)
  where
  helper : ∀ V → V ≢ [] → mem V ⊆ X → x ∈ ⟦ M' ⟧' (mem V • ρ')
    → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M' ⟧' (mem (u ∷ U) • ρ')
  helper [] ne _ _ = ⊥-elim (ne refl)
  helper (u ∷ U) _ sub x∈' = ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩

  env⊆ : ∀ (Vs : Var → List Value) → (∀ y → Vs y ≢ [] × mem (Vs y) ⊆ (X • ρ') y)
    → ∀ y → mem (Vs y) ⊆ (mem (Vs 0) • ρ') y
  env⊆ Vs ok zero = λ d z → z
  env⊆ Vs ok (suc y) = proj₂ (ok (suc y))

  go : (Σ[ Vs ∈ (Var → List Value) ] (∀ y → Vs y ≢ [] × mem (Vs y) ⊆ (X • ρ') y)
                                     × x ∈ ⟦ M' ⟧' (λ y → mem (Vs y)))
    → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M' ⟧' (mem (u ∷ U) • ρ')
  go ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
    helper (Vs 0) (proj₁ (ok 0)) (proj₂ (ok 0))
      (S4.⟦⟧-monotone {ρ = λ y → mem (Vs y)} {ρ′ = mem (Vs 0) • ρ'} M' (env⊆ Vs ok) x x∈fin)

{- Collecting the finite witnesses of a source application -------------------}

collect : ∀ (L N : 𝒫 Value) V → mem V ⊆ (L ● N)
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ]
      mem W ⊆ L × mem U ⊆ N × mem V ⊆ SApps W U × mem U ⊆ SArgs W
collect L N [] _ =
  ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩ ⟩ ⟩ ⟩
collect L N (w ∷ V) V⊆
    with V⊆ w (here refl) | collect L N V (λ d d∈ → V⊆ d (there d∈))
... | ⟨ U₀ , ⟨ e∈L , ⟨ U₀⊆N , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , ⟨ V⊆A , U⊆A ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ (U₀ ↦ w) ∷ W , ⟨ U₀ ++ U , ⟨ W⊆' , ⟨ U⊆' , ⟨ A' , UA' ⟩ ⟩ ⟩ ⟩ ⟩
  where
  inW : mem W ⊆ mem ((U₀ ↦ w) ∷ W)
  inW d d∈ = there d∈
  inU : mem U ⊆ mem (U₀ ++ U)
  inU d d∈ = ∈-++⁺ʳ U₀ d∈

  W⊆' : mem ((U₀ ↦ w) ∷ W) ⊆ L
  W⊆' _ (here refl) = e∈L
  W⊆' d (there d∈) = W⊆ d d∈

  U⊆' : mem (U₀ ++ U) ⊆ N
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U

  A' : mem (w ∷ V) ⊆ SApps ((U₀ ↦ w) ∷ W) (U₀ ++ U)
  A' _ (here refl) = sappwit U₀ (here refl) neU₀ (λ d d∈ → ∈-++⁺ˡ d∈)
  A' d (there d∈) = SApps-⊆ inW inU d (V⊆A d d∈)

  UA' : mem (U₀ ++ U) ⊆ SArgs ((U₀ ↦ w) ∷ W)
  UA' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = sargwit U₀ w (here refl) d∈U₀
  ... | inj₂ d∈U = SArgs-⊆ inW d (U⊆A d d∈U)

{- each source result of a case comes from one of the branches -}
case-side : ∀ (L M N : AST) (ρ : Env) {x} → x ∈ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
  → ((λ x → nonempty (Lefts (⟦ L ⟧ ρ)) × x ∈ ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ))
     ∪ (λ x → nonempty (Rights (⟦ L ⟧ ρ)) × x ∈ ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ))) x
case-side L M N ρ {x} (inj₁ ⟨ u , ⟨ U , ⟨ allL , x∈ ⟩ ⟩ ⟩) =
  inj₁ ⟨ ⟨ u , allL u (here refl) ⟩
       , S3.⟦⟧-monotone {ρ = mem (u ∷ U) • ρ} {ρ′ = Lefts (⟦ L ⟧ ρ) • ρ} M env⊆ x x∈ ⟩
  where
  env⊆ : ∀ y → (mem (u ∷ U) • ρ) y ⊆ (Lefts (⟦ L ⟧ ρ) • ρ) y
  env⊆ zero = allL
  env⊆ (suc y) = λ d d∈ → d∈
case-side L M N ρ {x} (inj₂ ⟨ u , ⟨ U , ⟨ allR , x∈ ⟩ ⟩ ⟩) =
  inj₂ ⟨ ⟨ u , allR u (here refl) ⟩
       , S3.⟦⟧-monotone {ρ = mem (u ∷ U) • ρ} {ρ′ = Rights (⟦ L ⟧ ρ) • ρ} N env⊆ x x∈ ⟩
  where
  env⊆ : ∀ y → (mem (u ∷ U) • ρ) y ⊆ (Rights (⟦ L ⟧ ρ) • ρ) y
  env⊆ zero = allR
  env⊆ (suc y) = λ d d∈ → d∈

{- The fundamental lemma ------------------------------------------------------}

delay-preserve : ∀ (M : AST) (ρ ρ' : Env) → nonempty-env ρ' → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ ⟦ M ⟧ ρ → Bnd k V → R k V (⟦ delay M ⟧' ρ')

preserve-nth : ∀ {n} (args : L3.Args (replicate n ■)) (ρ ρ' : Env) → nonempty-env ρ'
  → ρ ⊳ₑ ρ'
  → (i : Fin n) → ∀ V k → mem V ⊆ nthD (⟦ args ⟧₊ ρ) i → Bnd k V
  → R k V (nthD (⟦ del-map-args args ⟧₊' ρ') i)

preserve-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) (ρ ρ' : Env) → nonempty-env ρ'
  → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ 𝒯 n (⟦ args ⟧₊ ρ) → Bnd k V
  → R k V (𝒯 n (⟦ del-map-args args ⟧₊' ρ'))

preserve-clos : ∀ n (N : AST) (fvs : L3.Args (replicate n ■)) (ρ ρ' : Env)
  → nonempty-env ρ' → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ → Bnd k V
  → R k V (⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ')

preserve-case : ∀ (L M N : AST) (ρ ρ' : Env) → nonempty-env ρ' → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ → Bnd k V
  → R k V (⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ')

preserve-case-left : ∀ (L M N : AST) (ρ ρ' : Env) → nonempty-env ρ' → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ (λ x → nonempty (Lefts (⟦ L ⟧ ρ)) × x ∈ ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ))
  → Bnd k V → R k V (⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ')

preserve-case-right : ∀ (L M N : AST) (ρ ρ' : Env) → nonempty-env ρ' → ρ ⊳ₑ ρ'
  → ∀ V k → mem V ⊆ (λ x → nonempty (Rights (⟦ L ⟧ ρ)) × x ∈ ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ))
  → Bnd k V → R k V (⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ')

delay-preserve (` x) ρ ρ' NE' ρ⊳ = ρ⊳ x

delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) =
  preserve-clos n N fvs

delay-preserve (app ⦅ L ,, N ,, Nil ⦆) ρ ρ' NE' ρ⊳ V k V⊆ bV
    with collect (⟦ L ⟧ ρ) (⟦ N ⟧ ρ) V V⊆
... | ⟨ W , ⟨ U , ⟨ W⊆L , ⟨ U⊆N , ⟨ V⊆Apps , U⊆Args ⟩ ⟩ ⟩ ⟩ ⟩ =
  R-irr (depths W) k (Bnd-SApps (Bnd-depths W) V⊆Apps) bV
    (Obs.app-obs (delay-preserve L ρ ρ' NE' ρ⊳ W (suc (depths W)) W⊆L (Bnd-depths W))
       U (⟦ delay N ⟧' ρ') U⊆Args tt
       (delay-preserve N ρ ρ' NE' ρ⊳ U (depths W) U⊆N (Bnd-SArgs (Bnd-depths W) U⊆Args))
       V V⊆Apps)

delay-preserve (lit B c ⦅ Nil ⦆) ρ ρ' NE' ρ⊳ V k V⊆ bV =
  R-flat k V⊆ (λ v v∈ → ℬ-flat v (V⊆ v v∈))

delay-preserve (tuple n ⦅ args ⦆) = preserve-𝒯 args

delay-preserve (get i ⦅ M ,, Nil ⦆) ρ ρ' NE' ρ⊳ V k V⊆ bV =
  Obs.nth-obs (delay-preserve M ρ ρ' NE' ρ⊳ (lmap tupi V) (suc k) mV bm) i V
    (λ d d∈ → ∈-map⁺ tupi d∈)
  where
  tupi = λ d → tup[ i ] d
  mV : mem (lmap tupi V) ⊆ ⟦ M ⟧ ρ
  mV d d∈ with ∈-map⁻ tupi d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = V⊆ x x∈
  bm : Bnd (suc k) (lmap tupi V)
  bm d d∈ with ∈-map⁻ tupi d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = s≤s (bV x x∈)

delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ ρ' NE' ρ⊳ V zero V⊆ bV = ptt
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ ρ' NE' ρ⊳ V (suc k) V⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V⊆ _ ω∈)
  ; nonempty-obs = λ ne → inl-ne (ne-head ne)
  ; app-obs = λ U E _ _ _ W W⊆ →
      R-∅ k (λ w w∈ → V⊆ _ (SAppWit.entry∈ (W⊆ w w∈)))
  ; nth-obs = λ i W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  ; left-obs = λ W W⊆ →
      delay-preserve M ρ ρ' NE' ρ⊳ W k (λ d d∈ → V⊆ _ (W⊆ d d∈)) (Bnd-Lefts bV W⊆)
  ; right-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  }
  where
  inl-ne : Σ[ v ∈ Value ] v ⋵ V → nonempty (ℒ ⟨ ⟦ delay M ⟧' ρ' , ptt ⟩)
  inl-ne ⟨ v , v∈ ⟩ with ℒ-inv v (V⊆ v v∈)
  ... | ⟨ d , ⟨ refl , d∈ ⟩ ⟩
      with Obs.nonempty-obs (delay-preserve M ρ ρ' NE' ρ⊳ (d ∷ []) (suc (depth d))
                                (single⊆ d∈) (Bnd-single d)) (λ ())
  ... | ⟨ m , m∈ ⟩ = ⟨ left m , m∈ ⟩

delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ ρ' NE' ρ⊳ V zero V⊆ bV = ptt
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ ρ' NE' ρ⊳ V (suc k) V⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V⊆ _ ω∈)
  ; nonempty-obs = λ ne → inr-ne (ne-head ne)
  ; app-obs = λ U E _ _ _ W W⊆ →
      R-∅ k (λ w w∈ → V⊆ _ (SAppWit.entry∈ (W⊆ w w∈)))
  ; nth-obs = λ i W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  ; left-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  ; right-obs = λ W W⊆ →
      delay-preserve M ρ ρ' NE' ρ⊳ W k (λ d d∈ → V⊆ _ (W⊆ d d∈)) (Bnd-Rights bV W⊆)
  }
  where
  inr-ne : Σ[ v ∈ Value ] v ⋵ V → nonempty (ℛ ⟨ ⟦ delay M ⟧' ρ' , ptt ⟩)
  inr-ne ⟨ v , v∈ ⟩ with ℛ-inv v (V⊆ v v∈)
  ... | ⟨ d , ⟨ refl , d∈ ⟩ ⟩
      with Obs.nonempty-obs (delay-preserve M ρ ρ' NE' ρ⊳ (d ∷ []) (suc (depth d))
                                (single⊆ d∈) (Bnd-single d)) (λ ())
  ... | ⟨ m , m∈ ⟩ = ⟨ right m , m∈ ⟩

delay-preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = preserve-case L M N

preserve-nth {suc n} (M ,, args) ρ ρ' NE' ρ⊳ zero = delay-preserve M ρ ρ' NE' ρ⊳
preserve-nth {suc n} (M ,, args) ρ ρ' NE' ρ⊳ (suc i) = preserve-nth args ρ ρ' NE' ρ⊳ i

preserve-𝒯 {zero} args ρ ρ' NE' ρ⊳ V k V⊆ bV = R-∅ k V⊆
preserve-𝒯 {suc n} args ρ ρ' NE' ρ⊳ V zero V⊆ bV = ptt
preserve-𝒯 {suc n} args ρ ρ' NE' ρ⊳ V (suc k) V⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V⊆ _ ω∈)
  ; nonempty-obs = λ ne → tup-ne (ne-head ne)
  ; app-obs = λ U E _ _ _ W W⊆ →
      R-∅ k (λ w w∈ → V⊆ _ (SAppWit.entry∈ (W⊆ w w∈)))
  ; nth-obs = nth-case
  ; left-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  ; right-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆ _ (W⊆ d d∈))
  }
  where
  Ds = ⟦ args ⟧₊ ρ
  Ds' = ⟦ del-map-args args ⟧₊' ρ'

  tup-ne' : ∀ v → v ∈ 𝒯 (suc n) Ds → nonempty (𝒯 (suc n) Ds')
  tup-ne' (tup[ i ] d) ⟨ refl , d∈ ⟩
      with Obs.nonempty-obs (preserve-nth args ρ ρ' NE' ρ⊳ i (d ∷ []) (suc (depth d))
                               (single⊆ d∈) (Bnd-single d)) (λ ())
  ... | ⟨ d₀ , d₀∈ ⟩ = ⟨ tup[ i ] d₀ , ⟨ refl , d₀∈ ⟩ ⟩
  tup-ne' (const k) ()
  tup-ne' (V ↦ w) ()
  tup-ne' ν ()
  tup-ne' ω ()
  tup-ne' ⦅ u ∣ ()
  tup-ne' ∣ V ⦆ ()
  tup-ne' (left d) ()
  tup-ne' (right d) ()

  tup-ne : Σ[ v ∈ Value ] v ⋵ V → nonempty (𝒯 (suc n) Ds')
  tup-ne ⟨ v , v∈ ⟩ = tup-ne' v (V⊆ v v∈)

  nth-case : ∀ {m} (i : Fin m) W → mem W ⊆ Nths i V → R k W (Nth i (𝒯 (suc n) Ds'))
  nth-case i [] _ = R-∅ k (λ _ ())
  nth-case i (w ∷ W) W⊆ with V⊆ _ (W⊆ w (here refl))
  ... | ⟨ refl , _ ⟩ =
    R-mono k (λ d d∈ → ⟨ refl , d∈ ⟩)
      (preserve-nth args ρ ρ' NE' ρ⊳ i (w ∷ W) k sub (Bnd-Nths bV W⊆))
    where
    sub : mem (w ∷ W) ⊆ nthD Ds i
    sub d d∈ with V⊆ _ (W⊆ d d∈)
    ... | ⟨ refl , d∈' ⟩ = d∈'

preserve-clos n N fvs ρ ρ' NE' ρ⊳ V zero V⊆ bV = ptt
preserve-clos n N fvs ρ ρ' NE' ρ⊳ V (suc k) V⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (proj₂ (inner (const c) (V⊆ _ c∈)))
  ; ω-obs = λ ω∈ → ⊥-elim (proj₂ (inner ω (V⊆ _ ω∈)))
  ; nonempty-obs = λ ne → P'-ne (ne-head ne)
  ; app-obs = λ U E U⊆ _ rU X X⊆ → clos-app k bV U E U⊆ rU X X⊆
  ; nth-obs = λ i W W⊆ → R-∅ k (λ d d∈ → proj₂ (inner (tup[ i ] d) (V⊆ _ (W⊆ d d∈))))
  ; left-obs = λ W W⊆ → R-∅ k (λ d d∈ → proj₂ (inner (left d) (V⊆ _ (W⊆ d d∈))))
  ; right-obs = λ W W⊆ → R-∅ k (λ d d∈ → proj₂ (inner (right d) (V⊆ _ (W⊆ d d∈))))
  }
  where
  T = 𝒯 n (⟦ fvs ⟧₊ ρ)
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  D = ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ
  P' = ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ'

  Body : 𝒫 Value → 𝒫 Value → 𝒫 Value
  Body X Y = ⟦ N ⟧ (Y • X • (λ _ → Init))

  {- every element of a source closure is a function of its argument -}
  inner : ∀ v → v ∈ D → Σ[ Vt ∈ List Value ] v ∈ Λ ⟨ Body (mem Vt) , ptt ⟩
  inner v ⟨ Vt , ⟨ ⟨ v∈ , _ ⟩ , _ ⟩ ⟩ = ⟨ Vt , v∈ ⟩

  T'-ne : nonempty T → nonempty T'
  T'-ne ⟨ t , t∈ ⟩ =
    Obs.nonempty-obs (preserve-𝒯 fvs ρ ρ' NE' ρ⊳ (t ∷ []) (suc (depth t))
                        (single⊆ t∈) (Bnd-single t)) (λ ())

  T-ne : ∀ v → v ∈ D → nonempty T
  T-ne v ⟨ Vt , ⟨ _ , ⟨ Vt⊆T , neVt ⟩ ⟩ ⟩ = ne-mem neVt Vt⊆T

  {- a target closure contains ⦅ ν ∣ as soon as its environment is nonempty -}
  P'-ne : Σ[ v ∈ Value ] v ⋵ V → nonempty P'
  P'-ne ⟨ v , v∈ ⟩ with T'-ne (T-ne v (V⊆ v v∈))
  ... | ⟨ t' , t'∈ ⟩ = ⟨ ⦅ ν ∣ , ⟨ t' ∷ [] , ⟨ tt , ⟨ single⊆ t'∈ , (λ ()) ⟩ ⟩ ⟩ ⟩

  {- the environments captured by the elements of V, all at once -}
  collect-env : ∀ V₀ → mem V₀ ⊆ D
    → Σ[ Vs ∈ List Value ] mem Vs ⊆ T
        × (∀ v → v ⋵ V₀ → Σ[ Vt ∈ List Value ] mem Vt ⊆ mem Vs
                            × v ∈ Λ ⟨ Body (mem Vt) , ptt ⟩)
  collect-env [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
  collect-env (v ∷ V₀) V₀⊆
      with V₀⊆ v (here refl) | collect-env V₀ (λ d d∈ → V₀⊆ d (there d∈))
  ... | ⟨ Vt , ⟨ ⟨ v∈ , _ ⟩ , ⟨ Vt⊆T , _ ⟩ ⟩ ⟩ | ⟨ Vs , ⟨ Vs⊆T , f ⟩ ⟩ =
    ⟨ Vt ++ Vs , ⟨ G , H ⟩ ⟩
    where
    G : mem (Vt ++ Vs) ⊆ T
    G d d∈ with ∈-++⁻ Vt d∈
    ... | inj₁ d∈Vt = Vt⊆T d d∈Vt
    ... | inj₂ d∈Vs = Vs⊆T d d∈Vs
    H : ∀ u → u ⋵ (v ∷ V₀) → Σ[ Vt' ∈ List Value ] mem Vt' ⊆ mem (Vt ++ Vs)
                                × u ∈ Λ ⟨ Body (mem Vt') , ptt ⟩
    H _ (here refl) = ⟨ Vt , ⟨ (λ d d∈ → ∈-++⁺ˡ d∈) , v∈ ⟩ ⟩
    H u (there u∈) with f u u∈
    ... | ⟨ Vt' , ⟨ s , u∈' ⟩ ⟩ = ⟨ Vt' , ⟨ (λ d d∈ → ∈-++⁺ʳ Vt (s d d∈)) , u∈' ⟩ ⟩

  clos-app : ∀ j → Bnd (suc j) V → ∀ U E' → mem U ⊆ SArgs V → R j U E'
    → ∀ X → mem X ⊆ SApps V U → R j X (P' ⊙ E')
  clos-app zero _ U E' _ _ X _ = ptt
  clos-app (suc j) bV' U E' U⊆ rU [] _ = R-∅ (suc j) (λ _ ())
  clos-app (suc j) bV' U E' U⊆ rU (x ∷ X) X⊆ = R-mono (suc j) B⊆ IH
    where
    cenv = collect-env V V⊆
    Vs = proj₁ cenv
    Vs⊆T = proj₁ (proj₂ cenv)
    envOf = proj₂ (proj₂ cenv)

    wit = X⊆ x (here refl)

    NE-E' : nonempty E'
    NE-E' = Obs.nonempty-obs rU (ne-⊆ (SAppWit.U₀⊆ wit) (SAppWit.U₀≢[] wit))

    NE-T' : nonempty T'
    NE-T' = T'-ne (T-ne (SAppWit.U₀ wit ↦ x) (V⊆ _ (SAppWit.entry∈ wit)))

    ρs : Env
    ρs = mem U • mem Vs • (λ _ → Init)

    ρt : Env
    ρt = E' • T' • (λ _ → Init)

    X⊆B : mem (x ∷ X) ⊆ ⟦ N ⟧ ρs
    X⊆B y y∈ with X⊆ y y∈
    ... | sappwit U₀ e∈ _ U₀⊆U with envOf _ e∈
    ... | ⟨ Vt , ⟨ Vt⊆Vs , ⟨ y∈B , _ ⟩ ⟩ ⟩ =
      S3.⟦⟧-monotone {ρ = mem U₀ • mem Vt • (λ _ → Init)} {ρ′ = ρs} N env⊆ y y∈B
      where
      env⊆ : ∀ z → (mem U₀ • mem Vt • (λ _ → Init)) z ⊆ ρs z
      env⊆ zero = U₀⊆U
      env⊆ (suc zero) = Vt⊆Vs
      env⊆ (suc (suc z)) = λ d d∈ → d∈

    NE-ρt : nonempty-env ρt
    NE-ρt zero = NE-E'
    NE-ρt (suc zero) = NE-T'
    NE-ρt (suc (suc z)) = ⟨ ω , refl ⟩

    ρs⊳ρt : ρs ⊳ₑ ρt
    ρs⊳ρt zero Y i Y⊆ bY =
      R-irr (suc j) i (Bnd-⊆ Y⊆ (Bnd-SArgs bV' U⊆)) bY (R-⊆ (suc j) Y⊆ rU)
    ρs⊳ρt (suc zero) Y i Y⊆ bY =
      preserve-𝒯 fvs ρ ρ' NE' ρ⊳ Y i (λ y y∈ → Vs⊆T y (Y⊆ y y∈)) bY
    ρs⊳ρt (suc (suc z)) Y i Y⊆ bY = R-flat i Y⊆ (λ v v∈ → Init-flat (Y⊆ v v∈))

    IH : R (suc j) (x ∷ X) (⟦ delay N ⟧' ρt)
    IH = delay-preserve N ρs ρt NE-ρt ρs⊳ρt (x ∷ X) (suc j) X⊆B (Bnd-SApps bV' X⊆)

    {- the target closure, applied to its own environment, is the body -}
    B⊆ : ⟦ delay N ⟧' ρt ⊆ (P' ⊙ E')
    B⊆ y y∈ with tgt-continuous (delay N) ρt NE-ρt y y∈
    ... | ⟨ Vs' , ⟨ ok , y∈fin ⟩ ⟩ =
      ⟨ Vs' 0 , ⟨ ⟨ Vs' 1 , ⟨ ⟨ Vs' 1 , ⟨ ⟨ ⟨ y∈' , proj₁ (ok 0) ⟩ , proj₁ (ok 1) ⟩
                                       , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
                          , ⟨ cdr⊆ , proj₁ (ok 1) ⟩ ⟩ ⟩
                , ⟨ proj₂ (ok 0) , proj₁ (ok 0) ⟩ ⟩ ⟩
      where
      env⊆ : ∀ z → mem (Vs' z) ⊆ (mem (Vs' 0) • mem (Vs' 1) • (λ _ → Init)) z
      env⊆ zero = λ d d∈ → d∈
      env⊆ (suc zero) = λ d d∈ → d∈
      env⊆ (suc (suc z)) = proj₂ (ok (suc (suc z)))
      y∈' = S4.⟦⟧-monotone {ρ = λ z → mem (Vs' z)}
                           {ρ′ = mem (Vs' 0) • mem (Vs' 1) • (λ _ → Init)}
                           (delay N) env⊆ y y∈fin
      cdr⊆ : mem (Vs' 1) ⊆ Cdr P'
      cdr⊆ d d∈ = ⟨ Vs' 1 , ⟨ ⟨ ν , ⟨ tt , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩ , d∈ ⟩ ⟩

preserve-case L M N ρ ρ' NE' ρ⊳ V k V⊆ bV
    with partition V (λ v v∈ → case-side L M N ρ (V⊆ v v∈))
... | ⟨ Vl , ⟨ Vr , ⟨ Vl⊆ , ⟨ Vr⊆ , ⟨ V⊆' , V⊇' ⟩ ⟩ ⟩ ⟩ ⟩ =
  R-⊆ k V⊆'
    (R-++ k (preserve-case-left L M N ρ ρ' NE' ρ⊳ Vl k Vl⊆
               (Bnd-⊆ (λ d d∈ → V⊇' d (∈-++⁺ˡ d∈)) bV))
            (preserve-case-right L M N ρ ρ' NE' ρ⊳ Vr k Vr⊆
               (Bnd-⊆ (λ d d∈ → V⊇' d (∈-++⁺ʳ Vl d∈)) bV)))

preserve-case-left L M N ρ ρ' NE' ρ⊳ [] k _ _ = R-∅ k (λ _ ())
preserve-case-left L M N ρ ρ' NE' ρ⊳ (x ∷ V) k V⊆ bV = R-mono k M'⊆ IH
  where
  L' = ⟦ delay L ⟧' ρ'

  rL : ∀ Y j → mem Y ⊆ Lefts (⟦ L ⟧ ρ) → Bnd j Y → R j Y (Lefts L')
  rL Y j Y⊆ bY =
    Obs.left-obs (delay-preserve L ρ ρ' NE' ρ⊳ (lmap left Y) (suc j) mY bm) Y
      (λ d d∈ → ∈-map⁺ left d∈)
    where
    mY : mem (lmap left Y) ⊆ ⟦ L ⟧ ρ
    mY d d∈ with ∈-map⁻ left d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = Y⊆ y y∈
    bm : Bnd (suc j) (lmap left Y)
    bm d d∈ with ∈-map⁻ left d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = s≤s (bY y y∈)

  NE-Lefts' : nonempty (Lefts L')
  NE-Lefts' with proj₁ (V⊆ x (here refl))
  ... | ⟨ u , lu ⟩ =
    Obs.nonempty-obs (rL (u ∷ []) (suc (depth u)) (single⊆ lu) (Bnd-single u)) (λ ())

  ρL : Env
  ρL = Lefts (⟦ L ⟧ ρ) • ρ

  ρL' : Env
  ρL' = Lefts L' • ρ'

  NE-ρL' : nonempty-env ρL'
  NE-ρL' zero = NE-Lefts'
  NE-ρL' (suc y) = NE' y

  ρL⊳ : ρL ⊳ₑ ρL'
  ρL⊳ zero = rL
  ρL⊳ (suc y) = ρ⊳ y

  IH : R k (x ∷ V) (⟦ delay M ⟧' ρL')
  IH = delay-preserve M ρL ρL' NE-ρL' ρL⊳ (x ∷ V) k (λ d d∈ → proj₂ (V⊆ d d∈)) bV

  M'⊆ : ⟦ delay M ⟧' ρL' ⊆ ⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ'
  M'⊆ y y∈ with cont-1' (delay M) ρ' (Lefts L') NE' NE-Lefts' y y∈
  ... | ⟨ u , ⟨ U , ⟨ sub , y∈' ⟩ ⟩ ⟩ = inj₁ ⟨ u , ⟨ U , ⟨ sub , y∈' ⟩ ⟩ ⟩

preserve-case-right L M N ρ ρ' NE' ρ⊳ [] k _ _ = R-∅ k (λ _ ())
preserve-case-right L M N ρ ρ' NE' ρ⊳ (x ∷ V) k V⊆ bV = R-mono k N'⊆ IH
  where
  L' = ⟦ delay L ⟧' ρ'

  rR : ∀ Y j → mem Y ⊆ Rights (⟦ L ⟧ ρ) → Bnd j Y → R j Y (Rights L')
  rR Y j Y⊆ bY =
    Obs.right-obs (delay-preserve L ρ ρ' NE' ρ⊳ (lmap right Y) (suc j) mY bm) Y
      (λ d d∈ → ∈-map⁺ right d∈)
    where
    mY : mem (lmap right Y) ⊆ ⟦ L ⟧ ρ
    mY d d∈ with ∈-map⁻ right d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = Y⊆ y y∈
    bm : Bnd (suc j) (lmap right Y)
    bm d d∈ with ∈-map⁻ right d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = s≤s (bY y y∈)

  NE-Rights' : nonempty (Rights L')
  NE-Rights' with proj₁ (V⊆ x (here refl))
  ... | ⟨ u , ru ⟩ =
    Obs.nonempty-obs (rR (u ∷ []) (suc (depth u)) (single⊆ ru) (Bnd-single u)) (λ ())

  ρR : Env
  ρR = Rights (⟦ L ⟧ ρ) • ρ

  ρR' : Env
  ρR' = Rights L' • ρ'

  NE-ρR' : nonempty-env ρR'
  NE-ρR' zero = NE-Rights'
  NE-ρR' (suc y) = NE' y

  ρR⊳ : ρR ⊳ₑ ρR'
  ρR⊳ zero = rR
  ρR⊳ (suc y) = ρ⊳ y

  IH : R k (x ∷ V) (⟦ delay N ⟧' ρR')
  IH = delay-preserve N ρR ρR' NE-ρR' ρR⊳ (x ∷ V) k (λ d d∈ → proj₂ (V⊆ d d∈)) bV

  N'⊆ : ⟦ delay N ⟧' ρR' ⊆ ⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ'
  N'⊆ y y∈ with cont-1' (delay N) ρ' (Rights L') NE' NE-Rights' y y∈
  ... | ⟨ u , ⟨ U , ⟨ sub , y∈' ⟩ ⟩ ⟩ = inj₂ ⟨ u , ⟨ U , ⟨ sub , y∈' ⟩ ⟩ ⟩

{- The end theorem ------------------------------------------------------------}

delay-preserve-closed : ∀ (M : AST) V k → mem V ⊆ ⟦ M ⟧ ρ₀ → Bnd k V
  → R k V (⟦ delay M ⟧' ρ₀)
delay-preserve-closed M = delay-preserve M ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) Init⊳Init

preserve-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀
preserve-const M c c∈ =
  Obs.const-obs (delay-preserve-closed M (const c ∷ []) 1 (single⊆ c∈) (Bnd-single (const c)))
    c (here refl)

preserve-nonempty : ∀ (M : AST) → nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay M ⟧' ρ₀)
preserve-nonempty M ⟨ v , v∈ ⟩ =
  Obs.nonempty-obs (delay-preserve-closed M (v ∷ []) (suc (depth v)) (single⊆ v∈) (Bnd-single v))
    (λ ())

{- For a closed program, the delay pass preserves and reflects the constants
   it produces and whether it produces anything at all. -}
delay-correct-const : ∀ (M : AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀)
  × (const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ preserve-const M c , Reflect.reflect-const M c ⟩

delay-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay M ⟧' ρ₀))
  × (nonempty (⟦ delay M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀))
delay-correct-nonempty M = ⟨ preserve-nonempty M , Reflect.reflect-nonempty M ⟩
