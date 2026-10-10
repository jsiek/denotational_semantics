{-

  Continuity of the ISWIM graph-model operators.

  Each lemma says that an operator preserves continuity: if the
  denotations of its operands are monotone and continuous at ρ (every
  element is already produced by a finite, nonempty sub-environment of ρ),
  then so is the result. These are the per-operator facts needed for a
  ContinuousSemantics instance (see NewSemantics).

-}

open import SetsAsPredicates
open import NewDOpSig
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import NewEnv
  using (Env; nonempty-env; finiteNE-env; _⊆ₑ_; _⊔ₑ_; join-finiteNE-env; join-lub;
         initial-finiteNE-env; initial-fin; initial-fin-⊆; monotone-env)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module Compiler.Model.Graph.Domain.ISWIM.Continuity where

VEnv : Set₁
VEnv = Env Value

{- E is continuous at ρ (the same as NewSemantics.continuous-env) -}
Cont : (VEnv → 𝒫 Value) → VEnv → Set₁
Cont E ρ = ∀ v → v ∈ E ρ → Σ[ ρ′ ∈ VEnv ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ E ρ′

Mono : (VEnv → 𝒫 Value) → Set₁
Mono = monotone-env

{- Finite approximations of an environment ----------------------------------}

record Approx (ρ : VEnv) : Set₁ where
  constructor approx
  field
    env : VEnv
    fin : finiteNE-env env
    sub : env ⊆ₑ ρ
open Approx

approx-init : ∀ {ρ} → nonempty-env ρ → Approx ρ
approx-init {ρ} NE = approx (initial-finiteNE-env ρ NE) (initial-fin ρ NE) (initial-fin-⊆ ρ NE)

approx-join : ∀ {ρ} → Approx ρ → Approx ρ → Approx ρ
approx-join (approx ρ₁ f₁ s₁) (approx ρ₂ f₂ s₂) =
  approx (ρ₁ ⊔ₑ ρ₂) (join-finiteNE-env f₁ f₂) (join-lub s₁ s₂)

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

{- Operators that do not depend on the environment ---------------------------}

const-mono : ∀ {D : 𝒫 Value} → Mono (λ _ → D)
const-mono _ d d∈ = d∈

const-cont : ∀ {D : 𝒫 Value}{ρ} → nonempty-env ρ → Cont (λ _ → D) ρ
const-cont {D} NE v v∈ = done (λ _ → D) (approx-init NE) v v∈

{- Functions, whose body B binds one variable -----------------------------------}

Λ-mono-env : ∀ {B : VEnv → 𝒫 Value} → Mono B → Mono (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩)
Λ-mono-env m ρ⊆ ν tt = tt
Λ-mono-env m ρ⊆ (V ↦ w) ⟨ w∈ , neV ⟩ = ⟨ m (env⊆ ρ⊆) w w∈ , neV ⟩
  where
  env⊆ : ∀ {ρ ρ′ : VEnv} → (∀ x → ρ x ⊆ ρ′ x) → ∀ x → (mem V • ρ) x ⊆ (mem V • ρ′) x
  env⊆ ρ⊆ zero = λ d d∈ → d∈
  env⊆ ρ⊆ (suc x) = ρ⊆ x

Λ-cont : ∀ {B : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Mono B
  → (∀ V → V ≢ [] → Cont B (mem V • ρ))
  → Cont (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) ρ
Λ-cont {B} NE m c ν tt = done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) (approx-init NE) ν tt
Λ-cont {B} NE m c (V ↦ w) ⟨ w∈ , neV ⟩ with c V neV w w∈
... | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) t (V ↦ w) ⟨ m env⊆ w w∈₂ , neV ⟩
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem V • env t) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = λ d d∈ → d∈

{- Application ----------------------------------------------------------------}

⋆-mono-env : ∀ {E₁ E₂} → Mono E₁ → Mono E₂ → Mono (λ ρ → ⋆ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩)
⋆-mono-env m₁ m₂ ρ⊆ w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ m₁ ρ⊆ _ e∈ , ⟨ (λ d d∈ → m₂ ρ⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩

⋆-cont : ∀ {E₁ E₂ ρ} → nonempty-env ρ → Mono E₁ → Mono E₂ → Cont E₁ ρ → Cont E₂ ρ
  → Cont (λ ρ → ⋆ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) ρ
⋆-cont {E₁}{E₂} NE m₁ m₂ c₁ c₂ w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
    with one E₁ c₁ e∈ | many E₂ NE m₂ c₂ V V⊆
... | ⟨ a , e∈′ ⟩ | ⟨ b , V⊆′ ⟩ =
  done (λ ρ → ⋆ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) w
    ⟨ V , ⟨ m₁ (join-l a b) _ e∈′ , ⟨ (λ d d∈ → m₂ (join-r a b) d (V⊆′ d d∈)) , ne ⟩ ⟩ ⟩

{- Pairs ----------------------------------------------------------------------}

pair-mono-env : ∀ {E₁ E₂} → Mono E₁ → Mono E₂ → Mono (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩)
pair-mono-env m₁ m₂ ρ⊆ ⦅ f ∣ ⟨ v , ⟨ f∈ , v∈ ⟩ ⟩ = ⟨ v , ⟨ m₁ ρ⊆ f f∈ , m₂ ρ⊆ v v∈ ⟩ ⟩
pair-mono-env m₁ m₂ ρ⊆ ∣ v ⦆ ⟨ f , ⟨ f∈ , v∈ ⟩ ⟩ = ⟨ f , ⟨ m₁ ρ⊆ f f∈ , m₂ ρ⊆ v v∈ ⟩ ⟩

pair-cont : ∀ {E₁ E₂ ρ} → nonempty-env ρ → Mono E₁ → Mono E₂ → Cont E₁ ρ → Cont E₂ ρ
  → Cont (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) ρ
pair-cont {E₁}{E₂} NE m₁ m₂ c₁ c₂ ⦅ f ∣ ⟨ v , ⟨ f∈ , v∈ ⟩ ⟩
    with one E₁ c₁ f∈ | one E₂ c₂ v∈
... | ⟨ a , f∈′ ⟩ | ⟨ b , v∈′ ⟩ =
  done (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ⦅ f ∣
    ⟨ v , ⟨ m₁ (join-l a b) f f∈′ , m₂ (join-r a b) v v∈′ ⟩ ⟩
pair-cont {E₁}{E₂} NE m₁ m₂ c₁ c₂ ∣ v ⦆ ⟨ f , ⟨ f∈ , v∈ ⟩ ⟩
    with one E₁ c₁ f∈ | one E₂ c₂ v∈
... | ⟨ a , f∈′ ⟩ | ⟨ b , v∈′ ⟩ =
  done (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ∣ v ⦆
    ⟨ f , ⟨ m₁ (join-l a b) f f∈′ , m₂ (join-r a b) v v∈′ ⟩ ⟩

car-mono-env : ∀ {E} → Mono E → Mono (λ ρ → car ⟨ E ρ , ptt ⟩)
car-mono-env m ρ⊆ f f∈ = m ρ⊆ ⦅ f ∣ f∈

car-cont : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → car ⟨ E ρ , ptt ⟩) ρ
car-cont c f f∈ = c ⦅ f ∣ f∈

cdr-mono-env : ∀ {E} → Mono E → Mono (λ ρ → cdr ⟨ E ρ , ptt ⟩)
cdr-mono-env m ρ⊆ v v∈ = m ρ⊆ ∣ v ⦆ v∈

cdr-cont : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → cdr ⟨ E ρ , ptt ⟩) ρ
cdr-cont c v v∈ = c ∣ v ⦆ v∈

{- Tuples ---------------------------------------------------------------------}

𝒯-mono-env : ∀ {n} {Ds : VEnv → Results (𝒫 Value) (replicate n ■)}
  → (∀ i → Mono (λ ρ → nthD (Ds ρ) i)) → Mono (λ ρ → 𝒯 n (Ds ρ))
𝒯-mono-env {zero} m ρ⊆ ⟨⟩ tt = tt
𝒯-mono-env {suc n} m ρ⊆ (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⟨ refl , ⟨ m i ρ⊆ d d∈ , (λ j → ⟨ proj₁ (ne j) , m j ρ⊆ _ (proj₂ (ne j)) ⟩) ⟩ ⟩

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

𝒯-cont : ∀ {n} {Ds : VEnv → Results (𝒫 Value) (replicate n ■)} {ρ} → nonempty-env ρ
  → (∀ i → Mono (λ ρ → nthD (Ds ρ) i))
  → (∀ i → Cont (λ ρ → nthD (Ds ρ) i) ρ) → Cont (λ ρ → 𝒯 n (Ds ρ)) ρ
𝒯-cont {zero} {Ds} NE m c ⟨⟩ tt = done (λ ρ → 𝒯 zero (Ds ρ)) (approx-init NE) ⟨⟩ tt
𝒯-cont {suc n} {Ds} NE m c (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩
    with one (λ ρ → nthD (Ds ρ) i) (c i) d∈ | cover (λ j ρ → nthD (Ds ρ) j) NE m c ne
... | ⟨ a , d∈′ ⟩ | ⟨ b , ne′ ⟩ =
  done (λ ρ → 𝒯 (suc n) (Ds ρ)) (approx-join a b) (tup[ i ] d)
    ⟨ refl , ⟨ m i (join-l a b) d d∈′
             , (λ j → ⟨ proj₁ (ne′ j) , m j (join-r a b) _ (proj₂ (ne′ j)) ⟩) ⟩ ⟩

proj-mono-env : ∀ {n} (i : Fin n) {E} → Mono E → Mono (λ ρ → proj i ⟨ E ρ , ptt ⟩)
proj-mono-env i m ρ⊆ d d∈ = m ρ⊆ (tup[ i ] d) d∈

proj-cont : ∀ {n} (i : Fin n) {E ρ} → Cont E ρ → Cont (λ ρ → proj i ⟨ E ρ , ptt ⟩) ρ
proj-cont i c d d∈ = c (tup[ i ] d) d∈

{- Sums -----------------------------------------------------------------------}

ℒ-mono-env : ∀ {E} → Mono E → Mono (λ ρ → ℒ ⟨ E ρ , ptt ⟩)
ℒ-mono-env m ρ⊆ (left d) d∈ = m ρ⊆ d d∈

ℒ-cont : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → ℒ ⟨ E ρ , ptt ⟩) ρ
ℒ-cont c (left d) d∈ = c d d∈

ℛ-mono-env : ∀ {E} → Mono E → Mono (λ ρ → ℛ ⟨ E ρ , ptt ⟩)
ℛ-mono-env m ρ⊆ (right d) d∈ = m ρ⊆ d d∈

ℛ-cont : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → ℛ ⟨ E ρ , ptt ⟩) ρ
ℛ-cont c (right d) d∈ = c d d∈

{- Case analysis, whose branches B₁ and B₂ bind one variable -}
map-left⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → left d ∈ D) → mem (lmap left U) ⊆ D
map-left⊆ all d d∈ with ∈-map⁻ left d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

map-right⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → right d ∈ D) → mem (lmap right U) ⊆ D
map-right⊆ all d d∈ with ∈-map⁻ right d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

𝒞-cont : ∀ {L B₁ B₂ : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ
  → Mono L → Cont L ρ
  → Mono B₁ → (∀ V → V ≢ [] → Cont B₁ (mem V • ρ))
  → Mono B₂ → (∀ V → V ≢ [] → Cont B₂ (mem V • ρ))
  → Cont (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) ρ
𝒞-cont {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₁ ⟨ u , ⟨ U , ⟨ allL , w∈ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap left (u ∷ U)) (map-left⊆ allL) | c₁ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Ls⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (left d) (Ls⊆′ (left d) (∈-map⁺ left d∈)))
                     , m₁ env⊆ w w∈₂ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
𝒞-cont {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ ⟨ u , ⟨ U , ⟨ allR , w∈ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap right (u ∷ U)) (map-right⊆ allR) | c₂ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Rs⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (right d) (Rs⊆′ (right d) (∈-map⁺ right d∈)))
                     , m₂ env⊆ w w∈₂ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
