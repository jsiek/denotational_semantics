{-

  Continuity of the graph-model operators.

  Each lemma says that an operator preserves continuity (Continuous): if
  the bodies of its operands are monotone and continuous wherever the
  operands put them (every element is already produced by a finite,
  nonempty sub-environment), then so is the result. With monotonicity and
  consistency, this is what a language needs of each of its operators
  (Good); the properties of whole terms follow once, in SemanticsUtil.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
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

module proof.Framework.GraphModel.Continuity where

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
open Approx

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

{- the code of a closure is closed -}
ΛΛ-cont : Continuous (∁ (ν (ν ■)) ∷ []) ΛΛ
ΛΛ-cont _ NE _ = const-cont NE

{- Functions, whose body B binds one variable -----------------------------------}

Λ-cont′ : ∀ {B : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Mono B
  → (∀ V → V ≢ [] → Cont B (mem V • ρ)) → Cont (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) ρ
Λ-cont′ {B} NE m c ν tt = done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) (approx-init NE) ν tt
Λ-cont′ {B} NE m c (V ↦ w) ⟨ w∈ , neV ⟩ with c V (proj₁ neV) w w∈
... | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) t (V ↦ w) ⟨ m env⊆ w w∈₂ , neV ⟩
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem V • env t) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = λ d d∈ → d∈

Λ-cont : Continuous (ν ■ ∷ []) Λ
Λ-cont ⟨ B , _ ⟩ NE ⟨ ⟨ m , c ⟩ , _ ⟩ = Λ-cont′ {B} NE m c

{- Application ----------------------------------------------------------------}

⋆-cont : Continuous (■ ∷ ■ ∷ []) ⋆
⋆-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
    with one E₁ c₁ e∈ | many E₂ NE m₂ c₂ V V⊆
... | ⟨ a , e∈′ ⟩ | ⟨ b , V⊆′ ⟩ =
  done (λ ρ → ⋆ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) w
    ⟨ V , ⟨ m₁ (join-l a b) _ e∈′ , ⟨ (λ d d∈ → m₂ (join-r a b) d (V⊆′ d d∈)) , ne ⟩ ⟩ ⟩

{- Pairs ----------------------------------------------------------------------}

pair-cont : Continuous (■ ∷ ■ ∷ []) pair
pair-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩
    with one E₁ c₁ u∈ | one E₂ c₂ v∈
... | ⟨ a , u∈′ ⟩ | ⟨ b , v∈′ ⟩ =
  done (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ⦅ u , v ⦆
    ⟨ m₁ (join-l a b) u u∈′ , m₂ (join-r a b) v v∈′ ⟩

car-cont′ : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → car ⟨ E ρ , ptt ⟩) ρ
car-cont′ {E} c u ⟨ v , uv∈ ⟩ with c ⦅ u , v ⦆ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ v , uv∈′ ⟩ ⟩ ⟩ ⟩

cdr-cont′ : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → cdr ⟨ E ρ , ptt ⟩) ρ
cdr-cont′ {E} c v ⟨ u , uv∈ ⟩ with c ⦅ u , v ⦆ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ u , uv∈′ ⟩ ⟩ ⟩ ⟩

car-cont : Continuous (■ ∷ []) car
car-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ = car-cont′ {E} c

cdr-cont : Continuous (■ ∷ []) cdr
cdr-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ = cdr-cont′ {E} c

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

𝒯-cont : ∀ n → Continuous (replicate n ■) (𝒯 n)
𝒯-cont zero Es NE _ ⟨⟩ tt = done (λ ρ → 𝒯 zero (⟪ [] ⟫₊ Es ρ)) (approx-init NE) ⟨⟩ tt
𝒯-cont (suc n) Es NE ok (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩
    with one (λ ρ → nthD (⟪ replicate (suc n) ■ ⟫₊ Es ρ) i) (proj₂ (nth-ok Es ok i)) d∈
       | cover (λ j ρ → nthD (⟪ replicate (suc n) ■ ⟫₊ Es ρ) j) NE
           (λ j → proj₁ (nth-ok Es ok j)) (λ j → proj₂ (nth-ok Es ok j)) ne
... | ⟨ a , d∈′ ⟩ | ⟨ b , ne′ ⟩ =
  done (λ ρ → 𝒯 (suc n) (⟪ replicate (suc n) ■ ⟫₊ Es ρ)) (approx-join a b) (tup[ i ] d)
    ⟨ refl , ⟨ proj₁ (nth-ok Es ok i) (join-l a b) d d∈′
             , (λ j → ⟨ proj₁ (ne′ j) , proj₁ (nth-ok Es ok j) (join-r a b) _ (proj₂ (ne′ j)) ⟩) ⟩ ⟩

proj-cont : ∀ {n} (i : Fin n) → Continuous (■ ∷ []) (proj i)
proj-cont i _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ d d∈ = c (tup[ i ] d) d∈

{- Sums -----------------------------------------------------------------------}

inl-cont : Continuous (■ ∷ []) inl
inl-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (left d) d∈ = c d d∈

inr-cont : Continuous (■ ∷ []) inr
inr-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (right d) d∈ = c d d∈

{- Case analysis, whose branches B₁ and B₂ bind one variable -}
map-left⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → left d ∈ D) → mem (lmap left U) ⊆ D
map-left⊆ all d d∈ with ∈-map⁻ left d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

map-right⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → right d ∈ D) → mem (lmap right U) ⊆ D
map-right⊆ all d d∈ with ∈-map⁻ right d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

𝒞-cont′ : ∀ {L B₁ B₂ : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ
  → Mono L → Cont L ρ
  → Mono B₁ → (∀ V → V ≢ [] → Cont B₁ (mem V • ρ))
  → Mono B₂ → (∀ V → V ≢ [] → Cont B₂ (mem V • ρ))
  → Cont (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) ρ
𝒞-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap left (u ∷ U)) (map-left⊆ allL) | c₁ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Ls⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (left d) (Ls⊆′ (left d) (∈-map⁺ left d∈)))
                     , ⟨ m₁ env⊆ w w∈₂ , c ⟩ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
𝒞-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap right (u ∷ U)) (map-right⊆ allR) | c₂ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Rs⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (right d) (Rs⊆′ (right d) (∈-map⁺ right d∈)))
                     , ⟨ m₂ env⊆ w w∈₂ , c ⟩ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x

𝒞-cont : Continuous (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞
𝒞-cont ⟨ L , ⟨ B₁ , ⟨ B₂ , _ ⟩ ⟩ ⟩ NE ⟨ ⟨ mL , cL ⟩ , ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⟩ =
  𝒞-cont′ {L} {B₁} {B₂} NE mL cL m₁ c₁ m₂ c₂

{- Composites -------------------------------------------------------------------}

letD-cont : Continuous (■ ∷ ν ■ ∷ []) letD
letD-cont ⟨ M , ⟨ N , _ ⟩ ⟩ NE ⟨ okM , ⟨ okN , _ ⟩ ⟩ =
  ⋆-cont ⟨ (λ ρ → Λ ⟨ (λ X → N (X • ρ)) , ptt ⟩) , ⟨ M , ptt ⟩ ⟩ NE
    ⟨ ⟨ mono-env (ν ■ ∷ []) Λ-mono ⟨ N , ptt ⟩ ⟨ okN , ptt ⟩ , Λ-cont ⟨ N , ptt ⟩ NE ⟨ okN , ptt ⟩ ⟩
    , ⟨ okM , ptt ⟩ ⟩

⋆₂-cont : Continuous (■ ∷ ■ ∷ ■ ∷ []) ⋆₂
⋆₂-cont ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ NE ⟨ okL , ⟨ okM , ⟨ okN , _ ⟩ ⟩ ⟩ =
  ⋆-cont ⟨ (λ ρ → ⋆ ⟨ L ρ , ⟨ M ρ , ptt ⟩ ⟩) , ⟨ N , ptt ⟩ ⟩ NE
    ⟨ ⟨ mono-env (■ ∷ ■ ∷ []) ⋆-mono ⟨ L , ⟨ M , ptt ⟩ ⟩ okLM , ⋆-cont ⟨ L , ⟨ M , ptt ⟩ ⟩ NE okLM ⟩
    , ⟨ okN , ptt ⟩ ⟩
  where okLM = ⟨ okL , ⟨ okM , ptt ⟩ ⟩

closD-cont : ∀ n → Continuous (∁ (ν (ν ■)) ∷ replicate n ■) (closD n)
closD-cont n ⟨ B , Es ⟩ NE ⟨ okB , oks ⟩ =
  ⋆-cont ⟨ (λ ρ → ΛΛ (⟪ ∁ (ν (ν ■)) ∷ [] ⟫₊ ⟨ B , ptt ⟩ ρ))
         , ⟨ (λ ρ → 𝒯 n (⟪ replicate n ■ ⟫₊ Es ρ)) , ptt ⟩ ⟩ NE
    ⟨ ⟨ (λ _ d d∈ → d∈) , ΛΛ-cont ⟨ B , ptt ⟩ NE ⟨ okB , ptt ⟩ ⟩
    , ⟨ ⟨ mono-env (replicate n ■) (𝒯-mono n) Es oks , 𝒯-cont n Es NE oks ⟩ , ptt ⟩ ⟩

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

Λ-good : ∀ {P} → Good P (ν ■ ∷ []) Λ
Λ-good = mk-good Λ-mono Λ-consis Λ-cont

⋆-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) ⋆
⋆-good = mk-good ⋆-mono ⋆-consis ⋆-cont

pair-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) pair
pair-good = mk-good pair-mono pair-consis pair-cont

car-good : ∀ {P} → Good P (■ ∷ []) car
car-good = mk-good car-mono car-consis car-cont

cdr-good : ∀ {P} → Good P (■ ∷ []) cdr
cdr-good = mk-good cdr-mono cdr-consis cdr-cont

𝒯-good : ∀ {P} n → Good P (replicate n ■) (𝒯 n)
𝒯-good n = mk-good (𝒯-mono n) (𝒯-consis n) (𝒯-cont n)

proj-good : ∀ {P n} (i : Fin n) → Good P (■ ∷ []) (proj i)
proj-good i = mk-good (proj-mono i) (proj-consis i) (proj-cont i)

inl-good : ∀ {P} → Good P (■ ∷ []) inl
inl-good = mk-good inl-mono inl-consis inl-cont

inr-good : ∀ {P} → Good P (■ ∷ []) inr
inr-good = mk-good inr-mono inr-consis inr-cont

𝒞-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞
𝒞-good = mk-good 𝒞-mono 𝒞-consis 𝒞-cont

letD-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ []) letD
letD-good = mk-good letD-mono letD-consis letD-cont

⋆₂-good : ∀ {P} → Good P (■ ∷ ■ ∷ ■ ∷ []) ⋆₂
⋆₂-good = mk-good ⋆₂-mono ⋆₂-consis ⋆₂-cont

ΛΛ-good : ∀ {P} → Good P (∁ (ν (ν ■)) ∷ []) ΛΛ
ΛΛ-good = mk-good ΛΛ-mono ΛΛ-consis ΛΛ-cont

closD-good : ∀ {P} n → Good P (∁ (ν (ν ■)) ∷ replicate n ■) (closD n)
closD-good n = mk-good (closD-mono n) (closD-consis n) (closD-cont n)
