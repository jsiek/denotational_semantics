{-

  The error monad on 𝒫 Value (Framework/GraphModel/ErrorMonad.agda): its
  laws, the monotonicity, consistency and continuity of bind, once, and
  of the operators, derived from those of their kernels (the graph
  model's operators, proof/Framework/GraphModel/{Ops,Continuity}.agda);
  and the lifting of a relation on values through the monad.

  Consistency rests on ω being consistent only with itself: a consistent
  set that holds ω has no value, so a bind does not both err and run
  its continuation; and a value of the wrong kind is inconsistent with
  the values a kernel uses (~-kind), so a kernel does not both err on
  the kind of its operand and succeed.

-}

module proof.Framework.GraphModel.ErrorMonad where

open import Framework.GraphModel.ErrorMonad public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops hiding (strict)
open import proof.Framework.GraphModel.Env using (nonempty-env; _⊆ₑ_)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.Continuity
open import Framework.abt.Sig using (Result; ∁)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Maybe using (Maybe; nothing; just)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

{- ω, kinds and consistency -------------------------------------------------------}

ω~ : ∀ {v} → ω ~ v → v ≡ ω
ω~ {ω} _ = refl

~ω : ∀ {v} → v ~ ω → v ≡ ω
~ω {ω} _ = refl

ω? : ∀ w → w ≡ ω ⊎ w ≢ ω
ω? ω = inj₁ refl
ω? (const k) = inj₂ (λ ())
ω? (V ↦ w) = inj₂ (λ ())
ω? ν = inj₂ (λ ())
ω? ⦅ u , v ⦆ = inj₂ (λ ())
ω? (tup[ i ] d) = inj₂ (λ ())
ω? (left d) = inj₂ (λ ())
ω? (right d) = inj₂ (λ ())
ω? ⟨⟩ = inj₂ (λ ())

{- consistent values are of the same kind -}
~-kind : ∀ d e → d ~ e → kind d ≡ kind e
~-kind (const k) (const k') ⟨ refl , _ ⟩ = refl
~-kind (V ↦ w) (V' ↦ w') _ = refl
~-kind (V ↦ w) ν _ = refl
~-kind ν (V' ↦ w') _ = refl
~-kind ν ν _ = refl
~-kind ω ω _ = refl
~-kind ⦅ u , v ⦆ ⦅ u' , v' ⦆ _ = refl
~-kind (tup[ i ] d) (tup[ j ] e) ⟨ refl , _ ⟩ = refl
~-kind (left d) (left e) _ = refl
~-kind (right d) (right e) _ = refl
~-kind ⟨⟩ ⟨⟩ _ = refl

{- a set without errors -}
Clean : 𝒫 Value → Set
Clean D = ∀ d → d ∈ D → d ≢ ω

{- a set of values: nonempty, without ω -}
Val : 𝒫 Value → Set
Val D = Clean D × nonempty D

AllVal : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
AllVal n Ds = ∀ i → Val (nthD Ds i)

{- a set consistent with one that Errs has no value, and the other way -}
ω-Conv : ∀ {D E} → Every _~_ D E → ω ∈ D → Conv E → ⊥
ω-Conv D~ ω∈ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = d≢ (ω~ (D~ ω d ω∈ d∈))

Conv-ω : ∀ {D E} → Every _~_ D E → Conv D → ω ∈ E → ⊥
Conv-ω D~ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ ω∈ = d≢ (~ω (D~ d ω d∈ ω∈))

{- filters, and the values of a set -------------------------------------------------}

⇂-⊆ : ∀ {D P} → (D ⇂ P) ⊆ D
⇂-⊆ d d∈ = proj₁ d∈

⇂-mono : ∀ {D E P} → D ⊆ E → (D ⇂ P) ⊆ (E ⇂ P)
⇂-mono D⊆ d ⟨ d∈ , p ⟩ = ⟨ D⊆ d d∈ , p ⟩

⇂-~ : ∀ {D E P} → Every _~_ D E → Every _~_ (D ⇂ P) (E ⇂ P)
⇂-~ D~ a b a∈ b∈ = D~ a b (proj₁ a∈) (proj₁ b∈)

⇂-all : ∀ {D P} → (∀ d → d ∈ D → P d) → D ⊆ (D ⇂ P)
⇂-all p d d∈ = ⟨ d∈ , p d d∈ ⟩

⌊⌋-⊆ : ∀ {D} → ⌊ D ⌋ ⊆ D
⌊⌋-⊆ = ⇂-⊆

⌊⌋-mono : ∀ {D E} → D ⊆ E → ⌊ D ⌋ ⊆ ⌊ E ⌋
⌊⌋-mono = ⇂-mono

⌊⌋-clean : ∀ {D} → Clean D → D ⊆ ⌊ D ⌋
⌊⌋-clean = ⇂-all

⌊⌋-~ : ∀ {D E} → Every _~_ D E → Every _~_ ⌊ D ⌋ ⌊ E ⌋
⌊⌋-~ = ⇂-~

Conv-mono : ∀ {D E} → D ⊆ E → Conv D → Conv E
Conv-mono D⊆ ⟨ d , d∈ ⟩ = ⟨ d , ⌊⌋-mono D⊆ d d∈ ⟩

{- Bind: the monad laws, monotonicity and consistency --------------------------------}

{- left unit: bind on a set of values (a computation that returns them) -}
≫=-β : ∀ {D F} → Mono₁ F → Clean D → nonempty D → (D ≫= F) ≃ F D
≫=-β m cl ⟨ d , d∈ ⟩ =
  ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → ⊥-elim (cl ω ω∈ refl) ; w (inj₂ ⟨ _ , w∈ ⟩) → m ⌊⌋-⊆ w w∈ })
  , (λ w w∈ → inj₂ ⟨ ⟨ d , ⟨ d∈ , cl d d∈ ⟩ ⟩ , m (⌊⌋-clean cl) w w∈ ⟩) ⟩

{- right unit -}
≫=-η : ∀ {D} → (D ≫= λ X → X) ≃ D
≫=-η {D} = ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → ω∈ ; w (inj₂ ⟨ _ , w∈ ⟩) → proj₁ w∈ }) , G ⟩
  where
  G : D ⊆ (D ≫= λ X → X)
  G w w∈ with ω? w
  ... | inj₁ refl = inj₁ ⟨ refl , w∈ ⟩
  ... | inj₂ w≢ = inj₂ ⟨ ⟨ w , ⟨ w∈ , w≢ ⟩ ⟩ , ⟨ w∈ , w≢ ⟩ ⟩

{- associativity -}
≫=-assoc : ∀ {D F G} → Mono₁ G → ((D ≫= F) ≫= G) ≃ (D ≫= λ X → F X ≫= G)
≫=-assoc {D} {F} {G} m = ⟨ A , B ⟩
  where
  ⌊≫=⌋ : Conv D → ⌊ D ≫= F ⌋ ≃ ⌊ F ⌊ D ⌋ ⌋
  ⌊≫=⌋ c = ⟨ (λ { u ⟨ inj₁ ⟨ refl , _ ⟩ , u≢ ⟩ → ⊥-elim (u≢ refl) ; u ⟨ inj₂ ⟨ _ , u∈ ⟩ , u≢ ⟩ → ⟨ u∈ , u≢ ⟩ })
           , (λ u u∈ → ⟨ inj₂ ⟨ c , proj₁ u∈ ⟩ , proj₂ u∈ ⟩) ⟩
  A : ((D ≫= F) ≫= G) ⊆ (D ≫= λ X → F X ≫= G)
  A w (inj₁ ⟨ refl , inj₁ ⟨ _ , ω∈ ⟩ ⟩) = inj₁ ⟨ refl , ω∈ ⟩
  A w (inj₁ ⟨ refl , inj₂ ⟨ c , ω∈ ⟩ ⟩) = inj₂ ⟨ c , inj₁ ⟨ refl , ω∈ ⟩ ⟩
  A w (inj₂ ⟨ ⟨ u , ⟨ inj₁ ⟨ refl , _ ⟩ , u≢ ⟩ ⟩ , _ ⟩) = ⊥-elim (u≢ refl)
  A w (inj₂ ⟨ ⟨ u , ⟨ inj₂ ⟨ c , u∈ ⟩ , u≢ ⟩ ⟩ , w∈ ⟩) =
    inj₂ ⟨ c , inj₂ ⟨ ⟨ u , ⟨ u∈ , u≢ ⟩ ⟩ , m (proj₁ (⌊≫=⌋ c)) w w∈ ⟩ ⟩
  B : (D ≫= λ X → F X ≫= G) ⊆ ((D ≫= F) ≫= G)
  B w (inj₁ ⟨ refl , ω∈ ⟩) = inj₁ ⟨ refl , inj₁ ⟨ refl , ω∈ ⟩ ⟩
  B w (inj₂ ⟨ c , inj₁ ⟨ refl , ω∈ ⟩ ⟩) = inj₁ ⟨ refl , inj₂ ⟨ c , ω∈ ⟩ ⟩
  B w (inj₂ ⟨ c , inj₂ ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ ⟩) =
    inj₂ ⟨ ⟨ u , proj₂ (⌊≫=⌋ c) u u∈ ⟩ , m (proj₂ (⌊≫=⌋ c)) w w∈ ⟩

≫=-mono : ∀ {D D' F F'} → D ⊆ D' → (∀ {X X'} → X ⊆ X' → F X ⊆ F' X') → (D ≫= F) ⊆ (D' ≫= F')
≫=-mono D⊆ F⊆ w (inj₁ ⟨ refl , ω∈ ⟩) = inj₁ ⟨ refl , D⊆ ω ω∈ ⟩
≫=-mono D⊆ F⊆ w (inj₂ ⟨ c , w∈ ⟩) = inj₂ ⟨ Conv-mono D⊆ c , F⊆ (⌊⌋-mono D⊆) w w∈ ⟩

≫=-consis : ∀ {D D' F F'} → Every _~_ D D' → (∀ {X X'} → Every _~_ X X' → Every _~_ (F X) (F' X'))
  → Every _~_ (D ≫= F) (D' ≫= F')
≫=-consis D~ F~ u w (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
≫=-consis D~ F~ u w (inj₁ ⟨ refl , ω∈ ⟩) (inj₂ ⟨ c , _ ⟩) = ⊥-elim (ω-Conv D~ ω∈ c)
≫=-consis D~ F~ u w (inj₂ ⟨ c , _ ⟩) (inj₁ ⟨ refl , ω∈ ⟩) = ⊥-elim (Conv-ω D~ c ω∈)
≫=-consis D~ F~ u w (inj₂ ⟨ _ , u∈ ⟩) (inj₂ ⟨ _ , w∈ ⟩) = F~ (⌊⌋-~ D~) u w u∈ w∈

≫=-clean : ∀ {D F} → Clean D → Clean (F ⌊ D ⌋) → Clean (D ≫= F)
≫=-clean cD cF .ω (inj₁ ⟨ refl , ω∈ ⟩) refl = cD ω ω∈ refl
≫=-clean cD cF w (inj₂ ⟨ _ , w∈ ⟩) = cF w w∈

{- Lifting a relation through the monad -------------------------------------------------}

{- a consistent set with a value has no error -}
con-clean : ∀ {D} → Con D → Conv D → Clean D
con-clean cD c .ω ω∈ refl = Conv-ω cD c ω∈

{- a relation S between a value and a set, as the forward relations of the
   passes are: ω is related to the sets that hold ω, a value only to sets
   that have a value, and S is monotone in its set -}
record LiftRel (S : Value → 𝒫 Value → Set₁) : Set₁ where
  field
    ω→ : ∀ {D'} → S ω D' → ω ∈ D'
    →ω : ∀ {D'} → ω ∈ D' → S ω D'
    S-mono : ∀ {d D₁ D₂} → D₁ ⊆ D₂ → S d D₁ → S d D₂
    S-val : ∀ {d D'} → d ≢ ω → S d D' → Conv D'

{- each element of D is related to D' -}
Lifted : (Value → 𝒫 Value → Set₁) → 𝒫 Value → 𝒫 Value → Set₁
Lifted S D D' = ∀ d → d ∈ D → S d D'

{- bind preserves lifted relations: its continuations need only be related
   on the values of related sets -}
≫=-lift : ∀ {S D D' F F'} → LiftRel S → Con D' → Lifted S D D'
  → (Conv D → Conv D' → Lifted S ⌊ D ⌋ ⌊ D' ⌋ → Lifted S (F ⌊ D ⌋) (F' ⌊ D' ⌋))
  → Lifted S (D ≫= F) (D' ≫= F')
≫=-lift L cD' hD hF w (inj₁ ⟨ refl , ω∈ ⟩) = LiftRel.→ω L (inj₁ ⟨ refl , LiftRel.ω→ L (hD ω ω∈) ⟩)
≫=-lift L cD' hD hF w (inj₂ ⟨ c@(⟨ d , ⟨ d∈ , d≢ ⟩ ⟩) , w∈ ⟩) =
  S-mono (λ x x∈ → inj₂ ⟨ c' , x∈ ⟩) (hF c c' (λ a a∈ → S-mono (⌊⌋-clean (con-clean cD' c')) (hD a (proj₁ a∈))) w w∈)
  where open LiftRel L
        c' = S-val d≢ (hD d d∈)

{- the check of a kernel --------------------------------------------------------------}

{- every element of A that is not ω uses a value of kind k in X -}
Needs : Kind → 𝒫 Value → 𝒫 Value → Set
Needs k X A = ∀ w → w ∈ A → w ≡ ω ⊎ Σ[ u ∈ Value ] u ∈ X × kind u ≡ k

≫=-needs : ∀ {k X D F} → (∀ {Y} → Needs k X (F Y)) → Needs k X (D ≫= F)
≫=-needs h w (inj₁ ⟨ refl , _ ⟩) = inj₁ refl
≫=-needs h w (inj₂ ⟨ _ , w∈ ⟩) = h w w∈

checked-mono : ∀ {k X X' A A'} → X ⊆ X' → A ⊆ A' → checked k X A ⊆ checked k X' A'
checked-mono X⊆ A⊆ w (inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩) = inj₁ ⟨ refl , ⟨ d , ⟨ X⊆ d d∈ , dk ⟩ ⟩ ⟩
checked-mono X⊆ A⊆ w (inj₂ w∈) = inj₂ (A⊆ w w∈)

checked-consis : ∀ {k X X' A A'} → Every _~_ X X' → Every _~_ A A' → Needs k X A → Needs k X' A'
  → Every _~_ (checked k X A) (checked k X' A')
checked-consis X~ A~ n n' u w (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
checked-consis X~ A~ n n' u w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) (inj₂ w∈) with n' w w∈
... | inj₁ refl = tt
... | inj₂ ⟨ v , ⟨ v∈ , vk ⟩ ⟩ = ⊥-elim (ek (trans (~-kind e v (X~ e v e∈ v∈)) vk))
checked-consis X~ A~ n n' u w (inj₂ u∈) (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) with n u u∈
... | inj₁ refl = tt
... | inj₂ ⟨ v , ⟨ v∈ , vk ⟩ ⟩ = ⊥-elim (ek (trans (sym (~-kind v e (X~ v e v∈ e∈))) vk))
checked-consis X~ A~ n n' u w (inj₂ u∈) (inj₂ w∈) = A~ u w u∈ w∈

{- the check passes on a set of values of kind k -}
checked-ok : ∀ {k X A} → (∀ d → d ∈ X → kind d ≡ k) → checked k X A ≃ A
checked-ok ok = ⟨ (λ { w (inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩) → ⊥-elim (dk (ok d d∈)) ; w (inj₂ w∈) → w∈ })
                , (λ w w∈ → inj₂ w∈) ⟩

{- Continuity --------------------------------------------------------------------------}

⇂-cont : ∀ {E : VEnv → 𝒫 Value} {P ρ} → Cont E ρ → Cont (λ ρ → E ρ ⇂ P) ρ
⇂-cont c w ⟨ w∈ , p ⟩ with c w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ w∈′ , p ⟩ ⟩ ⟩ ⟩

⇂-ok : ∀ {E : VEnv → 𝒫 Value} {P ρ} → Mono E × Cont E ρ → Mono (λ ρ → E ρ ⇂ P) × Cont (λ ρ → E ρ ⇂ P) ρ
⇂-ok ⟨ m , c ⟩ = ⟨ (λ ρ⊆ → ⇂-mono (m ρ⊆)) , ⇂-cont c ⟩

⌊⌋-cont : ∀ {E : VEnv → 𝒫 Value} {ρ} → Cont E ρ → Cont (λ ρ → ⌊ E ρ ⌋) ρ
⌊⌋-cont = ⇂-cont

⌊⌋-ok : ∀ {E : VEnv → 𝒫 Value} {ρ} → Mono E × Cont E ρ → Mono (λ ρ → ⌊ E ρ ⌋) × Cont (λ ρ → ⌊ E ρ ⌋) ρ
⌊⌋-ok = ⇂-ok

{- a bind is continuous when its operand is, and its continuation is,
   on the values of the operand -}
{- (its continuation need only be continuous when the operand has a value) -}
≫=-cont′ : ∀ {E : VEnv → 𝒫 Value} {G : VEnv → 𝒫 Value → 𝒫 Value} {ρ} → Mono E → Cont E ρ
  → (∀ {ρ₁ ρ₂ X Y} → ρ₁ ⊆ₑ ρ₂ → X ⊆ Y → G ρ₁ X ⊆ G ρ₂ Y) → (Conv (E ρ) → Cont (λ ρ → G ρ ⌊ E ρ ⌋) ρ)
  → Cont (λ ρ → E ρ ≫= G ρ) ρ
≫=-cont′ {E} {G} mE cE mG cG w (inj₁ ⟨ refl , ω∈ ⟩) with one E cE ω∈
... | ⟨ a , ω∈′ ⟩ = done (λ ρ → E ρ ≫= G ρ) a ω (inj₁ ⟨ refl , ω∈′ ⟩)
≫=-cont′ {E} {G} mE cE mG cG w (inj₂ ⟨ ⟨ d , d∈ ⟩ , w∈ ⟩)
    with one (λ ρ → ⌊ E ρ ⌋) (⌊⌋-cont cE) d∈ | one (λ ρ → G ρ ⌊ E ρ ⌋) (cG ⟨ d , d∈ ⟩) w∈
... | ⟨ a , d∈′ ⟩ | ⟨ b , w∈′ ⟩ =
  done (λ ρ → E ρ ≫= G ρ) (approx-join a b) w
    (inj₂ ⟨ ⟨ d , ⌊⌋-mono (mE (join-l a b)) d d∈′ ⟩ , mG (join-r a b) (⌊⌋-mono (mE (join-r a b))) w w∈′ ⟩)

≫=-cont : ∀ {E : VEnv → 𝒫 Value} {G : VEnv → 𝒫 Value → 𝒫 Value} {ρ} → Mono E → Cont E ρ
  → (∀ {ρ₁ ρ₂ X Y} → ρ₁ ⊆ₑ ρ₂ → X ⊆ Y → G ρ₁ X ⊆ G ρ₂ Y) → Cont (λ ρ → G ρ ⌊ E ρ ⌋) ρ
  → Cont (λ ρ → E ρ ≫= G ρ) ρ
≫=-cont mE cE mG cG = ≫=-cont′ mE cE mG (λ _ → cG)

checked-cont : ∀ {k} {X A : VEnv → 𝒫 Value} {ρ} → Cont X ρ → Cont A ρ → Cont (λ ρ → checked k (X ρ) (A ρ)) ρ
checked-cont {k} {X} {A} cX cA w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) with one X cX e∈
... | ⟨ a , e∈′ ⟩ = done (λ ρ → checked k (X ρ) (A ρ)) a ω (inj₁ ⟨ refl , ⟨ e , ⟨ e∈′ , ek ⟩ ⟩ ⟩)
checked-cont cX cA w (inj₂ w∈) with cA w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ w∈′ ⟩ ⟩ ⟩

{- Operators: kernels under binds ------------------------------------------------------}

{- an operator strict in its first operand, and the check of the kind of
   that operand; the operators of ErrorMonad.agda are these combinations
   of the graph model's operators, by definition -}
strict : ∀ {bs} → DOp (𝒫 Value) (■ ∷ bs) → DOp (𝒫 Value) (■ ∷ bs)
strict g ⟨ D , Ds ⟩ = D ≫= λ X → g ⟨ X , Ds ⟩

checkₒ : ∀ {bs} → Kind → DOp (𝒫 Value) (■ ∷ bs) → DOp (𝒫 Value) (■ ∷ bs)
checkₒ k g ⟨ X , Ds ⟩ = checked k X (g ⟨ X , Ds ⟩)

swap : ∀ {bs} → DOp (𝒫 Value) (■ ∷ ■ ∷ bs) → DOp (𝒫 Value) (■ ∷ ■ ∷ bs)
swap g ⟨ D , ⟨ E , Ds ⟩ ⟩ = g ⟨ E , ⟨ D , Ds ⟩ ⟩

{- strict in the second operand -}
strict₂ : ∀ {bs} → DOp (𝒫 Value) (■ ∷ ■ ∷ bs) → DOp (𝒫 Value) (■ ∷ ■ ∷ bs)
strict₂ {bs} g = swap {bs} (strict {■ ∷ bs} (swap {bs} g))

⟪⟫₊-mono : ∀ bs (Es : Bodies bs) {ρ₁} → OK bs Es ρ₁ → ∀ {ρ ρ′} → ρ ⊆ₑ ρ′
  → results-rel-pres _⊆_ bs (⟪ bs ⟫₊ Es ρ) (⟪ bs ⟫₊ Es ρ′)
⟪⟫₊-mono [] _ _ _ = ptt
⟪⟫₊-mono (b ∷ bs) ⟨ E , Es ⟩ ⟨ ⟨ m , _ ⟩ , ok ⟩ ρ⊆ = ⟨ ⟪⟫-mono b m ρ⊆ , ⟪⟫₊-mono bs Es ok ρ⊆ ⟩

strict-good : ∀ {P bs} {g : DOp (𝒫 Value) (■ ∷ bs)} → Good P (■ ∷ bs) g → Good P (■ ∷ bs) (strict g)
strict-good {bs = bs} {g} G = record
  { mono = λ { _ _ ⟨ lift D⊆ , Ds⊆ ⟩ → lift (≫=-mono D⊆ λ X⊆ → lower (mono G _ _ ⟨ lift X⊆ , Ds⊆ ⟩)) }
  ; consis = λ p → λ { _ _ ⟨ lift D~ , Ds~ ⟩ → lift (≫=-consis D~ λ X~ → lower (consis G p _ _ ⟨ lift X~ , Ds~ ⟩)) }
  ; cont = λ { ⟨ E , Es ⟩ NE ⟨ ok₁@(⟨ m , c ⟩) , ok ⟩ →
      ≫=-cont m c (λ ρ⊆ X⊆ → lower (mono G _ _ ⟨ lift X⊆ , ⟪⟫₊-mono bs Es ok ρ⊆ ⟩))
        (cont G ⟨ (λ ρ → ⌊ E ρ ⌋) , Es ⟩ NE ⟨ ⌊⌋-ok ok₁ , ok ⟩) } }

checkₒ-good : ∀ {P bs k} {g : DOp (𝒫 Value) (■ ∷ bs)} → Good P (■ ∷ bs) g
  → (∀ {X Ds} → Needs k X (g ⟨ X , Ds ⟩)) → Good P (■ ∷ bs) (checkₒ k g)
checkₒ-good G n = record
  { mono = λ { _ _ Ds⊆@(⟨ lift X⊆ , _ ⟩) → lift (checked-mono X⊆ (lower (mono G _ _ Ds⊆))) }
  ; consis = λ p → λ { _ _ Ds~@(⟨ lift X~ , _ ⟩) → lift (checked-consis X~ (lower (consis G p _ _ Ds~)) n n) }
  ; cont = λ { Es@(⟨ E , _ ⟩) NE ok@(⟨ ⟨ _ , c ⟩ , _ ⟩) → checked-cont c (cont G Es NE ok) } }

swap-good : ∀ {P bs} {g : DOp (𝒫 Value) (■ ∷ ■ ∷ bs)} → Good P (■ ∷ ■ ∷ bs) g → Good P (■ ∷ ■ ∷ bs) (swap g)
swap-good G = record
  { mono = λ { ⟨ D , ⟨ E , Ds ⟩ ⟩ ⟨ D' , ⟨ E' , Ds' ⟩ ⟩ ⟨ r , ⟨ s , t ⟩ ⟩ → mono G ⟨ E , ⟨ D , Ds ⟩ ⟩ ⟨ E' , ⟨ D' , Ds' ⟩ ⟩ ⟨ s , ⟨ r , t ⟩ ⟩ }
  ; consis = λ p → λ { ⟨ D , ⟨ E , Ds ⟩ ⟩ ⟨ D' , ⟨ E' , Ds' ⟩ ⟩ ⟨ r , ⟨ s , t ⟩ ⟩ →
      consis G p ⟨ E , ⟨ D , Ds ⟩ ⟩ ⟨ E' , ⟨ D' , Ds' ⟩ ⟩ ⟨ s , ⟨ r , t ⟩ ⟩ }
  ; cont = λ { ⟨ E₁ , ⟨ E₂ , Es ⟩ ⟩ NE ⟨ o₁ , ⟨ o₂ , os ⟩ ⟩ → cont G ⟨ E₂ , ⟨ E₁ , Es ⟩ ⟩ NE ⟨ o₂ , ⟨ o₁ , os ⟩ ⟩ } }

{- a filter of the result, and of the first operand -}
⇂-good : ∀ {P bs Q} {g : DOp (𝒫 Value) bs} → Good P bs g → Good P bs (λ Ds → g Ds ⇂ Q)
⇂-good G = record
  { mono = λ Ds Es r → lift (⇂-mono (lower (mono G Ds Es r)))
  ; consis = λ p Ds Es r → lift (⇂-~ (lower (consis G p Ds Es r)))
  ; cont = λ Es NE ok → ⇂-cont (cont G Es NE ok) }

in⇂-good : ∀ {P bs Q} {g : DOp (𝒫 Value) (■ ∷ bs)} → Good P (■ ∷ bs) g
  → Good P (■ ∷ bs) (λ { ⟨ X , Ds ⟩ → g ⟨ X ⇂ Q , Ds ⟩ })
in⇂-good G = record
  { mono = λ { _ _ ⟨ lift X⊆ , r ⟩ → mono G _ _ ⟨ lift (⇂-mono X⊆) , r ⟩ }
  ; consis = λ p → λ { _ _ ⟨ lift X~ , r ⟩ → consis G p _ _ ⟨ lift (⇂-~ X~) , r ⟩ }
  ; cont = λ { ⟨ E , Es ⟩ NE ⟨ ok₁ , ok ⟩ → cont G ⟨ (λ ρ → E ρ ⇂ _) , Es ⟩ NE ⟨ ⇂-ok ok₁ , ok ⟩ } }

strict₂-good : ∀ {P bs} {g : DOp (𝒫 Value) (■ ∷ ■ ∷ bs)} → Good P (■ ∷ ■ ∷ bs) g → Good P (■ ∷ ■ ∷ bs) (strict₂ g)
strict₂-good G = swap-good (strict-good (swap-good G))

{- n operands, bound left to right -}
⊆s-refl : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → results-rel-pres _⊆_ (replicate n ■) Ds Ds
⊆s-refl zero _ = ptt
⊆s-refl (suc n) ⟨ D , Ds ⟩ = ⟨ lift (λ d z → z) , ⊆s-refl n Ds ⟩

Rel⊆ : ∀ n → (Results (𝒫 Value) (replicate n ■) → 𝒫 Value) → (Results (𝒫 Value) (replicate n ■) → 𝒫 Value) → Set₁
Rel⊆ n K K' = ∀ {Xs Ys} → results-rel-pres _⊆_ (replicate n ■) Xs Ys → K Xs ⊆ K' Ys

binds-mono : ∀ n {Ds Ds' K K'} → results-rel-pres _⊆_ (replicate n ■) Ds Ds' → Rel⊆ n K K'
  → binds n Ds K ⊆ binds n Ds' K'
binds-mono zero _ mK = mK ptt
binds-mono (suc n) ⟨ lift D⊆ , Ds⊆ ⟩ mK = ≫=-mono D⊆ (λ X⊆ → binds-mono n Ds⊆ (λ Xs⊆ → mK ⟨ lift X⊆ , Xs⊆ ⟩))

binds-consis : ∀ n {Ds Ds' K K'} → results-rel-pres (Every _~_) (replicate n ■) Ds Ds'
  → (∀ {Xs Ys} → results-rel-pres (Every _~_) (replicate n ■) Xs Ys → Every _~_ (K Xs) (K' Ys))
  → Every _~_ (binds n Ds K) (binds n Ds' K')
binds-consis zero _ cK = cK ptt
binds-consis (suc n) ⟨ lift D~ , Ds~ ⟩ cK = ≫=-consis D~ (λ X~ → binds-consis n Ds~ (λ Xs~ → cK ⟨ lift X~ , Xs~ ⟩))

{- (its continuation need only be continuous when the operands have values) -}
binds-cont′ : ∀ n (Es : Bodies (replicate n ■)) {K : VEnv → Results (𝒫 Value) (replicate n ■) → 𝒫 Value} {ρ}
  → nonempty-env ρ → OK (replicate n ■) Es ρ
  → (∀ {ρ₁ ρ₂ Xs Ys} → ρ₁ ⊆ₑ ρ₂ → results-rel-pres _⊆_ (replicate n ■) Xs Ys → K ρ₁ Xs ⊆ K ρ₂ Ys)
  → (∀ Ms → OK (replicate n ■) Ms ρ → (∀ i → nonempty (nthD (⟪ replicate n ■ ⟫₊ Ms ρ) i))
       → Cont (λ ρ → K ρ (⟪ replicate n ■ ⟫₊ Ms ρ)) ρ)
  → Cont (λ ρ → binds n (⟪ replicate n ■ ⟫₊ Es ρ) (K ρ)) ρ
binds-cont′ zero Es NE ok mK cK = cK ptt ptt (λ ())
binds-cont′ (suc n) ⟨ E , Es ⟩ NE ⟨ ok₁@(⟨ m , c ⟩) , ok ⟩ mK cK =
  ≫=-cont′ m c (λ ρ⊆ X⊆ → binds-mono n (⟪⟫₊-mono (replicate n ■) Es ok ρ⊆) (λ Xs⊆ → mK ρ⊆ ⟨ lift X⊆ , Xs⊆ ⟩))
    (λ cv → binds-cont′ n Es NE ok (λ ρ⊆ Xs⊆ → mK ρ⊆ ⟨ lift (⌊⌋-mono (m ρ⊆)) , Xs⊆ ⟩)
       (λ Ms okM ne → cK ⟨ (λ ρ → ⌊ E ρ ⌋) , Ms ⟩ ⟨ ⌊⌋-ok ok₁ , okM ⟩ (λ { zero → cv ; (suc i) → ne i })))

binds-cont : ∀ n (Es : Bodies (replicate n ■)) {K : VEnv → Results (𝒫 Value) (replicate n ■) → 𝒫 Value} {ρ}
  → nonempty-env ρ → OK (replicate n ■) Es ρ
  → (∀ {ρ₁ ρ₂ Xs Ys} → ρ₁ ⊆ₑ ρ₂ → results-rel-pres _⊆_ (replicate n ■) Xs Ys → K ρ₁ Xs ⊆ K ρ₂ Ys)
  → (∀ Ms → OK (replicate n ■) Ms ρ → Cont (λ ρ → K ρ (⟪ replicate n ■ ⟫₊ Ms ρ)) ρ)
  → Cont (λ ρ → binds n (⟪ replicate n ■ ⟫₊ Es ρ) (K ρ)) ρ
binds-cont n Es NE ok mK cK = binds-cont′ n Es NE ok mK (λ Ms okM _ → cK Ms okM)

{- left unit, for n operands that have values and no errors -}
binds-β : ∀ n {Ds K} → Rel⊆ n K K → AllVal n Ds → binds n Ds K ≃ K Ds
binds-β zero mK _ = ≃-refl
binds-β (suc n) {⟨ D , Ds ⟩} mK cn =
  ≃-trans (≫=-β (λ X⊆ → binds-mono n (⊆s-refl n Ds) (λ Xs⊆ → mK ⟨ lift X⊆ , Xs⊆ ⟩)) (proj₁ (cn zero)) (proj₂ (cn zero)))
          (binds-β n (λ Xs⊆ → mK ⟨ lift (λ d z → z) , Xs⊆ ⟩) (λ i → cn (suc i)))

{- equal operands, and continuations equal on their values -}
≫=-≃ : ∀ {D D' F F'} → D ≃ D' → (Conv D → Conv D' → F ⌊ D ⌋ ≃ F' ⌊ D' ⌋) → (D ≫= F) ≃ (D' ≫= F')
≫=-≃ ⟨ D⊆ , D⊇ ⟩ eq =
  ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , D⊆ ω ω∈ ⟩
       ; w (inj₂ ⟨ c , w∈ ⟩) → inj₂ ⟨ Conv-mono D⊆ c , proj₁ (eq c (Conv-mono D⊆ c)) w w∈ ⟩ })
  , (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , D⊇ ω ω∈ ⟩
       ; w (inj₂ ⟨ c' , w∈ ⟩) → inj₂ ⟨ Conv-mono D⊇ c' , proj₂ (eq (Conv-mono D⊇ c') c') w w∈ ⟩ }) ⟩

{- the left unit on a set of values, at its values: no monotonicity needed -}
≫=-val-β : ∀ {D F} → Val D → (D ≫= F) ≃ F ⌊ D ⌋
≫=-val-β ⟨ cl , ⟨ d , d∈ ⟩ ⟩ =
  ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → ⊥-elim (cl ω ω∈ refl) ; w (inj₂ ⟨ _ , w∈ ⟩) → w∈ })
  , (λ w w∈ → inj₂ ⟨ ⟨ d , ⟨ d∈ , cl d d∈ ⟩ ⟩ , w∈ ⟩) ⟩

≫=-cong : ∀ {D F F'} → (Conv D → F ⌊ D ⌋ ≃ F' ⌊ D ⌋) → (D ≫= F) ≃ (D ≫= F')
≫=-cong eq = ⟨ (λ { w (inj₁ e) → inj₁ e ; w (inj₂ ⟨ c , w∈ ⟩) → inj₂ ⟨ c , proj₁ (eq c) w w∈ ⟩ })
             , (λ { w (inj₁ e) → inj₁ e ; w (inj₂ ⟨ c , w∈ ⟩) → inj₂ ⟨ c , proj₂ (eq c) w w∈ ⟩ }) ⟩

{- the bound operands: values of the operands -}
Bound : ∀ n → Results (𝒫 Value) (replicate n ■) → Results (𝒫 Value) (replicate n ■) → Set
Bound n Xs Ds = ∀ i → nthD Xs i ⊆ nthD Ds i × Clean (nthD Xs i) × nonempty (nthD Xs i)

binds-cong : ∀ n {Ds K K'} → (∀ {Xs} → Bound n Xs Ds → K Xs ≃ K' Xs) → binds n Ds K ≃ binds n Ds K'
binds-cong zero eq = eq (λ ())
binds-cong (suc n) {⟨ D , Ds ⟩} {K} {K'} eq =
  ≫=-cong {D} {λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {λ X → binds n Ds (λ Xs → K' ⟨ X , Xs ⟩)} λ { ⟨ d , d∈ ⟩ → binds-cong n λ b → eq λ { zero → ⟨ ⌊⌋-⊆ , ⟨ (λ e e∈ → proj₂ e∈) , ⟨ d , d∈ ⟩ ⟩ ⟩ ; (suc i) → b i } }

binds-assoc : ∀ n {Ds K G} → Mono₁ G → (binds n Ds K ≫= G) ≃ binds n Ds (λ Xs → K Xs ≫= G)
binds-assoc zero m = ≃-refl
binds-assoc (suc n) {⟨ D , Ds ⟩} {K} {G} m =
  ≃-trans (≫=-assoc {D} {λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {G} m) (≫=-cong {D} {λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩) ≫= G} {λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩ ≫= G)} (λ _ → binds-assoc n m))

{- The operators are Good -------------------------------------------------------------}

⋆-needs : ∀ {F X} → Needs fun F (⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩)
⋆-needs w ⟨ V , ⟨ f∈ , _ ⟩ ⟩ = inj₂ ⟨ V ↦ w , ⟨ f∈ , refl ⟩ ⟩

Λᵐ-good : ∀ {P} → Good P (ν ■ ∷ []) Λᵐ
Λᵐ-good = ⇂-good Λ-good

⋆ᵐ-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) ⋆ᵐ
⋆ᵐ-good = strict-good (checkₒ-good (strict₂-good ⋆-good) (λ {X} {Ds} → ≫=-needs {D = proj₁ Ds} (λ {Y} → ⋆-needs {X} {Y})))

{- n binds of the operands of a Good kernel -}
binds-good : ∀ {P} n {g : DOp (𝒫 Value) (replicate n ■)} → Good P (replicate n ■) g
  → Good P (replicate n ■) (λ Ds → binds n Ds g)
binds-good n G = record
  { mono = λ _ _ Ds⊆ → lift (binds-mono n Ds⊆ (λ Xs⊆ → lower (mono G _ _ Xs⊆)))
  ; consis = λ p _ _ Ds~ → lift (binds-consis n Ds~ (λ Xs~ → lower (consis G p _ _ Xs~)))
  ; cont = λ Es NE ok → binds-cont n Es NE ok (λ _ Xs⊆ → lower (mono G _ _ Xs⊆)) (λ Ms okM → cont G Ms NE okM) }

𝒯ᵐ-good : ∀ {P} n → Good P (replicate n ■) (𝒯ᵐ n)
𝒯ᵐ-good n = binds-good n (𝒯-good n)

projᵐ-good : ∀ {P n} (i : Fin n) → Good P (■ ∷ []) (projᵐ i)
projᵐ-good i = strict-good (checkₒ-good (proj-good i) (λ d d∈ → inj₂ ⟨ _ , ⟨ d∈ , refl ⟩ ⟩))

inlᵐ-good : ∀ {P} → Good P (■ ∷ []) inlᵐ
inlᵐ-good = strict-good inl-good

inrᵐ-good : ∀ {P} → Good P (■ ∷ []) inrᵐ
inrᵐ-good = strict-good inr-good

𝒞-needs : ∀ {X Q F G} → Needs inj X (𝒞 ⟨ X ⇂ Q , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩)
𝒞-needs w (inj₁ ⟨ v , ⟨ V , ⟨ ls , _ ⟩ ⟩ ⟩) = inj₂ ⟨ left v , ⟨ proj₁ (ls v (here refl)) , refl ⟩ ⟩
𝒞-needs w (inj₂ ⟨ v , ⟨ V , ⟨ rs , _ ⟩ ⟩ ⟩) = inj₂ ⟨ right v , ⟨ proj₁ (rs v (here refl)) , refl ⟩ ⟩

𝒞ᵐ-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞ᵐ
𝒞ᵐ-good = strict-good (checkₒ-good (in⇂-good {Q = ValPayload} 𝒞-good) (λ {X} {Ds} → 𝒞-needs {X} {ValPayload} {proj₁ Ds} {proj₁ (proj₂ Ds)}))

letᵐ-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ []) letᵐ
letᵐ-good {P} = record
  { mono = λ { ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D⊆ , ⟨ F⊆ , _ ⟩ ⟩ →
      mono (⋆ᵐ-good {P}) _ _ ⟨ mono (Λᵐ-good {P}) ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F⊆ , ptt ⟩ , ⟨ D⊆ , ptt ⟩ ⟩ }
  ; consis = λ p → λ { ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ →
      consis (⋆ᵐ-good {P}) p _ _ ⟨ consis (Λᵐ-good {P}) p ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩ }
  ; cont = λ { ⟨ M , ⟨ N , _ ⟩ ⟩ NE ⟨ okM , ⟨ okN , _ ⟩ ⟩ →
      cont (⋆ᵐ-good {P}) ⟨ (λ ρ → Λᵐ ⟨ (λ X → N (X • ρ)) , ptt ⟩) , ⟨ M , ptt ⟩ ⟩ NE
        ⟨ ⟨ mono-env (ν ■ ∷ []) (mono (Λᵐ-good {P})) ⟨ N , ptt ⟩ ⟨ okN , ptt ⟩ , cont (Λᵐ-good {P}) ⟨ N , ptt ⟩ NE ⟨ okN , ptt ⟩ ⟩
        , ⟨ okM , ptt ⟩ ⟩ } }

{- Congruences ----------------------------------------------------------------------}

⋆ᵐ-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → ⋆ᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ᵐ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
⋆ᵐ-≃ D≃ E≃ = mono-≃ (mono (⋆ᵐ-good {⊤})) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

𝒯ᵐ-≃ : ∀ n {Ds Es} → (∀ i → nthD Ds i ≃ nthD Es i) → 𝒯ᵐ n Ds ≃ 𝒯ᵐ n Es
𝒯ᵐ-≃ n {Ds} {Es} eq = mono-≃ (mono (𝒯ᵐ-good {⊤} n)) (nthD⇒RRs Ds Es eq)

projᵐ-≃ : ∀ {n} (i : Fin n) {D E} → D ≃ E → projᵐ i ⟨ D , ptt ⟩ ≃ projᵐ i ⟨ E , ptt ⟩
projᵐ-≃ i D≃ = mono-≃ (mono (projᵐ-good {⊤} i)) ⟨ lift D≃ , ptt ⟩

inlᵐ-≃ : ∀ {D E} → D ≃ E → inlᵐ ⟨ D , ptt ⟩ ≃ inlᵐ ⟨ E , ptt ⟩
inlᵐ-≃ D≃ = mono-≃ (mono (inlᵐ-good {⊤})) ⟨ lift D≃ , ptt ⟩

inrᵐ-≃ : ∀ {D E} → D ≃ E → inrᵐ ⟨ D , ptt ⟩ ≃ inrᵐ ⟨ E , ptt ⟩
inrᵐ-≃ D≃ = mono-≃ (mono (inrᵐ-good {⊤})) ⟨ lift D≃ , ptt ⟩

{- the binders are equal when their bodies are, on finite sets of values -}
BodyEq : (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → Set
BodyEq F F' = ∀ V → V ≢ [] → V ≈ V → NoErr V → F (mem V) ≃ F' (mem V)

Λᵐ-≃ : ∀ {F F'} → BodyEq F F' → Λᵐ ⟨ F , ptt ⟩ ≃ Λᵐ ⟨ F' , ptt ⟩
Λᵐ-≃ eq = ⟨ G (λ V a b c → proj₁ (eq V a b c)) , G (λ V a b c → proj₂ (eq V a b c)) ⟩
  where
  G : ∀ {A B} → (∀ V → V ≢ [] → V ≈ V → NoErr V → A (mem V) ⊆ B (mem V)) → Λᵐ ⟨ A , ptt ⟩ ⊆ Λᵐ ⟨ B , ptt ⟩
  G h ν r = r
  G h (V ↦ w) ⟨ ⟨ w∈ , ⟨ ne , c ⟩ ⟩ , n ⟩ = ⟨ ⟨ h V ne c n w w∈ , ⟨ ne , c ⟩ ⟩ , n ⟩

letᵐ-≃ : ∀ {D D' F F'} → D ≃ D' → BodyEq F F' → letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letᵐ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letᵐ-≃ D≃ F≃ = ⋆ᵐ-≃ (Λᵐ-≃ F≃) D≃

BodyIn : (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → Set
BodyIn F F' = ∀ V → V ≢ [] → V ≈ V → NoErr V → F (mem V) ⊆ F' (mem V)

𝒞⇂-⊆ : ∀ {X X' A A' B B'} → X ⊆ X' → BodyIn A A' → BodyIn B B'
  → 𝒞 ⟨ X ⇂ ValPayload , ⟨ A , ⟨ B , ptt ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ X' ⇂ ValPayload , ⟨ A' , ⟨ B' , ptt ⟩ ⟩ ⟩
𝒞⇂-⊆ X⊆ A⊆ B⊆ w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
  inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⇂-mono {P = ValPayload} X⊆ _ (all d d∈)) , ⟨ A⊆ (v ∷ V) (λ ()) c (λ ω∈ → proj₂ (all ω ω∈) refl) w w∈ , c ⟩ ⟩ ⟩ ⟩
𝒞⇂-⊆ X⊆ A⊆ B⊆ w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
  inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⇂-mono {P = ValPayload} X⊆ _ (all d d∈)) , ⟨ B⊆ (v ∷ V) (λ ()) c (λ ω∈ → proj₂ (all ω ω∈) refl) w w∈ , c ⟩ ⟩ ⟩ ⟩

𝒞ᵐ-≃ : ∀ {D D' F F' G G'} → D ≃ D' → BodyEq F F' → BodyEq G G'
  → 𝒞ᵐ ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞ᵐ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞ᵐ-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  ⟨ ≫=-mono (proj₁ D≃) (λ X⊆ → checked-mono X⊆ (𝒞⇂-⊆ {A = F} {F'} {G} {G'} X⊆ (λ V a b c → proj₁ (F≃ V a b c)) (λ V a b c → proj₁ (G≃ V a b c))))
  , ≫=-mono (proj₂ D≃) (λ X⊆ → checked-mono X⊆ (𝒞⇂-⊆ {A = F'} {F} {G'} {G} X⊆ (λ V a b c → proj₂ (F≃ V a b c)) (λ V a b c → proj₂ (G≃ V a b c)))) ⟩

{- β laws ----------------------------------------------------------------------------}

Λᵐ-clean : ∀ {F} → Clean (Λᵐ ⟨ F , ptt ⟩)
Λᵐ-clean ω ⟨ () , _ ⟩ refl

Λᵐ-fun : ∀ {F} d → d ∈ Λᵐ ⟨ F , ptt ⟩ → kind d ≡ fun
Λᵐ-fun (V ↦ w) _ = refl
Λᵐ-fun ν _ = refl

{- the application of a set of functions is a bind of its argument -}
⋆-r : ∀ {F X Y} → X ⊆ Y → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩ ⊆ ⋆ ⟨ F , ⟨ Y , ptt ⟩ ⟩
⋆-r {F} {X} {Y} X⊆ = lower (⋆-mono ⟨ F , ⟨ X , ptt ⟩ ⟩ ⟨ F , ⟨ Y , ptt ⟩ ⟩ ⟨ lift (λ d z → z) , ⟨ lift X⊆ , ptt ⟩ ⟩)

⋆ᵐ-val : ∀ {F D} → Clean F → nonempty F → (∀ d → d ∈ F → kind d ≡ fun)
  → ⋆ᵐ ⟨ F , ⟨ D , ptt ⟩ ⟩ ≃ (D ≫= λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩)
⋆ᵐ-val {F} {D} clF neF kF =
  ≃-trans (≫=-β {F = λ G → checked fun G (D ≫= λ X → ⋆ ⟨ G , ⟨ X , ptt ⟩ ⟩)}
                (λ X⊆ → checked-mono X⊆ (≫=-mono (λ d z → z) (λ Y⊆ → lower (⋆-mono ⟨ _ , ⟨ _ , ptt ⟩ ⟩ ⟨ _ , ⟨ _ , ptt ⟩ ⟩ ⟨ lift X⊆ , ⟨ lift Y⊆ , ptt ⟩ ⟩))))
                clF neF)
          (checked-ok kF)

{- (λx. F x) applied to a consistent set of values D is F D -}
Λᵐ-β : ∀ {F D} → Mono₁ F → Finitary F D → Con D → Clean D → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ≃ F D
Λᵐ-β {F} {D} m fin cD clD =
  ⟨ (λ w w∈ → proj₁ (Λ-β m fin cD) w (A w w∈)) , (λ w w∈ → B w (proj₂ (Λ-β m fin cD) w w∈)) ⟩
  where
  A : ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ letD ⟨ D , ⟨ F , ptt ⟩ ⟩
  A w ⟨ V , ⟨ ⟨ e∈ , _ ⟩ , r ⟩ ⟩ = ⟨ V , ⟨ e∈ , r ⟩ ⟩
  B : letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ⊆ ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  B w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ e∈ , (λ ω∈ → clD ω (V⊆ ω ω∈) refl) ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩

{- let x = D in F x means F D, for D a consistent set of values -}
letᵐ-β : ∀ {F D} → Mono₁ F → Finitary F D → Con D → Val D → letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ F D
letᵐ-β {F} {D} m fin cD ⟨ clD , neD ⟩ =
  ≃-trans (⋆ᵐ-val {Λᵐ ⟨ F , ptt ⟩} {D} Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩ Λᵐ-fun)
  (≃-trans (≫=-β {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} (⋆-r {Λᵐ ⟨ F , ptt ⟩}) clD neD) (Λᵐ-β m fin cD clD))

{- a case on an injection of a consistent set of values D takes its
   branch on D -}
private
  𝒞ᵐ-inj : ∀ {D F G} (t : Value → Value) (op : DOp (𝒫 Value) (■ ∷ []))
    → (∀ {X Y} → X ⊆ Y → op ⟨ X , ptt ⟩ ⊆ op ⟨ Y , ptt ⟩) → (∀ {X} → Clean X → Clean (op ⟨ X , ptt ⟩))
    → (∀ d → d ∈ op ⟨ D , ptt ⟩ → kind d ≡ inj × ValPayload d)
    → (∀ d → d ∈ D → t d ∈ op ⟨ D , ptt ⟩)
    → Clean D → nonempty D
    → 𝒞ᵐ ⟨ D ≫= (λ X → op ⟨ X , ptt ⟩) , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ op ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
  𝒞ᵐ-inj {D} {F} {G} t op m cl k i clD ⟨ d , d∈ ⟩ =
    ≃-trans (𝒞ᵐ-≃ {F = F} {F} {G} {G} (≫=-β m clD ⟨ d , d∈ ⟩) (λ _ _ _ _ → ≃-refl) (λ _ _ _ _ → ≃-refl))
    (≃-trans (≫=-β (λ X⊆ → checked-mono X⊆ (𝒞⇂-⊆ {A = F} {F} {G} {G} X⊆ (λ _ _ _ _ w z → z) (λ _ _ _ _ w z → z))) (cl clD) ⟨ t d , i d d∈ ⟩)
    (≃-trans (checked-ok (λ e e∈ → proj₁ (k e e∈)))
       (𝒞-≃ {F = F} {F} {G} {G} ⟨ ⇂-⊆ , ⇂-all (λ e e∈ → proj₂ (k e e∈)) ⟩ (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl))))

𝒞ᵐ-inl-β : ∀ {D F G} → Mono₁ F → Finitary F D → Con D → Val D
  → 𝒞ᵐ ⟨ inlᵐ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ F D
𝒞ᵐ-inl-β {F = F} {G} m fin cD ⟨ clD , neD ⟩ =
  ≃-trans (𝒞ᵐ-inj {F = F} {G} left inl (λ X⊆ → lower (inl-mono _ _ ⟨ lift X⊆ , ptt ⟩)) (λ { c ω () refl })
             (λ { (left v) v∈ → ⟨ refl , clD v v∈ ⟩ }) (λ e e∈ → e∈) clD neD)
          (𝒞-inl-β {G = G} m fin cD)

𝒞ᵐ-inr-β : ∀ {D F G} → Mono₁ G → Finitary G D → Con D → Val D
  → 𝒞ᵐ ⟨ inrᵐ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ G D
𝒞ᵐ-inr-β {F = F} {G} m fin cD ⟨ clD , neD ⟩ =
  ≃-trans (𝒞ᵐ-inj {F = F} {G} right inr (λ X⊆ → lower (inr-mono _ _ ⟨ lift X⊆ , ptt ⟩)) (λ { c ω () refl })
             (λ { (right v) v∈ → ⟨ refl , clD v v∈ ⟩ }) (λ e e∈ → e∈) clD neD)
          (𝒞-inr-β {F = F} m fin cD)

𝒯-clean : ∀ n {Ds} → Clean (𝒯 n Ds)
𝒯-clean zero ω () refl
𝒯-clean (suc n) ω () refl

binds-clean : ∀ n {Ds K} → (∀ i → Clean (nthD Ds i)) → (∀ {Xs} → Clean (K Xs)) → Clean (binds n Ds K)
binds-clean zero _ cK = cK
binds-clean (suc n) {⟨ D , Ds ⟩} {K} cs cK =
  ≫=-clean {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (cs zero) (binds-clean n (λ i → cs (suc i)) cK)

{- a projection from a tuple of nonempty sets -}
projᵐ-𝒯 : ∀ n (Xs : Results (𝒫 Value) (replicate n ■)) → (∀ j → nonempty (nthD Xs j))
  → (i : Fin n) → projᵐ i ⟨ 𝒯 n Xs , ptt ⟩ ≃ nthD Xs i
projᵐ-𝒯 (suc n) Xs ne i =
  ≃-trans (≫=-β {F = λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} (λ X⊆ → checked-mono X⊆ (λ d → X⊆ (tup[ i ] d)))
                 (𝒯-clean (suc n)) ⟨ tup[ i ] _ , ⟨ refl , ⟨ proj₂ (ne i) , ne ⟩ ⟩ ⟩)
  (≃-trans (checked-ok (λ { (tup[ j ] d) ⟨ refl , _ ⟩ → refl }))
     ⟨ (λ { d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ → d∈ }) , (λ d d∈ → ⟨ refl , ⟨ d∈ , ne ⟩ ⟩) ⟩)

{- a projection from a tuple of sets of values -}
projᵐ-𝒯ᵐ : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → AllVal n Ds
  → (i : Fin n) → projᵐ i ⟨ 𝒯ᵐ n Ds , ptt ⟩ ≃ nthD Ds i
projᵐ-𝒯ᵐ n Ds cn i =
  ≃-trans (projᵐ-≃ i (binds-β n (λ Xs⊆ → lower (𝒯-mono n _ _ Xs⊆)) cn)) (projᵐ-𝒯 n Ds (λ j → proj₂ (cn j)) i)

{- Closures and pairs (Clos3, Clos4) --------------------------------------------------}

ΛΛᵐ-good : ∀ {P} → Good P (∁ (ν (ν ■)) ∷ []) ΛΛᵐ
ΛΛᵐ-good = ⇂-good ΛΛ-good

closᵐ-good : ∀ {P} n → Good P (∁ (ν (ν ■)) ∷ replicate n ■) (closᵐ n)
closᵐ-good {P} n = record
  { mono = λ { ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F⊆ , Ds⊆ ⟩ →
      mono (⋆ᵐ-good {P}) _ _ ⟨ mono (ΛΛᵐ-good {P}) ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F⊆ , ptt ⟩
                             , ⟨ mono (𝒯ᵐ-good {P} n) Ds Ds' Ds⊆ , ptt ⟩ ⟩ }
  ; consis = λ p → λ { ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ →
      consis (⋆ᵐ-good {P}) p _ _ ⟨ consis (ΛΛᵐ-good {P}) p ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩
                                 , ⟨ consis (𝒯ᵐ-good {P} n) p Ds Ds' Ds~ , ptt ⟩ ⟩ }
  ; cont = λ { ⟨ B , Es ⟩ NE ⟨ okB , oks ⟩ →
      cont (⋆ᵐ-good {P}) ⟨ (λ ρ → ΛΛᵐ (⟪ ∁ (ν (ν ■)) ∷ [] ⟫₊ ⟨ B , ptt ⟩ ρ))
                         , ⟨ (λ ρ → 𝒯ᵐ n (⟪ replicate n ■ ⟫₊ Es ρ)) , ptt ⟩ ⟩ NE
        ⟨ ⟨ (λ _ d d∈ → d∈) , const-cont NE ⟩
        , ⟨ ⟨ mono-env (replicate n ■) (mono (𝒯ᵐ-good {P} n)) Es oks , cont (𝒯ᵐ-good {P} n) Es NE oks ⟩ , ptt ⟩ ⟩ } }

pairᵐ-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) pairᵐ
pairᵐ-good = binds-good 2 pair-good

carᵐ-good : ∀ {P} → Good P (■ ∷ []) carᵐ
carᵐ-good = strict-good (checkₒ-good car-good (λ { w ⟨ v , p∈ ⟩ → inj₂ ⟨ _ , ⟨ p∈ , refl ⟩ ⟩ }))

cdrᵐ-good : ∀ {P} → Good P (■ ∷ []) cdrᵐ
cdrᵐ-good = strict-good (checkₒ-good cdr-good (λ { w ⟨ u , p∈ ⟩ → inj₂ ⟨ _ , ⟨ p∈ , refl ⟩ ⟩ }))

callᵐ-good : ∀ {P} → Good P (■ ∷ ■ ∷ ■ ∷ []) callᵐ
callᵐ-good = binds-good 3 (checkₒ-good ⋆₂-good (λ { w ⟨ U , ⟨ ⟨ V , ⟨ f∈ , _ ⟩ ⟩ , _ ⟩ ⟩ → inj₂ ⟨ _ , ⟨ f∈ , refl ⟩ ⟩ }))

{- the values of a bind are values of its continuation, on the values of
   its operand; the values of a check are values of its kernel -}
⌊≫=⌋ : ∀ {D F} → ⌊ D ≫= F ⌋ ⊆ F ⌊ D ⌋
⌊≫=⌋ w ⟨ inj₁ ⟨ refl , _ ⟩ , w≢ ⟩ = ⊥-elim (w≢ refl)
⌊≫=⌋ w ⟨ inj₂ ⟨ _ , w∈ ⟩ , _ ⟩ = w∈

⌊checked⌋ : ∀ {k X A} → ⌊ checked k X A ⌋ ⊆ A
⌊checked⌋ w ⟨ inj₁ ⟨ refl , _ ⟩ , w≢ ⟩ = ⊥-elim (w≢ refl)
⌊checked⌋ w ⟨ inj₂ w∈ , _ ⟩ = w∈

{- the code of a closure, applied to its environment T and then to E,
   contains its body on T and E, when they are consistent sets of values -}
ΛΛᵐ-β : ∀ {F T E} → Con T → Con E → Clean T → Clean E → nonempty T → nonempty E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ ⋆ᵐ ⟨ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
ΛΛᵐ-β {F} {T} {E} cT cE clT clE ⟨ t , t∈ ⟩ neE fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  proj₂ (⋆ᵐ-val {G} {E} clG ⟨ ν , ⟨ t ∷ [] , ⟨ ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ nt , tt ⟩ ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩ ⟩ kG) w
    (proj₂ (≫=-β {F = λ Y → ⋆ ⟨ G , ⟨ Y , ptt ⟩ ⟩} (⋆-r {G}) clE neE) w
      ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩
            , ⟨ U⊆ , neU ⟩ ⟩ ⟩)
  where
  G = ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  nt = λ { (here eq) → clT t t∈ (sym eq) }
  single⊆ : ∀ {v} {D : 𝒫 Value} → v ∈ D → mem (v ∷ []) ⊆ D
  single⊆ v∈ _ (here refl) = v∈
  clG : Clean G
  clG .ω ⟨ V , ⟨ ⟨ ⟨ () , _ ⟩ , _ ⟩ , _ ⟩ ⟩ refl
  kG : ∀ d → d ∈ G → kind d ≡ fun
  kG ν _ = refl
  kG (U ↦ x) _ = refl

{- Sets of values ----------------------------------------------------------------------}

Val⇒Conv : ∀ {D} → Val D → Conv D
Val⇒Conv ⟨ cl , ⟨ d , d∈ ⟩ ⟩ = ⟨ d , ⟨ d∈ , cl d d∈ ⟩ ⟩

⌊⌋-val : ∀ {D} → Conv D → Val ⌊ D ⌋
⌊⌋-val ⟨ d , d∈ ⟩ = ⟨ (λ e e∈ → proj₂ e∈) , ⟨ d , d∈ ⟩ ⟩

{- a consistent set with a value is a set of values -}
con-val : ∀ {D} → Con D → Conv D → Val D
con-val cD c@(⟨ d , ⟨ d∈ , _ ⟩ ⟩) = ⟨ con-clean cD c , ⟨ d , d∈ ⟩ ⟩

{- a finite set without ω that a binder binds is a set of values -}
noerr-val : ∀ V → V ≢ [] → NoErr V → Val (mem V)
noerr-val V ne n = ⟨ (λ { .ω ω∈ refl → n ω∈ }) , E≢[]⇒nonempty-mem ne ⟩

Val-≃ : ∀ {D E} → D ≃ E → Val D → Val E
Val-≃ ⟨ D⊆ , E⊆ ⟩ ⟨ cl , ⟨ d , d∈ ⟩ ⟩ = ⟨ (λ e e∈ → cl e (E⊆ e e∈)) , ⟨ d , D⊆ d d∈ ⟩ ⟩

{- Val is compositional through bind -}
≫=-val : ∀ {D F} → Val D → (∀ {X} → Val X → Val (F X)) → Val (D ≫= F)
≫=-val {D} {F} vD hF with hF (⌊⌋-val (Val⇒Conv vD))
... | ⟨ clF , ⟨ w , w∈ ⟩ ⟩ = ⟨ ≫=-clean {F = F} (proj₁ vD) clF , ⟨ w , inj₂ ⟨ Val⇒Conv vD , w∈ ⟩ ⟩ ⟩

binds-val : ∀ n {Ds K} → AllVal n Ds → (∀ {Xs} → AllVal n Xs → Val (K Xs)) → Val (binds n Ds K)
binds-val zero _ hK = hK (λ ())
binds-val (suc n) {⟨ D , Ds ⟩} {K} vs hK =
  ≫=-val {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (vs zero)
    (λ vX → binds-val n (λ i → vs (suc i)) (λ vXs → hK (λ { zero → vX ; (suc i) → vXs i })))

𝒯-val : ∀ n {Xs} → AllVal n Xs → Val (𝒯 n Xs)
𝒯-val zero _ = ⟨ 𝒯-clean zero , ⟨ ⟨⟩ , tt ⟩ ⟩
𝒯-val (suc n) vs with proj₂ (vs zero)
... | ⟨ d , d∈ ⟩ = ⟨ 𝒯-clean (suc n) , ⟨ tup[ zero ] d , ⟨ refl , ⟨ d∈ , (λ j → proj₂ (vs j)) ⟩ ⟩ ⟩ ⟩

𝒯ᵐ-val : ∀ n {Ds} → AllVal n Ds → Val (𝒯ᵐ n Ds)
𝒯ᵐ-val n vs = binds-val n vs (𝒯-val n)

inlᵐ-val : ∀ {D} → Val D → Val (inlᵐ ⟨ D , ptt ⟩)
inlᵐ-val vD = ≫=-val {F = λ X → inl ⟨ X , ptt ⟩} vD λ { ⟨ _ , ⟨ d , d∈ ⟩ ⟩ → ⟨ (λ { .ω () refl }) , ⟨ left d , d∈ ⟩ ⟩ }

inrᵐ-val : ∀ {D} → Val D → Val (inrᵐ ⟨ D , ptt ⟩)
inrᵐ-val vD = ≫=-val {F = λ X → inr ⟨ X , ptt ⟩} vD λ { ⟨ _ , ⟨ d , d∈ ⟩ ⟩ → ⟨ (λ { .ω () refl }) , ⟨ right d , d∈ ⟩ ⟩ }

{- left unit, for an operator whose kernel is Good -}
strict-β : ∀ {P bs} {g : DOp (𝒫 Value) (■ ∷ bs)} → Good P (■ ∷ bs) g → ∀ {D Ds}
  → results-rel-pres _⊆_ bs Ds Ds → Val D → strict g ⟨ D , Ds ⟩ ≃ g ⟨ D , Ds ⟩
strict-β G Ds⊆ ⟨ cl , ne ⟩ = ≫=-β (λ X⊆ → lower (mono G _ _ ⟨ lift X⊆ , Ds⊆ ⟩)) cl ne

{- the check passes on a consistent set with a value of its kind -}
checked-con : ∀ {k X A} → Con X → Σ[ d ∈ Value ] d ∈ X × kind d ≡ k → checked k X A ≃ A
checked-con cX ⟨ d , ⟨ d∈ , dk ⟩ ⟩ = checked-ok (λ e e∈ → trans (~-kind e d (cX e d e∈ d∈)) dk)

{- a let binds its operand into the plain application of its function -}
letᵐ-unfold : ∀ {D F} → letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ (D ≫= λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩)
letᵐ-unfold {D} {F} = ⋆ᵐ-val {Λᵐ ⟨ F , ptt ⟩} {D} Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩ Λᵐ-fun

{- n binds preserve lifted relations -}
binds-lift : ∀ {S} n {Ds Ds' : Results (𝒫 Value) (replicate n ■)} {K K'} → LiftRel S
  → (∀ i → Con (nthD Ds' i)) → (∀ i → Lifted S (nthD Ds i) (nthD Ds' i))
  → (∀ {Xs Xs'} → (∀ i → Clean (nthD Xs i)) → (∀ i → Lifted S (nthD Xs i) (nthD Xs' i)) → Lifted S (K Xs) (K' Xs'))
  → Lifted S (binds n Ds K) (binds n Ds' K')
binds-lift zero L c h hK = hK (λ ()) (λ ())
binds-lift (suc n) {⟨ D , Ds ⟩} {⟨ D' , Ds' ⟩} {K} {K'} L c h hK =
  ≫=-lift {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {F' = λ X → binds n Ds' (λ Xs → K' ⟨ X , Xs ⟩)} L (c zero) (h zero)
    λ _ _ hX → binds-lift n L (λ i → c (suc i)) (λ i → h (suc i))
      (λ cl hs → hK (λ { zero → (λ e e∈ → proj₂ e∈) ; (suc i) → cl i }) (λ { zero → hX ; (suc i) → hs i }))

{- the call of a closure, a pair of code G (a set of values) and an
   environment T, on E: its code's body on T and E -}
pair-call-β : ∀ {F T E} → Con T → Con E → Val T → Val E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → let P = pair ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ in
    F T E ⊆ callᵐ ⟨ carᵐ ⟨ P , ptt ⟩ , ⟨ cdrᵐ ⟨ P , ptt ⟩ , ⟨ E , ptt ⟩ ⟩ ⟩
pair-call-β {F} {T} {E} cT cE ⟨ clT , ⟨ t , t∈ ⟩ ⟩ ⟨ clE , neE ⟩ fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  inj₂ ⟨ ⟨ _ , c∈ ⟩ , inj₂ ⟨ ⟨ t , d∈ t t∈ ⟩ , inj₂ ⟨ ⟨ proj₁ neE , ⟨ proj₂ neE , clE _ (proj₂ neE) ⟩ ⟩
       , inj₂ ⟨ U , ⟨ ⟨ V , ⟨ c∈ , ⟨ (λ v v∈ → d∈ v (V⊆ v v∈)) , neV ⟩ ⟩ ⟩
                    , ⟨ (λ u u∈ → ⟨ U⊆ u u∈ , clE u (U⊆ u u∈) ⟩) , neU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  e∈ᵐ : _ ∈ ΛΛᵐ ⟨ F , ptt ⟩
  e∈ᵐ = ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩
  P = pair ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  cP : Conv P
  cP = ⟨ ⦅ ν , t ⦆ , ⟨ ⟨ ⟨ tt , tt ⟩ , t∈ ⟩ , (λ ()) ⟩ ⟩
  c∈ : (V ↦ (U ↦ w)) ∈ ⌊ carᵐ ⟨ P , ptt ⟩ ⌋
  c∈ = ⟨ inj₂ ⟨ cP , inj₂ ⟨ t , ⟨ ⟨ e∈ᵐ , t∈ ⟩ , (λ ()) ⟩ ⟩ ⟩ , (λ ()) ⟩
  d∈ : ∀ v → v ∈ T → v ∈ ⌊ cdrᵐ ⟨ P , ptt ⟩ ⌋
  d∈ v v∈ = ⟨ inj₂ ⟨ cP , inj₂ ⟨ ν , ⟨ ⟨ ⟨ tt , tt ⟩ , v∈ ⟩ , (λ ()) ⟩ ⟩ ⟩ , clT v v∈ ⟩

{- Code and machine state (Clos5, Imp, CFG, X86) ------------------------------------}

{- a function of two arguments, consistent in both, is consistent -}
ΛΛᵐ-con : ∀ {F : 𝒫 Value → 𝒫 Value → 𝒫 Value}
  → (∀ X X' Y Y' → Every _~_ X X' → Every _~_ Y Y' → Every _~_ (F X Y) (F X' Y'))
  → Con (ΛΛᵐ ⟨ F , ptt ⟩)
ΛΛᵐ-con F~ = Con-⊆ (ΛΛ-con F~) (λ d d∈ → proj₁ d∈)

errcode-con : Con errcode
errcode-con = ΛΛᵐ-con (λ _ _ _ _ _ _ → Con-⌈⌉ ω)

{- Congruences of the binders, from equal operands ----------------------------------}

𝒞ᵐ-RR : ∀ {D F G D' F' G'} → RRs (■ ∷ ν ■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
  → 𝒞ᵐ ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞ᵐ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞ᵐ-RR {F = F} {G} {F' = F'} {G'} ⟨ D≃ , ⟨ F≃ , ⟨ G≃ , _ ⟩ ⟩ ⟩ =
  𝒞ᵐ-≃ {F = F} {F'} {G} {G'} (lower D≃) (λ _ _ _ _ → lower (F≃ _ _ ≃-refl)) (λ _ _ _ _ → lower (G≃ _ _ ≃-refl))

letᵐ-RR : ∀ {D F D' F'} → RRs (■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ptt ⟩ ⟩ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
  → letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letᵐ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letᵐ-RR {F = F} {F' = F'} ⟨ D≃ , ⟨ F≃ , _ ⟩ ⟩ = letᵐ-≃ {F = F} {F'} (lower D≃) (λ _ _ _ _ → lower (F≃ _ _ ≃-refl))

ΛΛᵐ-≃ : ∀ {F F' : 𝒫 Value → 𝒫 Value → 𝒫 Value} → (∀ X Y → F X Y ≃ F' X Y)
  → ΛΛᵐ ⟨ F , ptt ⟩ ≃ ΛΛᵐ ⟨ F' , ptt ⟩
ΛΛᵐ-≃ eq = ⟨ ⇂-mono (proj₁ (ΛΛ-≃ eq)) , ⇂-mono (proj₂ (ΛΛ-≃ eq)) ⟩

{- Binds and lets -------------------------------------------------------------------}

{- a let is the bind of its body, when the body is monotone and finitary
   on the values of the operand -}
letᵐ-≫= : ∀ {D G} → Mono₁ G → Con D → (Conv D → Finitary G ⌊ D ⌋) → letᵐ ⟨ D , ⟨ G , ptt ⟩ ⟩ ≃ (D ≫= G)
letᵐ-≫= {D} {G} mG cD fin =
  ≃-trans (letᵐ-unfold {D} {G})
    (≫=-cong {D} {λ X → ⋆ ⟨ Λᵐ ⟨ G , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} {G}
       (λ c → Λᵐ-β mG (fin c) (Con-⊆ cD ⌊⌋-⊆) (λ d d∈ → proj₂ d∈)))

{- n binds of equal operands -}
binds-≃ : ∀ n {Ds Es K} → Rel⊆ n K K → RRs (replicate n ■) Ds Es → binds n Ds K ≃ binds n Es K
binds-≃ n mK eq = ⟨ binds-mono n (proj₁ (RRs⇒⊆ eq)) mK , binds-mono n (proj₂ (RRs⇒⊆ eq)) mK ⟩

{- code is a set of values -}
ΛΛᵐ-val : ∀ {F} → Val (ΛΛᵐ ⟨ F , ptt ⟩)
ΛΛᵐ-val = ⟨ (λ { .ω ⟨ () , _ ⟩ refl }) , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩

{- code is equal when its bodies are, on finite sets of values -}
BodyEq₂ : (𝒫 Value → 𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value → 𝒫 Value) → Set
BodyEq₂ F F' = ∀ V U → V ≢ [] → V ≈ V → NoErr V → U ≢ [] → U ≈ U → NoErr U → F (mem V) (mem U) ≃ F' (mem V) (mem U)

ΛΛᵐ-≃′ : ∀ {F F'} → BodyEq₂ F F' → ΛΛᵐ ⟨ F , ptt ⟩ ≃ ΛΛᵐ ⟨ F' , ptt ⟩
ΛΛᵐ-≃′ {F} {F'} eq = ⟨ G (λ V U a b c d e f → proj₁ (eq V U a b c d e f)) , G (λ V U a b c d e f → proj₂ (eq V U a b c d e f)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value → 𝒫 Value}
    → (∀ V U → V ≢ [] → V ≈ V → NoErr V → U ≢ [] → U ≈ U → NoErr U → A (mem V) (mem U) ⊆ B (mem V) (mem U))
    → ΛΛᵐ ⟨ A , ptt ⟩ ⊆ ΛΛᵐ ⟨ B , ptt ⟩
  G h ν r = r
  G h (V ↦ ν) r = r
  G h (V ↦ (U ↦ w)) ⟨ ⟨ ⟨ w∈ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , cV ⟩ ⟩ , ⟨ nV , nU ⟩ ⟩ =
    ⟨ ⟨ ⟨ h V U neV cV nV neU cU nU w w∈ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , cV ⟩ ⟩ , ⟨ nV , nU ⟩ ⟩

{- Operators as binds of kernels ---------------------------------------------------}

{- an operator on n operands that binds them, left to right, and applies a
   monotone kernel to their values -}
record Kernel (n : ℕ) : Set₁ where
  constructor mkK
  field
    kern : Results (𝒫 Value) (replicate n ■) → 𝒫 Value
    kmono : Rel⊆ n kern kern
open Kernel public

bindsₖ : ∀ {n} → Kernel n → Results (𝒫 Value) (replicate n ■) → 𝒫 Value
bindsₖ {n} O Ds = binds n Ds (kern O)

bindsₖ-≃ : ∀ {n} (O : Kernel n) {Ds Es} → RRs (replicate n ■) Ds Es → bindsₖ O Ds ≃ bindsₖ O Es
bindsₖ-≃ {n} O = binds-≃ n (kmono O)

{- the kernel with its first operand fixed to D -}
_▷_ : ∀ {n} → 𝒫 Value → Kernel (suc n) → Kernel n
D ▷ O = mkK (λ Xs → kern O ⟨ D , Xs ⟩) (λ s → kmono O ⟨ lift (λ d d∈ → d∈) , s ⟩)

▷-clean : ∀ {n} (O : Kernel (suc n)) {X} Ds → Clean X → bindsₖ (⌊ X ⌋ ▷ O) Ds ≃ bindsₖ (X ▷ O) Ds
▷-clean {n} O Ds cl = ⟨ binds-mono n (⊆s-refl n Ds) (λ s → kmono O ⟨ lift ⌊⌋-⊆ , s ⟩)
                      , binds-mono n (⊆s-refl n Ds) (λ s → kmono O ⟨ lift (⌊⌋-clean cl) , s ⟩) ⟩

{- the operators, as binds of these kernels (by definition) -}
call-k : Kernel 3
call-k = mkK (λ { ⟨ F , ⟨ E , ⟨ X , _ ⟩ ⟩ ⟩ → checked fun F (⋆ ⟨ ⋆ ⟨ F , ⟨ E , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩) })
  (λ s → checked-mono (lower (proj₁ s)) (lower (⋆₂-mono _ _ s)))

pair-k : Kernel 2
pair-k = mkK pair (λ s → lower (pair-mono _ _ s))

car-k cdr-k inl-k inr-k : Kernel 1
car-k = mkK (λ { ⟨ X , _ ⟩ → checked prod X (car ⟨ X , ptt ⟩) }) (λ s → checked-mono (lower (proj₁ s)) (lower (car-mono _ _ s)))
cdr-k = mkK (λ { ⟨ X , _ ⟩ → checked prod X (cdr ⟨ X , ptt ⟩) }) (λ s → checked-mono (lower (proj₁ s)) (lower (cdr-mono _ _ s)))
inl-k = mkK (λ { ⟨ X , _ ⟩ → inl ⟨ X , ptt ⟩ }) (λ s → lower (inl-mono _ _ s))
inr-k = mkK (λ { ⟨ X , _ ⟩ → inr ⟨ X , ptt ⟩ }) (λ s → lower (inr-mono _ _ s))

tuple-k : ∀ n → Kernel n
tuple-k n = mkK (𝒯 n) (λ s → lower (𝒯-mono n _ _ s))

get-k : ∀ {n} (i : Fin n) → Kernel 1
get-k {n} i = mkK (λ { ⟨ X , _ ⟩ → checked (tup n) X (proj i ⟨ X , ptt ⟩) })
  (λ s → checked-mono (lower (proj₁ s)) (lower (proj-mono i _ _ s)))

{- case on its first operand, with the branches E and F -}
case-k : (E F : 𝒫 Value → 𝒫 Value) → Kernel 1
case-k E F = mkK (λ { ⟨ X , _ ⟩ → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩) })
  (λ s → checked-mono (lower (proj₁ s)) (𝒞⇂-⊆ {A = E} {E} {F} {F} (lower (proj₁ s)) (λ _ _ _ _ w w∈ → w∈) (λ _ _ _ _ w w∈ → w∈)))

{- Finitary continuations: a bind and a case commute with a bind ---------------------}

{- G uses only a finite, nonempty part of any nonempty set -}
FinOn : (𝒫 Value → 𝒫 Value) → Set₁
FinOn G = ∀ Y → nonempty Y → Finitary G Y

{- finitely many elements, each in F of a finite part of X, are all in F
   of one finite part of X -}
many-runs : ∀ {F : 𝒫 Value → 𝒫 Value} {X} → Mono₁ F → ∀ U → U ≢ []
  → (∀ u → u ∈ mem U → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ X × u ∈ F (mem V))
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ X × mem U ⊆ F (mem V)
many-runs mF [] ne _ = ⊥-elim (ne refl)
many-runs mF (u ∷ []) _ runs with runs u (here refl)
... | ⟨ V , ⟨ neV , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩ = ⟨ V , ⟨ neV , ⟨ V⊆ , (λ { _ (here refl) → u∈ }) ⟩ ⟩ ⟩
many-runs mF (u ∷ u' ∷ U) _ runs with runs u (here refl) | many-runs mF (u' ∷ U) (λ ()) (λ d d∈ → runs d (there d∈))
... | ⟨ V , ⟨ neV , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩ | ⟨ V' , ⟨ _ , ⟨ V'⊆ , U⊆ ⟩ ⟩ ⟩ =
  ⟨ V ++ V' , ⟨ (λ eq → neV (++-conicalˡ V V' eq)) , ⟨ (λ d d∈ → [ V⊆ d , V'⊆ d ]′ (∈-++⁻ V d∈))
  , (λ { _ (here refl) → mF (λ _ → ∈-++⁺ˡ) _ u∈ ; d (there d∈) → mF (λ _ → ∈-++⁺ʳ V) d (U⊆ d d∈) }) ⟩ ⟩ ⟩

{- a bind of a finitary operand into a finitary continuation is finitary -}
≫=-fin : ∀ {F G X} → Mono₁ F → Finitary F X → Mono₁ G → FinOn G → Finitary (λ Y → F Y ≫= G) X
≫=-fin mF fin mG fG w (inj₁ ⟨ refl , ω∈ ⟩) with fin ω ω∈
... | ⟨ V , ⟨ ne , ⟨ V⊆ , ω∈' ⟩ ⟩ ⟩ = ⟨ V , ⟨ ne , ⟨ V⊆ , inj₁ ⟨ refl , ω∈' ⟩ ⟩ ⟩ ⟩
≫=-fin {F} {G} {X} mF fin mG fG w (inj₂ ⟨ c , w∈ ⟩) with fG ⌊ F X ⌋ c w w∈
... | ⟨ U , ⟨ neU , ⟨ U⊆ , w∈' ⟩ ⟩ ⟩ with many-runs mF U neU (λ u u∈ → fin u (proj₁ (U⊆ u u∈)))
... | ⟨ V , ⟨ neV , ⟨ V⊆ , U⊆' ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ neV , ⟨ V⊆ , inj₂ ⟨ c' , mG (λ u u∈ → ⟨ U⊆' u u∈ , proj₂ (U⊆ u u∈) ⟩) w w∈' ⟩ ⟩ ⟩ ⟩
  where c' = let ⟨ u , u∈ ⟩ = E≢[]⇒nonempty-mem neU in ⟨ u , ⟨ U⊆' u u∈ , proj₂ (U⊆ u u∈) ⟩ ⟩

{- a check commutes with a bind -}
checked-≫= : ∀ {k X A G} → Mono₁ G → (checked k X A ≫= G) ≃ checked k X (A ≫= G)
checked-≫= {k} {X} {A} {G} mG = ⟨ L , R ⟩
  where
  L : (checked k X A ≫= G) ⊆ checked k X (A ≫= G)
  L w (inj₁ ⟨ refl , inj₁ ⟨ _ , b ⟩ ⟩) = inj₁ ⟨ refl , b ⟩
  L w (inj₁ ⟨ refl , inj₂ ω∈ ⟩) = inj₂ (inj₁ ⟨ refl , ω∈ ⟩)
  L w (inj₂ ⟨ ⟨ d , d∈ ⟩ , w∈ ⟩) = inj₂ (inj₂ ⟨ ⟨ d , ⟨ ⌊checked⌋ {k} {X} {A} d d∈ , proj₂ d∈ ⟩ ⟩ , mG (λ e e∈ → ⟨ ⌊checked⌋ {k} {X} {A} e e∈ , proj₂ e∈ ⟩) w w∈ ⟩)
  R : checked k X (A ≫= G) ⊆ (checked k X A ≫= G)
  R w (inj₁ ⟨ refl , b ⟩) = inj₁ ⟨ refl , inj₁ ⟨ refl , b ⟩ ⟩
  R w (inj₂ (inj₁ ⟨ refl , ω∈ ⟩)) = inj₁ ⟨ refl , inj₂ ω∈ ⟩
  R w (inj₂ (inj₂ ⟨ ⟨ d , d∈ ⟩ , w∈ ⟩)) = inj₂ ⟨ ⟨ d , ⟨ inj₂ (proj₁ d∈) , proj₂ d∈ ⟩ ⟩ , mG (λ e e∈ → ⟨ inj₂ (proj₁ e∈) , proj₂ e∈ ⟩) w w∈ ⟩

{- the values of one branch of a case, from finitely many payload sets,
   come from the branch on their union -}
gather-runs : ∀ {Q : 𝒫 Value} {E G : 𝒫 Value → 𝒫 Value} {w} → Con Q → Mono₁ E → Mono₁ G
  → ∀ U → U ≢ [] → (∀ u → u ∈ mem U → Σ[ W ∈ List Value ] W ≢ [] × mem W ⊆ Q × u ∈ E (mem W))
  → (∀ u → u ∈ mem U → u ≢ ω) → w ∈ G (mem U)
  → Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → Q d) × w ∈ (E (mem (v ∷ V)) ≫= G) × (v ∷ V) ≈ (v ∷ V)
gather-runs cQ mE mG U neU runs nω w∈ with many-runs mE U neU runs
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , U⊆ ⟩ ⟩ ⟩ =
  ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ inj₂ ⟨ conv , mG (λ u u∈ → ⟨ U⊆ u u∈ , nω u u∈ ⟩) _ w∈ ⟩ , Con⇒≈ (v ∷ V) cQ V⊆ ⟩ ⟩ ⟩ ⟩
  where conv = let ⟨ u , u∈ ⟩ = E≢[]⇒nonempty-mem neU in ⟨ u , ⟨ U⊆ u u∈ , nω u u∈ ⟩ ⟩

{- a case commutes with a finitary bind -}
𝒞-≫= : ∀ {P E F G} → Con P → Mono₁ E → Mono₁ F → Mono₁ G → FinOn G
  → (𝒞 ⟨ P , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ ≫= G) ≃ 𝒞 ⟨ P , ⟨ (λ Y → E Y ≫= G) , ⟨ (λ Y → F Y ≫= G) , ptt ⟩ ⟩ ⟩
𝒞-≫= {P} {E} {F} {G} cP mE mF mG fG = ⟨ L , R ⟩
  where
  C = 𝒞 ⟨ P , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩
  L : (C ≫= G) ⊆ 𝒞 ⟨ P , ⟨ (λ Y → E Y ≫= G) , ⟨ (λ Y → F Y ≫= G) , ptt ⟩ ⟩ ⟩
  L w (inj₁ ⟨ refl , inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩ ⟩) = inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₁ ⟨ refl , ω∈ ⟩ , c ⟩ ⟩ ⟩ ⟩
  L w (inj₁ ⟨ refl , inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩ ⟩) = inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₁ ⟨ refl , ω∈ ⟩ , c ⟩ ⟩ ⟩ ⟩
  L w (inj₂ ⟨ cv , w∈ ⟩) with fG ⌊ C ⌋ cv w w∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u₀ ∷ U , ⟨ _ , ⟨ U⊆ , w∈' ⟩ ⟩ ⟩ with proj₁ (U⊆ u₀ (here refl))
  ...   | inj₁ ⟨ v₀ , ⟨ V₀ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₁ (gather-runs (λ d d' d∈ d'∈ → cP _ _ d∈ d'∈) mE mG (u₀ ∷ U) (λ ()) runs (λ u u∈ → proj₂ (U⊆ u u∈)) w∈')
    where
    runs : ∀ u → u ∈ mem (u₀ ∷ U) → Σ[ W ∈ List Value ] W ≢ [] × mem W ⊆ (λ d → left d ∈ P) × u ∈ E (mem W)
    runs u u∈ with proj₁ (U⊆ u u∈)
    ... | inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₂ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cP _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  ...   | inj₂ ⟨ v₀ , ⟨ V₀ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₂ (gather-runs (λ d d' d∈ d'∈ → cP _ _ d∈ d'∈) mF mG (u₀ ∷ U) (λ ()) runs (λ u u∈ → proj₂ (U⊆ u u∈)) w∈')
    where
    runs : ∀ u → u ∈ mem (u₀ ∷ U) → Σ[ W ∈ List Value ] W ≢ [] × mem W ⊆ (λ d → right d ∈ P) × u ∈ F (mem W)
    runs u u∈ with proj₁ (U⊆ u u∈)
    ... | inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₁ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cP _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  R : 𝒞 ⟨ P , ⟨ (λ Y → E Y ≫= G) , ⟨ (λ Y → F Y ≫= G) , ptt ⟩ ⟩ ⟩ ⊆ (C ≫= G)
  R w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₁ ⟨ refl , ω∈ ⟩ , c ⟩ ⟩ ⟩ ⟩) = inj₁ ⟨ refl , inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩ ⟩
  R w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₂ ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ ⟨ u , ⟨ inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ proj₁ u∈ , c ⟩ ⟩ ⟩ ⟩ , proj₂ u∈ ⟩ ⟩
         , mG (λ e e∈ → ⟨ inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ proj₁ e∈ , c ⟩ ⟩ ⟩ ⟩ , proj₂ e∈ ⟩) w w∈ ⟩
  R w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₁ ⟨ refl , ω∈ ⟩ , c ⟩ ⟩ ⟩ ⟩) = inj₁ ⟨ refl , inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩ ⟩
  R w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ inj₂ ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ ⟨ u , ⟨ inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ proj₁ u∈ , c ⟩ ⟩ ⟩ ⟩ , proj₂ u∈ ⟩ ⟩
         , mG (λ e e∈ → ⟨ inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ proj₁ e∈ , c ⟩ ⟩ ⟩ ⟩ , proj₂ e∈ ⟩) w w∈ ⟩

{- so the case of the monad commutes with a finitary bind -}
𝒞ᵐ-≫= : ∀ {A F₁ F₂ G} → Con A → Mono₁ F₁ → Mono₁ F₂ → Mono₁ G → FinOn G
  → (𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩ ≫= G) ≃ 𝒞ᵐ ⟨ A , ⟨ (λ Y → F₁ Y ≫= G) , ⟨ (λ Y → F₂ Y ≫= G) , ptt ⟩ ⟩ ⟩
𝒞ᵐ-≫= {A} {F₁} {F₂} {G} cA m₁ m₂ mG fG =
  ≃-trans (≫=-assoc {A} {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)} mG)
    (≫=-cong {A} {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≫= G}
               {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ Y → F₁ Y ≫= G) , ⟨ (λ Y → F₂ Y ≫= G) , ptt ⟩ ⟩ ⟩)} λ _ → ≃-trans (checked-≫= mG)
       (⟨ checked-mono (λ d z → z) (proj₁ eq) , checked-mono (λ d z → z) (proj₂ eq) ⟩))
  where
  eq = 𝒞-≫= {⌊ A ⌋ ⇂ ValPayload} {F₁} {F₂} {G} (Con-⊆ cA (λ d d∈ → proj₁ (proj₁ d∈))) m₁ m₂ mG fG

{- An optional continuation: a bind into a finitary continuation (lift locals) ------}

K⟨_⟩ : Maybe (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
K⟨ nothing ⟩ D = D
K⟨ just G ⟩ D = D ≫= G

KOK : Maybe (𝒫 Value → 𝒫 Value) → Set₁
KOK nothing = Lift _ ⊤
KOK (just G) = Mono₁ G × FinOn G

K-mono : ∀ k → KOK k → Mono₁ K⟨ k ⟩
K-mono nothing _ X⊆ = X⊆
K-mono (just G) ⟨ mG , _ ⟩ X⊆ = ≫=-mono X⊆ mG

K-≃ : ∀ k → KOK k → ∀ {D D'} → D ≃ D' → K⟨ k ⟩ D ≃ K⟨ k ⟩ D'
K-≃ k ok ⟨ D⊆ , D⊇ ⟩ = ⟨ K-mono k ok D⊆ , K-mono k ok D⊇ ⟩

K-fin : ∀ k → KOK k → ∀ {F X} → Mono₁ F → Finitary F X → Finitary (λ Y → K⟨ k ⟩ (F Y)) X
K-fin nothing _ mF fin = fin
K-fin (just G) ⟨ mG , fG ⟩ mF fin = ≫=-fin mF fin mG fG

{- K after a monotone, finitary body is again a finitary continuation -}
K-ok : ∀ k → KOK k → ∀ {F} → Mono₁ F → FinOn F → KOK (just (λ X → K⟨ k ⟩ (F X)))
K-ok k ok mF fF = ⟨ (λ X⊆ → K-mono k ok (mF X⊆)) , (λ Y neY → K-fin k ok mF (fF Y neY)) ⟩

{- K commutes with a bind and with a case -}
let-law : ∀ k → KOK k → ∀ {D F} → K⟨ k ⟩ (D ≫= F) ≃ (D ≫= λ X → K⟨ k ⟩ (F X))
let-law nothing _ = ≃-refl
let-law (just G) ⟨ mG , _ ⟩ {D} {F} = ≫=-assoc {D} {F} mG

case-law : ∀ k → KOK k → ∀ {A F₁ F₂} → Con A → Mono₁ F₁ → Mono₁ F₂
  → K⟨ k ⟩ (𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≃ 𝒞ᵐ ⟨ A , ⟨ (λ X → K⟨ k ⟩ (F₁ X)) , ⟨ (λ X → K⟨ k ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
case-law nothing _ cA m₁ m₂ = ≃-refl
case-law (just G) ⟨ mG , fG ⟩ cA m₁ m₂ = 𝒞ᵐ-≫= cA m₁ m₂ mG fG

{- Congruences of the operators of pairs and calls -}

callᵐ-≃ : ∀ {L L' M M' N N'} → L ≃ L' → M ≃ M' → N ≃ N'
  → callᵐ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ≃ callᵐ ⟨ L' , ⟨ M' , ⟨ N' , ptt ⟩ ⟩ ⟩
callᵐ-≃ L≃ M≃ N≃ = mono-≃ (mono (callᵐ-good {⊤})) ⟨ lift L≃ , ⟨ lift M≃ , ⟨ lift N≃ , ptt ⟩ ⟩ ⟩

pairᵐ-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → pairᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ pairᵐ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
pairᵐ-≃ D≃ E≃ = mono-≃ (mono (pairᵐ-good {⊤})) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

carᵐ-≃ : ∀ {D D'} → D ≃ D' → carᵐ ⟨ D , ptt ⟩ ≃ carᵐ ⟨ D' , ptt ⟩
carᵐ-≃ D≃ = mono-≃ (mono (carᵐ-good {⊤})) ⟨ lift D≃ , ptt ⟩

cdrᵐ-≃ : ∀ {D D'} → D ≃ D' → cdrᵐ ⟨ D , ptt ⟩ ≃ cdrᵐ ⟨ D' , ptt ⟩
cdrᵐ-≃ D≃ = mono-≃ (mono (cdrᵐ-good {⊤})) ⟨ lift D≃ , ptt ⟩

{- Congruences of the operators of machine state -}

payloadᵐ-mono : ∀ {D D'} → D ⊆ D' → payloadᵐ D ⊆ payloadᵐ D'
payloadᵐ-mono D⊆ = ≫=-mono D⊆ P
  where
  P : ∀ {X X'} → X ⊆ X' → checked inj X (payloadD (X ⇂ ValPayload)) ⊆ checked inj X' (payloadD (X' ⇂ ValPayload))
  P X⊆ = checked-mono X⊆ (λ { v (inj₁ l) → inj₁ (⇂-mono {P = ValPayload} X⊆ _ l) ; v (inj₂ r) → inj₂ (⇂-mono {P = ValPayload} X⊆ _ r) })

payloadᵐ-≃ : ∀ {D D'} → D ≃ D' → payloadᵐ D ≃ payloadᵐ D'
payloadᵐ-≃ ⟨ D⊆ , D⊇ ⟩ = ⟨ payloadᵐ-mono D⊆ , payloadᵐ-mono D⊇ ⟩

strictᵐ-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → strictᵐ D E ≃ strictᵐ D' E'
strictᵐ-≃ ⟨ D⊆ , D⊇ ⟩ ⟨ E⊆ , E⊇ ⟩ = ⟨ ≫=-mono D⊆ (λ _ → E⊆) , ≫=-mono D⊇ (λ _ → E⊇) ⟩


{- What a bind needs of its operand: an error, or a value ---------------------------}

{- D holds an error or has a value -}
Has : 𝒫 Value → Set
Has D = ω ∈ D ⊎ Conv D

ne-has : ∀ {D} → nonempty D → Has D
ne-has ⟨ d , d∈ ⟩ with ω? d
... | inj₁ refl = inj₁ d∈
... | inj₂ d≢ = inj₂ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩

≫=-ω₁ : ∀ {D F} → ω ∈ D → ω ∈ (D ≫= F)
≫=-ω₁ ω∈ = inj₁ ⟨ refl , ω∈ ⟩

≫=-ω₂ : ∀ {D F} → Conv D → ω ∈ F ⌊ D ⌋ → ω ∈ (D ≫= F)
≫=-ω₂ c ω∈ = inj₂ ⟨ c , ω∈ ⟩

{- an element of a bind: the operand holds an error or has a value; a
   value of the bind is one of the continuation on the values -}
≫=-has : ∀ {D F w} → w ∈ (D ≫= F) → Has D
≫=-has (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ ω∈
≫=-has (inj₂ ⟨ c , _ ⟩) = inj₂ c

≫=-conv : ∀ {D F w} → w ∈ (D ≫= F) → w ≢ ω → Conv D × w ∈ F ⌊ D ⌋
≫=-conv (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
≫=-conv (inj₂ p) _ = p

{- a strict write of D before X is X, when an error in D is one of X, and
   each element of X needs D to hold an error or a value, a value for a value -}
strictᵐ-skip : ∀ {D X} → (∀ w → w ∈ X → Has D) → (ω ∈ D → ω ∈ X) → (∀ w → w ∈ X → w ≢ ω → Conv D)
  → strictᵐ D X ≃ X
strictᵐ-skip {D} {X} has ωX val = ⟨ G , H ⟩
  where
  G : strictᵐ D X ⊆ X
  G w (inj₁ ⟨ refl , ω∈ ⟩) = ωX ω∈
  G w (inj₂ ⟨ _ , w∈ ⟩) = w∈
  H : X ⊆ strictᵐ D X
  H w w∈ with ω? w
  ... | inj₂ w≢ = inj₂ ⟨ val w w∈ w≢ , w∈ ⟩
  ... | inj₁ refl with has ω w∈
  ...   | inj₁ ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  ...   | inj₂ c = inj₂ ⟨ c , w∈ ⟩

strictᵐ-≃′ : ∀ {D X X'} → X ≃ X' → (∀ w → w ∈ X → Has D) → (ω ∈ D → ω ∈ X) → (∀ w → w ∈ X → w ≢ ω → Conv D)
  → strictᵐ D X ≃ X'
strictᵐ-≃′ X≃ has ωX val = ≃-trans (strictᵐ-skip has ωX val) X≃

{- a write of D that is followed by D -}
strictᵐ-self : ∀ {D Z} → Z ≃ D → strictᵐ D Z ≃ D
strictᵐ-self Z≃ = ≃-trans (strictᵐ-skip (λ w w∈ → ne-has ⟨ w , proj₁ Z≃ w w∈ ⟩) (λ ω∈ → proj₂ Z≃ ω ω∈)
  (λ w w∈ w≢ → ⟨ w , ⟨ proj₁ Z≃ w w∈ , w≢ ⟩ ⟩)) Z≃

{- a call Errs on an error in its operands, left to right; a value of it
   needs values of its operands -}
callᵐ-ω : ∀ {L M N} → Has L → ω ∈ M ⊎ (Conv M × ω ∈ N) → ω ∈ callᵐ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩
callᵐ-ω (inj₁ ωL) _ = inj₁ ⟨ refl , ωL ⟩
callᵐ-ω (inj₂ cL) (inj₁ ωM) = inj₂ ⟨ cL , inj₁ ⟨ refl , ωM ⟩ ⟩
callᵐ-ω (inj₂ cL) (inj₂ ⟨ cM , ωN ⟩) = inj₂ ⟨ cL , inj₂ ⟨ cM , inj₁ ⟨ refl , ωN ⟩ ⟩ ⟩

callᵐ-conv : ∀ {L M N w} → w ∈ callᵐ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ → w ≢ ω → Conv M × Conv N
callᵐ-conv (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
callᵐ-conv (inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩) w≢ = ⊥-elim (w≢ refl)
callᵐ-conv (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩ ⟩) w≢ = ⊥-elim (w≢ refl)
callᵐ-conv (inj₂ ⟨ _ , inj₂ ⟨ cM , inj₂ ⟨ cN , _ ⟩ ⟩ ⟩) _ = ⟨ cM , cN ⟩

{- the elements of a let of a set of values: its body on finite parts of it -}
LetEntry : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
LetEntry D H w = Σ[ V ∈ List Value ] V ≢ [] × V ≈ V × NoErr V × mem V ⊆ D × w ∈ H (mem V)

letᵐ-entries : ∀ {D H} → Val D → letᵐ ⟨ D , ⟨ H , ptt ⟩ ⟩ ≃ LetEntry D H
letᵐ-entries {D} {H} vD =
  ≃-trans (letᵐ-unfold {D} {H}) (≃-trans (≫=-val-β {F = λ X → ⋆ ⟨ Λᵐ ⟨ H , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} vD)
    ⟨ (λ { w ⟨ V , ⟨ ⟨ ⟨ w∈ , ⟨ ne , c ⟩ ⟩ , n ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ → ⟨ V , ⟨ ne , ⟨ c , ⟨ n , ⟨ (λ d d∈ → proj₁ (V⊆ d d∈)) , w∈ ⟩ ⟩ ⟩ ⟩ ⟩ })
    , (λ { w ⟨ V , ⟨ ne , ⟨ c , ⟨ n , ⟨ V⊆ , w∈ ⟩ ⟩ ⟩ ⟩ ⟩ →
             ⟨ V , ⟨ ⟨ ⟨ w∈ , ⟨ ne , c ⟩ ⟩ , n ⟩ , ⟨ (λ d d∈ → ⟨ V⊆ d d∈ , (λ { refl → n d∈ }) ⟩) , ne ⟩ ⟩ ⟩ }) ⟩)

{- Laws used by adequacy for Clos5 and X86 --------------------------------------------}

{- the call of code, on an environment and an argument that are sets of
   values, runs its body on them -}
callᵐ-β : ∀ {F T E} → Con T → Con E → Val T → Val E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ callᵐ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ⟨ E , ptt ⟩ ⟩ ⟩
callᵐ-β {F} cT cE vT@(⟨ clT , _ ⟩) vE@(⟨ clE , _ ⟩) fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  inj₂ ⟨ ⟨ ν , ⟨ ⟨ tt , tt ⟩ , (λ ()) ⟩ ⟩ , inj₂ ⟨ Val⇒Conv vT , inj₂ ⟨ Val⇒Conv vE , inj₂
    ⟨ U , ⟨ ⟨ V , ⟨ ⟨ ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩ , (λ ()) ⟩
                , ⟨ (λ v v∈ → ⟨ V⊆ v v∈ , clT v (V⊆ v v∈) ⟩) , neV ⟩ ⟩ ⟩
          , ⟨ (λ u u∈ → ⟨ U⊆ u u∈ , clE u (U⊆ u u∈) ⟩) , neU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

pairᵐ-val : ∀ {D E} → Val D → Val E → Val (pairᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩)
pairᵐ-val {D} {E} vD vE = ≫=-val {F = λ X → E ≫= λ Y → pair ⟨ X , ⟨ Y , ptt ⟩ ⟩} vD λ vX →
  ≫=-val {F = λ Y → pair ⟨ _ , ⟨ Y , ptt ⟩ ⟩} vE λ { vY → ⟨ (λ { .ω () refl }) , ⟨ ⦅ proj₁ (proj₂ vX) , proj₁ (proj₂ vY) ⦆
                                                         , ⟨ proj₂ (proj₂ vX) , proj₂ (proj₂ vY) ⟩ ⟩ ⟩ }

{- the components of a pair of sets of values -}
carᵐ-pair : ∀ {D E} → Val D → Val E → D ⊆ carᵐ ⟨ pairᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩ , ptt ⟩
carᵐ-pair vD@(⟨ clD , _ ⟩) vE@(⟨ _ , ⟨ b , b∈ ⟩ ⟩) d d∈ =
  inj₂ ⟨ Val⇒Conv (pairᵐ-val vD vE) , inj₂ ⟨ b , ⟨ inj₂ ⟨ Val⇒Conv vD , inj₂ ⟨ Val⇒Conv vE , ⟨ ⟨ d∈ , clD d d∈ ⟩ , ⟨ b∈ , proj₁ vE b b∈ ⟩ ⟩ ⟩ ⟩ , (λ ()) ⟩ ⟩ ⟩

cdrᵐ-pair : ∀ {D E} → Val D → Val E → E ⊆ cdrᵐ ⟨ pairᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩ , ptt ⟩
cdrᵐ-pair vD@(⟨ _ , ⟨ a , a∈ ⟩ ⟩) vE@(⟨ clE , _ ⟩) d d∈ =
  inj₂ ⟨ Val⇒Conv (pairᵐ-val vD vE) , inj₂ ⟨ a , ⟨ inj₂ ⟨ Val⇒Conv vD , inj₂ ⟨ Val⇒Conv vE , ⟨ ⟨ a∈ , proj₁ vD a a∈ ⟩ , ⟨ d∈ , clE d d∈ ⟩ ⟩ ⟩ ⟩ , (λ ()) ⟩ ⟩ ⟩

isinlᵐ-mono : ∀ {D D'} → D ⊆ D' → isinlᵐ D ⊆ isinlᵐ D'
isinlᵐ-mono D⊆ = ≫=-mono D⊆ P
  where
  P : ∀ {X X'} → X ⊆ X' → checked inj X (isinlD X) ⊆ checked inj X' (isinlD X')
  P X⊆ = checked-mono X⊆ (λ { w (inj₁ ⟨ u , ⟨ l , e ⟩ ⟩) → inj₁ ⟨ u , ⟨ X⊆ _ l , e ⟩ ⟩
                             ; w (inj₂ ⟨ u , ⟨ r , e ⟩ ⟩) → inj₂ ⟨ u , ⟨ X⊆ _ r , e ⟩ ⟩ })

{- a let of finitely many values of its operand: its body on them -}
letᵐ-intro : ∀ {D F V w} → V ≢ [] → V ≈ V → NoErr V → mem V ⊆ D → w ∈ F (mem V) → w ∈ letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩
letᵐ-intro {D} {F} {V} ne c n V⊆ w∈ = proj₂ (letᵐ-unfold {D} {F}) _
  (inj₂ ⟨ ⟨ proj₁ v , ⟨ V⊆ _ (proj₂ v) , (λ e → n (subst (λ x → x ∈ mem V) e (proj₂ v))) ⟩ ⟩
        , ⟨ V , ⟨ ⟨ ⟨ w∈ , ⟨ ne , c ⟩ ⟩ , n ⟩ , ⟨ (λ d d∈ → ⟨ V⊆ d d∈ , (λ { refl → n d∈ }) ⟩) , ne ⟩ ⟩ ⟩ ⟩)
  where v = E≢[]⇒nonempty-mem ne

letᵐ-ω : ∀ {D F} → ω ∈ D → ω ∈ letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩
letᵐ-ω {D} {F} ω∈ = proj₂ (letᵐ-unfold {D} {F}) ω (inj₁ ⟨ refl , ω∈ ⟩)

{- an entry of code, and its call on parts of the environment and argument -}
ΛΛᵐ-entry : ∀ {F V U w} → w ∈ F (mem V) (mem U) → V ≢ [] → V ≈ V → NoErr V → U ≢ [] → U ≈ U → NoErr U
  → (V ↦ (U ↦ w)) ∈ ΛΛᵐ ⟨ F , ptt ⟩
ΛΛᵐ-entry w∈ neV cV nV neU cU nU = ⟨ ⟨ ⟨ w∈ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , cV ⟩ ⟩ , ⟨ nV , nU ⟩ ⟩

callᵐ-intro : ∀ {L M N V U w} → (V ↦ (U ↦ w)) ∈ L → V ≢ [] → U ≢ [] → mem V ⊆ ⌊ M ⌋ → mem U ⊆ ⌊ N ⌋
  → w ∈ callᵐ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩
callᵐ-intro {V = V} {U} e∈ neV neU V⊆ U⊆ =
  inj₂ ⟨ ⟨ _ , ⟨ e∈ , (λ ()) ⟩ ⟩ , inj₂ ⟨ ⟨ proj₁ v , V⊆ _ (proj₂ v) ⟩ , inj₂ ⟨ ⟨ proj₁ u , U⊆ _ (proj₂ u) ⟩
       , inj₂ ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , (λ ()) ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where v = E≢[]⇒nonempty-mem neV
        u = E≢[]⇒nonempty-mem neU

{- n binds: their operands' values, and an error in them, left to right -}
⌊_⌋s : ∀ {n} → Results (𝒫 Value) (replicate n ■) → Results (𝒫 Value) (replicate n ■)
⌊_⌋s {zero} _ = ptt
⌊_⌋s {suc n} ⟨ D , Ds ⟩ = ⟨ ⌊ D ⌋ , ⌊ Ds ⌋s ⟩

binds-intro : ∀ n {Ds : Results (𝒫 Value) (replicate n ■)} {K w} → (∀ i → Conv (nthD Ds i)) → w ∈ K ⌊ Ds ⌋s → w ∈ binds n Ds K
binds-intro zero c w∈ = w∈
binds-intro (suc n) {⟨ D , Ds ⟩} c w∈ = inj₂ ⟨ c zero , binds-intro n (λ i → c (suc i)) w∈ ⟩

conv-⌊⌋s : ∀ n {Ds : Results (𝒫 Value) (replicate n ■)} → (∀ i → Conv (nthD Ds i)) → ∀ i → nonempty (nthD ⌊ Ds ⌋s i)
conv-⌊⌋s (suc n) c zero = c zero
conv-⌊⌋s (suc n) c (suc i) = conv-⌊⌋s n (λ j → c (suc j)) i

Errs : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
Errs zero _ = ⊥
Errs (suc n) ⟨ D , Ds ⟩ = ω ∈ D ⊎ (Conv D × Errs n Ds)

errs-ω : ∀ n {Ds K} → Errs n Ds → ω ∈ binds n Ds K
errs-ω (suc n) (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
errs-ω (suc n) {⟨ D , Ds ⟩} (inj₂ ⟨ c , e ⟩) = inj₂ ⟨ c , errs-ω n e ⟩

errs-mono : ∀ n {Ds Es} → results-rel-pres _⊆_ (replicate n ■) Ds Es → Errs n Ds → Errs n Es
errs-mono (suc n) ⟨ lift D⊆ , _ ⟩ (inj₁ ω∈) = inj₁ (D⊆ ω ω∈)
errs-mono (suc n) ⟨ lift D⊆ , s ⟩ (inj₂ ⟨ c , e ⟩) = inj₂ ⟨ Conv-mono D⊆ c , errs-mono n s e ⟩

{- the check of a single value of the wrong kind Errs -}
bad-one : ∀ {k} u {F : 𝒫 Value → 𝒫 Value} → u ≢ ω → kind u ≢ k → ω ∈ (mem (u ∷ []) ≫= λ X → checked k X (F X))
bad-one u u≢ k≢ = inj₂ ⟨ ⟨ u , ⟨ here refl , u≢ ⟩ ⟩ , inj₁ ⟨ refl , ⟨ u , ⟨ ⟨ here refl , u≢ ⟩ , k≢ ⟩ ⟩ ⟩ ⟩

isinlᵐ-consis : ∀ {D D'} → Every _~_ D D' → Every _~_ (isinlᵐ D) (isinlᵐ D')
isinlᵐ-consis D~ = ≫=-consis D~ λ X~ → checked-consis X~ (K~ X~) needs needs
  where
  K~ : ∀ {X X'} → Every _~_ X X' → Every _~_ (isinlD X) (isinlD X')
  K~ X~ _ _ (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) = tt
  K~ X~ _ _ (inj₁ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) (inj₂ ⟨ _ , ⟨ v∈ , refl ⟩ ⟩) = ⊥-elim (X~ _ _ u∈ v∈)
  K~ X~ _ _ (inj₂ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) (inj₁ ⟨ _ , ⟨ v∈ , refl ⟩ ⟩) = ⊥-elim (X~ _ _ u∈ v∈)
  K~ X~ _ _ (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) = tt
  needs : ∀ {X} → Needs inj X (isinlD X)
  needs _ (inj₁ ⟨ u , ⟨ u∈ , refl ⟩ ⟩) = inj₂ ⟨ left u , ⟨ u∈ , refl ⟩ ⟩
  needs _ (inj₂ ⟨ u , ⟨ u∈ , refl ⟩ ⟩) = inj₂ ⟨ right u , ⟨ u∈ , refl ⟩ ⟩

payloadᵐ-consis : ∀ {D D'} → Every _~_ D D' → Every _~_ (payloadᵐ D) (payloadᵐ D')
payloadᵐ-consis D~ = ≫=-consis D~ λ X~ → checked-consis X~ (K~ X~) needs needs
  where
  K~ : ∀ {X X'} → Every _~_ X X' → Every _~_ (payloadD (X ⇂ ValPayload)) (payloadD (X' ⇂ ValPayload))
  K~ X~ _ _ (inj₁ u∈) (inj₁ v∈) = X~ _ _ (proj₁ u∈) (proj₁ v∈)
  K~ X~ _ _ (inj₁ u∈) (inj₂ v∈) = ⊥-elim (X~ _ _ (proj₁ u∈) (proj₁ v∈))
  K~ X~ _ _ (inj₂ u∈) (inj₁ v∈) = ⊥-elim (X~ _ _ (proj₁ u∈) (proj₁ v∈))
  K~ X~ _ _ (inj₂ u∈) (inj₂ v∈) = X~ _ _ (proj₁ u∈) (proj₁ v∈)
  needs : ∀ {X} → Needs inj X (payloadD (X ⇂ ValPayload))
  needs v (inj₁ l) = inj₂ ⟨ left v , ⟨ proj₁ l , refl ⟩ ⟩
  needs v (inj₂ r) = inj₂ ⟨ right v , ⟨ proj₁ r , refl ⟩ ⟩

{- every entry is code, a function -}
ΛΛᵐ-fun : ∀ {F} d → d ∈ ΛΛᵐ ⟨ F , ptt ⟩ → kind d ≡ fun
ΛΛᵐ-fun ν _ = refl
ΛΛᵐ-fun (V ↦ w) _ = refl


isinlᵐ-≃ : ∀ {D D'} → D ≃ D' → isinlᵐ D ≃ isinlᵐ D'
isinlᵐ-≃ ⟨ D⊆ , D⊇ ⟩ = ⟨ isinlᵐ-mono D⊆ , isinlᵐ-mono D⊇ ⟩
