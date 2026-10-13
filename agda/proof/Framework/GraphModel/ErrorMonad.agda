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
open import Framework.abt.Sig using (Result)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

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

{- a set consistent with one that errs has no value, and the other way -}
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

{- Lifting a relation on values through the monad ---------------------------------------}

{- every element of D has a related element of D': ω an ω, a value a value
   related by R -}
_⊑[_]_ : 𝒫 Value → (Value → Value → Set) → 𝒫 Value → Set
D ⊑[ R ] D' = (ω ∈ D → ω ∈ D') × (∀ d → d ∈ ⌊ D ⌋ → Σ[ d' ∈ Value ] d' ∈ ⌊ D' ⌋ × R d d')

{- bind preserves lifted relations: its continuations need only be related
   on related sets of values -}
≫=-⊑ : ∀ {R S D D' F F'} → D ⊑[ R ] D' → (∀ {X X'} → Clean X → X ⊑[ R ] X' → F X ⊑[ S ] F' X')
  → (D ≫= F) ⊑[ S ] (D' ≫= F')
≫=-⊑ {R} {S} {D} {D'} {F} {F'} ⟨ ωD , vD ⟩ hF = ⟨ A , B ⟩
  where
  X⊑ : ⌊ D ⌋ ⊑[ R ] ⌊ D' ⌋
  X⊑ = ⟨ (λ { ⟨ _ , ω≢ ⟩ → ⊥-elim (ω≢ refl) })
       , (λ d d∈ → let ⟨ d' , ⟨ d'∈ , r ⟩ ⟩ = vD d (proj₁ d∈) in ⟨ d' , ⟨ ⟨ d'∈ , proj₂ d'∈ ⟩ , r ⟩ ⟩) ⟩
  cv : Conv D → Conv D'
  cv ⟨ d , d∈ ⟩ = let ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = vD d d∈ in ⟨ d' , d'∈ ⟩
  A : ω ∈ (D ≫= F) → ω ∈ (D' ≫= F')
  A (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ ⟨ refl , ωD ω∈ ⟩
  A (inj₂ ⟨ c , ω∈ ⟩) = inj₂ ⟨ cv c , proj₁ (hF (λ d d∈ → proj₂ d∈) X⊑) ω∈ ⟩
  B : ∀ w → w ∈ ⌊ D ≫= F ⌋ → Σ[ w' ∈ Value ] w' ∈ ⌊ D' ≫= F' ⌋ × S w w'
  B w ⟨ inj₁ ⟨ refl , _ ⟩ , w≢ ⟩ = ⊥-elim (w≢ refl)
  B w ⟨ inj₂ ⟨ c , w∈ ⟩ , w≢ ⟩ with proj₂ (hF (λ d d∈ → proj₂ d∈) X⊑) w ⟨ w∈ , w≢ ⟩
  ... | ⟨ w' , ⟨ ⟨ w'∈ , w'≢ ⟩ , r ⟩ ⟩ = ⟨ w' , ⟨ ⟨ inj₂ ⟨ cv c , w'∈ ⟩ , w'≢ ⟩ , r ⟩ ⟩

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
≫=-cont : ∀ {E : VEnv → 𝒫 Value} {G : VEnv → 𝒫 Value → 𝒫 Value} {ρ} → Mono E → Cont E ρ
  → (∀ {ρ₁ ρ₂ X Y} → ρ₁ ⊆ₑ ρ₂ → X ⊆ Y → G ρ₁ X ⊆ G ρ₂ Y) → Cont (λ ρ → G ρ ⌊ E ρ ⌋) ρ
  → Cont (λ ρ → E ρ ≫= G ρ) ρ
≫=-cont {E} {G} mE cE mG cG w (inj₁ ⟨ refl , ω∈ ⟩) with one E cE ω∈
... | ⟨ a , ω∈′ ⟩ = done (λ ρ → E ρ ≫= G ρ) a ω (inj₁ ⟨ refl , ω∈′ ⟩)
≫=-cont {E} {G} mE cE mG cG w (inj₂ ⟨ ⟨ d , d∈ ⟩ , w∈ ⟩)
    with one (λ ρ → ⌊ E ρ ⌋) (⌊⌋-cont cE) d∈ | one (λ ρ → G ρ ⌊ E ρ ⌋) cG w∈
... | ⟨ a , d∈′ ⟩ | ⟨ b , w∈′ ⟩ =
  done (λ ρ → E ρ ≫= G ρ) (approx-join a b) w
    (inj₂ ⟨ ⟨ d , ⌊⌋-mono (mE (join-l a b)) d d∈′ ⟩ , mG (join-r a b) (⌊⌋-mono (mE (join-r a b))) w w∈′ ⟩)

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

binds-cont : ∀ n (Es : Bodies (replicate n ■)) {K : VEnv → Results (𝒫 Value) (replicate n ■) → 𝒫 Value} {ρ}
  → nonempty-env ρ → OK (replicate n ■) Es ρ
  → (∀ {ρ₁ ρ₂ Xs Ys} → ρ₁ ⊆ₑ ρ₂ → results-rel-pres _⊆_ (replicate n ■) Xs Ys → K ρ₁ Xs ⊆ K ρ₂ Ys)
  → (∀ Ms → OK (replicate n ■) Ms ρ → Cont (λ ρ → K ρ (⟪ replicate n ■ ⟫₊ Ms ρ)) ρ)
  → Cont (λ ρ → binds n (⟪ replicate n ■ ⟫₊ Es ρ) (K ρ)) ρ
binds-cont zero Es NE ok mK cK = cK ptt ptt
binds-cont (suc n) ⟨ E , Es ⟩ NE ⟨ ok₁@(⟨ m , c ⟩) , ok ⟩ mK cK =
  ≫=-cont m c (λ ρ⊆ X⊆ → binds-mono n (⟪⟫₊-mono (replicate n ■) Es ok ρ⊆) (λ Xs⊆ → mK ρ⊆ ⟨ lift X⊆ , Xs⊆ ⟩))
    (binds-cont n Es NE ok (λ ρ⊆ Xs⊆ → mK ρ⊆ ⟨ lift (⌊⌋-mono (m ρ⊆)) , Xs⊆ ⟩)
       (λ Ms okM → cK ⟨ (λ ρ → ⌊ E ρ ⌋) , Ms ⟩ ⟨ ⌊⌋-ok ok₁ , okM ⟩))

{- left unit, for n operands that have values and no errors -}
binds-β : ∀ n {Ds K} → Rel⊆ n K K → (∀ i → Clean (nthD Ds i) × nonempty (nthD Ds i)) → binds n Ds K ≃ K Ds
binds-β zero mK _ = ≃-refl
binds-β (suc n) {⟨ D , Ds ⟩} mK cn =
  ≃-trans (≫=-β (λ X⊆ → binds-mono n (⊆s-refl n Ds) (λ Xs⊆ → mK ⟨ lift X⊆ , Xs⊆ ⟩)) (proj₁ (cn zero)) (proj₂ (cn zero)))
          (binds-β n (λ Xs⊆ → mK ⟨ lift (λ d z → z) , Xs⊆ ⟩) (λ i → cn (suc i)))

{- The operators are Good -------------------------------------------------------------}

⋆-needs : ∀ {F X} → Needs fun F (⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩)
⋆-needs w ⟨ V , ⟨ f∈ , _ ⟩ ⟩ = inj₂ ⟨ V ↦ w , ⟨ f∈ , refl ⟩ ⟩

Λᵐ-good : ∀ {P} → Good P (ν ■ ∷ []) Λᵐ
Λᵐ-good = ⇂-good Λ-good

⋆ᵐ-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) ⋆ᵐ
⋆ᵐ-good = strict-good (checkₒ-good (strict₂-good ⋆-good) (λ {X} {Ds} → ≫=-needs {D = proj₁ Ds} (λ {Y} → ⋆-needs {X} {Y})))

𝒯ᵐ-good : ∀ {P} n → Good P (replicate n ■) (𝒯ᵐ n)
𝒯ᵐ-good n = record
  { mono = λ _ _ Ds⊆ → lift (binds-mono n Ds⊆ (λ Xs⊆ → lower (𝒯-mono n _ _ Xs⊆)))
  ; consis = λ _ _ _ Ds~ → lift (binds-consis n Ds~ (λ Xs~ → lower (𝒯-consis n _ _ Xs~)))
  ; cont = λ Es NE ok → binds-cont n Es NE ok (λ _ Xs⊆ → lower (𝒯-mono n _ _ Xs⊆)) (λ Ms okM → 𝒯-cont n Ms NE okM) }

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

{- (λx. F x) D means F D, for D a consistent set of values -}
letᵐ-β : ∀ {F D} → Mono₁ F → Finitary F D → Con D → Clean D → nonempty D → letᵐ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ F D
letᵐ-β {F} {D} m fin cD clD neD =
  ≃-trans (≫=-β {F = λ G → checked fun G (D ≫= λ X → ⋆ ⟨ G , ⟨ X , ptt ⟩ ⟩)}
                (λ X⊆ → checked-mono X⊆ (≫=-mono (λ d z → z) (λ Y⊆ → lower (⋆-mono ⟨ _ , ⟨ _ , ptt ⟩ ⟩ ⟨ _ , ⟨ _ , ptt ⟩ ⟩ ⟨ lift X⊆ , ⟨ lift Y⊆ , ptt ⟩ ⟩))))
                Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩)
  (≃-trans (checked-ok Λᵐ-fun)
  (≃-trans (≫=-β {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}
                (λ Y⊆ → lower (⋆-mono ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ _ , ptt ⟩ ⟩ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ _ , ptt ⟩ ⟩ ⟨ lift (λ d z → z) , ⟨ lift Y⊆ , ptt ⟩ ⟩)) clD neD)
     ⟨ (λ w w∈ → proj₁ (Λ-β m fin cD) w (A w w∈)) , (λ w w∈ → B w (proj₂ (Λ-β m fin cD) w w∈)) ⟩))
  where
  A : ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ letD ⟨ D , ⟨ F , ptt ⟩ ⟩
  A w ⟨ V , ⟨ ⟨ e∈ , _ ⟩ , r ⟩ ⟩ = ⟨ V , ⟨ e∈ , r ⟩ ⟩
  B : letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ⊆ ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  B w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ e∈ , (λ ω∈ → clD ω (V⊆ ω ω∈) refl) ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩

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

𝒞ᵐ-inl-β : ∀ {D F G} → Mono₁ F → Finitary F D → Con D → Clean D → nonempty D
  → 𝒞ᵐ ⟨ inlᵐ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ F D
𝒞ᵐ-inl-β {F = F} {G} m fin cD clD neD =
  ≃-trans (𝒞ᵐ-inj {F = F} {G} left inl (λ X⊆ → lower (inl-mono _ _ ⟨ lift X⊆ , ptt ⟩)) (λ { c ω () refl })
             (λ { (left v) v∈ → ⟨ refl , clD v v∈ ⟩ }) (λ e e∈ → e∈) clD neD)
          (𝒞-inl-β {G = G} m fin cD)

𝒞ᵐ-inr-β : ∀ {D F G} → Mono₁ G → Finitary G D → Con D → Clean D → nonempty D
  → 𝒞ᵐ ⟨ inrᵐ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ G D
𝒞ᵐ-inr-β {F = F} {G} m fin cD clD neD =
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

{- a projection from a tuple of sets of values -}
projᵐ-𝒯ᵐ : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → (∀ j → Clean (nthD Ds j) × nonempty (nthD Ds j))
  → (i : Fin n) → projᵐ i ⟨ 𝒯ᵐ n Ds , ptt ⟩ ≃ nthD Ds i
projᵐ-𝒯ᵐ (suc n) Ds cn i =
  ≃-trans (projᵐ-≃ i (binds-β (suc n) (λ Xs⊆ → lower (𝒯-mono (suc n) _ _ Xs⊆)) cn))
  (≃-trans (≫=-β {F = λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} (λ X⊆ → checked-mono X⊆ (λ d → X⊆ (tup[ i ] d)))
                 (𝒯-clean (suc n)) ⟨ tup[ i ] _ , ⟨ refl , ⟨ proj₂ (proj₂ (cn i)) , ne ⟩ ⟩ ⟩)
  (≃-trans (checked-ok (λ { (tup[ j ] d) ⟨ refl , _ ⟩ → refl }))
     ⟨ (λ { d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ → d∈ }) , (λ d d∈ → ⟨ refl , ⟨ d∈ , ne ⟩ ⟩) ⟩))
  where ne = λ j → proj₂ (cn j)
