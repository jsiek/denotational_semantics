open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import NewDomain
open import NewDOp
open import NewClos3
open import NewClos4 
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import NewCompiler using (delay; del-map-args)
open import NewEnv
open import Primitives

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)

{-
tos : List Value → List Value
to : Value → Value
to (const x) = const x
to (fv , FV ⊢ v , V ↦ w) = ⦅ ω , [] ⊢ to fv , tos FV ↦ (ω , [] ⊢ to v , tos V ↦ to w) ∣ to fv ,  tos FV ⦆
to (fv , FV ⊢ν) = ⦅ ω , [] ⊢ to fv , tos FV ↦ (ω , [] ⊢ν) ∣ to fv , tos FV ⦆
to ω = ω
to ⦅ u ∣ v , V ⦆ = ω
to ∥ xs ∥ = ∥ tos xs ∥
to (left v , V) = left to v , tos V
to (right v , V) = right to v , tos V
tos List.[] = []
tos (d List.∷ ds) = to d List.∷ tos ds

to-set : 𝒫 Value → 𝒫 Value
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d

_to-⊆_ : 𝒫 Value → 𝒫 Value → Set
A to-⊆ B = ∀ d → d ∈ A → to d ∈ B

env-map : ∀ {A B : Set} → (A → B) → (ℕ → 𝒫 A) → (ℕ → 𝒫 B)
env-map {A} {B} f ρ x b = Σ[ a ∈ A ] a ∈ (ρ x) × b ≡ f a

delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)
-}

{-
fros : List Value → List Value
fro : Value → Value
fro (const x) = const x
fro (fv , FV ⊢ v , V ↦ w) = ω
fro (fv , FV ⊢ν) = ω
fro ω = ω
fro ⦅ (_ , _ ⊢ν) ∣ fv , FV ⦆ = fro fv , fros FV ⊢ν
fro ⦅ (_ , _ ⊢ fv , FV ↦ (_ , _ ⊢ν)) ∣ fv' , FV' ⦆ = fro fv' , fros FV' ⊢ν
fro ⦅ _ , _ ⊢ fv , FV ↦ (_ , _ ⊢ v , V ↦ w) ∣ fv' , FV' ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fro v , fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν
fro ⦅ U ∣ v , V ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v , V) = left fro v , fros V
fro (right v , V) = right fro v , fros V
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds

{- thought : salient is on post-delay semantics, and so it shouldn't care about annotations -}
salient : Value → Set
salients : List Value → Set
salient (const k) = True
salient (fv , FV ⊢ v , V ↦ w) = salients (v ∷ V) × salient w
salient (fv , FV ⊢ν) = salients (fv ∷ FV)
salient ω = True
salient ⦅ (a , A ⊢ fv , FV ↦ w) ∣ fv' , FV' ⦆ = 
 {- other thought : I think the proof itself handles non-functional or empty function w's,
    so we only have to worry about the outermost structure of the closure -}
  salients (fv ∷ FV)
  × salient w
  × salients (fv' ∷ FV')
  × mem (fv ∷ FV) ⊆ mem (fv' ∷ FV')
salient ⦅ f ∣ fv' , FV' ⦆ = False
salient ∥ ds ∥ = salients ds
salient (left v , V) = salients (v ∷ V)
salient (right v , V) = salients (v ∷ V)
salients [] = True
salients (d ∷ ds) = salient d × salients ds

delay-reflect : ∀ M ρ d → salient d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect : ∀ {n} args ρ → results-rel-pres _fro-⊆-sal_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ)) 
delay-reflect-⊆ : ∀ M ρ V → salients V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ)) 
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)
-}


{- 
data _≈del_ : List Value → List Value → Set
data _~del_ : Value → Value → Set where
  ~del-const : ∀ {B} (k : base-rep B) → const k ~del const k
  ~del-ω : ω ~del ω
  ~del-L : ∀ {v V v' V'} 
           → (v ∷ V) ≈del (v' ∷ V')
           → (left v , V) ~del (left v' , V')
  ~del-R : ∀ {v V v' V'} 
           → (v ∷ V) ≈del (v' ∷ V')
           → (right v , V) ~del (right v' , V')
  ~del-ν : ∀ {fv FV fv' FV' a A b B c C} 
           → mem (fv' ∷ FV') ⊆ mem (fv ∷ FV)
           → (a , A ⊢ν) ~del ⦅ (b , B ⊢ fv' , FV' ↦ (c , C ⊢ν)) ∣ fv , FV ⦆
  ~del-clos : ∀ {fv FV fv' FV' v V v' V' w w' a A b B c C} 
           → mem (fv' ∷ FV') ⊆ mem (fv ∷ FV)
           → ((¬ ((v ∷ V) ≈del (v' ∷ V'))) ⊎ ((v ∷ V) ≈del (v' ∷ V')) × w ~del w')
           → (a , A ⊢ v , V ↦ w) ~del ⦅ (b , B ⊢ fv' , FV' ↦ (c , C ⊢ v' , V' ↦ w')) ∣ fv , FV ⦆
  ~del-tup : ∀ {ds ds'}
           → ds ≈del ds'
           → ∥ ds ∥ ~del ∥ ds' ∥
  ~del-pair : ∀ {d fv FV} → ⦅ d ∣ fv , FV ⦆ ~del ω

data _≈del_ where
  ≈del-nil : [] ≈del []
  ≈del-cons : ∀ {v v' V V'}
            → v ~del v'
            → V ≈del V'
            → (v ∷ V) ≈del (v' ∷ V')

del-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → Σ[ ρ' ∈ Env Value ] ~del-env ρ ρ' × Σ[ d' ∈ Value ] d ~del d' × d' ∈ ⟦ delay M ⟧' ρ'
del-preserve M ρ d d∈ = ⟨ env-map to ρ , ⟨ (λ i d' d'∈ → ⟨ to d' , ⟨ ⟨ d' , ⟨ d'∈ , refl ⟩ ⟩ , ~del-to d' ⟩ ⟩) , ⟨ to d , ⟨ ~del-to d , delay-preserve M ρ d d∈ ⟩ ⟩ ⟩ ⟩


del-reflect : ∀ M ρ' d' → d' ∈ ⟦ delay M ⟧' ρ' 
            → ∀ ρ → ~del-env-rev ρ ρ' → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × d ~del d'
{- del-args-reflect : ∀ {n} args ρ → results-rel-pres _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))  -}
del-reflect-⊆ : ∀ M ρ' V' → mem V' ⊆ ⟦ delay M ⟧' ρ' → 
   ∀ ρ → ~del-env-rev ρ ρ' → Σ[ V ∈ List Value ] mem V ⊆ ⟦ M ⟧ ρ × V ≈del V'
-}


ℬ-const : ∀ {B k} → ℬ B k ptt ≃ ⌈ const {B} k ⌉
ℬ-const {B} {k} = ⟨ forw , backw ⟩
   where
   forw : ℬ B k ptt ⊆ ⌈ const k ⌉
   forw (const {B'} k') d∈ with base-eq? B B'
   ... | yes refl = cong const (sym d∈)
   ... | no neq = ⊥-elim d∈
   backw : ⌈ const k ⌉ ⊆ ℬ B k ptt
   backw .(const k) refl with base-eq? B B
   ... | yes refl = refl
   ... | no neq = ⊥-elim (neq refl)




{- should I be worried about respecting setoid equality?? -}
{- current answer:
   I don't have to, because denotations _will be_ defined by denot-ops -}
data _~d_ : 𝒫 Value → 𝒫 Value → Set₁ where
  ~d-ω : ∀ {D D'} → D ω → D' ω → D ~d D'
  ~d-ℬ : ∀ {B} (k : base-rep B) → ℬ B k ptt ~d ℬ B k ptt
  ~d-ℒ : ∀ {D D'}
       → D ~d D'
       → ℒ ⟨ D , ptt ⟩ ~d ℒ ⟨ D' , ptt ⟩
  ~d-ℛ : ∀ {D D'}
       → D ~d D'
       → ℛ ⟨ D , ptt ⟩ ~d ℛ ⟨ D' , ptt ⟩
  ~d-pair : ∀ {D D' f fv FV} → D ⦅ f ∣ fv , FV ⦆ → D' ω → D ~d D'
  ~d-ν-ν : ∀ {D D' fv FV fv' FV' a A b B c C} 
        → D (a , A ⊢ν) 
        → D' ⦅ b , B ⊢ fv , FV ↦ (c , C ⊢ν) ∣ fv' , FV' ⦆
        → D ~d D'
  ~d-ν-↦ : ∀ {D D' fv FV v' V' w' fv' FV' a A b B c C}
        → D (a , A ⊢ν)
        → D' ⦅ b , B ⊢ fv , FV ↦ (c , C ⊢ v' , V' ↦ w') ∣ fv' , FV' ⦆
        → ¬ (mem (fv ∷ FV) ⊆ (cdr ⟨ D' , ptt ⟩))
        → D ~d D'
  ~d-↦ : ∀ {D D' fv FV v V w v' V' w' fv' FV' a A b B c C}
      → D (a , A ⊢ v , V ↦ w)
      → D' ⦅ b , B ⊢ fv , FV ↦ (c , C ⊢ v' , V' ↦ w') ∣ fv' , FV' ⦆
      → mem (fv ∷ FV) ⊆ (cdr ⟨ D' , ptt ⟩)
      → D ~d D'

{-
~d-⊆ : ∀ {D D' U U'} → D ~d D' → U ⊆ D → U' ⊆ D' → U ~d U'
~d-⊆ 
-}

delay-correct : ∀ M ρ ρ' 
              → (∀ i → ρ i ~d (ρ' i))
              → ⟦ M ⟧ ρ ~d ⟦ delay M ⟧' ρ'
delay-correct (` x) ρ ρ' ρ~ = ρ~ x
delay-correct (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ' ρ~ = {!   !}
delay-correct (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ = {!   !}
delay-correct (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ = ~d-ℬ k
delay-correct (tuple n ⦅ args ⦆) ρ ρ' ρ~ = {!   !}
delay-correct (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ = {!   !}
delay-correct (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ = ~d-ℒ (delay-correct M ρ ρ' ρ~)
delay-correct (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ = ~d-ℛ (delay-correct M ρ ρ' ρ~)
delay-correct (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ' ρ~ = {!   !}



{- 
data _≈del_ : List Value → List Value → Set
data _~del_ : Value → Value → Set where
  ~del-const : ∀ {B} (k : base-rep B) → const k ~del const k
  ~del-ω : ω ~del ω
  ~del-L : ∀ {v V v' V'} 
           → (v ∷ V) ≈del (v' ∷ V')
           → (left v , V) ~del (left v' , V')
  ~del-R : ∀ {v V v' V'} 
           → (v ∷ V) ≈del (v' ∷ V')
           → (right v , V) ~del (right v' , V')
  ~del-ν : ∀ {fv FV fv' FV' a A b B c C} 
           → mem (fv' ∷ FV') ⊆ mem (fv ∷ FV)
           → (a , A ⊢ν) ~del ⦅ (b , B ⊢ fv' , FV' ↦ (c , C ⊢ν)) ∣ fv , FV ⦆
  ~del-clos : ∀ {fv FV fv' FV' v V v' V' w w' a A b B c C} 
           → mem (fv' ∷ FV') ⊆ mem (fv ∷ FV)
           → ((¬ ((v ∷ V) ≈del (v' ∷ V'))) ⊎ ((v ∷ V) ≈del (v' ∷ V')) × w ~del w')
           → (a , A ⊢ v , V ↦ w) ~del ⦅ (b , B ⊢ fv' , FV' ↦ (c , C ⊢ v' , V' ↦ w')) ∣ fv , FV ⦆
  ~del-tup : ∀ {ds ds'}
           → ds ≈del ds'
           → ∥ ds ∥ ~del ∥ ds' ∥
  ~del-pair : ∀ {d fv FV} → ⦅ d ∣ fv , FV ⦆ ~del ω

data _≈del_ where
  ≈del-nil : [] ≈del []
  ≈del-cons : ∀ {v v' V V'}
            → v ~del v'
            → V ≈del V'
            → (v ∷ V) ≈del (v' ∷ V')
-}

