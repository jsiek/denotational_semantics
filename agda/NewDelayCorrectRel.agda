{-# OPTIONS --no-positivity-check #-}

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

to-ne : ∀ V → V ≢ [] → tos V ≢ []
to-ne [] neV = ⊥-elim (neV refl)
to-ne (x ∷ V) neV ()

tos-length : ∀ V → length (tos V) ≡ length V
tos-length [] = refl
tos-length (x ∷ V) = cong suc (tos-length V)

tos-nth : ∀ V i → to (nth V i) ≡ nth (tos V) i
tos-nth [] zero = refl
tos-nth (x ∷ V) zero = refl
tos-nth [] (suc i) = refl
tos-nth (x ∷ V) (suc i) = tos-nth V i

to-∈-mem : ∀ {a}{V} → a ∈ (mem V) → to a ∈ mem (tos V)
to-∈-mem (here px) = here (cong to px)
to-∈-mem (there a∈) = there (to-∈-mem a∈)

∈-mem-tos : ∀ {d}{V} → d ∈ mem (tos V) → Σ[ a ∈ Value ] a ∈ mem V × d ≡ to a
∈-mem-tos {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-tos {d} {x ∷ V} (there d∈) with ∈-mem-tos d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

to-mem-rewrite : ∀ V ρ → env-map to (mem V • ρ) ⊆ₑ (mem (tos V)) • env-map to ρ
to-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = to-∈-mem a∈V
to-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx


delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)

delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv , FV ⊢ν) ⟨ fv∈𝒯fvs , FV⊆𝒯fvs ⟩ = ⟨ G1 , G3 ⟩
  where
  G1 : (ω , [] ⊢ to fv , tos FV ↦ (ω , [] ⊢ν)) ∈ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ delay N ⟧' (Y • X • (λ _ x → x ≡ ω))) , ptt ⟩) , ptt ⟩
  G1 = tt
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯fvs
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv , FV ⊢ v , V ↦ w) ⟨ fv∈𝒯 , ⟨ FV⊆𝒯 , w∈N ⟩ ⟩
  = ⟨ G1 , G3 ⟩
  where
  H : env-map to (mem (v ∷ V) • mem (fv ∷ FV) • (λ x → NewClos3.init))
         ⊆ₑ mem (tos (v ∷ V)) • mem (tos (fv ∷ FV)) • (λ x → NewClos4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : (ω , [] ⊢ to fv , tos FV ↦ (ω , [] ⊢ to v , tos V ↦ to w)) 
     ∈ Λ ⟨ (λ X → Λ ⟨ ⟦ clear' (bind' (bind' (ast' (delay N)))) ⟧ₐ' (env-map to ρ) X 
          , ptt ⟩) , ptt ⟩
  G1 = NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) 
                (delay-preserve N (mem (v ∷ V) • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w w∈N)
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯 a a∈)
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ v , ⟨ V , ⟨ fv , ⟨ FV , ⟨ FV⊢V↦d∈M , V⊆N ⟩ ⟩ ⟩ ⟩ ⟩ 
  with delay-preserve M ρ (fv , FV ⊢ v , V ↦ d) FV⊢V↦d∈M | delay-preserve-⊆ N ρ (v ∷ V) V⊆N
... | clos∈M' | V'⊆N' = 
   ⟨ to v , ⟨ tos V , ⟨ ω , ⟨ [] , ⟨ ⟨ to fv , ⟨ tos FV , ⟨ ω , ⟨ [] , 
     ⟨ ⟨ to fv , ⟨ tos FV , clos∈M' ⟩ ⟩ , second ⟩ ⟩ ⟩ ⟩ ⟩ , V'⊆N' ⟩ ⟩ ⟩ ⟩ ⟩
   where
   second : ∀ d' → d' ∈ mem (to fv ∷ tos FV) → d' ∈ cdr ⟨ ⟦ delay M ⟧' (env-map to ρ) , ptt ⟩
   second d' d'∈tosFV = ⟨ ω , [] ⊢ to fv , tos FV ↦ (ω , [] ⊢ to v , tos V ↦ to d) , ⟨ to fv , ⟨ tos FV , ⟨ clos∈M' , d'∈tosFV ⟩ ⟩ ⟩ ⟩
delay-preserve (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = d∈
delay-preserve (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ ρ → to d ∈ ⟦ delay (tuple n ⦅ args ⦆ ) ⟧' (env-map to ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-preserve arg ρ d d∈ , ds'∈ ⟩  
delay-preserve (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ tos ds , ⟨ subst (Data.Nat._<_ i) (sym (tos-length ds)) i≤ 
  , ⟨ delay-preserve M ρ ∥ ds ∥ ds∈ , tos-nth ds i ⟩ ⟩ ⟩
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (left v , V) V⊆ = 
  delay-preserve-⊆ M ρ (v ∷ V) V⊆
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (right v , V) V⊆ = 
  delay-preserve-⊆ M ρ (v ∷ V) V⊆
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ to v , ⟨ tos V , ⟨ delay-preserve L ρ (left v , V) LV∈ 
        , NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay M) 
                               (to-mem-rewrite (v ∷ V) ρ) (to d) 
                               (delay-preserve M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ to v , ⟨ tos V , ⟨ delay-preserve L ρ (right v , V) RV∈ 
        , NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) 
                               (to-mem-rewrite (v ∷ V) ρ) (to d) 
                               (delay-preserve N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩

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

≈del-length : ∀ {V V'} → V ≈del V' → length V ≡ length V'
≈del-length ≈del-nil = refl
≈del-length (≈del-cons v~ V~) = cong suc (≈del-length V~)

≈del-nth : ∀ {V V'} → V ≈del V' → ∀ i → nth V i ~del nth V' i
≈del-nth ≈del-nil i = ~del-ω
≈del-nth (≈del-cons v~ V~) zero = v~
≈del-nth (≈del-cons v~ V~) (suc i) = ≈del-nth V~ i

≈del-tos : ∀ ds → ds ≈del (tos ds)
~del-to : ∀ d → d ~del (to d)
~del-to (const k) = ~del-const k
~del-to (d , FV ⊢ d₁ , V ↦ d₂) = ~del-clos (λ v z → z) (inj₂ ⟨ ≈del-cons (~del-to d₁) (≈del-tos V) , ~del-to d₂ ⟩)
~del-to (d , FV ⊢ν) = ~del-ν (λ v z → z)
~del-to ω = ~del-ω
~del-to ⦅ d ∣ d₁ , FV ⦆ = ~del-pair
~del-to ∥ ds ∥ = ~del-tup (≈del-tos ds)
~del-to (left v , V) = ~del-L (≈del-cons (~del-to v) (≈del-tos V))
~del-to (right v , V) = ~del-R (≈del-cons (~del-to v) (≈del-tos V))
≈del-tos [] = ≈del-nil
≈del-tos (x ∷ ds) = ≈del-cons (~del-to x) (≈del-tos ds)

~del-env : Env Value → Env Value → Set
~del-env ρ ρ' = ∀ i d → d ∈ ρ i → Σ[ d' ∈ Value ] d' ∈ ρ' i × d ~del d'

~del-env-rev : Env Value → Env Value → Set
~del-env-rev ρ ρ' = ∀ i d' → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × d ~del d'

del-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → Σ[ ρ' ∈ Env Value ] ~del-env ρ ρ' × Σ[ d' ∈ Value ] d ~del d' × d' ∈ ⟦ delay M ⟧' ρ'
del-preserve M ρ d d∈ = ⟨ env-map to ρ , ⟨ (λ i d' d'∈ → ⟨ to d' , ⟨ ⟨ d' , ⟨ d'∈ , refl ⟩ ⟩ , ~del-to d' ⟩ ⟩) , ⟨ to d , ⟨ ~del-to d , delay-preserve M ρ d d∈ ⟩ ⟩ ⟩ ⟩


del-reflect : ∀ M ρ' d' → d' ∈ ⟦ delay M ⟧' ρ' 
            → ∀ ρ → ~del-env-rev ρ ρ' → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × d ~del d'
{- del-args-reflect : ∀ {n} args ρ → results-rel-pres _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))  -}
del-reflect-⊆ : ∀ M ρ' V' → mem V' ⊆ ⟦ delay M ⟧' ρ' → 
   ∀ ρ → ~del-env-rev ρ ρ' → Σ[ V ∈ List Value ] mem V ⊆ ⟦ M ⟧ ρ × V ≈del V'
del-reflect (` x) ρ' d' d'∈ ρ ρ~ = ρ~ x d' d'∈ {- ⟨ d , ⟨ d∈ , refl ⟩ ⟩ -}
del-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' 
  ⦅ fv , FV ⊢ν ∣ fv' , FV' ⦆ ⟨ f∈ , T⊆ ⟩ ρ ρ~ 
  = {!   !} 
del-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' 
  ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ν)) ∣ fv' , FV' ⦆ ⟨ f∈ , T⊆ ⟩ ρ ρ~ 
  = {!   !}
del-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' 
  ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ v , V ↦ w)) ∣ fv' , FV' ⦆ ⟨ w∈ , T⊆ ⟩ ρ ρ~ 
  = {!   !}
{- ⦅ (fv , FV ⊢ν) ∣ fv' , FV' ⦆ ⟨ f∈ , T⊆ ⟩ 
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ del-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (T⊆ b (there b∈))
del-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ν)) ∣ fv' , FV' ⦆ ⟨ F⊆ , T⊆ ⟩
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ del-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (there a∈))
del-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ v , V ↦ w)) ∣ fv' , FV' ⦆ ⟨ w∈ , T⊆ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
... | no FV⊈ = ⟨ G3 (fro fv') (here refl) , (λ b b∈ → G3 b (there b∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ del-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (there a∈))
... | yes FV⊆ = ⟨ G3 (fro fv) (here refl) , ⟨ (λ x x∈ → G3 x (there x∈)) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv ∷ FV) • λ x → NewClos4.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init))
  G1 = NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (del-reflect N (mem (v ∷ V) • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ del-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv (T⊆ fv (FV⊆ fv (here refl)))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (FV⊆ a (there a∈)))
-}
del-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ' d' d'∈ ρ ρ~ = {!   !}
{- 
   ⟨ v , ⟨ V , ⟨ fvouter , ⟨ FVouter , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩ with inner-app
... | ⟨ fv , ⟨ FV , ⟨ a , ⟨ A , ⟨ ⟨ fv' , ⟨ FV' , U∈M' ⟩ ⟩ , vV'⊆sndM' ⟩ ⟩ ⟩ ⟩ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') | del-reflect M ρ ⦅ a , A ⊢ fv , FV ↦ (fvouter , FVouter ⊢ v , V ↦ d) ∣ fv' , FV' ⦆ U∈M'
... | no FV⊈ |  q = ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ ⟩
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  {-
  G1 : {!   !}
  G1 = {! del-reflect M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = del-reflect-⊆ N ρ (v ∷ V) V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ HOLE , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = del-reflect-⊆ N ρ (v ∷ V) V⊆N' {- del-reflect M ρ ⦅ (fv' , FV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}
-}

del-reflect (lit B k ⦅ Nil ⦆) ρ' (const {B'} k') d'∈ ρ ρ~ = ⟨ const k' , ⟨ d'∈ , ~del-const k' ⟩ ⟩
del-reflect (tuple n ⦅ args ⦆) ρ' d' d'∈ ρ ρ~ = {!   !}
{- G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ del-reflect arg ρ d d∈ , ds'∈ ⟩
-}
del-reflect (get i ⦅ M ,, Nil ⦆) ρ' d' ⟨ ds' , ⟨ i≤ , ⟨ ds'∈ , refl ⟩ ⟩ ⟩ ρ ρ~ 
  with del-reflect M ρ' ∥ ds' ∥ ds'∈ ρ ρ~
... | ⟨ ∥ ds ∥ , ⟨ ds∈ , ~del-tup ds≈ ⟩ ⟩ = 
  ⟨ nth ds i , 
  ⟨ ⟨ ds , ⟨ subst (Data.Nat._<_ i) (sym (≈del-length ds≈)) i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ 
    , ≈del-nth ds≈ i ⟩ ⟩
{- ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ del-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
-}
del-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' (left v' , V') V'⊆ ρ ρ~
  with del-reflect M ρ' v' (V'⊆ v' (here refl)) ρ ρ~ | del-reflect-⊆ M ρ' V' (λ d z → V'⊆ d (there z)) ρ ρ~
... | ⟨ v , ⟨ v∈ , v~ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , V≈ ⟩ ⟩ = ⟨ left v , V , ⟨ G , ~del-L (≈del-cons v~ V≈) ⟩ ⟩ 
  where
  G : mem (v ∷ V) ⊆ ⟦ M ⟧ ρ
  G d (here refl) = v∈
  G d (there d∈) = V⊆ d d∈
del-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' (right v' , V') V'⊆ ρ ρ~  
  with del-reflect M ρ' v' (V'⊆ v' (here refl)) ρ ρ~ | del-reflect-⊆ M ρ' V' (λ d z → V'⊆ d (there z)) ρ ρ~
... | ⟨ v , ⟨ v∈ , v~ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , V≈ ⟩ ⟩ = ⟨ right v , V , ⟨ G , ~del-R (≈del-cons v~ V≈) ⟩ ⟩ 
  where
  G : mem (v ∷ V) ⊆ ⟦ M ⟧ ρ
  G d (here refl) = v∈
  G d (there d∈) = V⊆ d d∈
del-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ' d' d'∈ ρ ρ~ = {!   !}
{- 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ del-reflect L ρ (left v , V) LV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (del-reflect M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
del-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ del-reflect L ρ (right v , V) RV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (del-reflect N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
-}
del-reflect-⊆ M ρ' [] V'⊆ ρ ρ~ = ⟨ [] , ⟨ (λ x ()) , ≈del-nil ⟩ ⟩
del-reflect-⊆ M ρ' (v' ∷ V') V'⊆ ρ ρ~ with 
   del-reflect M ρ' v' (V'⊆ v' (here refl)) ρ ρ~ 
   | del-reflect-⊆ M ρ' V' (λ d z → V'⊆ d (there z)) ρ ρ~
... | ⟨ v , ⟨ v∈ , v~ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , V≈ ⟩ ⟩ = ⟨ v ∷ V , ⟨ G , ≈del-cons v~ V≈ ⟩ ⟩
  where
  G : mem (v ∷ V) ⊆ ⟦ M ⟧ ρ
  G d (here refl) = v∈
  G d (there d∈) = V⊆ d d∈