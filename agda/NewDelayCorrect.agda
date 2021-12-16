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
to (fv , FV ⊢ V ↦ w) = ⦅ ω , [] ⊢ tos (fv ∷ FV) ↦ (ω , [] ⊢ tos V ↦ to w) , tos (fv ∷ FV) ⦆
to (fv , FV ⊢ν) = ⦅ ω , [] ⊢ tos (fv ∷ FV) ↦ (ω , [] ⊢ν) , tos (fv ∷ FV) ⦆
to ω = ω
to ⦅ u , V ⦆ = ⦅ to u , tos V ⦆
to ∥ xs ∥ = ∥ tos xs ∥
to (left V) = left (tos V)
to (right V) = right (tos V)
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
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv , FV ⊢ν) ⟨ fv∈𝒯fvs , FV⊆𝒯fvs ⟩ = ⟨ G1 , ⟨ G3 , (λ ()) ⟩ ⟩
  where
  G1 : (ω , [] ⊢ tos (fv ∷ FV) ↦ (ω , [] ⊢ν)) ∈ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ delay N ⟧' (Y • X • (λ _ x → x ≡ ω))) , ptt ⟩) , ptt ⟩
  G1 = ⟨ tt , (λ ()) ⟩
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯fvs
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv , FV ⊢ V ↦ w) ⟨ fv∈𝒯 , ⟨ FV⊆𝒯 , ⟨ w∈N , neV ⟩ ⟩ ⟩
  = ⟨ G1 , ⟨ G3 , (λ ()) ⟩ ⟩
  where
  H : env-map to (mem V • mem (fv ∷ FV) • (λ x → NewClos3.init))
         ⊆ₑ mem (tos V) • mem (tos (fv ∷ FV)) • (λ x → NewClos4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : (ω , [] ⊢ tos (fv ∷ FV) ↦ (ω , [] ⊢ tos V ↦ to w)) 
     ∈ Λ ⟨ (λ X → Λ ⟨ ⟦ clear' (bind' (bind' (ast' (delay N)))) ⟧ₐ' (env-map to ρ) X 
          , ptt ⟩) , ptt ⟩
  G1 = 
    ⟨ ⟨ NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) 
                (delay-preserve N (mem V • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w w∈N) 
      , to-ne V neV ⟩ , (λ ()) ⟩
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ 𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯 a a∈)
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ V , ⟨ fv , ⟨ FV , ⟨ FV⊢V↦d∈M , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩ ⟩ 
  with delay-preserve M ρ (fv , FV ⊢ V ↦ d) FV⊢V↦d∈M | delay-preserve-⊆ N ρ V V⊆N
... | clos∈M' | V'⊆N' = 
    ⟨ tos V , ⟨ ω , ⟨ [] , 
    ⟨ ⟨ tos (fv ∷ FV) , ⟨ ω , ⟨ [] , ⟨ ⟨ to fv ∷ tos FV , ⟨ clos∈M' , (λ ()) ⟩ ⟩ , ⟨ second , (λ ()) ⟩ ⟩ ⟩ ⟩ ⟩ 
    , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
   where
   second : (x : Value) (x₁ : Any (_≡_ x) (tos (fv ∷ FV))) → Σ Value
             (λ z → Σ (List Value) (λ z₁ → Σ (⟦ delay M ⟧'
            (λ z₂ x₂ → Σ Value (λ z₃ → Σ (ρ z₂ z₃) (λ _ → x₂ ≡ to z₃))) ⦅ z , z₁ ⦆)
             (λ _ → Any (_≡_ x) z₁)))
   second d' d'∈tosFV = ⟨ (ω , [] ⊢ tos (fv ∷ FV) ↦ (ω , [] ⊢ tos V ↦ to d)) , ⟨ tos (fv ∷ FV) , ⟨ clos∈M' , d'∈tosFV ⟩ ⟩ ⟩
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
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (left V) ⟨ neV , V⊆ ⟩ = 
  ⟨ to-ne V neV , delay-preserve-⊆ M ρ V V⊆ ⟩
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (right V) ⟨ neV , V⊆ ⟩ = 
  ⟨ to-ne V neV , delay-preserve-⊆ M ρ V V⊆ ⟩
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ tos V , ⟨ delay-preserve L ρ (left V) LV∈ 
        , NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay M) 
                               (to-mem-rewrite V ρ) (to d) 
                               (delay-preserve M (mem V • ρ) d d∈) ⟩ ⟩
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) = 
   inj₂ ⟨ tos V , ⟨ delay-preserve L ρ (right V) RV∈ 
        , NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) 
                               (to-mem-rewrite V ρ) (to d) 
                               (delay-preserve N (mem V • ρ) d d∈) ⟩ ⟩
delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩





{-
need to check for equality of fv' with fv
and FV' with FV

-}

fros : List Value → List Value
fro : Value → Value
fro (const x) = const x
fro (fv , FV ⊢ V ↦ w) = ω
fro (fv , FV ⊢ν) = ω
fro ω = ω
fro ⦅ (_ , _ ⊢ν) , (fv ∷ FV) ⦆ = fro fv , fros FV ⊢ν
fro ⦅ (_ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ν)) , (fv' ∷ FV') ⦆ = fro fv' , fros FV' ⊢ν
fro ⦅ _ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν
fro ⦅ U , V ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left V) = left (fros V)
fro (right V) = right (fros V)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value → 𝒫 Value
fro-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (nth V i) ≡ nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

fro-mem-rewrite : ∀ V ρ → env-map fro (mem V • ρ) ⊆ₑ (mem (fros V)) • env-map fro ρ
fro-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = fro-∈-mem a∈V
fro-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx


delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect : ∀ {n} args ρ → results-rel-pres _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ)) 
delay-reflect-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (fv , FV ⊢ν) , [] ⦆ ⟨ f∈ , ⟨ T⊆ , neT ⟩ ⟩ = ⊥-elim (neT refl)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (fv , FV ⊢ν) , fv' ∷ FV' ⦆ ⟨ f∈ , ⟨ T⊆ , neT ⟩ ⟩ 
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (T⊆ b (there b∈))
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (fv , FV ⊢ V ↦ w) , [] ⦆ ⟨ ⟨ F⊆ , neF ⟩ , ⟨ T⊆ , neT ⟩ ⟩ = ⊥-elim (neT refl)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (a , A ⊢ [] ↦ (b , B ⊢ν)) , fv' ∷ FV' ⦆ ⟨ f∈ , ⟨ T⊆ , neT ⟩ ⟩
  = proj₂ f∈ refl
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (a , A ⊢ (fv ∷ FV) ↦ (b , B ⊢ν)) , fv' ∷ FV' ⦆ ⟨ ⟨ F⊆ , neF ⟩ , ⟨ T⊆ , neT ⟩ ⟩
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (there a∈))
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ (a , A ⊢ [] ↦ (b , B ⊢ V ↦ w)) , fv' ∷ FV' ⦆ ⟨ ⟨ F⊆ , neF ⟩ , ⟨ T⊆ , neT ⟩ ⟩ = 
  neF refl
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ (a , A ⊢ (fv ∷ FV) ↦ (b , B ⊢ V ↦ w)) , fv' ∷ FV' ⦆ ⟨ ⟨ ⟨ w∈ , neV ⟩ , neF ⟩ , ⟨ T⊆ , neT ⟩ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
... | no FV⊈ = ⟨ G3 (fro fv') (here refl) , (λ b b∈ → G3 b (there b∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (there a∈))
... | yes FV⊆ = ⟨ G3 (fro fv) (here refl) , ⟨ (λ x x∈ → G3 x (there x∈)) , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  H : env-map fro (mem V • mem (fv ∷ FV) • λ x → NewClos4.init)
      ⊆ₑ mem (fros V) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init))
  G1 = NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect N (mem V • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv (T⊆ fv (FV⊆ fv (here refl)))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (FV⊆ a (there a∈)))

delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ V , ⟨ fvouter , ⟨ FVouter , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ ⟩ ⟩ with inner-app
... | ⟨ [] , ⟨ a , ⟨ A , ⟨ d∈fstM' , ⟨ []⊆sndM' , neV' ⟩ ⟩ ⟩ ⟩ ⟩ = ⊥-elim (neV' refl)
... | ⟨ (fv ∷ FV) , ⟨ a , ⟨ A , ⟨ ⟨ [] , ⟨ U∈M' , ne[] ⟩ ⟩ , ⟨ vV'⊆sndM' , neFV ⟩ ⟩ ⟩ ⟩ ⟩ = ⊥-elim (ne[] refl)
... | ⟨ (fv ∷ FV) , ⟨ a , ⟨ A , ⟨ ⟨ fv' ∷ FV' , ⟨ U∈M' , neU₂ ⟩ ⟩ , ⟨ vV'⊆sndM' , neFV ⟩ ⟩ ⟩ ⟩ ⟩ 
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') | delay-reflect M ρ ⦅ a , A ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d) , fv' ∷ FV' ⦆ U∈M'
... | no FV⊈ | G1 = 
   ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ G2 , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G1 : ?
  G1 = ?
  G2 : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect-⊆ N ρ V V⊆N'
... | yes FV⊆ | G1
  =  ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ G1 , ⟨ G2 , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect-⊆ N ρ V V⊆N' {- delay-reflect M ρ ⦅ (fv' , FV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}

delay-reflect (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = d∈
delay-reflect (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d d∈ , ds'∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left V) ⟨ neV , V⊆ ⟩ = 
  ⟨ fro-ne V neV , delay-reflect-⊆ M ρ V V⊆ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right V) ⟨ neV , V⊆ ⟩ = 
  ⟨ fro-ne V neV , delay-reflect-⊆ M ρ V V⊆ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ fros V , ⟨ delay-reflect L ρ (left V) LV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite V ρ) (fro d) 
                               (delay-reflect M (mem V • ρ) d d∈) ⟩ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) = 
   inj₂ ⟨ fros V , ⟨ delay-reflect L ρ (right V) RV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite V ρ) (fro d) 
                               (delay-reflect N (mem V • ρ) d d∈) ⟩ ⟩
delay-reflect-⊆ M ρ [] V⊆ = λ d ()
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect M ρ d (V⊆ d (here refl))
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect {zero} args ρ = lift tt
del-map-args-reflect {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect M ρ) , del-map-args-reflect args ρ ⟩