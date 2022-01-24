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





{-
need to check for equality of fv' with fv
and FV' with FV

-}

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

salient-∈-mem : ∀ {V}{v} → salients V → v ∈ (mem V) → salient v
salient-∈-mem {x ∷ V} ⟨ fst , snd ⟩ (here refl) = fst
salient-∈-mem {x ∷ V} ⟨ fst , snd ⟩ (there v∈) = salient-∈-mem snd v∈

left-salient : ∀ M ρ → (salρ : ∀ i v → v ∈ ρ i → Σ[ v' ∈ Value ] v' ∈ ρ i × salient v') 
    → ∀ v V → left v , V ∈ ⟦ delay M ⟧' ρ → Σ[ v' ∈ Value ] Σ[ V' ∈ List Value ] left v' , V' ∈ ⟦ delay M ⟧' ρ × salients (v' ∷ V')
left-salient M ρ salρ v V l∈ = {!   !}

terminating-has-salience : ∀ M ρ 
    → (salρ : ∀ i v → v ∈ ρ i → Σ[ v' ∈ Value ] v' ∈ ρ i × salient v') 
    → ∀ d → d ∈ ⟦ delay M ⟧' ρ → Σ[ d' ∈ Value ] d' ∈ ⟦ delay M ⟧' ρ × salient d'
{- terminating-has-salience-⊆ : ∀ M ρ -}
terminating-has-salience (` x) ρ salρ d d∈ = salρ x d d∈
terminating-has-salience (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ salρ d d∈ = 
  {!   !}
terminating-has-salience (app ⦅ M ,, N ,, Nil ⦆) ρ salρ d d∈ = {!   !}
terminating-has-salience (lit B k ⦅ Nil ⦆) ρ salρ (const k₁) d∈ = ⟨ const k₁ , ⟨ d∈ , tt ⟩ ⟩
terminating-has-salience (tuple n ⦅ args ⦆) ρ salρ d d∈ = {!   !}
terminating-has-salience (get i ⦅ M ,, Nil ⦆) ρ salρ d ⟨ fst , snd ⟩ = {!   !}
terminating-has-salience (inl-op ⦅ M ,, Nil ⦆) ρ salρ (left v , V) d∈ = 
  ⟨ left v , V , ⟨ d∈ , {!   !} ⟩ ⟩
terminating-has-salience (inr-op ⦅ M ,, Nil ⦆) ρ salρ (right v , V) d∈ = 
  ⟨ right v , V , ⟨ d∈ , {!   !} ⟩ ⟩
terminating-has-salience (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ salρ d (inj₁ ⟨ v , ⟨ V , ⟨ left∈ , d∈ ⟩ ⟩ ⟩)
  with terminating-has-salience L ρ salρ (left v , V) left∈
... | ⟨ v' , ⟨ v'∈ , salv' ⟩ ⟩
  with terminating-has-salience M (mem (v ∷ V) • ρ) {! v'∈  !} d d∈
... | ⟨ d' , ⟨ d'∈ , sald' ⟩ ⟩ = 
  ⟨ d' , ⟨ inj₁ ⟨ v , ⟨ V , ⟨ left∈ , d'∈ ⟩ ⟩ ⟩ , sald' ⟩ ⟩
terminating-has-salience (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ salρ d (inj₂ ⟨ v , ⟨ V , ⟨ right∈ , d∈ ⟩ ⟩ ⟩)
  = {!    !}

fro-set : 𝒫 Value → 𝒫 Value
fro-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

_fro-⊆-sal_ : 𝒫 Value → 𝒫 Value → Set
A fro-⊆-sal B = ∀ d → salient d → d ∈ A → fro d ∈ B

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


delay-reflect : ∀ M ρ d → salient d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect : ∀ {n} args ρ → results-rel-pres _fro-⊆-sal_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ)) 
delay-reflect-⊆ : ∀ M ρ V → salients V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect (` x) ρ d dsal d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (fv , FV ⊢ν) ∣ fv' , FV' ⦆ () ⟨ f∈ , T⊆ ⟩ 
 {- = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → salient d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d dsal refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ dsal , dsals ⟩ ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d dsal d∈ , G2 n fvs ∥ ds ∥ dsals ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv' {!  !} (T⊆ fv' (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b {!   !} (T⊆ b (there b∈)) -}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ν)) ∣ fv' , FV' ⦆ 
  ⟨ salFV , ⟨ salB ,  ⟨ salFV' , FV⊆ ⟩ ⟩ ⟩  ⟨ F⊆ , T⊆ ⟩
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → salient d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d dsal refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ dsal , dssal ⟩ ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d dsal d∈ , G2 n fvs ∥ ds ∥ dssal ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (proj₁ salFV') (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (salient-∈-mem (proj₂ salFV') a∈) (T⊆ a (there a∈))
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ v , V ↦ w)) ∣ fv' , FV' ⦆ 
  ⟨ salFV , ⟨ ⟨ salV , salw ⟩ , ⟨ salFV' , FV⊆ ⟩ ⟩ ⟩ ⟨ w∈ , T⊆ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
... | no FV⊈ = ⟨ G3 (fro fv') (here refl) , (λ b b∈ → G3 b (there b∈)) ⟩
  where
  G2 : ∀ n fvs d → salient d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d dsal refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ dsal , dssal ⟩ ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d dsal d∈ , G2 n fvs ∥ ds ∥ dssal ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (proj₁ salFV') (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (salient-∈-mem (proj₂ salFV') a∈) (T⊆ a (there a∈))
... | yes FV⊆ = ⟨ G3 (fro fv) (here refl) , ⟨ (λ x x∈ → G3 x (there x∈)) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv ∷ FV) • λ x → NewClos4.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv ∷ FV)) • (λ x → NewClos3.init))
  G1 = NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect N (mem (v ∷ V) • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w salw
                     w∈)
  G2 : ∀ n fvs d → salient d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d dsal refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ dsal , dssal ⟩ ⟨ d∈ , ds∈ ⟩ = 
     ⟨ delay-reflect fv ρ d dsal d∈ , G2 n fvs ∥ ds ∥ dssal ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv (proj₁ salFV) (T⊆ fv (FV⊆ fv (here refl)))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = 
     G2 n fvs a (salient-∈-mem (proj₂ salFV) a∈) (T⊆ a (FV⊆ a (there a∈)))
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d dsal
   ⟨ v , ⟨ V , ⟨ fvouter , ⟨ FVouter , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩ with inner-app
... | ⟨ fv , ⟨ FV , ⟨ a , ⟨ A , ⟨ ⟨ fv' , ⟨ FV' , U∈M' ⟩ ⟩ , FV⊆sndM' ⟩ ⟩ ⟩ ⟩ ⟩
   with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
      | delay-reflect M ρ ⦅ a , A ⊢ fv , FV ↦ (fvouter , FVouter ⊢ v , V ↦ d) ∣ fv' , FV' ⦆ {!   !} U∈M'
... | yes eq | q
    =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ q , delay-reflect-⊆ N ρ (v ∷ V) {!   !} V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩
... | no neq | q = {! U∈M' !}
    {-
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
      | delay-reflect M ρ ⦅ a , A ⊢ fv , FV ↦ (fvouter , FVouter ⊢ v , V ↦ d) ∣ fv' , FV' ⦆ {!   !} U∈M'
... | no FV⊈ |  q = ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ {!inner-app   !} , G2 ⟩ ⟩ ⟩ ⟩ ⟩
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  {-
  G1 : {!   !}
  G1 = {! delay-reflect M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect-⊆ N ρ (v ∷ V) hole? V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ hole? , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect-⊆ N ρ (v ∷ V) hole? V⊆N' {- delay-reflect M ρ ⦅ (fv' , FV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}
-}
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const {B'} k') dsal d∈ = d∈
delay-reflect (tuple n ⦅ args ⦆) ρ d dsal d∈ = G n args ρ d dsal d∈
  where
  G : ∀ n args ρ d → salient d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d dsal refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ dsal , dssal ⟩ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ dssal ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d dsal d∈ , ds'∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d dsal ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect M ρ ∥ ds ∥ {! ds∈  !} ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left v , V) dsal V⊆ = 
  delay-reflect-⊆ M ρ (v ∷ V) dsal V⊆
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right v , V) dsal V⊆ = 
  delay-reflect-⊆ M ρ (v ∷ V) dsal V⊆
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d dsal 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect L ρ (left v , V) {!   !} LV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect M (mem (v ∷ V) • ρ) d dsal d∈) ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d dsal
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect L ρ (right v , V) {!   !} RV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect N (mem (v ∷ V) • ρ) d dsal d∈) ⟩ ⟩ ⟩
delay-reflect-⊆ M ρ [] dsals V⊆ = λ d ()
delay-reflect-⊆ M ρ (d ∷ V) ⟨ dsal , Vsals ⟩ V⊆ d' (here refl) = 
  delay-reflect M ρ d dsal (V⊆ d (here refl))
delay-reflect-⊆ M ρ (d ∷ V) ⟨ dsal , Vsals ⟩ V⊆ d' (there d'∈frosV) = 
  delay-reflect-⊆ M ρ V Vsals (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect {zero} args ρ = lift tt
del-map-args-reflect {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect M ρ) , del-map-args-reflect args ρ ⟩




delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ)) 
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (fv , FV ⊢ν) ∣ fv' , FV' ⦆ ⟨ f∈ , T⊆ ⟩ 
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (T⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ν)) ∣ fv' , FV' ⦆ ⟨ F⊆ , T⊆ ⟩
  = ⟨ G3 (fro fv') (here refl) , (λ d d∈ → G3 d (there d∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv' ∷ FV')) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv' (T⊆ fv' (here refl))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (there a∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ (a , A ⊢ fv , FV ↦ (b , B ⊢ v , V ↦ w)) ∣ fv' , FV' ⦆ ⟨ w∈ , T⊆ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') 
... | no FV⊈ = ⟨ G3 (fro fv') (here refl) , (λ b b∈ → G3 b (there b∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
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
          (delay-reflect' N (mem (v ∷ V) • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ 𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 b (here refl) = G2 n fvs fv (T⊆ fv (FV⊆ fv (here refl)))
  G3 b (there b∈) with ∈-mem-fros b∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (T⊆ a (FV⊆ a (there a∈)))

delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ v , ⟨ V , ⟨ fvouter , ⟨ FVouter , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩ with inner-app
... | ⟨ fv , ⟨ FV , ⟨ a , ⟨ A , ⟨ ⟨ fv' , ⟨ FV' , U∈M' ⟩ ⟩ , vV'⊆sndM' ⟩ ⟩ ⟩ ⟩ ⟩
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') | delay-reflect' M ρ ⦅ a , A ⊢ fv , FV ↦ (fvouter , FVouter ⊢ v , V ↦ d) ∣ fv' , FV' ⦆ U∈M'
... | no FV⊈ |  q = ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ ⟩
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  {-
  G1 : {!   !}
  G1 = {! delay-reflect' M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' {- delay-reflect' M ρ ⦅ (fv' , FV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}

delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = d∈
delay-reflect' (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ (left v , V) V⊆ = 
  delay-reflect'-⊆ M ρ (v ∷ V) V⊆
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ (right v , V) V⊆ = 
  delay-reflect'-⊆ M ρ (v ∷ V) V⊆
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (left v , V) LV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v , V) RV∈ 
        , NewClos3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect' M ρ) , del-map-args-reflect' args ρ ⟩


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