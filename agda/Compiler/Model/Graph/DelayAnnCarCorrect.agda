open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Model.Graph.DomainAnnFun as D3
open import Model.Graph.DomainAnnCar as D4
  renaming (Value to Value')
open import Model.Graph.OperationAnnFun as Op3
open import Model.Graph.OperationAnnCar as Op4
open import Model.Graph.Clos3 as L3
open import Model.Graph.Clos4AnnCar as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import Model.Graph.DelayAnnCar using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; reduce)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; map⁻)
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
open import Data.Bool using (Bool; true; false)

module Model.Graph.DelayAnnCarCorrect where


tos : List Value → List Value'
to : Value → Value'
to (const x) = const x
to (FV ⊢ V ↦ w) = ⦅ (tos FV ↦ (tos V ↦ to w)) , tos FV ⦆
to (FV ⊢ν) = ⦅ (tos FV ↦ ν) , tos FV ⦆
to (FV ⊢ V ↦' w) = ∣ tos FV ⦆ {- still needed? -}
to (FV ⊢ν') = ∣ tos FV ⦆       {- still needed? -}
to ω = ω
to ∥ vs ∥ = ∥ tos vs ∥
to (left v) = left (to v)
to (right v) = right (to v)
tos List.[] = []
tos (d List.∷ ds) = to d ∷ tos ds

to-set : 𝒫 Value → 𝒫 Value'
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d

_to-⊆_ : 𝒫 Value → 𝒫 Value' → Set
A to-⊆ B = ∀ d → d ∈ A → to d ∈ B

env-map : ∀ {A B : Set} → (A → B) → (ℕ → 𝒫 A) → (ℕ → 𝒫 B)
env-map {A} {B} f ρ x b = Σ[ a ∈ A ] a ∈ (ρ x) × b ≡ f a

to-ne : ∀ V → V ≢ [] → tos V ≢ []
to-ne [] neV = ⊥-elim (neV refl)
to-ne (x ∷ V) neV ()

tos-length : ∀ V → length (tos V) ≡ length V
tos-length [] = refl
tos-length (x ∷ V) = cong suc (tos-length V)

tos-nth : ∀ V i → to (Op3.nth V i) ≡ Op4.nth (tos V) i
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
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres' _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)

delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ν , ⟨ ⟨ w∈N , neV ⟩ , ⟨ _ 
        , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
   ⟨ ⟨ tt , to-ne FV neFV ⟩ , ⟨ IHV , to-ne FV neFV ⟩ ⟩ 
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHV : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ V ↦ w , ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ _ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = 
      ⟨ ⟨ ⟨ stepN , to-ne V neV ⟩ , to-ne FV neFV ⟩ , ⟨ IHfvs , to-ne FV neFV ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHfvs : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHfvs d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
  IHN : to w ∈ ⟦ delay N ⟧' (env-map to (mem V • mem FV • (λ _ x → x ≡ ω)))
  IHN = delay-preserve N (mem V • mem FV • (λ _ x → x ≡ ω)) w w∈N
  H : env-map to (mem V • mem FV • (λ x → L3.init))
         ⊆ₑ mem (tos V) • mem (tos FV) • (λ x → L4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  stepN : to w ∈ ⟦ delay N ⟧' (mem (tos V) • mem (tos FV) • (λ x → L4.init))
  stepN = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) IHN
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ν' , ⟨ ⟨ w∈N , neV ⟩ , ⟨ ⟨ w'∈N , neV' ⟩ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ν , ⟨ tt , ⟨ IHV , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHV : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ V ↦' w , ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ ⟨ ⟨ w'∈N , neV' ⟩ , neFV'' ⟩ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = 
  ⟨ ν , ⟨ tt , ⟨ IHfvs , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHfvs : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHfvs d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
  IHN : to w ∈ ⟦ delay N ⟧' (env-map to (mem V • mem FV • (λ _ x → x ≡ ω)))
  IHN = delay-preserve N (mem V • mem FV • (λ _ x → x ≡ ω)) w w∈N
  H : env-map to (mem V • mem FV • (λ x → L3.init))
         ⊆ₑ mem (tos V) • mem (tos FV) • (λ x → L4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  stepN : to w ∈ ⟦ delay N ⟧' (mem (tos V) • mem (tos FV) • (λ x → L4.init))
  stepN = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) IHN
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d 
  ⟨ FV , ⟨ neFV , ⟨ V , ⟨ FV⊢V↦d∈M , ⟨ _ , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with delay-preserve M ρ (FV ⊢ V ↦ d) FV⊢V↦d∈M
    | delay-preserve-⊆ N ρ V V⊆N
... | clos∈M' | V'⊆N' = 
    ⟨ tos V , ⟨ ⟨ tos FV , ⟨ ⟨ tos FV , clos∈M' ⟩ , ⟨ second , to-ne FV neFV ⟩ ⟩ ⟩ 
    , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩
{-  ⟨ tos V , ⟨ ⟨ tos FV , ⟨ clos∈M' , ⟨ second , to-ne FV neFV ⟩ ⟩ ⟩ 
  , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩ -}
   where
   second : ∀ d' → d' ∈ mem (tos FV) → d' ∈ cdr ⟨ ⟦ delay M ⟧' (env-map to ρ) , ptt ⟩
   second d' d'∈ = inj₂ ⟨ tos FV ↦ (tos V ↦ to d) , ⟨ tos FV , ⟨ clos∈M' , d'∈ ⟩ ⟩ ⟩

   {- ⟨ tos FV , ⟨ HOLE , d'∈ ⟩ ⟩ -}
delay-preserve (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-preserve (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ ρ → to d ∈ ⟦ delay (tuple n ⦅ args ⦆ ) ⟧' (env-map to ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-preserve arg ρ d d∈ , ds'∈ ⟩  
delay-preserve (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ tos ds , ⟨ subst (Data.Nat._<_ i) (sym (tos-length ds)) i≤ 
  , ⟨ delay-preserve M ρ ∥ ds ∥ ds∈ , tos-nth ds i ⟩ ⟩ ⟩
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-preserve M ρ v v∈
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-preserve M ρ v v∈ 
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
     inj₁ ⟨ to v , ⟨ tos V , ⟨ G , G2 ⟩ ⟩ ⟩
  where
  H : ∀ V' → (∀ d' → d' ∈ mem V' → left d' ∈ ⟦ L ⟧ ρ) → mem (Data.List.map left V') ⊆ ⟦ L ⟧ ρ
  H (x ∷ V') H' .(left x) (here refl) = H' x (here refl)
  H (x ∷ V') H' d' (there d'∈) = H V' (λ d' z → H' d' (there z)) d' d'∈
  H0 : ∀ {x : Value'} v V → x ∈ mem (tos (v ∷ V)) → left x ∈ mem (left (to v) ∷ tos (Data.List.map left V))
  H0 v V (here refl) = here refl
  H0 v (x ∷ V) (there (here refl)) = there (here refl)
  H0 v (x ∷ V) (there (there x∈)) = there (H0 x V (there x∈))
  G : ∀ d' → d' ∈ mem (tos (v ∷ V)) → left d' ∈ ⟦ delay L ⟧' (env-map to ρ)
  G d' d'∈ = delay-preserve-⊆ L ρ (Data.List.map left (v ∷ V)) (H (v ∷ V) LV∈) (left d') (H0 v V d'∈)
  H2 : env-map to (mem (v ∷ V) • ρ)
         ⊆ₑ mem (tos (v ∷ V)) • env-map to ρ
  H2 zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H2 (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G2 : to d ∈ ⟦ delay M ⟧' (mem (tos (v ∷ V)) • env-map to ρ)
  G2 = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay M) H2 (to d) 
                             (delay-preserve M (mem (v ∷ V) • ρ) d d∈)
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = inj₂ ⟨ to v , ⟨ tos V , ⟨ G , G2 ⟩ ⟩ ⟩
     where
  H : ∀ V' → (∀ d' → d' ∈ mem V' → right d' ∈ ⟦ L ⟧ ρ) → mem (Data.List.map right V') ⊆ ⟦ L ⟧ ρ
  H (x ∷ V') H' .(right x) (here refl) = H' x (here refl)
  H (x ∷ V') H' d' (there d'∈) = H V' (λ d' z → H' d' (there z)) d' d'∈
  H0 : ∀ {x : Value'} v V → x ∈ mem (tos (v ∷ V)) → right x ∈ mem (right (to v) ∷ tos (Data.List.map right V))
  H0 v V (here refl) = here refl
  H0 v (x ∷ V) (there (here refl)) = there (here refl)
  H0 v (x ∷ V) (there (there x∈)) = there (H0 x V (there x∈))
  G : ∀ d' → d' ∈ mem (tos (v ∷ V)) → right d' ∈ ⟦ delay L ⟧' (env-map to ρ)
  G d' d'∈ = delay-preserve-⊆ L ρ (Data.List.map right (v ∷ V)) (H (v ∷ V) RV∈) (right d') (H0 v V d'∈)
  H2 : env-map to (mem (v ∷ V) • ρ)
         ⊆ₑ mem (tos (v ∷ V)) • env-map to ρ
  H2 zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H2 (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G2 : to d ∈ ⟦ delay N ⟧' (mem (tos (v ∷ V)) • env-map to ρ)
  G2 = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H2 (to d) 
                             (delay-preserve N (mem (v ∷ V) • ρ) d d∈)

delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩


{- ============================================================================
    Reverse Direction
 ============================================================================ -}

{- With this semantics, we're doing something weird with our "annotations"
  we're actually just encoding extra information about the cdr in our "car" values
  We allow the cdr operator to access the information in these car values 
  as long as the information is consistent with the pair denotation.
  Semantically, we can sort of imagine that this amounts to also
  doing a simultaneous car operation while doing cdr.

  Really, there's no need for the _proof_ itself to do this...
   but rather in order to map target values in a pair denotation back to corresponding
   source values (in a function denotation), we need both car and cdr information,
   which we don't have when we only have access to a single value.
   ...  the proof has access to all the values it needs to do the reasoning,
   but we want to define the relation between denotations 
   as a function between individual values.
-}

{- So, with normal annotations, we want to treat them as if they do not carry
   denotational information... and so we generally have a priniciple that the
   introduction operators can introduce annotations but the
   elimination operators cannot depend on annotations 
   (except perhaps to give another annotation).
   These are weird because they _do_ carry valid semantic info,
   and we _do_ key off of them.  So this is a case of us using an alternate
   but equivalent denotation rather than "annotations" per se.
-}

{-  For this reason, we don't use a prior trick for storing information instead
    of values as annotations. ...we make the check explicitly during the defintion
    of our "fro" function rather than store the answer to that check in the denotation.
    We need to store the value anyway for this case: "fro ⦅ ν , FV ⦆ = fros FV ⊢ν."
    So storing just the true/false information is not sufficient anyway.
     -}

{- another oddity of this function is that there are "more values" that 
  could perhaps in some other system be mapped to valid application results on the source side.
  But we only map the values that will _evidently_ succeed in self-application to non-empty
  source values.  This is why we need full pair values, so that there is evidence that self-application
  can succeed. If self-application fails, then we know that we can always map to the empty function value.
  -}

fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ∣ FV ⦆ = fros FV ⊢ν
fro ⦅ ν , FV ⦆ = fros FV ⊢ν
fro ⦅ FV ↦ ν , FV' ⦆ = fros FV' ⊢ν
fro ⦅ FV ↦ (V ↦ w) , FV' ⦆ with FV D4.mem⊆? FV'
... | yes FV⊆FV' =  fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fros FV' ⊢ν
fro ⦅ u , FV ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value' → 𝒫 Value
fro-set S v = Σ[ d ∈ Value' ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value' → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (Op4.nth V i) ≡ Op3.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value' ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)


keylemma : ∀ D → pair ⟨ car ⟨ D , ptt ⟩ , ⟨ cdr ⟨ D , ptt ⟩ , ptt ⟩ ⟩ ⊆ D
keylemma D ⦅ d , V ⦆ ⟨ ⟨ V' , p∈ ⟩ , ⟨ V⊆cdrD , neV ⟩ ⟩ = {!   !}
keylemma D ∣ V ⦆ ⟨ u , ⟨ ⟨ FV , uFV∈D ⟩ , ⟨ V⊆cdrD , neV ⟩ ⟩ ⟩ = {!   !}


{-
old version

⦅ d ∣ ∈ pair (car D , cdr D) 
→
d ∈ car D
→ 
⦅ d ∣ ∈ D


∣ V ⦆ ∈ pair (car D , cdr D)
→ 
V ⊆ cdr D, neV
→
∀ v ∈ V → ∃ V'. ∣ V' ⦆ ∈ D and v ∈ V'
→
∣ V ⦆ ∈ D ???

... only by V ⊆ ⋃(V')
  and ∣ ⋃(V') ⦆ ∈ D, I think...




if I have values...
⦅ u ∣ and ∣ v ⦆
and maybe annotated values
⦅ u , V ⦆ and ∣ v ⦆

pair :
 ⦅ u , V ⦆  = u ∈ D₁ × V ⊆ D₂
 ∣ v ⦆ = v ∈ D₂

car : 
  d = ∃ V'. ⦅ d , V' ⦆ ∈ D
cdr :
  d = ∣ d ⦆ ∈ D
  ???????
  d = ∃ u V'. ⦅ u , V' ⦆ ∈ D and d ∈ V'


sanity check.
pair (car D , cdr D) ⊆? D
d d∈⦅car,cdr⦆
→ 
 - d = ⦅ u , V ⦆
   → u ∈ car D and V ⊆ cdr D
   → ∃V'. ⦅ u , V' ⦆ ∈ D
 - d = ∣ v ⦆
   → v ∈ cdr D
   → ∣ v ⦆ ∈ D


then
fro : 
⦅ ν , FV' ⦆ = FV' ⊢ν
⦅ FV ↦ ν , FV' ⦆ = FV' ⊢ν
⦅ FV ↦ (V ↦ w) , FV' ⦆ = FV ⊢ V ↦ w , whenever FV ⊆ FV'
⦅ u , V ⦆ = ω
fro ∣ fv' ⦆ = fv' ∷ [] ⊢ν




-}


delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect : ∀ {n} args ρ
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect-⊆ : ∀ M ρ V
  → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ∣ FV ⦆ 
  ⟨ f , ⟨ f∈ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = 
  ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ν , ⟨ ⟨ tt , fro-ne FV neFV ⟩ 
  , ⟨ ⟨ tt , fro-ne FV neFV ⟩ , ⟨ G3 , ⟨ fro-ne FV neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ ν , FV ⦆
  ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ν , ⟨ ⟨ tt , fro-ne FV neFV ⟩ 
  , ⟨ ⟨ tt , fro-ne FV neFV ⟩ , ⟨ G3 , ⟨ fro-ne FV neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ ⟨ ν∈ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ν , ⟨ ⟨ tt , fro-ne FV neFV ⟩ 
  , ⟨ ⟨ tt , fro-ne FV neFV ⟩ , ⟨ G3 , ⟨ fro-ne FV neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV ↦ (V ↦ w) , FV' ⦆ 
  ⟨ ⟨ ⟨ w∈ , neV ⟩ , neFV ⟩ , ⟨ FV'⊆ , neFV' ⟩ ⟩ = 
   ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ fros V ↦ fro w , ⟨ ⟨ ⟨ {!   !} , fro-ne V neV ⟩ , fro-ne FV neFV ⟩ 
   , ⟨ ⟨ ⟨ {!   !} , fro-ne V neV ⟩ , fro-ne FV neFV ⟩ , ⟨ {!   !} , ⟨ fro-ne FV neFV , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV') ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV'⊆ b b∈)

{-
 ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  with FV' D4.mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → L4.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
-}
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ ⟨ FV'' , FV↦[V↦d]∈carM' ⟩ , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩
  with FV D4.mem⊆? FV'' 
    | delay-reflect M ρ ⦅ FV ↦ (V ↦ d) , FV'' ⦆ FV↦[V↦d]∈carM'
    | delay-reflect-⊆ N ρ V V⊆N'
... | no FV⊈FV'' | IHM | IHN = 
  ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  where
  key' : ⦅ FV ↦ (V ↦ d) , FV ⦆ ∈ pair ⟨ car ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ , ⟨ cdr ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ , ptt ⟩ ⟩
  key' = ⟨ ⟨ FV'' , FV↦[V↦d]∈carM' ⟩ , ⟨ FV⊆cdrM' , neFV ⟩ ⟩
  FV⊆cdrM : ∀ v → v ∈ mem FV → {!   !}
  FV⊆cdrM v v∈FV with FV⊆cdrM' v v∈FV
  ... | inj₁ ⟨ FV' , ⟨ ∣FV'⦆∈M , v∈FV' ⟩ ⟩ = {!   !}
  ... | inj₂ ⟨ u , ⟨ FV' , ⟨ ⦅u,FV'⦆∈M , v∈FV' ⟩ ⟩ ⟩ = {!   !}
  key : ⦅ FV ↦ (V ↦ d) , FV ⦆ ∈ ⟦ delay M ⟧' ρ
  key = {!   !}
... | yes FV⊆FV'' | IHM | IHN
  = ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ {!   !} , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
{-
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect-⊆ N ρ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV D4.mem⊆? (FV ++ FV') | delay-reflect M ρ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV))
-}
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect (tuple n ⦅ args ⦆) ρ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d d∈ , ds'∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (left b) (LV∈ b b∈)
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (right b) (RV∈ b b∈)
delay-reflect-⊆ M ρ [] V⊆ = λ d ()
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect M ρ d (V⊆ d (here refl))
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect {zero} args ρ = lift tt
del-map-args-reflect {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect M ρ) , del-map-args-reflect args ρ ⟩





{-
Fun : Value' → Set
Fun (V ↦ d) = True
Fun ν = True
Fun d = False

data _⊑_ : Value' → Value' → Set where
  ⊑-ω : ω ⊑ ω
  ⊑-const : ∀ {B k} → const {B} k ⊑ const k
  ⊑-ν : ∀ {d} → Fun d → ν ⊑ d
  ⊑-↦ : ∀ {V w w1} → w ⊑ w1
          → (V ↦ w) ⊑ (V ↦ w1)
  ⊑-nil : ∥ [] ∥ ⊑ ∥ [] ∥
  ⊑-cons : ∀ {d d1 ds ds1} 
          → (d⊑ : d ⊑ d1)
          → (ds⊑ : ∥ ds ∥ ⊑ ∥ ds1 ∥)
          → ∥ d ∷ ds ∥ ⊑ ∥ d1 ∷ ds1 ∥
  ⊑-pair : ∀ {u u1 V V1}
          → (⊑u : u ⊑ u1)
          → (⊑V : ∀ v → v ∈ mem V 
                → Σ[ v1 ∈ Value' ] (mem V1 v1) × v ⊑ v1)
          → ⦅ u , V ⦆ ⊑ ⦅ u1 , V1 ⦆
  ⊑-left : ∀ {d d1} → d ⊑ d1 → left d ⊑ left d1
  ⊑-right : ∀ {d d1} → d ⊑ d1 → right d ⊑ right d1

⊑-refl : ∀ {d} → d ⊑ d
⊑-mem-refl : ∀ V d → d ∈ (mem V) → d ⊑ d
⊑-refl {const k} = ⊑-const
⊑-refl {V ↦ d} = ⊑-↦ ⊑-refl
⊑-refl {ν} = ⊑-ν tt
⊑-refl {ω} = ⊑-ω
⊑-refl {⦅ d , V ⦆} = ⊑-pair ⊑-refl V⊑V
  where
  V⊑V : (x : Value') (x₁ : Any (_≡_ x) V) → Σ Value' (λ z → Σ (Any (_≡_ z) V) (λ _ → x ⊑ z))
  V⊑V v v∈ = ⟨ v , ⟨ v∈ , ⊑-mem-refl V v v∈ ⟩ ⟩
⊑-refl {∥ [] ∥} = ⊑-nil
⊑-refl {∥ x ∷ ds ∥} = ⊑-cons ⊑-refl ⊑-refl
⊑-refl {left d} = ⊑-left ⊑-refl
⊑-refl {right d} = ⊑-right ⊑-refl
⊑-mem-refl (x ∷ V) .x (here refl) = ⊑-refl
⊑-mem-refl (x ∷ V) d (there d∈V) = ⊑-mem-refl V d d∈V


{- This version with infinite sets seems to fail.
   Let's attempt to consider distributivity over finite sets,
   which makes more sense anyway.
   -}
data _⊑'_ : Value' → 𝒫 Value' → Set where
   ⊑'-single : ∀ {u v D} 
              → v ∈ D → u ⊑ v
              → u ⊑' D
   ⊑'-dist-↦ : ∀ {V w D}
              → w ⊑' (Op4.⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩)
              → (V ↦ w) ⊑' D
   ⊑'-dist-pair : ∀ {u V D}
              → u ⊑' car ⟨ D , ptt ⟩
              → (∀ v → v ∈ mem V → v ⊑' cdr ⟨ D , ptt ⟩)
              → ⦅ u , V ⦆ ⊑' D           
   ⊑'-left : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → z) , ⟨ (λ z → ⌈ ω ⌉) , ptt ⟩ ⟩ ⟩
             → left d ⊑' D
   ⊑'-right : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → ⌈ ω ⌉) , ⟨ (λ z → z) , ptt ⟩ ⟩ ⟩
             → right d ⊑' D
   ⊑'-tup : ∀ {ds D}
             → (∀ i → Op4.nth ds i ⊑' Op4.proj i ⟨ D , ptt ⟩)
             → ∥ ds ∥ ⊑' D

{-
data _⊑'_ : Value' → List Value' → Set where
   ⊑'-single : ∀ {u v D} 
              → v ∈ mem D → u ⊑ v
              → u ⊑' D
   ⊑'-dist-↦ : ∀ {V w D}
              → w ⊑' (Op4.⋆ ⟨ mem D , ⟨ mem V , ptt ⟩ ⟩)
              → (V ↦ w) ⊑' mem D
   ⊑'-dist-pair : ∀ {u V D} 
              → u ⊑' car ⟨ D , ptt ⟩
              → (∀ v → v ∈ mem V → v ⊑' cdr ⟨ D , ptt ⟩)
              → ⦅ u , V ⦆ ⊑' D           
   ⊑'-left : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → z) , ⟨ (λ z → ⌈ ω ⌉) , ptt ⟩ ⟩ ⟩
             → left d ⊑' D
   ⊑'-right : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → ⌈ ω ⌉) , ⟨ (λ z → z) , ptt ⟩ ⟩ ⟩
             → right d ⊑' D
   ⊑'-tup : ∀ {ds D}
             → (∀ i → Op4.nth ds i ⊑' Op4.proj i ⟨ D , ptt ⟩)
             → ∥ ds ∥ ⊑' D
-}

⊑-closed : (𝒫 Value') → Set
⊑-closed D = ∀ u v → v ∈ D → u ⊑ v → u ∈ D

⊑'-closed : (𝒫 Value') → Set
⊑'-closed D = ∀ d → d ⊑' D → d ∈ D

⋆-⊑-closed : op-pred-pres ⊑-closed (■ ∷ ■ ∷ []) Op4.⋆
⋆-⊑-closed ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟨ dcM , ⟨ dcN , ptt ⟩ ⟩ = lift G
  where
  G : ⊑-closed (Op4.⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩)
  G u v ⟨ V , ⟨ u∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ u⊑v = 
    ⟨ V , ⟨ lower dcM (V ↦ u) (V ↦ v) u∈ (⊑-↦ u⊑v) , ⟨ V⊆ , neV ⟩ ⟩ ⟩

⋆-⊑'-closed : op-pred-pres ⊑'-closed (■ ∷ ■ ∷ []) Op4.⋆
⋆-⊑'-closed ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟨ dcM , ⟨ dcN , ptt ⟩ ⟩ = lift G
  where
  G : ⊑'-closed (Op4.⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩)
  G d d⊑'⋆MN = ⟨ {!   !} , ⟨ lower dcM {!   !} (⊑'-dist-↦ {!   !}) , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩

{-
  w ⊑' ⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩
  -------------------------------
  V ↦ w ⊑' D

  d ⊑' ⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩

-}

⊑-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑-closed ρ)
              → ⊑-closed (⟦ M ⟧' ρ)
⊑-closed-⟦⟧' (# x) ρ ρ~ = ρ~ x
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .ν v v∈M (⊑-ν x) = tt
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ w) (V' ↦ ν) ⟨ w'∈ΛM , neV ⟩ (⊑-↦ (⊑-ν x)) = ⟨ tt , neV ⟩
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ w) (V' ↦ (V'' ↦ w')) ⟨ w'∈ΛM , neV ⟩ (⊑-↦ (⊑-ν x)) = 
  ⟨ tt , neV ⟩
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ (V' ↦ w)) (V ↦ (V' ↦ w')) ⟨ ⟨ w'∈M , neV'' ⟩ , neV ⟩ (⊑-↦ (⊑-↦ u⊑v)) = 
  ⟨ ⟨ ⊑-closed-⟦⟧' N  (mem V' • mem V • (λ _ x → x ≡ ω)) {!   !} w w' w'∈M u⊑v , neV'' ⟩ , neV ⟩
⊑-closed-⟦⟧' (app ⦅ L ,, M ,, N ,, Nil ⦆') ρ ρ~ u v 
  ⟨ V , ⟨ ⟨ FV , ⟨ w∈L , ⟨ FV⊆M , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N , neV ⟩ ⟩ ⟩ u⊑v =
   ⟨ V , ⟨ ⟨ FV , ⟨ ⊑-closed-⟦⟧' L ρ ρ~ (FV ↦ (V ↦ u)) (FV ↦ (V ↦ v)) w∈L (⊑-↦ (⊑-↦ u⊑v)) , ⟨ FV⊆M , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N , neV ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ .(const _) .(const _) v∈M ⊑-const = v∈M
⊑-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ .ν v v∈M (⊑-ν x) = {!   !} {- contradiction -}
⊑-closed-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ ρ~ ⦅ u , V ⦆ ⦅ u' , V' ⦆ 
   ⟨ u'∈M , ⟨ V'⊆N , neV' ⟩ ⟩ (⊑-pair u⊑v ⊑V) = 
   ⟨ ⊑-closed-⟦⟧' M ρ ρ~ u u' u'∈M u⊑v , ⟨ {!   !} , {!   !} ⟩ ⟩
⊑-closed-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ FV , ⟨ p∈ , neFV ⟩ ⟩ u⊑v =
   ⟨ FV , ⟨ ⊑-closed-⟦⟧' M ρ ρ~ ⦅ u , FV ⦆ ⦅ v , FV ⦆ p∈ (⊑-pair u⊑v FV⊑FV) , neFV ⟩ ⟩
  where
  FV⊑FV : (x : Value') (x₁ : Any (_≡_ x) FV) → Σ Value' (λ z → Σ (Any (_≡_ z) FV) (λ _ → x ⊑ z))
  FV⊑FV v v∈ = ⟨ v , ⟨ v∈ , ⊑-mem-refl FV v v∈ ⟩ ⟩
⊑-closed-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ f , ⟨ FV , ⟨ p∈ , v∈FV ⟩ ⟩ ⟩ u⊑v =
   ⟨ f , ⟨ (u ∷ []) , ⟨ ⊑-closed-⟦⟧' M ρ ρ~ ⦅ f , u ∷ [] ⦆ ⦅ f , FV ⦆ p∈ 
                                  (⊑-pair ⊑-refl H) , here refl ⟩ ⟩ ⟩
  where
  H : (x : Value') (x₁ : Any (_≡_ x) (u ∷ [])) →
      Σ Value' (λ z → Σ (Any (_≡_ z) FV) (λ _ → x ⊑ z))
  H d (here refl) = ⟨ v , ⟨ v∈FV , u⊑v ⟩ ⟩
⊑-closed-⟦⟧' (tuple n ⦅ args ⦆') ρ ρ~ u v v∈M u⊑v = {!   !}
⊑-closed-⟦⟧' (get i ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ vs , ⟨ i≤ , ⟨ vs∈ , refl ⟩ ⟩ ⟩ u⊑v 
  = ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (inl-op ⦅ M ,, Nil ⦆') ρ ρ~ (left u) (left v) v∈M (⊑-left u⊑v)= 
  ⊑-closed-⟦⟧' M ρ ρ~ u v v∈M u⊑v
⊑-closed-⟦⟧' (inr-op ⦅ M ,, Nil ⦆') ρ ρ~ (right u) (right v) v∈M (⊑-right u⊑v) = 
  ⊑-closed-⟦⟧' M ρ ρ~ u v v∈M u⊑v
⊑-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u v 
  (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆L , v∈M[V'] ⟩ ⟩ ⟩) u⊑v = 
  inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆L , ⊑-closed-⟦⟧' M (mem (v' ∷ V') • ρ) {!   !} u v v∈M[V'] u⊑v ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u v 
  (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆L , v∈N[V'] ⟩ ⟩ ⟩) u⊑v = 
  inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆L , ⊑-closed-⟦⟧' N (mem (v' ∷ V') • ρ) {!   !}  u v v∈N[V'] u⊑v ⟩ ⟩ ⟩


⊑'-closed⇒⊑-closed : ∀ {D} → ⊑'-closed D → ⊑-closed D
⊑'-closed⇒⊑-closed H u v v∈D u⊑v = H u (⊑'-single v∈D u⊑v)

⊑'-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑'-closed ρ)
              → ⊑'-closed (⟦ M ⟧' ρ)
⊑'-closed-⟦⟧' (# x) ρ ρ~ = ρ~ x
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ u (⊑'-single x x₁) 
  = {! ⊑-closed-⟦⟧' ? ρ   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(_ ↦ _) (⊑'-dist-↦ u⊑'M) 
  = {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(⦅ _ , _ ⦆) (⊑'-dist-pair u⊑'M x) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(left _) (⊑'-left u⊑'M) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(right _) (⊑'-right u⊑'M) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(∥ _ ∥) (⊑'-tup x) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (app ⦅ L ,, M ,, N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (tuple n ⦅ args ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (get i ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (inl-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (inr-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}



{-
⊑'-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑'-closed ρ)
              → ⊑'-closed (⟦ M ⟧' ρ)
⊑'-closed-⟦⟧' M ρ ρ~ u (⊑'-single {u} {v} v∈M u⊑v) = 
  ⊑-closed-⟦⟧' M ρ (λ i → ⊑'-closed⇒⊑-closed (ρ~ i)) u v v∈M u⊑v
⊑'-closed-⟦⟧' M ρ ρ~ (V ↦ w) (⊑'-dist-↦ u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (⦅ u , v ⦆) (⊑'-dist-pair u⊑'M x) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (left u) (⊑'-left u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (right v) (⊑'-right u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (∥ ds ∥) (⊑'-tup x) = {!   !}
-}

keylemma : ∀ {u1 V1 u2 V2 D} → ⊑'-closed D
         → ⦅ u1 , V1 ⦆ ∈ D → ⦅ u2 , V2 ⦆ ∈ D
         → V1 ≢ []
         → ⦅ u1 , V2 ⦆ ∈ D
keylemma {u1}{V1}{u2}{V2}{D} ⊑'-D p1∈ p2∈ neV1 = 
  ⊑'-D ⦅ u1 , V2 ⦆ (⊑'-dist-pair H1 H2)
  where
  H1 : u1 ⊑' car ⟨ D , ptt ⟩
  H1 = ⊑'-single ⟨ V1 , ⟨ p1∈ , neV1 ⟩ ⟩ ⊑-refl
  H2 : ∀ v → v ∈ mem V2 → v ⊑' cdr ⟨ D , ptt ⟩
  H2 v v∈ = ⊑'-single ⟨ u2 , ⟨ V2 , ⟨ p2∈ , v∈ ⟩ ⟩ ⟩ ⊑-refl

{-
data _⊑'_⊔_ : Value' → Value' → Value' → Set where
  ⊑'-⊔-R1 : ∀ {u v} → u ⊑' u ⊔ v
  ⊑'-⊔-R2 : ∀ {u v} → v ⊑' u ⊔ v
  ⊑'-⊔-dist-fun : ∀ {V w w1 w2} 
               → w ⊑' w1 ⊔ w2
               → V ↦ w ⊑' V ↦ w1 ⊔ V ↦ w2
  ⊑'-⊔-dist-pair : ∀ {u u1 u2 V V1 V2}
               → u ⊑' u1 ⊔ u2
               → (∀ v → v ∈ mem V
                 → Σ[ v1 ∈ Value' ] Σ[ v2 ∈ Value' ]
                     (v1 ∈ mem V1 ⊎ v1 ∈ mem V2)
                   × (v2 ∈ mem V1 ⊎ v2 ∈ mem V2)
                   × v ⊑' v1 ⊔ v2)
               → ⦅ u , V ⦆ ⊑' ⦅ u1 , V1 ⦆ ⊔ ⦅ u2 , V2 ⦆
-}



{-
reverse direction explanation and design decisions:

Our values for this direction include annotated pairs.
All pairs represent closures, and they contain a single value followed 
  by a list of values.
⦅ u , V ⦆

The interesting case is when the first part contains a (2-ary) function 
  and the second part contains a rep of the captured local environment.
⦅ FV' ↦ (V ↦ w) , FV ⦆
  When such closures are applied, we apply the first projection 
  to the second projection and then to the argument.
  Given such a value, we can determine that the
  application succeeds if FV' ⊆ FV. However, if FV' ⊈ FV,
  we cannot conclude that the application fails. This is because we take
  first and second projections of the denotation: a set of such pairs.
  What we really need to track is whether,
Given a pair ⦅ FV' ↦ (V ↦ w) , FV ⦆ in a denotation D,
  is FV' ⊆ cdr D or not?
This is something that we can determine when we create the pairs and carry as an annotation.
  ⦅ FV' ↦ (V ↦ w) , FV ⦆ ∈ D
  where 
  b = true when FV' ⊆ cdr D, and
  b = false otherwise (but everything else about the denotation of pair holds)
Intuitively, this means that when a lambda generates a pair that represents
  self-application (of the function in the closure to its captured environment)
  we mark that pair with true. And when it generates a pair based on taking
  some garbage as input (a pair outside of the calling convention), then
  we mark that pair as false.


For the closure case, these annotations are sufficient for us to have a theorem
  written with a function fro : Value → Value such that we get the theorem 
delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ).
  The function is simply based on whether self-application would succeed or fail
  on the value; if it would fail, we map it to the empty function which is
  always in a function declaration.

fro ⦅ ν , FV ⦆) = fros FV ⊢ν
fro ⦅ FV' ↦ ν , FV ⦆) = fros FV ⊢ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros FV' ⊢ fros V ↦ fro w
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros FV ⊢ν {- NOT for app; this a default value for closure case -}
fro ⦅ u , v ⦆) = ω

app M N ->  ((car M')  (cdr M')) N'
d' ∈ target ==> d ∈ source  (where d' ~ d)

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ u , V ⦆) = u ∈ D₁ × mem V ⊆ D₂ × V ≢ []
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ U ↦ w , V ⦆) = 
   (mem U ⊆ D₂ × U ≢ []) × (U ↦ w ∈ D₁) × mem V ⊆ D₂ × V ≢ []
{- could do U ⊆ V also, would get neU for free -}
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False


let y = 5; let g = λ x. y x; (g 2)
              ν               ν · 2
let y = 5; < λ f. λ x. f[0] x , [ y ] > ; ((g[0] g[1]) 2)
           ⦅ ([ 2 ↦ 3 ]) ↦ (2 ↦ 3) , [ 5 ] ⦆    (([ 2 ↦ 3 ]) ↦ (2 ↦ 3)) · [ 5 ] · 2
           ⦅ ([ 5 ]) ↦ XX , [ 5 ] ⦆                 can we prove ν ∈ g[0] g[1] XX
let d' ∈ delay (application)
  ...  case (looks bad)  -> contradiction
      => bad[0] bad[1] = {ν} ... contradicts that the app succeeds.
  ...  case (looks good) -> straightforward proof

let d' ∈ delay (application)
  - things we know
  -> construct a nice enough pair of values
    FV ↦ V ↦ d ∈ g[0] and FV' ⊆ g[1]
    ⦅ FV ↦ V ↦ d , XX ⦆ ∈ g
     and we know FV ⊆ cdr g
    ∀ fv ∈ FV' → ∃ ?,V → ⦅ XX , V ⦆ ∈ g × fv ∈ V

    then, there must be a single pair that is "good"
    ⦅ FV ↦ V ↦ d , FV' ⦆ ∈ g   -> application succeeds, we get result.
    then fro (construction) ∈ the application
      because 



However, such a function will not be enough for an application case.
While a "false" tag indicates that an application of the arrow should fail,
this information is available at the closure introduction site, but 
this information isn't available at the application site... so we define
a logical relation to carry that information.

...
a potential problem or complication: a "false" tag as currently defined
doesn't actually indicate that the application will fail, but 
is just not a guarantee of success. If we wanted "false" to indicate
the negation of FV' ⊆ FV... then our pair operator may no longer be monotonic.

...
another approach that we can use to tackle this (while using a function)
is to prove that given our compatible first and second projections, there
exists a pair which contains both of those projections in the denotation.
This is a pain, because it essentially requires proving down-closed-ness on
an ordering and union-closed-ness on denotations in our language.
I'll want to do this proof on paper befrore I attempt it, because
I'm not certain at this moment that the approach guarantees success.

...
Another approach might be to prove that
any time a pair is in a denotation and self-application succeeds, then
there exists a true-tagged version of that pair in the denotation as well.
-}

{-
Current attempt:
I'm fairly committed to avoiding ordering and joining, so let's first try
the relational approach, but while sidestepping the monotonicity problem...

The idea is to push all of the info in the annotation into the relation,
and "remove the annotation to permit monotonicity".

...or in our case, we simply ignore the existing annotation, which already
permits monotonicity.

f ∈ car g 
FV ⊆ cdr g
----------------
⦅ f , FV ⦆ ∈ g


g1 ⊔ g2 ⊑ g 



application union-closed

(a ↦ b) union (c ↦ d)  

x , x' ∈ app A B
x union x' ∈ app A B

(a ↦ x) , (a' ↦ x') ∈ A
a , a' ∈ B
a union a' ∈ B
(a union a' ↦ x union x′) ∈ A

we know a ↦ x union a' ↦ x' ∈ A (by IH of union-closed)
a union a' ↦ x union x'  ⊑ a ↦ x union a' ↦ x' is true
... use ⊑-closed to finish the proof.

a ↦ x
a' ↦ x'
a intersection a' ↦ x union x'

a ⊔ b ∈ D =  a ∈ D ∧ b ∈ D

A ↦ (x,Y) ⊔ A ↦ (x',Y')
(or A and A', but A ~ A' guaranteed)
A ↦ (x ⊔ x' , Y ++ Y') 


-}


{-

data add2cdr : Value' → Value' → Value' → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆

get-cdr : ∀ (D : 𝒫 Value') u {v u+v} → add2cdr u v u+v
        → 𝒫 Value'
get-cdr D u +cdr-pair = cdr ⟨ D , ptt ⟩
get-cdr D (V ↦ w) (+cdr-↦ +cdr) = 
  get-cdr (Op4.⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩) w +cdr
get-cdr D (left u) (+cdr-left +cdr) = 
  get-cdr (Op4.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D (right u) (+cdr-right +cdr) =
  get-cdr (Op4.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-head +cdr) = 
  get-cdr (Op4.proj 0 ⟨ D , ptt ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-tail +cdr) = 
  get-cdr (rest ⟨ D , ptt ⟩) ∥ us ∥ +cdr
get-cdr D ⦅ u , V ⦆ (+cdr-car +cdr) = 
  get-cdr (car ⟨ D , ptt ⟩) u +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-here +cdr) = 
  get-cdr (cdr ⟨ D , ptt ⟩) v +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-there +cdr) = 
  get-cdr D ⦅ u , V ⦆ +cdr

get-cdr-mono : ∀ {D D'} u {v u+v} (+cdr : add2cdr u v u+v) 
             → D' ⊆ D' → get-cdr D u +cdr ⊆ get-cdr D u +cdr
get-cdr-mono (V ↦ u) (+cdr-↦ +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , V ⦆ +cdr-pair D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , V ⦆ (+cdr-car +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-here +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-there +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-head +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-tail +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono (left u) (+cdr-left +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono (right u) (+cdr-right +cdr) D⊆ u+v u+v∈ = {!   !}

+cdr-closed : (D : 𝒫 Value') → Set
+cdr-closed D = ∀ u v u+v 
              → (+cdr : add2cdr u v u+v)
              → u ∈ D → v ∈ get-cdr D u +cdr
              → u+v ∈ D

cdr-closure-n : ℕ → (D : 𝒫 Value') → 𝒫 Value'
cdr-closure-n zero D = D
cdr-closure-n (suc n) D d+v = 
  Σ[ d ∈ Value' ] Σ[ v ∈ Value' ] Σ[ +cdr ∈ add2cdr d v d+v ] 
     (d ∈ (cdr-closure-n n D) × v ∈ get-cdr (cdr-closure-n n D) d +cdr)

cdr-closure : 𝒫 Value' → 𝒫 Value'
cdr-closure D d = Σ[ n ∈ ℕ ] cdr-closure-n n D d

cdr-closure-closed : ∀ D → +cdr-closed (cdr-closure D)
cdr-closure-closed D u v u+v +cdr ⟨ n , u∈ ⟩ v∈ = 
   ⟨ suc n , ⟨ u , ⟨ v , ⟨ +cdr , ⟨ u∈ , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩

cdr-closure-⊆ : ∀ D → D ⊆ cdr-closure D
cdr-closure-⊆ D d d∈ = ⟨ zero , d∈ ⟩


{-

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn

-}   
{-
cdr-closure-n : ∀ (n : ℕ) → (D : 𝒫 Value') → 𝒫 Value'
cdr-closure zero D = D
cdr-closure (suc n) D d+v = 
  Σ[ d ∈ Value' ] Σ[ v ∈ Value' ] Σ[ +cdr ∈ add2cdr d v d+v ] (d ∈ D × v ∈ get-cdr D d +cdr)

smash-closed : (D : 𝒫 Value') → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value') → 𝒫 Value'
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value' ] Σ[ u2 ∈ Value' ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value') → 𝒫 Value'
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

-}

+cdr-⟦⟧' : ∀ M' ρ' 
         → (ρ'~ : ∀ i → +cdr-closed (ρ' i))
          → +cdr-closed (⟦ M' ⟧' ρ')
+cdr-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
+cdr-⟦⟧' (lit B k ⦅ Nil ⦆') ρ' ρ'~ (const k') v u+v ()
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ u , v ∷ V ⦆) 
  +cdr-pair u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ _ , V ⦆) 
  (+cdr-car +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-here +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-there +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fst-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (snd-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left u) v (left u+v) (+cdr-left +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right u) v (right u+v) (+cdr-right +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (tuple n ⦅ args' ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ' ρ'~ 
  (FV ↦ (V ↦ w)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) ⟨ ⟨ w∈N , neV ⟩ , neFV ⟩ v∈cdr 
  = ⟨ ⟨ +cdr-⟦⟧' N {!   !} {!   !} w v u+v +cdr w∈N {!   !} , neV ⟩ , neFV ⟩
+cdr-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr 
  ⟨ V , ⟨ ⟨ FV , ⟨ u∈L' , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ v∈cdr = 
  ⟨ V , ⟨ ⟨ FV , ⟨ {!   !}  , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩
  where
  G : (FV ↦ (V ↦ u+v)) ∈ ⟦ L' ⟧' ρ'
  G = +cdr-⟦⟧' L' ρ' ρ'~ (FV ↦ (V ↦ u)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) 
      u∈L' {!  !}

keylemma : ∀ D → +cdr-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma D ccD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma D ccD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD = 
  ccD ⦅ f , V' ++ V ⦆ v ⦅ f , v ∷ V' ++ V ⦆ +cdr-pair 
      (keylemma D ccD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 
      (V'⊆cdrD v (here refl))


{- =============================================================================
   Current attempt
   =============================================================================
This get-cdr formulation is ugly.  Instead of adding a value to a cdr
and checking elsewhere that the value sits in an appropriate denotation, we'll
join values of similar shape, and this will ensure things sit in the right places.
-}


{- I want to start simple with consistent/joinable arrows... let's not worry 
   just yet about whether there are cases where we can "join" domains of arrows -}

data _≈≈_ : List Value' → List Value' → Set
data _~∥~_ : List Value' → List Value' → Set
data _~~_ : Value' → Value' → Set where
  ~~-const : ∀ {B k} → const {B} k ~~ const k
  ~~-ω : ω ~~ ω
  ~~-ν-ν : ν ~~ ν
  ~~-ν-↦ : ∀ {V w} → ν ~~ (V ↦ w)
  ~~-↦-ν : ∀ {V w} → (V ↦ w) ~~ ν
  ~~-↦-↦ : ∀ {V w w'} 
          → (w~ : w ~~ w')
          → (V ↦ w) ~~ (V ↦ w')
  ~~-left : ∀ {d d'}
          → (d~ : d ~~ d')
          → left d ~~ left d'
  ~~-right : ∀ {d d'}
          → (d~ : d ~~ d')
          → right d ~~ right d'
  ~~-tup : ∀ {ds ds'}
          → (ds~ : ds ~∥~ ds')
          → ∥ ds ∥ ~~ ∥ ds' ∥
  ~~-pair : ∀ {u u' V V'}
          → (u~ : u ~~ u')
          → (V≈ : V ≈≈ V')
          → ⦅ u , V ⦆ ~~ ⦅ u' , V' ⦆
data _~∥~_ where
   [] : [] ~∥~ []
   _∷_ : ∀ {d d' ds ds'}
       → (d~ : d ~~ d')
       → (ds~ : ds ~∥~ ds')
       → (d ∷ ds) ~∥~ (d' ∷ ds')

data _≈≈_ where
  ≈≈[] : ∀ {V'} → [] ≈≈ V'
  ≈≈∷ : ∀ {v V V'}
     → All (v ~~_) V'
     → V ≈≈ V'
     → (v ∷ V) ≈≈ V'

_⊔cdr_[_] : (u v : Value') → u ~~ v → Value'
_⊔cdr∥_[_] : (ds ds' : List Value') → ds ~∥~ ds' → List Value'
_⨆cdr_[_] : (V V' : List Value') → V ≈≈ V' → List Value'
(const k) ⊔cdr .(const _) [ ~~-const ] = const k
.ω ⊔cdr .ω [ ~~-ω ] = ω
.ν ⊔cdr .ν [ ~~-ν-ν ] = ν
.ν ⊔cdr (V ↦ w) [ ~~-ν-↦ ] = V ↦ w
(V ↦ w) ⊔cdr .ν [ ~~-↦-ν ] = V ↦ w
(V ↦ w) ⊔cdr (V ↦ w') [ ~~-↦-↦ w~ ] = V ↦ (w ⊔cdr w' [ w~ ])
(left d) ⊔cdr (left d') [ ~~-left d~ ] = left (d ⊔cdr d' [ d~ ])
(right d) ⊔cdr (right d') [ ~~-right d~ ] = right (d ⊔cdr d' [ d~ ])
(∥ ds ∥) ⊔cdr (∥ ds' ∥) [ ~~-tup ds~ ] = ∥ ds ⊔cdr∥ ds' [ ds~ ] ∥
⦅ u , V ⦆ ⊔cdr ⦅ u' , V' ⦆ [ ~~-pair u~ V≈ ] = 
   ⦅ u ⊔cdr u' [ u~ ] , V ⨆cdr V' [ V≈ ] ⦆
.[] ⊔cdr∥ .[] [ [] ] = []
(d ∷ ds) ⊔cdr∥ (d' ∷ ds') [ d~ ∷ ds~ ] = d ⊔cdr d' [ d~ ] ∷ (ds ⊔cdr∥ ds' [ ds~ ])
.[] ⨆cdr V' [ ≈≈[] ] = V'
(v ∷ V) ⨆cdr V' [ ≈≈∷ v~ V≈ ] = 
   reduce (λ {x} v~~x → v ⊔cdr x [ v~~x ]) v~ ++ (V ⨆cdr V' [ V≈ ]) 

{-
 : Value' → Value' → Value' → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆
-}


{- =============================================================================
   ACTUAL Current attempt
   =============================================================================
The ~~ relation was not useful on its own, and I don't really want
join to be a function (because the way it maps in the ≈≈ case explodes and is gross).

So we want to define something similar, but that is just join as a relation.
-}



data _▹_◃_ : Value' → Value' → Value' → Set where
    smash-pair-L : ∀ {u1 u2 V1 V2 v2}
            → v2 ∈ mem V2
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u1 , v2 ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-pair-R : ∀ {u1 u2 V1 V2 v1}
            → v1 ∈ mem V1
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v1 ∷ V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-↦ : ∀ {V w1 w2 w} 
            → w1 ▹ w ◃ w2  
            → (V ↦ w1) ▹ (V ↦ w) ◃ (V ↦ w2)
    smash-left : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → left v1 ▹ left v ◃ left v2
    smash-right : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → right v1 ▹ right v ◃ right v2
    smash-car-L : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-car-R : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-L : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v2∈ : v2 ∈ mem V2)
            → ⦅ u1 , v1 ∷ V1 ⦆ ▹ ⦅ u1 , v ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-R : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v1∈ : v1 ∈ mem V1)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v ∷ V1 ⦆ ◃ ⦅ u2 , v2 ∷ V2 ⦆
    smash-cdr-there-L : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , v ∷ V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-there-R : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , v ∷ V2 ⦆
    smash-nil : ∥ [] ∥ ▹ ∥ [] ∥ ◃ ∥ [] ∥
    smash-cons : ∀ {d1 d2 d ds1 ds2 ds}
            → (d⊔ : d1 ▹ d ◃ d2)
            → (ds⊔ : ∥ ds1 ∥ ▹ ∥ ds ∥ ◃ ∥ ds2 ∥)
            → ∥ d1 ∷ ds1 ∥ ▹ ∥ d ∷ ds ∥ ◃ ∥ d2 ∷ ds2 ∥
  {-
    smash-head : ∀ {v1 v2 v vs} → v1 ▹ v ◃ v2
            → ∥ v1 ∷ vs ∥ ▹ ∥ v ∷ vs ∥ ◃ ∥ v2 ∷ vs ∥
    smash-tail : ∀ {v vs1 vs2 vs} → ∥ vs1 ∥ ▹ ∥ vs ∥ ◃ ∥ vs2 ∥
            → ∥ v ∷ vs1 ∥  ▹ ∥ v ∷ vs ∥ ◃ ∥ v ∷ vs2 ∥
    -}

data _▹[_]◃_ : List Value' → List Value' → List Value' → Set where
    [] : [] ▹[ [] ]◃ []
    _∷_ : ∀ {d1 d2 d ds1 ds2 ds}
        → (d⊔ : d1 ▹ d ◃ d2)
        → (ds⊔ : ds1 ▹[ ds ]◃ ds2)
        → (d1 ∷ ds1) ▹[ (d ∷ ds) ]◃ (d2 ∷ ds2)
data _▹▹_◃◃_ : List Value' → List Value' → List Value' → Set where
    ▹[]◃ : ∀ {V2} → [] ▹▹ V2 ◃◃ V2
    ▹∷◃ : ∀ {v1 V1 V2 V}
        → (V⨆ : V1 ▹▹ V ◃◃ V2)
        → (v1 ∷ V1) ▹▹ V ◃◃ V2


smash-mem : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → d1 ∈ mem FV1 → d2 ∈ mem FV2 → List Value'
smash-mem {d1} {d2} {d} smash {FV1 = d1 ∷ FV1} (here refl) d2∈ = d ∷ FV1
smash-mem {d1} {d2} {d} smash {FV1 = d' ∷ FV1} (there d1∈) d2∈ = 
   d' ∷ smash-mem smash d1∈ d2∈

smash-mem-ne : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → d ∈ mem (smash-mem smash d1∈ d2∈)
smash-mem-ne smash (here refl) d2∈ = here refl
smash-mem-ne smash (there d1∈) d2∈ = there (smash-mem-ne smash d1∈ d2∈)

smash-cdr-L : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {u1 u2 FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → ⦅ u1 , FV1 ⦆ ▹ ⦅ u1 , smash-mem smash d1∈ d2∈ ⦆ ◃ ⦅ u2 , FV2 ⦆
smash-cdr-L smash (here refl) d2∈ = smash-cdr-here-L smash d2∈
smash-cdr-L smash (there d1∈) d2∈ = smash-cdr-there-L (smash-cdr-L smash d1∈ d2∈)

smash-closed : (D : 𝒫 Value') → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value') → 𝒫 Value'
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value' ] Σ[ u2 ∈ Value' ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value') → 𝒫 Value'
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn


smash-⟦⟧' : ∀ M' ρ' 
          → (ρ'~ : ∀ i → smash-closed (ρ' i))
          → smash-closed (⟦ M' ⟧' ρ')
smash-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ V1 ⦆) 
          (smash-pair-L x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u2 , _ ∷ V2 ⦆) 
          (smash-pair-R x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V1 ⦆) 
          (smash-car-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V2 ⦆) 
          (smash-car-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ _ ⦆) 
          (smash-cdr-here-L smash v2∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ u2 , _ ∷ V1 ⦆) 
          (smash-cdr-here-R smash v1∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
          ⟨ FV1 , ⟨ p1∈ , neFV1 ⟩ ⟩ ⟨ FV2 , ⟨ p2∈ , neFV2 ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ d1 , FV1 ⦆ ⦅ d2 , FV2 ⦆ ⦅ d , FV1 ⦆ 
                 (smash-car-L smash) p1∈ p2∈
... | IH
    = ⟨ FV1 , ⟨ IH , neFV1 ⟩ ⟩
smash-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
  ⟨ f1 , ⟨ FV1 , ⟨ p1∈ , d1∈ ⟩ ⟩ ⟩  ⟨ f2 , ⟨ FV2 , ⟨ p2∈ , d2∈ ⟩ ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ f1 , FV1 ⦆ ⦅ f2 , FV2 ⦆
                 ⦅ f1 , smash-mem smash d1∈ d2∈ ⦆
                 (smash-cdr-L smash d1∈ d2∈) p1∈ p2∈
... | IH
    = ⟨ f1 , ⟨ smash-mem smash d1∈ d2∈ , ⟨ IH , smash-mem-ne smash d1∈ d2∈ ⟩ ⟩ ⟩

smash-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left d1) (left d2) (left d)
    (smash-left smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right d1) (right d2) (right d)
    (smash-right smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  with smash-⟦⟧' M' ((mem (v1 ∷ V1 ++ v2 ∷ V2)) • ρ') {!   !} d1 d2 d smash 
                   {! d1∈M'  !} {! d2∈M'  !}
... | IH = inj₁ ⟨ v1 , ⟨ V1 ++ (v2 ∷ V2) , ⟨ {!   !} , IH ⟩ ⟩ ⟩
  {- in the IH, expand each of the environments for the d1∈ d2∈ premises -}
  {- even-worse... we have to extend the environment by the 
     smash-closure of v1 ∷ V1 ++ v2 ∷ V2... -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩) (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = inj₂ {!   !}  {- similar to first case -}
smash-⟦⟧' (fun-op ⦅ args ⦆') ρ' ρ'~ = {!   !}
smash-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (tuple n ⦅ args ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ d1 d2 smash d1∈ d2∈ = {!   !}



keylemma' : ∀ D → smash-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma' D scD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma' D scD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD with V'⊆cdrD v (here refl)
... | ⟨ f' , ⟨ FV , ⟨ p∈ , v∈FV ⟩ ⟩ ⟩ = 
  scD ⦅ f' , FV ⦆ ⦅ f , V' ++ V ⦆ ⦅ f , v ∷ V' ++ V ⦆ (smash-pair-R v∈FV) 
      p∈ 
      (keylemma' D scD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 


fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ⦅ ν , FV ⦆ = fros FV ⊢ν
fro ⦅ V ↦ ν , FV ⦆ = fros FV ⊢ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆ with FV' D4.mem⊆? FV
... | yes FV'⊆FV =  fros FV' ⊢ fros V ↦ fro w
... | no FV'⊈FV = fros FV ⊢ν
fro ⦅ u , v ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value' → 𝒫 Value
fro-set S v = Σ[ d ∈ Value' ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value' → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (Op4.nth V i) ≡ Op3.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value' ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)


delay-reflect' : ∀ M ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ 
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ ρ~ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ ν , FV ⦆ 
  ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  with FV' D4.mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → L4.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ with FV↦[V↦d]∈carM'
... | ⟨ FV' , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ = 
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect'-⊆ N ρ ρ~ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ ρ~) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV D4.mem⊆? (FV ++ FV') | delay-reflect' M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV))
delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect' (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ ρ~ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ~ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect' M (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (left b) (LV∈ b b∈)
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect' N (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (right b) (RV∈ b b∈)
delay-reflect'-⊆ M ρ ρ~ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ ρ~ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ ρ~ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ ρ~ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ ρ~ = 
  ⟨ lift (delay-reflect' M ρ ρ~) , del-map-args-reflect' args ρ ρ~ ⟩


{-
data _⊢_≈fro_ : 𝒫 Value' → List Value' → List Value → Set₁
data _⊢_~fros_ : 𝒫 Value' → List Value' → List Value → Set₁
data _⊢_~fro_ : 𝒫 Value' → Value' → Value → Set₁ where
  fro-ω : ∀ {D} → D ⊢ ω ~fro ω
  fro-const : ∀ {D B k} → D ⊢ const {B} k ~fro const k
  fro-left : ∀ {d d' D} → (d~ : D ⊢ d ~fro d')
           → Op4.ℒ ⟨ D , ptt ⟩ ⊢ left d ~fro left d'
  fro-right : ∀ {d d' D} → (d~ : D ⊢ d ~fro d')
           → Op4.ℛ ⟨ D , ptt ⟩ ⊢ right d ~fro right d'
  fro-tup : ∀ {ds ds' D} → (ds~ : D ⊢ ds ≈fro ds')
          → D ⊢ ∥ ds ∥ ~fro ∥ ds' ∥
  fro-ν : ∀ {FV FV' b D}
        → (FV~ : D ⊢ FV ~fros FV')
        → D ⊢ ⦅ ν , FV ⦆) ~fro (FV' ⊢ν)
  fro-↦-ν : ∀ {FV FV' V b D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ ⦅ V ↦ ν , FV ⦆) ~fro (FV' ⊢ν) 
  fro-clos-true : ∀ {FV FV' V V' w w' FVcdr D}
          → (FV~ : D ⊢ FV ~fros FV')
          → (V~ : D ⊢ V ~fros V')
          → (w~ : D ⊢ w ~fro w')
          → D ⊢ ⦅ FV ↦ (V ↦ w) , FVcdr ⦆) ~fro (FV' ⊢ V' ↦ w')
  fro-clos-false : ∀ {FV FV' dom V w D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ ⦅ dom ↦ (V ↦ w) , FV ⦆) ~fro (FV' ⊢ν)


data _⊢_≈fro_ where
  [] : ∀ {D} → D ⊢ [] ≈fro []
  _∷_ : ∀ {d d' ds ds' D}
        → (d~ : D ⊢ d ~fro d')
        → (ds~ : D ⊢ ds ≈fro ds')
        → D ⊢ (d ∷ ds) ≈fro (d' ∷ ds')

data _⊢_~fros_ where
  [] : ∀ {D} → D ⊢ [] ~fros []
  _∷_ : ∀ {d d' ds ds' D}
        → (d~ : D ⊢ d ~fro d')
        → (ds~ : D ⊢ ds ~fros ds')
        → D ⊢ (d ∷ ds) ~fros (d' ∷ ds')




{- 

This has to be existentially quantified on at least D 
... this could become a mess... might need to say something like
∃ d D. d ∈ ⟦ M ⟧ ρ × D ⊢ d' ~fro d      

NOTES:
 - the relation will have to be closed upward on denotations, relying on the monotonicity of the operators
 - [theorem] × D ⊆ ⟦ M ⟧ ρ ??? 
 - 

-}
delay-reflect : ∀ M (ρ' : Env Value') (ρ : Env Value)
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d)
              → ∀ d'
              → d' ∈ ⟦ delay M ⟧' ρ' 
              → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d
delay-reflect-⊆ : ∀ M ρ' ρ 
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d)
              → ∀ V'
              → mem V' ⊆ ⟦ delay M ⟧' ρ'
              → Σ[ V ∈ List Value ] mem V ⊆ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value' ] D ⊢ V' ~fros V
delay-reflect (` i) ρ' ρ ρ~ d' d'∈ = ρ~ d'∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (left d') d'∈ 
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ Op4.ℒ ⟨ D , ptt ⟩ , fro-left ~d ⟩ ⟩ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (right d') d'∈
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ Op4.ℛ ⟨ D , ptt ⟩ , fro-right ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) 
  with delay-reflect-⊆ L ρ' ρ ρ~ (v' ∷ V') {! V'⊆   !}
... | ⟨ V , ⟨ V⊆ , ⟨ DV , ~V ⟩ ⟩ ⟩
  with (delay-reflect M (mem (v' ∷ V') • ρ') {!   !} {!   !} d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ Dd , ~d ⟩ ⟩ ⟩ = 
  ⟨ d , ⟨ inj₁ ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , d∈ ⟩ ⟩ ⟩ , ⟨ Dd , ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) = {!   !}
delay-reflect M ρ' ρ ρ~ d' d'∈ = {!   !}
delay-reflect-⊆ M ρ' ρ ρ~ [] V'⊆ = ⟨ [] , ⟨ (λ d ()) , ⟨ ⟦ delay M ⟧' ρ' , [] ⟩ ⟩ ⟩
delay-reflect-⊆ M ρ' ρ ρ~ (d' ∷ V') V'⊆
  with delay-reflect M ρ' ρ ρ~ d' (V'⊆ d' (here refl)) 
     | delay-reflect-⊆ M ρ' ρ ρ~ V' (λ d z → V'⊆ d (there z))
... | ⟨ d , ⟨ d∈ , ⟨ D1 , ~d ⟩ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , ⟨ D2 , ~V ⟩ ⟩ ⟩ 
    = ⟨ d ∷ V , ⟨ G , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
  where
  G : mem (d ∷ V) ⊆ ⟦ M ⟧ ρ
  G d' (here refl) = d∈
  G d' (there d'∈) = V⊆ d' d'∈

{-
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
-}







{-
need to check for equality of fv' with fv
and FV' with FV

-}

{-






fro-mem-rewrite : ∀ V ρ → env-map fro (mem V • ρ) ⊆ₑ (mem (fros V)) • env-map fro ρ
fro-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = fro-∈-mem a∈V
fro-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx

fro-⊆-mem : ∀ {V' V} → mem V' ⊆ mem V → mem (fros V') ⊆ (mem (fros V))
fro-⊆-mem V⊆ d d∈ with ∈-mem-fros d∈ 
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem (V⊆ a a∈)

{-
data _⊑_⊔_ : Value → Value → Value → Set where
  ⊑-clos-L : ∀ {f₁} f₂ {fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₁ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  ⊑-clos-R : ∀ f₁ {f₂ fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₂ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  {- the next case is probably not good enough, 
     but I can workshop it while working on the theorem -}
  ⊑-↦-L : ∀ {v₁ V₁ w₁ v₂ V₂ w₂ w a A b B}
       → w ⊑ w₁ ⊔ w₂
       → (a , A ⊢ v₁ , V₁ ↦ w) ⊑ (a , A ⊢ v₁ , V₁ ↦ w₁) ⊔ (b , B ⊢ v₂ , V₂ ↦ w₂)
  {- also need other cases; will add as needed -}


⊔-⊑-closed : ∀ M ρ v₁ v₂ d
           {- insert same closed condition on ρ -}
            → v₁ ∈ ⟦ delay M ⟧' ρ
            → v₂ ∈ ⟦ delay M ⟧' ρ
            → d ⊑ v₁ ⊔ v₂
            → d ∈ ⟦ delay M ⟧' ρ
⊔-⊑-closed (` x) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
  ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (app ⦅ M ,, N ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (lit B k ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple zero ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple (suc n) ⦅ M ,, Ms ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (get i ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inl-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inr-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
-}

{-crucial lemma: closures-are-products -}
{-
closures-are-products : ∀ M ρ f fv FV fv' FV'
                      → mem FV ⊆ cdr ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ 
                      → ⦅ f ∣ fv' ∷ fV' ⦆ ∈ ⟦ delay M ⟧' ρ
                      → ⦅ f ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
closures-are-products M ρ f fv FV fv' FV' FV⊆ f∈ = 
  ⊔-⊑-closed M ρ ⦅ f ∣ fv' ∷ fV' ⦆ ⦅ proj₁ G ∣ fv ∷ fV ⦆ ⦅ f ∣ fv ∷ fV ⦆ 
                  f∈ (proj₂ G) (⊑-clos-R (proj₁ G) (λ d d∈ → inj₂ d∈))
  where 
  G : Σ[ f' ∈ Value ] ⦅ f' ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
  G = HOLE
  {- this proof is bad so far... just need to recur on FV and use f directly as the f'
    with base case using ⦅ f ∣ fv' ∷ fV' ⦆ -}
-}


delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d d∈ = {!   !}

{-
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ( ⦅ ν , fv' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv'∈ ⟩ ⟩ 
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ ν , fv'' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv''∈ ⟩ ⟩
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩
   with (fv' ∷ FV') D4.mem⊆? FV
... | no FV'⊈ = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩ | yes FV'⊆ = 
   ⟨ G3 (fro fv') (fro-∈-mem (FV'⊆ fv' (here refl))) , ⟨ (λ d' d'∈ → G3 d' (fro-⊆-mem FV'⊆ d' (there d'∈))) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv' ∷ FV') • λ x → L4.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem (v ∷ V) • mem (fv' ∷ FV') • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
-}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ v , ⟨ V , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ with inner-app
... | ⟨ v' , ⟨ V' , ⟨ q , V'⊆sndM' ⟩ ⟩ ⟩    = {!  q !}

{-
   with delay-reflect' M ρ (fv' ∷ FV' ⊢⦅ fv ∷ FV ↦ (v ∷ V ↦ d) , fv'' ⦆) ⦅FV↦V↦d∣FV'⦆∈M
... | IHM with FV D4.mem⊆? (fv' ∷ FV')
... | yes FV⊆ =
   ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ IHM , delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩
... | no ¬FV⊆ = HOLE
-}
{- should be a contradiction -}
   {- the codomain isn't a subset of the annotation -}
   {- not a contradiction, but we know that this can't ALWAYS be true -}  

   
   
     {-
  ⟨ fro v , ⟨ fros V , ⟨ G1+IH , G2 ⟩ ⟩ ⟩
  where
  G1 : (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ (v ∷ V ↦ d)) , fv ⦆) ∈ ⟦ delay M ⟧' ρ
  G1 = {! FV⊆sndM' !}
  G1+IH : (fro v ∷ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  G1+IH with delay-reflect' M ρ (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d)) , fv ⦆) G1 
  ... | ihres with FV D4.mem⊆? FV
  ... | no neq = ⊥-elim (neq λ z z∈ → z∈)
  ... | yes eq = ihres
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
  -}

{-



-}


{-
    with FV mem⊆? (fv' ∷ FV') | delay-reflect' M ρ ⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d) ∣ fv' ∷ fV' ⦆ U∈M'
... | no FV⊈ |  q = ⊥-elim (FV⊈ G)
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  G : mem FV ⊆ (mem (fv' ∷ FV'))
  G d' d'∈ with FV⊆sndM' d' d'∈ 
  ... | ⟨ q , ⟨ p , ⟨ P , ⟨ qP∈M , d'∈P ⟩ ⟩ ⟩ ⟩ = HOLE
  {-
  G1 : {!   !}
  G1 = {! delay-reflect' M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ HOLE , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' {- delay-reflect' M ρ ⦅ (fv' ∷ fV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}
-}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ FV ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with FV mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}

delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = {! d∈   !}
delay-reflect' (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (left v) LV∈ 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩ -}
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect' M ρ) , del-map-args-reflect' args ρ ⟩


-}

-}

-}
-}