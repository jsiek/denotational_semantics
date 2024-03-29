open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import NewDomainMultiAnnLam as D3
open import NewDomainMultiAnnPair as D4
  renaming (Value to Value')
open import NewDOpMultiAnnLam as Op3
open import NewDOpMultiAnnPair as Op4
open import NewClos3Multi
open import NewClos4Multi
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import NewCompilerMulti using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
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


{- 
forward direction design decision summary: whether to have finite sets in pairs
 - if you have finite sets in pairs, then in the app case of the forward direction
   the set started as an annotation to the lambda
   and the IH (by definition of `to') sets it as the domain of the resultant arrow, and the env representation.
   Then the initial application of the closure to itself succeeds handily.
     This is satisfied in the closure case by definition of lambda making the annotation a subset of the environment which evaluates the arrow properly.
 -  if you don't have finite sets in pairs, then in the app case of the forward direction
    the IH (via a function to) can't map all of the values over unless
       + `to' is not a function (or it's a function to lists) or
          ...the relation is a better idea because `to' as a function to lists is nightmarish
          ...with a relation, we need _all_ related pairs to be in the target denotation
             so that we can get the result for each part of the environment subset
       + the pairs that we map have to have annotations which store the image
         ...then we have the problem of preserving the MEANING of the annotation
            from the formation of the closure to the elimination of the closure;
            this means that at formation of a closure we know that the annotations
            is a subset of the cdr of the closure denotation...
            but we don't know this important detail at the application site.
So, what this means is that if we eschew finite sets in our pairs, then we need to have
  a relation instead of a function to map our values across our theorem.

The relation for the forward pass for multi is annoying enough to write that I would rather stay with special closures for now.

data _~tos_ : List Value → List Value' → Set
data _~to_ : Value → Value' → Set where
  to-const : ∀ {B k} → const {B} k ~to (const k)
  to-ω : ω ~to ω
  to-left : ∀ {d d'} → (d~ : d ~to d') → left d ~to (left d')
  to-right : ∀ {d d'} → (d~ : d ~to d') → right d ~to (right d')
  to-tup : ∀ {ds ds'} → (ds~ : ds ~tos ds') → ∥ ds ∥ ~to ∥ ds' ∥
  to-ν : ∀ {fv fv' FV FV'} → (fv ∷ FV) ~tos (fv' ∷ FV')
       → ∀ {fv''} → fv'' ∈ mem (fv' ∷ FV') 
       → (fv ∷ FV ⊢ν) ~to (⦅ fv' ∷ FV' ↦ ν , fv'' ⦆⊢ true)

The main issue is this definition of ~tos, which doesn't seem powerful enough for function cases.
data _~tos_ where
  [] : [] ~tos []
  _∷_ : ∀ {d d' ds ds'} → (d~ : d ~to d') → (ds~ : ds ~tos ds')
        → (d ∷ ds) ~tos (d' ∷ ds')

 -}


tos : List Value → List Value'
to : Value → Value'
to (const x) = const x
to (FV ⊢ V ↦ w) = (⦅ (tos FV ↦ (tos V ↦ to w)) , tos FV ⦆⊢ true)
to (FV ⊢ν) = (⦅ (tos FV ↦ ν) , tos FV ⦆⊢ true)
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
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (FV ⊢ν) ⟨ FV⊆𝒯fvs , neFV ⟩ = 
  ⟨ ⟨ G3 , to-ne FV neFV ⟩ , ⟨ ⟨ tt , to-ne FV neFV ⟩ , ⟨ G3 , to-ne FV neFV ⟩ ⟩ ⟩
  where
  G1 : (tos FV ↦ ν) ∈ Op4.Λ ⟨ (λ X → Op4.Λ ⟨ (λ Y → ⟦ delay N ⟧' (Y • X • (λ _ x → x ≡ ω))) , ptt ⟩) , ptt ⟩
  G1 = ⟨ tt , to-ne FV neFV ⟩
  G2 : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (FV ⊢ V ↦ w) ⟨ FV⊆𝒯 , ⟨ neFV , ⟨ w∈N , neV ⟩ ⟩ ⟩
  = ⟨ ⟨ G3 , to-ne FV neFV ⟩ , ⟨ G1 , ⟨ G3 , to-ne FV neFV ⟩ ⟩ ⟩ 
  where
  H : env-map to (mem V • mem FV • (λ x → NewClos3Multi.init))
         ⊆ₑ mem (tos V) • mem (tos FV) • (λ x → NewClos4Multi.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : (tos FV ↦ (tos V ↦ to w)) 
     ∈ Op4.Λ ⟨ (λ X → Op4.Λ ⟨ ⟦ clear' (bind' (bind' (ast' (delay N)))) ⟧ₐ' (env-map to ρ) X 
          , ptt ⟩) , ptt ⟩
  G1 = ⟨ ⟨ NewClos4Multi.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) 
          (delay-preserve N (mem V • mem FV • (λ _ x → x ≡ ω)) w w∈N) 
       , to-ne V neV ⟩ , to-ne FV neFV ⟩
  G2 : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯 a a∈)
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ FV , ⟨ neFV , ⟨ V , ⟨ FV⊢V↦d∈M , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩ ⟩ 
  with delay-preserve M ρ (FV ⊢ V ↦ d) FV⊢V↦d∈M | delay-preserve-⊆ N ρ V V⊆N
... | clos∈M' | V'⊆N' = 
  ⟨ tos V , ⟨ ⟨ tos FV , ⟨ ⟨ tos FV , ⟨ true , ⟨ clos∈M' , to-ne FV neFV ⟩ ⟩ ⟩ , ⟨ second , to-ne FV neFV ⟩ ⟩ ⟩ 
  , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩
   where
   second : ∀ d' → d' ∈ mem (tos FV) → d' ∈ cdr ⟨ ⟦ delay M ⟧' (env-map to ρ) , ptt ⟩
   second d' d'∈ = ⟨ tos FV ↦ (tos V ↦ to d) , ⟨ tos FV , ⟨ true , ⟨ clos∈M' , d'∈ ⟩ ⟩ ⟩ ⟩
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
  G2 = NewClos4Multi.⟦⟧-monotone {{Clos4-Semantics}} (delay M) H2 (to d) 
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
  G2 = NewClos4Multi.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H2 (to d) 
                             (delay-preserve N (mem (v ∷ V) • ρ) d d∈)
delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩




{-
reverse direction explanation and design decisions:

Our values for this direction include annotated pairs.
All pairs represent closures, and they contain a single value followed 
  by a list of values.
⦅ u , V ⦆⊢ b

The interesting case is when the first part contains a (2-ary) function 
  and the second part contains a rep of the captured local environment.
⦅ FV' ↦ (V ↦ w) , FV ⦆⊢ b
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
  ⦅ FV' ↦ (V ↦ w) , FV ⦆⊢ b ∈ D
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

fro (⦅ ν , FV ⦆⊢ b) = fros FV ⊢ν
fro (⦅ FV' ↦ ν , FV ⦆⊢ b) = fros FV ⊢ν
fro (⦅ FV' ↦ (V ↦ w) , FV ⦆⊢ true) = fros FV' ⊢ fros V ↦ fro w
fro (⦅ FV' ↦ (V ↦ w) , FV ⦆⊢ false) = fros FV ⊢ν {- NOT for app; this a default value for closure case -}
fro (⦅ u , v ⦆⊢ b) = ω

app M N ->  ((car M')  (cdr M')) N'
d' ∈ target ==> d ∈ source  (where d' ~ d)

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ (⦅ u , V ⦆⊢ false) = u ∈ D₁ × mem V ⊆ D₂ × V ≢ []
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ (⦅ U ↦ w , V ⦆⊢ true) = 
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

data add2cdr : Value' → Value' → Value' → Set where
  +cdr-pair : ∀ {u V b v} →
     add2cdr (⦅ u , V ⦆⊢ b) v (⦅ u , v ∷ V ⦆⊢ b)

data _▹_◃_ : Value' → Value' → Value' → Set where
  smash-pair : ∀ {u V b u' V' b'}
            → (⦅ u , V ⦆⊢ b) ▹ (⦅ u , V' ⦆⊢ b) ◃ (⦅ u' , V' ⦆⊢ b')
  smash-↦ : ∀ {V w1 w2 w} 
            → w1 ▹ w ◃ w2  
            → (V ↦ w1) ▹ (V ↦ w) ◃ (V ↦ w2)
  smash-left : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → left v1 ▹ left v ◃ left v2
  smash-right : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → right v1 ▹ right v ◃ right v2
  smash-head : ∀ {v1 v2 v vs} → v1 ▹ v ◃ v2
            → ∥ v1 ∷ vs ∥  ▹ ∥ v ∷ vs ∥ ◃ ∥ v2 ∷ vs ∥
  smash-tail : ∀ {v vs1 vs2 vs} → ∥ vs1 ∥ ▹ ∥ vs ∥ ◃ ∥ vs2 ∥
            → ∥ v ∷ vs1 ∥  ▹ ∥ v ∷ vs ∥ ◃ ∥ v ∷ vs2 ∥
  smash-car :  ∀ {u1 u2 u V1 V2 b1 b2}
            → u1 ▹ u ◃ u2
            → (⦅ u1 , V1 ⦆⊢ b1) ▹ (⦅ u , V1 ⦆⊢ b1) ◃ (⦅ u2 , V2 ⦆⊢ b2)
  smash-cdr-here : ∀ {u1 u2 v1 v2 V1 V2 v b1 b2}
            → (v2∈ : v2 ∈ mem V2)
            → v1 ▹ v ◃ v2
            → (⦅ u1 , (v1 ∷ V1) ⦆⊢ b1) ▹ (⦅ u1 , (v ∷ V1) ⦆⊢ b1) ◃ (⦅ u2 , V2 ⦆⊢ b2)
  smash-cdr-there : ∀ {u1 u2 v1 V1 V2 V b1 b2}
            → (⦅ u1 , V1 ⦆⊢ b1) ▹ (⦅ u1 , V ⦆⊢ b1) ◃ (⦅ u2 , V2 ⦆⊢ b2)
            → (⦅ u1 , (v1 ∷ V1) ⦆⊢ b1) ▹ (⦅ u1 , (v1 ∷ V) ⦆⊢ b1) ◃ (⦅ u2 , V2 ⦆⊢ b2)

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

smash-cdr : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {u1 u2 FV1 FV2 b1 b2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          →  
            (⦅ u1 , FV1 ⦆⊢ b1) ▹ ⦅ u1 , smash-mem smash d1∈ d2∈ ⦆⊢ b1 ◃ (⦅ u2 , FV2 ⦆⊢ b2)
smash-cdr smash (here refl) d2∈ = smash-cdr-here d2∈ smash
smash-cdr smash (there d1∈) d2∈ = smash-cdr-there (smash-cdr smash d1∈ d2∈)

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


{- case-case requires environment-monotonicity 
   and consistency of denotations -}
pair-inv : ∀ {u V b D1 D2} → (⦅ u , V ⦆⊢ b) ∈ Op4.pair ⟨ D1 , ⟨ D2 , ptt ⟩ ⟩
         → u ∈ D1 × mem V ⊆ D2 × V ≢ []
pair-inv {V₁ ↦ u} {V} {false} p∈ = p∈
pair-inv {V₁ ↦ u} {V} {true} p∈ = proj₂ p∈
pair-inv {u} {V} {false} p∈ = p∈
pair-inv {const k} {V} {true} ()
pair-inv {ν} {V} {true} ()
pair-inv {ω} {V} {true} ()
pair-inv {⦅ u , d₂ ⦆⊢ b} {V} {true} ()
pair-inv {∥ ds ∥} {V} {true} ()
pair-inv {left u} {V} {true} ()
pair-inv {right u} {V} {true} ()


smash-⟦⟧' : ∀ M' ρ' 
          → (ρ'~ : ∀ i → smash-closed (ρ' i))
          → smash-closed (⟦ M' ⟧' ρ')
smash-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ b1) (⦅ u2 , V2 ⦆⊢ b2) d smash-pair
          = {!   !}
{-
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ U1 ↦ v1 , V1 ⦆⊢ true) (⦅ u2 , V2 ⦆⊢ false) d smash-pair 
          ⟨ ⟨ U1⊆cdr , neU1 ⟩ , ⟨ f∈ , ⟨ V1⊆ , neV1 ⟩ ⟩ ⟩  ⟨ u2∈ , ⟨ V2⊆ , neV2 ⟩ ⟩ 
          = ⟨ ⟨ U1⊆cdr , neU1 ⟩ , ⟨ f∈ , ⟨ V2⊆ , neV2 ⟩ ⟩ ⟩
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ false) (⦅ U2 ↦ v2 , V2 ⦆⊢ true) d smash-pair 
          ⟨ u1∈ , ⟨ V1⊆ , neV1 ⟩ ⟩  ⟨ ⟨ U2⊆cdr , neU2 ⟩ , ⟨ g∈ , ⟨ V2⊆ , neV2 ⟩ ⟩ ⟩ 
          = ⟨ u1∈ , ⟨ V2⊆ , neV2 ⟩ ⟩
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ false) (⦅ u2 , V2 ⦆⊢ false) d smash-pair
          ⟨ u1∈ , ⟨ V1⊆ , neV1 ⟩ ⟩ ⟨ u2∈ , ⟨ V2⊆ , neV2 ⟩ ⟩ 
          = ⟨ u1∈ , ⟨ V2⊆ , neV2 ⟩ ⟩
-}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ b1) (⦅ u2 , V2 ⦆⊢ b2) d (smash-car smash)
          p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ b1) (⦅ u2 , V2 ⦆⊢ b2) d (smash-cdr-here d2∈ smash)
          p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~
          (⦅ u1 , V1 ⦆⊢ b1) (⦅ u2 , V2 ⦆⊢ b2) d (smash-cdr-there smash)
          p1∈ p2∈ = {!   !}
smash-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
          ⟨ FV1 , ⟨ b1 , ⟨ p1∈ , neFV1 ⟩ ⟩ ⟩ ⟨ FV2 , ⟨ b2 , ⟨ p2∈ , neFV2 ⟩ ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ (⦅ d1 , FV1 ⦆⊢ b1) (⦅ d2 , FV2 ⦆⊢ b2) (⦅ d , FV1 ⦆⊢ b1) 
                 (smash-car smash) p1∈ p2∈
... | IH
    = ⟨ FV1 , ⟨ b1 , ⟨ IH , neFV1 ⟩ ⟩ ⟩
smash-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
  ⟨ f1 , ⟨ FV1 , ⟨ b1 , ⟨ p1∈ , d1∈ ⟩ ⟩ ⟩ ⟩  ⟨ f2 , ⟨ FV2 , ⟨ b2 , ⟨ p2∈ , d2∈ ⟩ ⟩ ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ (⦅ f1 , FV1 ⦆⊢ b1) (⦅ f2 , FV2 ⦆⊢ b2) 
                 (⦅ f1 , smash-mem smash d1∈ d2∈ ⦆⊢ b1)
                 (smash-cdr smash d1∈ d2∈) p1∈ p2∈
... | IH
    = ⟨ f1 , ⟨ smash-mem smash d1∈ d2∈ , ⟨ b1 , ⟨ IH , smash-mem-ne smash d1∈ d2∈ ⟩ ⟩ ⟩ ⟩

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




fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro (⦅ ν , FV ⦆⊢ b) = fros FV ⊢ν
fro (⦅ V ↦ ν , FV ⦆⊢ b) = fros FV ⊢ν
fro (⦅ FV' ↦ (V ↦ w) , FV ⦆⊢ b) with FV' D4.mem⊆? FV
... | yes FV'⊆FV =  fros FV' ⊢ fros V ↦ fro w
... | no FV'⊈FV = fros FV ⊢ν
fro (⦅ u , v ⦆⊢ b) = ω
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




delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d d∈ = {!   !}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ with FV↦[V↦d]∈carM'
... | ⟨ FV' , ⟨ b , ⟨ ⦅FV↦[V↦d],FV'⦆b∈M' , neFV' ⟩ ⟩ ⟩ = 
  ⟨ fros FV , ⟨ fro-ne FV neFV , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G : ⦅ FV ↦ (V ↦ d) , FV ⦆⊢ b ∈ ⟦ delay M ⟧' ρ
  G = smash-⟦⟧' (delay M) ρ {!   !} 
               (⦅ FV ↦ (V ↦ d) , FV' ⦆⊢ b) (⦅ {!   !} , FV ⦆⊢ {!   !}) 
               (⦅ FV ↦ (V ↦ d) , FV ⦆⊢ b) smash-pair ⦅FV↦[V↦d],FV'⦆b∈M' {! FV⊆cdrM'   !}
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV D4.mem⊆? FV | delay-reflect' M ρ (⦅ FV ↦ (V ↦ d) , FV ⦆⊢ b) G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (λ d z → z))
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect'-⊆ N ρ V V⊆N'
  {-
... | ⟨ FV' , ⟨ false , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ ⟩ = HOLE
... | ⟨ FV' , ⟨ true , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ ⟩ with
  delay-reflect'-⊆ N ρ V V⊆N' | delay-reflect' M ρ (⦅ FV ↦ (V ↦ d) , FV' ⦆⊢ true) ⦅FV↦[V↦d],FV'⦆∈M'
... | frosV⊆N | froFV⊢V↦d∈M = 
  ⟨ fros FV , ⟨ fro-ne FV neFV , ⟨ fros V , ⟨ froFV⊢V↦d∈M , ⟨ frosV⊆N , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
-}
delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
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
        , NewClos3Multi.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , NewClos3Multi.⟦⟧-monotone {{Clos3-Semantics}} N  
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
        → D ⊢ (⦅ ν , FV ⦆⊢ b) ~fro (FV' ⊢ν)
  fro-↦-ν : ∀ {FV FV' V b D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ (⦅ V ↦ ν , FV ⦆⊢ b) ~fro (FV' ⊢ν) 
  fro-clos-true : ∀ {FV FV' V V' w w' FVcdr D}
          → (FV~ : D ⊢ FV ~fros FV')
          → (V~ : D ⊢ V ~fros V')
          → (w~ : D ⊢ w ~fro w')
          → D ⊢ (⦅ FV ↦ (V ↦ w) , FVcdr ⦆⊢ true) ~fro (FV' ⊢ V' ↦ w')
  fro-clos-false : ∀ {FV FV' dom V w D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ (⦅ dom ↦ (V ↦ w) , FV ⦆⊢ false) ~fro (FV' ⊢ν)


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
  H : env-map fro (mem (v ∷ V) • mem (fv' ∷ FV') • λ x → NewClos4Multi.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → NewClos3Multi.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → NewClos3Multi.init))
  G1 = NewClos3Multi.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
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
        , NewClos3Multi.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , NewClos3Multi.⟦⟧-monotone {{Clos3-Semantics}} N  
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