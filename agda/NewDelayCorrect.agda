open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import NewDOp
open import NewClos3
open import NewClos4 
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import NewCompiler using (delay; del-map-args)
open import NewEnv
open import Primitives

{-

open import ISWIMClos1
open import ISWIMClos2
  renaming (Term to Term₂; Arg to Arg₂; Args to Args₂; `_ to #_;
      pair to pair₂; fst to fst₂; snd to snd₂; tuple to tuple₂;
      $ to %; _❲_❳ to _❲_❳₂; inl to inl₂; inr to inr₂; case to case₂;
      cons to cons₂; ast to ast₂; nil to nil₂; _⦅_⦆ to _⦅_⦆₂;
      ⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧₂ₐ; ⟦_⟧₊ to ⟦_⟧₂₊)

-}


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)


tos : List Value → List Value
to : Value → Value
to (const x) = const x
to (fvs ⊢ V ↦ w) = ⦅ [] ⊢ (∥ tos fvs ∥ ∷ []) ↦ ([] ⊢ tos V ↦ to w) , ∥ tos fvs ∥ ⦆
to ν = ⦅ ν , ∥ [] ∥ ⦆
to ω = ω
to ⦅ v , v₁ ⦆ = ⦅ to v , to v₁ ⦆
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

to-mem-rewrite : ∀ V ρ → env-map to (mem V • ρ) ⊆ₑ (mem (tos V)) • env-map to ρ
to-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = to-∈-mem a∈V
to-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx



{-

tos : List Value → List Value
to : Value → List Value
to (const x) = const x
to (fvs ⊢ V ↦ w) = ⦅ [] ⊢ (∥ tos fvs ∥ ∷ []) ↦ ([] ⊢ tos V ↦ to w) , ∥ tos fvs ∥ ⦆

(to produces list of values)
to (FVS ⊢ V ↦ w) =
   [ ⦅ [] ⊢ tos FVS ↦ ([] ⊢ tos V ↦ to w) , tofvs ⦆
   for tofvs in tos FVS]

(multi-valued pairs)
to (FVS ⊢ V ↦ w) = ⦅ ⌈ [] ⊢ tos FVS ↦ ([] ⊢ tos V ↦ to w) ⌉ , tos FVS ⦆
⟦ ⦅ M , N ⦆ ⟧ρ = ⦅ V, W ⦆ where V ⊆ ⟦ M ⟧ρ, W ⊆ ⟦ N ⟧ρ
⟦ fst M ⟧ρ = { v | v ∈ V, ⦅ V, W ⦆ ∈ ⟦ M ⟧ρ }


to ν = ⦅ ν , ∥ [] ∥ ⦆
to ω = ω
to ⦅ v , v₁ ⦆ = ⦅ to v , to v₁ ⦆
to ∥ xs ∥ = ∥ tos xs ∥
to (left V) = left (tos V)
to (right V) = right (tos V)
tos List.[] = []
tos (d List.∷ ds) = to d List.∷ tos ds

to-set : 𝒫 Value → 𝒫 Value
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d

-}


{- ============================================================================
         SUMMARY OF PROBLEM 
   =========================================================================== -}
{-
closure case

given
fvs ⊢ V ↦ w ∈ 𝒜 n (Λ (F (𝒯 FVs)))

want to show
⦅ (∥ fvs' ∥ ∷ []) ↦ (V' ↦ w') , ∥ fvs' ∥ ⦆ ∈ pair (Λ (λ X → Λ (λ Y → F' X Y))) (𝒯 FVs')


fact: ∥ fvs ∥ ∈ 𝒯 FVs
fact: w ∈ ⟦ F ⟧ (mem V • (𝒯 FVs) • init)
but we want:  w' ∈ ⟦ F' ⟧ (mem V' • ⌈ ∥ fvs' ∥ ⌉ • init )
and we only have our IH:  w' ∈ ⟦ F' ⟧ (mem V' • (map to (𝒯 FVs)) • init )


if we want to define a _function_ on annotated values for the correctness of the delay pass,
then annotations will be placed as the domain of an arrow...

fvs | V -> w  ==>  fvs -> V -> w

this means that the fvs are going from semantically irrelevant to semantically relevant.
Specifically, we must satisfy the property that if we extend the environment with fvs,
then we receive (V -> w) after evaluation.

Subproblem 1: we need fvs to be list-valued, then, in that we will be replacing the environment with
fvs from a _single_ arrow value to verify that its codomain lies in some denotation.

Subproblem 2: we need to record (and maintain) the property that fvs is 
a sufficient environment extension for the arrow it annotates...
but our denotational operators have no concept of environments...
so how could we use one of them to record such a property?
(if we can't, is there a strategy for capturing a finite subset of the environment
that we can tell later is sufficient?)

Subproblem 3: (overlaps 1 and 2) 
Specifically,
the IH for the closure proof has a _bigger_ environment than what's expected by the current relation/thoerem.
Thus, we can't use monotonicity with respect to the environment to "grow" the result from our IH to satisfy the goal.


Proposed solutions:
Solution 1: Finite environments.
We use Fold instead of Fold2, and we only keep List Value in our environment.
Pros: continuity is always enforced
Cons: We have fewer thoerems on open terms...  not sure how this would affect the adequacy proofs.
How the problem is solved:  Our annotations then capture the entire environment,
and so any property guaranteed in that environment (i.e. the arrow evaluates to its output upon application)
is also guaranteed under the annotations.

Difficulty with solution 1... how do we know that the captured environment entries are finite?
are there both finite and non-finite denotations/results? We could verify this when looking at the syntax, but I'm not sure we could when defining a dnotational operator.


Solution 2: We abandon the function-iness of the relation/proof.
We write a relational version of "to" and pick out values that work using an existential quantifier...
then in the proof we rely on continuity to know that finite sets exist.
That is, we don't compute the value, but we know that it will exist because we make sure
all the necessary annotations are there... and we pick one that satisfies continuity and show it must be in there and it must be related. 

Solution 3: ?




-}







delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ) 

delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op zero ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ν d∈ = ⟨ tt , refl ⟩
delay-preserve (clos-op zero ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ([] ⊢ V ↦ w) ⟨ w∈N , neV ⟩ = 
  ⟨ ⟨ ⟨ NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) (H V) (to w) 
                              (delay-preserve N (mem V • (λ x → x ≡ ∥ [] ∥) • 
                              (λ x → NewClos3.init)) w w∈N) 
      , to-ne V neV ⟩ , (λ ()) ⟩ , refl ⟩
  where
  H : ∀ V → env-map to (mem V • 𝒯 zero (lift tt) • (λ x → NewClos3.init))
         ⊆ₑ mem (tos V) • mem (∥ [] ∥ ∷ []) • (λ x → NewClos4.init)
  H V zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H V (suc zero) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = here refl
  H V (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
delay-preserve (clos-op (suc n) ⦅ ! clear (bind (bind (ast N))) ,, (FV ,, FVs) ⦆) ρ ((fv ∷ fvs) ⊢ V ↦ w) d∈
   with un-𝒜 (suc n) ⟨ {!   !} , lift tt ⟩ (⟦ FV ,, FVs ⟧₊ ρ) (fv ∷ fvs) V w d∈
... | ⟨ ⟨ w∈N , neV ⟩ , fvs∈𝒯FVs ⟩ =
   ⟨ ⟨ ⟨ NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) {! H2 V   !} (to w) (IH1 w ρ' w∈N) , {!   !} ⟩ , (λ ()) ⟩ ,  ⟨ delay-preserve FV ρ fv (proj₁ d∈) , {! fvs∈𝒯FVs  !} ⟩ ⟩
   where
   ρ' : Env Value
   ρ' = (mem V) • Dfold ■ ■ (suc n) 𝒯-cons (λ x → x ≡ ∥ [] ∥) (⟦ FV ,, FVs ⟧₊ ρ) • (λ _ x → x ≡ ω)
{-   
   𝒯-cons ⟨ Fold2.fold NewClos3.Op NewClos3.sig 𝕆-Clos3 (λ x → x ≡ ω) ρ FV , ⟨ Dfold ■ ■ n 𝒯-cons (λ x → x ≡ ∥ [] ∥)  (Fold2.fold-args NewClos3.Op NewClos3.sig 𝕆-Clos3 (λ x → x ≡ ω) ρ
  FVs) , lift tt ⟩ ⟩
-}
   H2 : ∀ V → env-map to ((mem V) • Dfold ■ ■ (suc n) 𝒯-cons (λ x → x ≡ ∥ [] ∥) (⟦ FV ,, FVs ⟧₊ ρ) • (λ _ x → x ≡ ω))
         ⊆ₑ mem (tos V) • mem (∥ to fv ∷ tos fvs ∥ ∷ []) • (λ x → NewClos4.init)
   H2 V zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
   H2 V (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = {!   !}
   H2 V (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
   IH1 : ∀ d ρ → d ∈ ⟦ N ⟧ ρ → to d ∈ ⟦ delay N ⟧' (env-map to ρ)
   IH1 d ρ = delay-preserve N ρ d
   IH2 : results-rel-pres _to-⊆_ (replicate n ■) (⟦ FVs ⟧₊ ρ) (⟦ del-map-args FVs ⟧₊' (env-map to ρ))
   IH2 = del-map-args-preserve FVs ρ


{-
  G : ∀ n N fvs ρ d → d ∈ ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ 
    → to d ∈ ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' (env-map to ρ)
  G zero N fvs ρ ([] ⊢ V ↦ w) ⟨ w∈N , neV ⟩ = 
    ⟨ ⟨ ⟨ NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) (H V) (to w) 
                              (delay-preserve N (mem V • (λ x → x ≡ ∥ [] ∥) • (λ x → NewClos3.init)) w w∈N) 
        , to-ne V neV ⟩ , (λ  ()) ⟩ , refl ⟩
  G zero N fvs ρ ν d∈ = ⟨ tt , refl ⟩
  G (suc n) N (fv ,, fvs) ρ ((fv' ∷ fvs') ⊢ V ↦ w) ⟨ d∈ , ds∈ ⟩ 
    with un-𝒜 (suc n) ⟨ ( ⟦ clear (bind (bind (ast N))) ⟧ₐ ρ ) (𝒯 (suc n) (⟦ (fv ,, fvs) ⟧₊ ρ)) , lift tt ⟩ (⟦ (fv ,, fvs) ⟧₊  ρ) (fv' ∷ fvs') V w ⟨ d∈ , ds∈ ⟩
  ... | ⟨ ⟨ w∈N , neV ⟩ , fv,fvs∈𝒯 ⟩ =  ⟨ {!   !} , {!  fv,fvs∈𝒯  !} ⟩
 -}

 {-   
 𝕆-Clos3 (clos-op n) ⟨ F , Ds ⟩ = 𝒜 (suc n) ⟨ (Λ ⟨ F (𝒯 n (D ,, Ds)) , ptt ⟩) , ( D ,, Ds) ⟩
                            = 𝒜-cons D (DFold 𝒜-cons (Λ ...) Ds)
 
     ⟨ ⟨ ⟨ NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) {!   !} (to w) 
            (delay-preserve N (mem V • 𝒯 (suc n) {!   !} • (λ _ x → x ≡ ω)) w w∈N) 
            , to-ne V neV ⟩ , (λ ()) ⟩ , ? ⟩
 -} 

  {-
un-𝒜 : ∀ n F Ds fvs V w → fvs ⊢ V ↦ w ∈ 𝒜 n ⟨ Λ F , Ds ⟩ 
      → [] ⊢ V ↦ w ∈ Λ F × ∥ fvs ∥ ∈ 𝒯 n Ds
un-𝒜 zero F Ds [] V w d∈ = ⟨ d∈ , refl ⟩
un-𝒜 zero F Ds (x ∷ fvs) V w ()
un-𝒜 (suc n) F ⟨ D , Ds ⟩ (x ∷ fvs) V w ⟨ d∈ , ds∈ ⟩ with un-𝒜 n F Ds fvs V w ds∈
... | ⟨ q , q' ⟩ = ⟨ q , ⟨ d∈ , q' ⟩ ⟩
  -}

  {-
  with G n N fvs ρ (fvs' ⊢ V ↦ w) {! ds∈   !}
  ... | q = 
    ⟨ ⟨ ⟨ {!  !} , {!  to-ne V neV !} ⟩ , (λ ()) ⟩ , ⟨ delay-preserve fv ρ fv' d∈ , {!   !} ⟩ ⟩
  -}

{-
 NewClos4.⟦⟧-monotone {{Clos4-Semantics}} (delay M) 
                               (to-mem-rewrite V ρ) (to d) 
                               (delay-preserve M (mem V • ρ) d d∈)


𝕆-Clos3 (clos-op n) ⟨ F , Ds ⟩ = 𝒜 n ⟨ (Λ ⟨ F (𝒯 n Ds) , ptt ⟩) , Ds ⟩



-}


delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ V , ⟨ fvs , ⟨ fvs⊢V↦d∈M , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩
  with delay-preserve M ρ (fvs ⊢ V ↦ d) fvs⊢V↦d∈M | delay-preserve-⊆ N ρ V V⊆N
... | clos∈M' | V'⊆N' = ⟨ tos V , ⟨ [] , ⟨ ⟨ ∥ tos fvs ∥ ∷ [] , ⟨ [] 
          , ⟨ ⟨ ∥ tos fvs ∥ , clos∈M' ⟩ 
          , ⟨ G (λ z → Σ Value (λ z₁ → ⦅ z₁ , z ⦆ ∈ ⟦ delay M ⟧' (env-map to ρ))) 
          ⟨ [] ⊢ ∥ tos fvs ∥ ∷ [] ↦ ([] ⊢ tos V ↦ to d) , clos∈M' ⟩ 
          , (λ ()) ⟩ ⟩ ⟩ ⟩ , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩ ⟩ 
   where
   G : ∀ (P : Value → Set) →  P ∥ tos fvs ∥ → ∀ d → Any (_≡_ d) (∥ tos fvs ∥ ∷ []) → P d
   G P Pd .(∥ tos fvs ∥) (here refl) = Pd
delay-preserve (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = d∈
delay-preserve (pair-op ⦅ M ,, N ,, Nil ⦆) ρ ⦅ d1 , d2 ⦆ ⟨ d1∈ , d2∈ ⟩ = 
  ⟨ delay-preserve M ρ d1 d1∈ , delay-preserve N ρ d2 d2∈ ⟩
delay-preserve (fst-op ⦅ M ,, Nil ⦆) ρ d1 ⟨ d2 , d∈ ⟩ = 
  ⟨ to d2 , delay-preserve M ρ ⦅ d1 , d2 ⦆ d∈ ⟩
delay-preserve (snd-op ⦅ M ,, Nil ⦆) ρ d2 ⟨ d1 , d∈ ⟩ = 
  ⟨ to d1 , delay-preserve M ρ ⦅ d1 , d2 ⦆ d∈ ⟩
delay-preserve (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ ρ → to d ∈ ⟦ delay (tuple n ⦅ args ⦆ ) ⟧' (env-map to ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-preserve arg ρ d d∈ , ds'∈ ⟩  
     {- if this breaks, we may have to pass an argument, an IH, that this should work -}
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
  del-map-args-preserve : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ)) -}



data delay-val-list : List Value → List Value → Set
data delay-val : Value → Value → Set where
   dv-const : ∀ {B k} → delay-val (const {B} k) (const {B} k)
   dv-ω : delay-val ω ω
   dv-pair : ∀ {v₁ v₂ v₁' v₂'} → (dv₁ : delay-val v₁ v₁') → (dv₂ : delay-val v₂ v₂')
     → delay-val ⦅ v₁ , v₂ ⦆ ⦅ v₁' , v₂' ⦆
   dv-left : ∀ {V V'} → (dV : delay-val-list V V') → delay-val (left V) (left V')
   dv-right : ∀ {V V'} → (dV : delay-val-list V V') → delay-val (right V) (right V')
   dv-tup : ∀ {ds ds'} → (dvs : delay-val-list ds ds') → delay-val ∥ ds ∥ ∥ ds' ∥
   dv-ν : delay-val ν ⦅ ν , ∥ [] ∥ ⦆
   dv-↦ : ∀ {V w FVs' V' w' fvs' ignored}
      {-  → (FVs'-env : Σ[ M ∈ AST' ] w' ∈ ⟦ M ⟧' (mem V' • mem FVs' • (λ x → NewClos4.init))) -}
           {- ^this^ is uncertain -}
        → (dvV : delay-val-list V V')
        → (dvw : delay-val w w')
        → (fvs'∈ : ∥ fvs' ∥ ∈ (mem FVs'))
        ------------------------------------------------------------------
        → delay-val (ignored ⊢ V ↦ w) ⦅ [] ⊢ FVs' ↦ ([] ⊢ V' ↦ w') , ∥ fvs' ∥ ⦆ 

data delay-val-list where
   dv-nil : delay-val-list [] []
   dv-cons : ∀ {d d' ds ds'} → delay-val d d' → delay-val-list ds ds' 
      → delay-val-list (d ∷ ds) (d' ∷ ds')


_dv_ : Value → Value → Set
d dv d' = delay-val d d'

_dvₑ_ : Env Value → Env Value → Set
ρ dvₑ ρ' = ∀ i d → d ∈ ρ i → Σ[ d' ∈ Value ] d' ∈ ρ' i × d dv d'
   {- I think this in the right direction -}









{-

delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ) 

-}

{- delay-preserve, relational version -}

dv-fun : ∀ (d : Value) → Σ[ d' ∈ Value ] d dv d'
dv-list-fun : ∀ (ds : List Value) → Σ[ ds' ∈ List Value ] delay-val-list ds ds'
dv-fun (const {B} x) = ⟨ const x , dv-const ⟩
dv-fun (x ⊢ x₁ ↦ d) = ⟨ ⦅ {!   !} , {!   !} ⦆ , dv-↦ {!   !} {!   !} {!   !} ⟩
dv-fun ν = ⟨ ⦅ ν , ∥ [] ∥ ⦆ , dv-ν ⟩
dv-fun ω = ⟨ ω , dv-ω ⟩
dv-fun ⦅ d , d₁ ⦆ with dv-fun d | dv-fun d₁
... | ⟨ d' , dvd' ⟩ | ⟨ d₁' , dvd₁' ⟩ = ⟨ ⦅ d' , d₁' ⦆ , dv-pair dvd' dvd₁' ⟩
dv-fun ∥ x ∥ with dv-list-fun x
... | ⟨ x' , dvx' ⟩ = ⟨ ∥ x' ∥ , dv-tup dvx' ⟩
dv-fun (left x) with dv-list-fun x
... | ⟨ x' , dvx' ⟩ = ⟨ left x' , dv-left dvx' ⟩
dv-fun (right x) with dv-list-fun x
... | ⟨ x' , dvx' ⟩ = ⟨ right x' , dv-right dvx' ⟩
dv-list-fun [] = ⟨ [] , dv-nil ⟩
dv-list-fun (x ∷ ds) with dv-fun x | dv-list-fun ds
... | ⟨ x' , dvx' ⟩ | ⟨ ds' , dvds' ⟩ = ⟨ x' ∷ ds' , dv-cons dvx' dvds' ⟩

DP : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → Σ[ ρ' ∈ (Env Value) ]  ρ dvₑ ρ' × Σ[ d' ∈ Value ] d' ∈ ⟦ delay M ⟧' ρ' × d dv d'
{- DP-map-args : ∀ {n} args ρ → results-rel-pres _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
   DP-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ) 
   -}
DP (` x) ρ d d∈ρx = ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩
DP (clos-op zero ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ν d∈ = {!   !}
DP (clos-op zero ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ([] ⊢ V ↦ w) ⟨ w∈N , neV ⟩ = {!   !}
DP (clos-op (suc n) ⦅ ! clear (bind (bind (ast N))) ,, (FV ,, FVs) ⦆) ρ ((fv ∷ fvs) ⊢ V ↦ w) d∈ = {!   !}
DP (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ V , ⟨ fvs , ⟨ fvs⊢V↦d∈M , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩ = {!   !}
{-  with DP M ρ (fvs ⊢ V ↦ d) fvs⊢V↦d∈M | DP-⊆ N ρ V V⊆N
... | clos∈M' | V'⊆N' = ⟨ tos V , ⟨ [] , ⟨ ⟨ ∥ tos fvs ∥ ∷ [] , ⟨ [] 
          , ⟨ ⟨ ∥ tos fvs ∥ , clos∈M' ⟩ 
          , ⟨ G (λ z → Σ Value (λ z₁ → ⦅ z₁ , z ⦆ ∈ ⟦ delay M ⟧' (env-map to ρ))) 
          ⟨ [] ⊢ ∥ tos fvs ∥ ∷ [] ↦ ([] ⊢ tos V ↦ to d) , clos∈M' ⟩ 
          , (λ ()) ⟩ ⟩ ⟩ ⟩ , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩ ⟩ 
   where
   G : ∀ (P : Value → Set) →  P ∥ tos fvs ∥ → ∀ d → Any (_≡_ d) (∥ tos fvs ∥ ∷ []) → P d
   G P Pd .(∥ tos fvs ∥) (here refl) = Pd
   -}
DP (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = {!   !}
DP (pair-op ⦅ M ,, N ,, Nil ⦆) ρ ⦅ d1 , d2 ⦆ ⟨ d1∈ , d2∈ ⟩ = 
  {!   !}
DP (fst-op ⦅ M ,, Nil ⦆) ρ d1 ⟨ d2 , d∈ ⟩ = 
  {!   !}
DP (snd-op ⦅ M ,, Nil ⦆) ρ d2 ⟨ d1 , d∈ ⟩ = 
  {!   !}
DP (tuple n ⦅ args ⦆) ρ d d∈ = {!   !}
DP (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  {!   !}
DP (inl-op ⦅ M ,, Nil ⦆) ρ (left V) ⟨ neV , V⊆ ⟩ = 
  {!   !}
DP (inr-op ⦅ M ,, Nil ⦆) ρ (right V) ⟨ neV , V⊆ ⟩ = 
  {!   !}
DP (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   {!   !}
DP (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) = 
   {!   !}

{-
DP-⊆ M ρ [] V⊆ = λ d ()
DP-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  DP M ρ d (V⊆ d (here refl))
DP-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  DP-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (DP M ρ) , del-map-args-preserve args ρ ⟩
-}
