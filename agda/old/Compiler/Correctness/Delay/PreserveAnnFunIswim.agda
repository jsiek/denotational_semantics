{-# OPTIONS --allow-unsolved-metas #-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Filter.Domain.AnnFun.Domain as DSource
open import Compiler.Model.Filter.Domain.ISWIM.Domain as DTarget
  renaming (Value to Value'; wf to wf'; _~_ to _~'_; _d≟_ to _d≟'_;
            ⊔-closed to ⊔-closed'; singleton-⊔-closed to singleton-⊔-closed';
            _⊑_ to _⊑'_; ⊑-closed to ⊑-closed';
            ⊑-closure to ⊑-closure'; ⊑-closure-closed to ⊑-closure'-closed;
            ⊑-closure-⊔-closed to ⊑-closure'-⊔-closed;
            ⊑-refl to ⊑-refl'; _◃_▹_ to _◃'_▹'_)
open import Compiler.Model.Filter.Domain.AnnFun.Ops as OpSource
open import Compiler.Model.Filter.Domain.ISWIM.Ops as OpTarget
open import Compiler.Model.Filter.Sem.Clos3AnnFun as Source
open import Compiler.Model.Filter.Sem.Clos4Iswim as Target
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; reduce)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; map⁻)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; suc; zero)
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

module Compiler.Correctness.Delay.PreserveAnnFunIswim where

{- NOTE: Need to search for TODO and resolve issues -}


{-
Miscellaneous TODO:
 - going to need to refactor Ordering properties into OrderingAux probably
   + do Aux files know about environments and denotations?
-}

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
       → (fv ∷ FV ⊢ν) ~to ⦅ fv' ∷ FV' ↦ ν , fv'' ⦆)

The main issue is this definition of ~tos, which doesn't seem powerful enough for function cases.
data _~tos_ where
  [] : [] ~tos []
  _∷_ : ∀ {d d' ds ds'} → (d~ : d ~to d') → (ds~ : ds ~tos ds')
        → (d ∷ ds) ~tos (d' ∷ ds')

 -}


tos : ∀ {n} → Vec Value n → Vec Value' n
to : Value → Value'
to (const x) = const x
to (FV ⊢ V ↦ w) = ⦅ (to FV ↦ (to V ↦ to w)) ∣ ⊔ ∣ to FV ⦆
to (FV ⊢ν) = ⦅ (to FV ↦ ν) ∣ ⊔ ∣ to FV ⦆
to ω = ω
to (tup[ i ] d) = tup[ i ] (to d)
to (left v) = left (to v)
to (right v) = right (to v)
to ⦅ u ∣ = ⦅ to u ∣
to ∣ v ⦆ = ∣ to v ⦆
to (u ⊔ v) = to u ⊔ (to v)
tos [] = []
tos (d ∷ ds) = to d ∷ tos ds

to-set : 𝒫 Value → 𝒫 Value'
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d

_to-⊆_ : 𝒫 Value → 𝒫 Value' → Set
A to-⊆ B = ∀ d → d ∈ A → to d ∈ B

env-map : ∀ {A B : Set} → (A → B) → (ℕ → 𝒫 A) → (ℕ → 𝒫 B)
env-map {A} {B} f ρ x b = Σ[ a ∈ A ] a ∈ (ρ x) × b ≡ f a


to-split-⊑ : ∀ {u uL uR} → uL ◃ u ▹ uR → to u ⊑' (to uL ⊔ to uR)
to-split-⊑ split-⊔ = DTarget.⊔⊑⊔ ⊑-refl' ⊑-refl'
to-split-⊑ {FV ⊢ u ↦ v}{FV ⊢ u ↦ vL}{FV ⊢ u ↦ vR} (split-↦ split) = 
  DTarget.⊑-⊔-L (DTarget.⊑-trans {⦅ to FV ↦ to u ↦ to v ∣}
    {⦅ to FV ↦ to u ↦ to vL ∣ ⊔ ⦅ to FV ↦ to u ↦ to vR ∣}
    {⦅ to FV ↦ to u ↦ to vL , to FV ⦆' ⊔  ⦅ to FV ↦ to u ↦ to vR , to FV ⦆'}
     (DTarget.⊑-trans {⦅ to FV ↦ to u ↦ to v ∣}{⦅ to FV ↦ to u ↦ (to vL ⊔ to vR) ∣}
                       {⦅ to FV ↦ to u ↦ to vL ∣ ⊔ ⦅ to FV ↦ to u ↦ to vR ∣} 
                       (DTarget.⊑-fst (DTarget.⊑-↦ ⊑-refl' (DTarget.⊑-↦ ⊑-refl' (to-split-⊑ split)))) 
                       (DTarget.⊑-dist-⊔ (split-fst (split-↦ (split-↦ split-⊔))))) 
                       (DTarget.⊔⊑⊔ (DTarget.⊑-⊔-R1 ⊑-refl') (DTarget.⊑-⊔-R1 ⊑-refl'))) 
                       (DTarget.⊑-⊔-R1 (DTarget.⊑-⊔-R2 ⊑-refl'))
to-split-⊑ (split-fst split) = DTarget.⊑-trans (DTarget.⊑-fst (to-split-⊑ split)) 
                                           (DTarget.⊑-dist-⊔ (split-fst split-⊔))
to-split-⊑ (split-snd split) = DTarget.⊑-trans (DTarget.⊑-snd (to-split-⊑ split)) 
                                           (DTarget.⊑-dist-⊔ (split-snd split-⊔))
to-split-⊑ (split-tup split) = DTarget.⊑-trans (DTarget.⊑-tup (to-split-⊑ split)) 
                                           (DTarget.⊑-dist-⊔ (split-tup split-⊔))
to-split-⊑ (split-left split) = DTarget.⊑-trans (DTarget.⊑-left (to-split-⊑ split)) 
                                           (DTarget.⊑-dist-⊔ (split-left split-⊔))
to-split-⊑ (split-right split) = DTarget.⊑-trans (DTarget.⊑-right (to-split-⊑ split)) 
                                           (DTarget.⊑-dist-⊔ (split-right split-⊔))

to-mono : ∀ {u v} → u ⊑ v → to u ⊑' to v
to-mono ⊑-ω = ⊑-ω
to-mono ⊑-ν-ν = ⊑-refl'
to-mono ⊑-ν-↦ = 
  DTarget.⊔⊑⊔ (DTarget.⊑-fst (DTarget.⊑-↦ ⊑-refl' ⊑-ν-↦)) ⊑-refl'
to-mono ⊑-const = ⊑-const
to-mono (⊑-⊔-R1-å åu u⊑v) = DTarget.⊑-⊔-R1 (to-mono u⊑v)
to-mono (⊑-⊔-R2-å åu u⊑v) = DTarget.⊑-⊔-R2 (to-mono u⊑v)
to-mono (⊑-fst-å åu u⊑v) = DTarget.⊑-fst (to-mono u⊑v)
to-mono (⊑-snd-å åu u⊑v) = DTarget.⊑-snd (to-mono u⊑v)
to-mono (⊑-tup-å åu u⊑v) = DTarget.⊑-tup (to-mono u⊑v)
to-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = 
  DTarget.⊔⊑⊔ (DTarget.⊑-fst (DTarget.⊑-↦ ⊑-refl' (DTarget.⊑-↦ (to-mono u⊑v) (to-mono u⊑v₁)))) 
               ⊑-refl'
to-mono (⊑-left-å åu u⊑v) = DTarget.⊑-left (to-mono u⊑v)
to-mono (⊑-right-å åu u⊑v) = DTarget.⊑-right (to-mono u⊑v)
to-mono (⊑-split split ⊑L ⊑R) = 
  DTarget.⊑-trans (to-split-⊑ split) (DTarget.⊑-⊔-L (to-mono ⊑L) (to-mono ⊑R))



postulate
  ⟦⟧'-⊑-closed : ∀ (M : AST') ρ (u v : Value') → v ∈ ⟦ M ⟧' ρ → u ⊑' v → u ∈ ⟦ M ⟧' ρ
  ⟦⟧'-⊔-closed : ∀ (M : AST') ρ (u v : Value') → u ∈ ⟦ M ⟧' ρ → v ∈ ⟦ M ⟧' ρ
                → (u ⊔ v) ∈ ⟦ M ⟧' ρ
  ⟦⟧-⊔-closed : ∀ (M : AST) ρ (u v : Value) → u ∈ ⟦ M ⟧ ρ → v ∈ ⟦ M ⟧ ρ
                → (u ⊔ v) ∈ ⟦ M ⟧ ρ
  ⟦⟧-⊑-closed : ∀ (M : AST) ρ (u v : Value) → v ∈ ⟦ M ⟧ ρ → u ⊑ v → u ∈ ⟦ M ⟧ ρ 


helpful-lemma : ∀ M ρ u v → (u ⊔ v) ∈ ⟦ M ⟧' ρ → u ∈ ⟦ M ⟧' ρ × v ∈ ⟦ M ⟧' ρ
helpful-lemma M ρ u v u⊔v∈M = 
  ⟨ ⟦⟧'-⊑-closed M ρ u (u ⊔ v) u⊔v∈M (DTarget.⊑-⊔-R1 ⊑-refl') 
  , ⟦⟧'-⊑-closed M ρ v (u ⊔ v) u⊔v∈M (DTarget.⊑-⊔-R2 ⊑-refl') ⟩

delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
delay-args-preserve-nth : ∀ {n} args (i : Fin n) ρ d 
   → d ∈ OpSource.nthD (⟦ args ⟧₊ ρ) i
   → to d ∈ OpTarget.nthD (⟦ del-map-args args ⟧₊' (env-map to ρ)) i
delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d 
  ⟨ ω , ⟨ FV , ⟨ w , ⟨ w∈ΛN[FV] , ⟨ FV∈𝒯fvs , refl ⟩ ⟩ ⟩ ⟩ ⟩ with w | w∈ΛN[FV]
... | ω | tt = tt
... | ω ⊢ν | tt = ⟨ ⟨ to FV , ⟨ tt , G3 ⟩ ⟩ 
    , ⟨ to FV ↦ ν , ⟨ tt , G3 ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ ρ) 
                 → to d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 n fvs ω d∈ = tt
  G2 n fvs (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ = ⟨ G2 n fvs d d∈ , G2 n fvs d₁ d₁∈ ⟩
  G2 (suc n) fvs (tup[ i ] d) ⟨ refl , d∈ ⟩ =
     ⟨ refl , delay-args-preserve-nth fvs i ρ d d∈ ⟩
  G3 : to FV ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 = G2 n fvs FV FV∈𝒯fvs
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d 
  ⟨ ω , ⟨ FV , ⟨ w , ⟨ w∈ΛN[FV] , ⟨ FV∈𝒯fvs , refl ⟩ ⟩ ⟩ ⟩ ⟩ 
    | ω ⊢ V ↦ w' | w'∈N[FV][V] = 
  ⟨ ⟨ to FV , ⟨ G1 , G3 ⟩ ⟩  
  , ⟨ to FV ↦ to V ↦ to w' , ⟨ G1 , G3 ⟩ ⟩ ⟩
  where
  IH : to w' ∈ ⟦ delay N ⟧' (env-map to ((⊑-closure V) • (⊑-closure FV) • (λ i d → d ≡ ω)))
  IH = delay-preserve N ((⊑-closure V) • (⊑-closure FV) • (λ i d → d ≡ ω)) w' w'∈N[FV][V]
  H : (env-map to ((⊑-closure V) • (⊑-closure FV) • (λ i d → d ≡ ω))) ⊆ₑ ((⊑-closure' (to V)) • (⊑-closure' (to FV)) • (λ i d → d ≡ ω))
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = to-mono a⊑
  H (suc zero) d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = to-mono a⊑
  H (suc (suc i)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : to w' ∈ ⟦ delay N ⟧' ((⊑-closure' (to V)) • (⊑-closure' (to FV)) • (λ i d → d ≡ ω))
  G1 = Target.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w') IH
  G2 : ∀ n fvs d → d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ ρ) 
                 → to d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 n fvs ω d∈ = tt
  G2 n fvs (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ = ⟨ G2 n fvs d d∈ , G2 n fvs d₁ d₁∈ ⟩
  G2 (suc n) fvs (tup[ i ] d) ⟨ refl , d∈ ⟩ =
    ⟨ refl , delay-args-preserve-nth fvs i ρ d d∈ ⟩
  G3 : to FV ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 = G2 n fvs FV FV∈𝒯fvs
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d 
  ⟨ ω , ⟨ FV , ⟨ w , ⟨ w∈ΛN[FV] , ⟨ FV∈𝒯fvs , refl ⟩ ⟩ ⟩ ⟩ ⟩
    | u ⊔ v | ⟨ u∈ΛN[FV] , v∈ΛN[FV] ⟩ = {!   !}
{- TODO termination checking fails on these... we can
  do induction here on the size of the value instead of on the structure of the value
  as the annotation will not affect value size. But this might have consequences
  for the theorem statement and may just take time to thread through.

  ⟨ delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
                   ρ (annot u FV) 
                   ⟨ ω , ⟨ FV , ⟨ u , ⟨ u∈ΛN[FV] , ⟨ FV∈𝒯fvs , refl ⟩ ⟩ ⟩ ⟩ ⟩ 
  , delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
                   ρ (annot v FV)
                   ⟨ ω , ⟨ FV , ⟨ v , ⟨ v∈ΛN[FV] , ⟨ FV∈𝒯fvs , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
                   -}
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d 
    ⟨ FV , ⟨ V , ⟨ FV⊢V↦d∈M , V∈N ⟩ ⟩ ⟩ 
  with delay-preserve M ρ (FV ⊢ V ↦ d) FV⊢V↦d∈M | delay-preserve N ρ V V∈N
... | IHM | toV∈N' = 
  ⟨ to V , ⟨ ⟨ to FV , IHM' ⟩ , toV∈N' ⟩ ⟩
  where
  IHM' : ⦅ to FV ↦ to V ↦ to d ∣ ∈ ⟦ delay M ⟧' (env-map to ρ)
       × ∣ to FV ⦆ ∈ ⟦ delay M ⟧' (env-map to ρ)
  IHM' = helpful-lemma (delay M) (env-map to ρ) ⦅ to FV ↦ to V ↦ to d ∣ ∣ to FV ⦆ IHM
delay-preserve (lit B k ⦅ Nil ⦆) ρ ω tt = tt
delay-preserve (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-preserve (lit B k ⦅ Nil ⦆) ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-preserve (lit B k ⦅ Nil ⦆) ρ u u∈ 
  , delay-preserve (lit B k ⦅ Nil ⦆) ρ v v∈ ⟩
delay-preserve (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ ρ → to d ∈ ⟦ delay (tuple n ⦅ args ⦆ ) ⟧' (env-map to ρ) 
  G n args ρ ω tt = tt
  G (suc n) args ρ (tup[ i ] d) ⟨ refl , d∈ ⟩ = 
    ⟨ refl , delay-args-preserve-nth args i ρ d d∈ ⟩
  G n args ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G n args ρ u u∈ , G n args ρ v v∈ ⟩
delay-preserve (get i ⦅ M ,, Nil ⦆) ρ d d∈ = delay-preserve M ρ (tup[ i ] d) d∈
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ ω tt = tt
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-preserve M ρ v v∈
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ =
  ⟨ delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ u u∈ 
  , delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ ω tt = tt
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-preserve M ρ v v∈
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ u u∈ 
  , delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
  inj₁ ⟨ to V , ⟨ delay-preserve L ρ (left V) LV∈ , G1 ⟩ ⟩
  where
  IH : to d ∈ ⟦ delay M ⟧' (env-map to ((⊑-closure V) • ρ))
  IH = delay-preserve M ((⊑-closure V) • ρ) d d∈
  H : (env-map to ((⊑-closure V) • ρ)) ⊆ₑ ((⊑-closure' (to V)) • env-map to ρ)
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = to-mono a⊑
  H (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G1 : to d ∈ ⟦ delay M ⟧' ((⊑-closure' (to V)) • env-map to ρ)
  G1 = Target.⟦⟧-monotone {{Clos4-Semantics}} (delay M) H (to d) IH
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) = 
  inj₂ ⟨ to V , ⟨ delay-preserve L ρ (right V) RV∈ , G1 ⟩ ⟩
  where
  IH : to d ∈ ⟦ delay N ⟧' (env-map to ((⊑-closure V) • ρ))
  IH = delay-preserve N ((⊑-closure V) • ρ) d d∈
  H : (env-map to ((⊑-closure V) • ρ)) ⊆ₑ ((⊑-closure' (to V)) • env-map to ρ)
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = to-mono a⊑
  H (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G1 : to d ∈ ⟦ delay N ⟧' ((⊑-closure' (to V)) • env-map to ρ)
  G1 = Target.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to d) IH

delay-args-preserve-nth {.(suc _)} (arg ,, args) zero ρ d d∈ = delay-preserve arg ρ d d∈
delay-args-preserve-nth {.(suc _)} (arg ,, args) (suc i) ρ d d∈ = delay-args-preserve-nth args i ρ d d∈


{-
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres' _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)
-}
{-
delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩
  -}
