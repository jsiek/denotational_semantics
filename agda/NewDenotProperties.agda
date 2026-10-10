{-# OPTIONS --safe #-}
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s; _+_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import abt.Sig
open import abt.Var
open import abt.GSubst using (_•_)
open import NewSigUtil
open import NewSyntaxUtil
open import NewDOpSig

module NewDenotProperties where


{- =================== Monotonicity ================================= -}

monotone : ∀ {A : Set} bs b → DFun (𝒫 A) bs b → Set₁
monotone bs b 𝒻 = fun-rel-pres _⊆_ bs b 𝒻 𝒻

𝕆-monotone : ∀ {A : Set} {Op} sig → DOpSig {Op = Op} (𝒫 A) sig → Set₁
𝕆-monotone sig 𝕆 = opsig-rel-pres _⊆_ sig 𝕆 𝕆

congruent : ∀ {A : Set} bs b → DFun (𝒫 A) bs b → Set₁
congruent bs b 𝒻 = fun-rel-pres _≃_ bs b 𝒻 𝒻

𝕆-congruent : ∀ {A : Set} {Op} sig → DOpSig {Op = Op} (𝒫 A) sig → Set₁
𝕆-congruent sig 𝕆 = opsig-rel-pres _≃_ sig 𝕆 𝕆


{- =================== Consitency ================================= -}

Every : ∀ {A : Set} (R : A → A → Set) → 𝒫 A → 𝒫 A → Set
Every R A B = ∀ a b → a ∈ A → b ∈ B → R a b

Every-⊆ : ∀ {T R A B U V}
     → Every {T} R A B → U ⊆ A → V ⊆ B → Every R U V
Every-⊆ A~B U⊆A V⊆B a b a∈U b∈V = A~B a b (U⊆A a a∈U) (V⊆B b b∈V)

consistent : ∀ {A : Set} (consistent : A → A → Set) bs b → DFun (𝒫 A) bs b → Set₁
consistent consistent bs b 𝒻 = fun-rel-pres (Every consistent) bs b 𝒻 𝒻

𝕆-consistent : ∀ {A : Set} (consistent : A → A → Set) {Op} sig → DOpSig {Op = Op} (𝒫 A) sig → Set₁
𝕆-consistent consistent sig 𝕆 = opsig-rel-pres (Every consistent) sig 𝕆 𝕆

