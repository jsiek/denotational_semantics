
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig

module proof.Framework.GraphModel.DenotProperties where


{- =================== Monotonicity ================================= -}

monotone : ∀ {A : Set} bs b → DFun (𝒫 A) bs b → Set₁
monotone bs b 𝒻 = fun-rel-pres _⊆_ bs b 𝒻 𝒻

𝕆-monotone : ∀ {A : Set} {Op} sig → DOpSig {Op = Op} (𝒫 A) sig → Set₁
𝕆-monotone sig 𝕆 = opsig-rel-pres _⊆_ sig 𝕆 𝕆

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

