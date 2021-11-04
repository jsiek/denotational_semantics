
module ResultsCurried where

open import Primitives
open import Utilities using (extensionality)
open import SetsAsPredicates
open import Var
open import Substitution using (_•_)
open import ScopedTuple hiding (𝒫)
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public
open import Sig

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate; map)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)


private
  variable
   ℓ : Level
   A : Set ℓ


DenotFun : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
DenotFun A [] c = Result A c
DenotFun A (b ∷ bs) c = Result A b → DenotFun A bs c

DenotOp : ∀ {ℓ} A → List Sig → Set ℓ
DenotOp A bs = DenotFun A bs ■

DenotOps : ∀ {Op : Set} {ℓ} A → (sig : Op → List Sig) → Set ℓ
DenotOps A sig = ∀ op → DenotOp A (sig op)

{- =============== Types for the preservation of a relation on a DenotFun/Op ================ -}

Fun-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Fun-Rel {ℓ} A = ∀ bs c → DenotFun A bs c → DenotFun A bs c → Set (lsuc lzero l⊔ ℓ)

Op-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Op-Rel {ℓ} A = ∀ bs → DenotOp A bs → DenotOp A bs → Set (lsuc lzero l⊔ ℓ)

DenotOps-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DenotOps-Rel {ℓ} A = ∀ {Op} (sig : Op → List Sig) → DenotOps A sig → DenotOps A sig → Set (lsuc lzero l⊔ ℓ)

result-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ b → Result A b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres {ℓ} R ■ a1 a2 = Lift (lsuc lzero l⊔ ℓ) (R a1 a2)
result-rel-pres R (ν b) f1 f2 = ∀ a1 a2 → R a1 a2 → result-rel-pres R b (f1 a1) (f2 a2)
result-rel-pres R (∁ b) = result-rel-pres R b

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → Fun-Rel A
fun-rel-pres {ℓ} R [] c 𝒻 ℊ = result-rel-pres R c 𝒻 ℊ
fun-rel-pres R (b ∷ bs) c 𝒻 ℊ = ∀ D E → result-rel-pres R b D E → fun-rel-pres R bs c (𝒻 D) (ℊ E)

op-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → Op-Rel A
op-rel-pres {ℓ} R [] 𝒻 ℊ = Lift (lsuc lzero l⊔ ℓ) (R 𝒻 ℊ)
op-rel-pres R (b ∷ bs) 𝒻 ℊ = ∀ D E → result-rel-pres R b D E → op-rel-pres R bs (𝒻 D) (ℊ E)

ops-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DenotOps-Rel A
ops-rel-pres R sig 𝕆₁ 𝕆₂ = ∀ op → op-rel-pres R (sig op) (𝕆₁ op) (𝕆₂ op)


DApp : ∀ {ℓ} {A : Set ℓ} b bs c
  → DenotFun A (b ∷ bs) c → Result A b → DenotFun A bs c
DApp b bs c F a = F a


DComp1 : ∀ {ℓ} {A : Set ℓ} b c cs d
  → DenotFun A (b ∷ []) c → DenotFun A (c ∷ cs) d
  → DenotFun A (b ∷ cs) d
DComp1 b c cs d 𝒻 ℊ = λ z → ℊ (𝒻 z)

DComp : ∀ {ℓ} {A : Set ℓ} bs c cs d
  → DenotFun A bs c → DenotFun A (c ∷ cs) d
  → DenotFun A (bs ++ cs) d
DComp [] c cs d 𝒻 ℊ = ℊ 𝒻
DComp (x ∷ bs) c cs d 𝒻 ℊ = λ z → DComp bs c cs d (𝒻 z) ℊ

DApp-pres : ∀ {ℓ}{A : Set ℓ} R b bs c
   → (𝒻1 𝒻2 : DenotFun A (b ∷ bs) c) → (a1 a2 : Result A b )
   → fun-rel-pres R (b ∷ bs) c 𝒻1 𝒻2
   → result-rel-pres R b a1 a2
   → fun-rel-pres R bs c (DApp b bs c 𝒻1 a1) (DApp b bs c 𝒻2 a2)
DApp-pres R b bs c 𝒻1 𝒻2 a1 a2 𝒻-pres a1Ra2 = 
  𝒻-pres a1 a2 a1Ra2
  
DComp-pres : ∀ {ℓ}{A : Set ℓ} R bs c cs d
   (𝒻1 𝒻2 : DenotFun A bs c) (ℊ1 ℊ2 : DenotFun A (c ∷ cs) d)
    → fun-rel-pres R bs c 𝒻1 𝒻2 → fun-rel-pres R (c ∷ cs) d ℊ1 ℊ2
    → fun-rel-pres R (bs ++ cs) d (DComp bs c cs d 𝒻1 ℊ1) (DComp bs c cs d 𝒻2 ℊ2)
DComp-pres R [] c cs d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻-pres ℊ-pres = ℊ-pres 𝒻1 𝒻2 𝒻-pres
DComp-pres R (b ∷ bs) c cs d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻-pres ℊ-pres D E RDE = 
  DComp-pres R bs c cs d (𝒻1 D) (𝒻2 E) ℊ1 ℊ2 (𝒻-pres D E RDE) ℊ-pres


{-   =========== Preserved Properties ================ -}


monotone : ∀ {A : Set} bs b → DenotFun (𝒫 A) bs b → Set₁
monotone bs b 𝒻 = fun-rel-pres _⊆_ bs b 𝒻 𝒻

𝕆-monotone : ∀ {A : Set} {Op} sig → DenotOps {Op = Op} (𝒫 A) sig → Set₁
𝕆-monotone sig 𝕆 = ops-rel-pres _⊆_ sig 𝕆 𝕆

congruent : ∀ {A : Set} bs b → DenotFun (𝒫 A) bs b → Set₁
congruent bs b 𝒻 = fun-rel-pres _≃_ bs b 𝒻 𝒻

𝕆-congruent : ∀ {A : Set} {Op} sig → DenotOps {Op = Op} (𝒫 A) sig → Set₁
𝕆-congruent sig 𝕆 = ops-rel-pres _≃_ sig 𝕆 𝕆

Every : ∀ {A : Set} (R : Rel A lzero) → 𝒫 A → 𝒫 A → Set
Every R A B = ∀ a b → a ∈ A → b ∈ B → R a b

Every-⊆ : ∀ {T R A B U V}
     → Every {T} R A B → U ⊆ A → V ⊆ B → Every R U V
Every-⊆ A~B U⊆A V⊆B a b a∈U b∈V = A~B a b (U⊆A a a∈U) (V⊆B b b∈V)

{- this can be used similarly... 
  for a denotational function: fun-rel-pres (Every R)
  for a DenotOps : ops-rel-pres (Every R) 
-}

{- for example, this can be used to define consistency, based on some 
   consistent : Value → Value → Set -}

fun-consistent : ∀ {A : Set} (consistent : A → A → Set) bs b → DenotFun (𝒫 A) bs b → Set₁
fun-consistent consistent bs b 𝒻 = fun-rel-pres (Every consistent) bs b 𝒻 𝒻

𝕆-consistent : ∀ {A : Set} (consistent : A → A → Set) {Op} sig → DenotOps {Op = Op} (𝒫 A) sig → Set₁
𝕆-consistent consistent sig 𝕆 = ops-rel-pres (Every consistent) sig 𝕆 𝕆


{- Continuity appears to be a different beast... relying on info about the environment -}
{- But I wonder if a part of it can be factored into a propert about
  just the denotational operators -}


{- =============== translating to and from tuples =============== -}

uncurryFun : ∀ {ℓ} {A : Set ℓ} {bs c} → DenotFun A bs c → (Tuple bs (Result A) → Result A c)
uncurryFun {bs = []} 𝒻 _ = 𝒻
uncurryFun {bs = (b ∷ bs)} 𝒻 ⟨ D , Ds ⟩ = uncurryFun (𝒻 D) Ds  

curryFun : ∀ {ℓ} {A : Set ℓ} {bs c} → (Tuple bs (Result A) → Result A c) → DenotFun A bs c
curryFun {bs = []} 𝒻 = 𝒻 (lift tt)
curryFun {bs = (b ∷ bs)} 𝒻 D = curryFun (λ Ds → 𝒻 ⟨ D , Ds ⟩)


