module NewDOpSig where

open import Primitives
open import SetsAsPredicates
open import abt.Var
open import abt.GSubst using (_•_)
open import abt.ScopedTuple hiding (𝒫)
open import abt.Sig using (Sig; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public
open import abt.Sig

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

Results : ∀ {ℓ} → Set ℓ → List Sig → Set ℓ
Results A bs = Tuple bs (Result A)

DFun : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
DFun A bs c = Results A bs → Result A c

DOp : ∀ {ℓ} A → List Sig → Set ℓ
DOp A bs = DFun A bs ■

DOpSig : ∀ {Op : Set} {ℓ} A → (sig : Op → List Sig) → Set ℓ
DOpSig A sig = ∀ op → DOp A (sig op)

{- =============== Types for the preservation of a relation on a DFun/Op ================ -}

DFun-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DFun-Rel {ℓ} A = ∀ bs c → DFun A bs c → DFun A bs c → Set (lsuc lzero l⊔ ℓ)

DOp-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOp-Rel {ℓ} A = ∀ bs → DOp A bs → DOp A bs → Set (lsuc lzero l⊔ ℓ)

DOpSig-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOpSig-Rel {ℓ} A = ∀ {Op} (sig : Op → List Sig) → DOpSig A sig → DOpSig A sig → Set (lsuc lzero l⊔ ℓ)

result-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ b → Result A b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres {ℓ} R ■ a1 a2 = Lift (lsuc lzero l⊔ ℓ) (R a1 a2)
result-rel-pres R (ν b) f1 f2 = ∀ a1 a2 → R a1 a2 → result-rel-pres R b (f1 a1) (f2 a2)
result-rel-pres R (∁ b) = result-rel-pres R b

results-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ bs → Results A bs → Results A bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres R [] _ _ = ⊤
results-rel-pres R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres R b D E × results-rel-pres R bs Ds Es

result-rel-pres' : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set) → (∀ b → Result A b → Result B b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres' {ℓ} R ■ a b = Lift (lsuc lzero l⊔ ℓ) (R a b)
result-rel-pres' R (ν 𝓈) f g = ∀ a b → R a b → result-rel-pres' R 𝓈 (f a) (g b)
result-rel-pres' R (∁ 𝓈) = result-rel-pres' R 𝓈

results-rel-pres' : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set) 
      → (∀ bs → Results A bs → Results B bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres' R [] _ _ = ⊤
results-rel-pres' R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres' R b D E × results-rel-pres' R bs Ds Es

result-rel-pres-1 : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set (lsuc lzero)) → (∀ b → Result A b → Result B b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres-1 {ℓ} R ■ a b = Lift (lsuc lzero l⊔ ℓ) (R a b)
result-rel-pres-1 R (ν 𝓈) f g = ∀ a b → R a b → result-rel-pres-1 R 𝓈 (f a) (g b)
result-rel-pres-1 R (∁ 𝓈) = result-rel-pres-1 R 𝓈

results-rel-pres-1 : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set (lsuc lzero)) 
      → (∀ bs → Results A bs → Results B bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres-1 R [] _ _ = ⊤
results-rel-pres-1 R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres-1 R b D E × results-rel-pres-1 R bs Ds Es

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DFun-Rel A
fun-rel-pres R bs c f g = ∀ Ds Es → results-rel-pres R bs Ds Es → result-rel-pres R c (f Ds) (g Es)

op-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DOp-Rel A
op-rel-pres R bs = fun-rel-pres R bs ■

opsig-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DOpSig-Rel A
opsig-rel-pres R sig O₁ O₂ = ∀ op → op-rel-pres R (sig op) (O₁ op) (O₂ op)


{- =============== Types for the preservation of a predicate on a DFun/Op ================ -}

DFun-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DFun-Pred {ℓ} A = ∀ bs c → DFun A bs c → Set (lsuc lzero l⊔ ℓ)

Op-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Op-Pred {ℓ} A = ∀ bs → DOp A bs → Set (lsuc lzero l⊔ ℓ)

DOpSig-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOpSig-Pred {ℓ} A = ∀ {Op} (sig : Op → List Sig) → DOpSig A sig → Set (lsuc lzero l⊔ ℓ)

result-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → (∀ b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-pred-pres {ℓ} P ■ a = Lift (lsuc lzero l⊔ ℓ) (P a)
result-pred-pres P (ν b) f = ∀ a → P a → result-pred-pres P b (f a)
result-pred-pres P (∁ b) = result-pred-pres P b

results-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → (∀ bs → Results A bs → Set (lsuc lzero l⊔ ℓ))
results-pred-pres P [] _ = ⊤
results-pred-pres P (b ∷ bs) ⟨ D , Ds ⟩ = 
  result-pred-pres P b D × results-pred-pres P bs Ds

fun-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → DFun-Pred A
fun-pred-pres {ℓ} P bs c F = ∀ Ds → results-pred-pres P bs Ds → result-pred-pres P c (F Ds)

op-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → Op-Pred A
op-pred-pres P bs = fun-pred-pres P bs ■

opsig-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → DOpSig-Pred A
opsig-pred-pres P sig O = ∀ op → op-pred-pres P (sig op) (O op)


{- ============================= Combinators ============================= -}

DApp1 : ∀ {ℓ} {A : Set ℓ} b bs c
  → DFun A (b ∷ bs) c → Result A b → DFun A bs c
DApp1 b bs c F a Ds = F ⟨ a , Ds ⟩

DComp1 : ∀ {ℓ} {A : Set ℓ} b c cs d
  → DFun A (b ∷ []) c → DFun A (c ∷ cs) d
  → DFun A (b ∷ cs) d
DComp1 b c cs d f g ⟨ D , Ds ⟩ = g ⟨ f ⟨ D , ptt ⟩ , Ds ⟩

Dfold : ∀ {ℓ}{A : Set ℓ} b c n → DFun A (b ∷ c ∷ []) c
    → Result A c
    → DFun A (replicate n b) c
Dfold b c zero f a (ptt) = a
Dfold b c (suc n) f a ⟨ D , Ds ⟩ = f ⟨ D , ⟨ Dfold b c n f a Ds , ptt ⟩ ⟩

DApp1-pres : ∀ {ℓ}{A : Set ℓ} R b bs c
   → (f1 f2 : DFun A (b ∷ bs) c) → (a1 a2 : Result A b )
   → fun-rel-pres R (b ∷ bs) c f1 f2
   → result-rel-pres R b a1 a2
   → fun-rel-pres R bs c (DApp1 b bs c f1 a1) (DApp1 b bs c f2 a2)
DApp1-pres R b bs c f1 f2 a1 a2 f-pres a1Ra2 Ds1 Ds2 Ds1RDs2 = 
  f-pres ⟨ a1 , Ds1 ⟩ ⟨ a2 , Ds2 ⟩ ⟨ a1Ra2 , Ds1RDs2 ⟩

DComp1-pres : ∀ {ℓ}{A : Set ℓ} R b c cs d
   (f1 f2 : DFun A (b ∷ []) c) (g1 g2 : DFun A (c ∷ cs) d)
    → fun-rel-pres R (b ∷ []) c f1 f2 → fun-rel-pres R (c ∷ cs) d g1 g2
    → fun-rel-pres R (b ∷ cs) d (DComp1 b c cs d f1 g1) (DComp1 b c cs d f2 g2)
DComp1-pres R b c cs d f1 f2 g1 g2 f-pres g-pres ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ ERD , EsRDs ⟩ = 
  g-pres  ⟨ f1  ⟨ D , ptt ⟩ , Ds ⟩ ⟨ f2 ⟨ E , ptt ⟩ , Es ⟩ 
          ⟨ f-pres ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ ERD , ptt ⟩ , EsRDs ⟩

Dfold-pres : ∀ {ℓ}{A : Set ℓ} R b c n
  → (f1 f2 : DFun A (b ∷ c ∷ []) c)
  → (a1 a2 : Result A c)
  → fun-rel-pres R (b ∷ c ∷ []) c f1 f2
  → result-rel-pres R c a1 a2
  → fun-rel-pres R (replicate n b) c (Dfold b c n f1 a1) (Dfold b c n f2 a2)
Dfold-pres R b c zero f1 f2 a1 a2 f~ a~ _ _ _ = a~
Dfold-pres R b c (suc n) f1 f2 a1 a2 f~ a~ ⟨ D1 , Ds1 ⟩ ⟨ D2 , Ds2 ⟩ ⟨ D~ , Ds~ ⟩ = 
  f~ ⟨ D1 , ⟨ Dfold b c n f1 a1 Ds1 , ptt ⟩ ⟩ ⟨ D2 , ⟨ Dfold b c n f2 a2 Ds2 , ptt ⟩ ⟩ 
     ⟨ D~ , ⟨ Dfold-pres R b c n f1 f2 a1 a2 f~ a~ Ds1 Ds2 Ds~ , ptt ⟩ ⟩


{-

Diter : ∀ {ℓ}{A : Set ℓ} (n : ℕ) bs c → (f₀ : DFun A bs c) 
     → (f : DFun A bs c → DFun A bs c)
     → DFun A bs c
Diter zero bs c f₀ f = f₀
Diter (suc n) bs c f₀ f = f (Diter n bs c f₀ f)

Diter-pres : ∀ {ℓ}{A : Set ℓ} R (n : ℕ) bs c → (f₀ f₀' : DFun A bs c)
   → (f f' : DFun A bs c → DFun A bs c)
   → fun-rel-pres R bs c f₀ f₀'
   → (∀ g g' → fun-rel-pres R bs c g g' → fun-rel-pres R bs c (f g) (f' g'))
   → fun-rel-pres R bs c (Diter n bs c f₀ f) (Diter n bs c f₀' f')
Diter-pres R zero bs c f₀ f₀' f f' f₀~ f~ = f₀~
Diter-pres R (suc n) bs c f₀ f₀' f f' f₀~ f~ = 
  f~ (Diter n bs c f₀ f) (Diter n bs c f₀' f') (Diter-pres R n bs c f₀ f₀' f f' f₀~ f~)

DComp-rest : ∀ {ℓ} {A : Set ℓ} bs c d → DFun A bs c → DFun A (c ∷ bs) d
  → DFun A bs d
DComp-rest [] c d f g = g f
DComp-rest (x ∷ bs) c d f g D = DComp-rest bs c d (f D) (λ z → g z D)

DComp-rest-pres : ∀ {ℓ}{A : Set ℓ} R bs c d
  → (f1 f2 : DFun A bs c)
  → (g1 g2 : Result A c → DFun A bs d)
  → fun-rel-pres R bs c f1 f2
  → fun-rel-pres R (c ∷ bs) d g1 g2
  → fun-rel-pres R bs d (DComp-rest bs c d f1 g1) (DComp-rest bs c d f2 g2)
DComp-rest-pres R [] c d f1 f2 g1 g2 f~ g~ = g~ f1 f2 f~
DComp-rest-pres R (x ∷ bs) c d f1 f2 g1 g2 f~ g~ D1 D2 D~ = 
  DComp-rest-pres R bs c d (f1 D1) (f2 D2) (λ z → g1 z D1) (λ z → g2 z D2) 
                  (f~ D1 D2 D~) (λ D E z → g~ D E z D1 D2 D~)

DComp-n-1 : ∀ {ℓ}{A : Set ℓ} bs c d → DFun A bs c → DFun A (c ∷ []) d → DFun A bs d
DComp-n-1 [] c d f g = g f
DComp-n-1 (b ∷ bs) c d f g D = DComp-n-1 bs c d (f D) g

DComp-n-1-pres : ∀ {ℓ}{A : Set ℓ} R bs c d
  → (f1 f2 : DFun A bs c)
  → (g1 g2 : DFun A (c ∷ []) d)
  → fun-rel-pres R bs c f1 f2
  → fun-rel-pres R (c ∷ []) d g1 g2
  → fun-rel-pres R bs d (DComp-n-1 bs c d f1 g1) (DComp-n-1 bs c d f2 g2)
DComp-n-1-pres R [] c d f1 f2 g1 g2 f~ g~ = g~ f1 f2 f~
DComp-n-1-pres R (x ∷ bs) c d f1 f2 g1 g2 f~ g~ D E D~ = 
  DComp-n-1-pres R bs c d (f1 D) (f2 E) g1 g2 (f~ D E D~) g~

Dmap : ∀ {ℓ}{A : Set ℓ} {b}{c}{d}{n} → DFun A (b ∷ []) c 
     → DFun A (replicate n c) d →  DFun A (replicate n b) d
Dmap {n = zero} f F = F
Dmap {n = suc n} f F D = Dmap {n = n} f (F (f D))



-}



