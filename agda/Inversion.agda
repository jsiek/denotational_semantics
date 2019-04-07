module Inversion where

open import Lambda
open import ValueBCD
open import Sem
open import Rename

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit

{-

  Inversion (aka Generation) Lemmas

-}

Λ℘ : ∀{B}{P} → (f : base-rep B → rep P) → Value → Set
Λ℘ f ⊥ = ⊤
Λ℘ f (lit x) = Bot
Λ℘{B}{P} f (v₁ ↦ v₂) = ∀{k : base-rep B} → v₁ ⊑ lit {B} k → ℘ {P} (f k) v₂
Λ℘{B}{P} f (v₁ ⊔ v₂) = (Λ℘{B}{P} f v₁) × (Λ℘{B}{P} f v₂)

Λ℘-⊑ : ∀{B}{P}{f : base-rep B → rep P}{v v' : Value}
     → Λ℘{B}{P} f v → v' ⊑ v → Λ℘{B}{P} f v'
Λ℘-⊑ d Bot⊑ = tt
Λ℘-⊑ d Lit⊑ = d
Λ℘-⊑{B}{P}{f} d (Fun⊑ lt1 lt2) {k} lt3 =
   let pfk = d {k} (Trans⊑ lt1 lt3) in
   ℘-⊑ pfk lt2
Λ℘-⊑ ⟨ d1 , d2 ⟩ (Dist⊑{v₁}{v₂}{v₃}) lt =
   ℘-⊔ (d1 lt) (d2 lt)
Λ℘-⊑ d (ConjL⊑ lt lt₁) = ⟨ Λ℘-⊑ d lt , Λ℘-⊑ d lt₁ ⟩
Λ℘-⊑ d (ConjR1⊑ lt) = Λ℘-⊑ (proj₁ d) lt
Λ℘-⊑ d (ConjR2⊑ lt) = Λ℘-⊑ (proj₂ d) lt
Λ℘-⊑ d (Trans⊑ lt lt₁) = Λ℘-⊑ (Λ℘-⊑ d lt₁) lt


{-

  The inequality v ⊑ v₁ ↦ v₂ says that everything in v is a function
  that jives with v₁ ↦ v₂. 

  The following is a more direct characterization of everything in v
  is a function that jives with v₁ ↦ v₂. It is syntax directed on v
  and does not have a transitivity clause.

-}

data AllFuns : Value → Value → Value → Set where
  af-fun : ∀{v₁ v₂ v₃ v₄ : Value}
         → v₁ ⊑ v₃ → v₄ ⊑ v₂
         → AllFuns (v₃ ↦ v₄) v₁ v₂ 
  af-⊔ : ∀{v₁ v₂ v₃ v₄ : Value}
       → AllFuns v₃ v₁ v₂  → AllFuns v₄ v₁ v₂
       → AllFuns (v₃ ⊔ v₄) v₁ v₂ 
  af-⊥ : ∀{v₁ v₂ : Value} → AllFuns ⊥ v₁ v₂ 

{-

  The AllFuns property is preserved going down.

-}

AllFuns-⊑ : ∀{v v' v₁ v₂ : Value}
      → AllFuns v v₁ v₂ → v' ⊑ v
      → AllFuns v' v₁ v₂
AllFuns-⊑ af Bot⊑ = af-⊥
AllFuns-⊑ af Lit⊑ = af
AllFuns-⊑ (af-fun x x₁) (Fun⊑ lt lt₁) = af-fun (Trans⊑ x lt) (Trans⊑ lt₁ x₁)
AllFuns-⊑ (af-⊔ (af-fun x x₁) (af-fun x₂ x₃)) Dist⊑ = af-fun x₂ (ConjL⊑ x₁ x₃)
AllFuns-⊑ af (ConjL⊑ lt lt₁) = af-⊔ (AllFuns-⊑ af lt) (AllFuns-⊑ af lt₁)
AllFuns-⊑ (af-⊔ af af₁) (ConjR1⊑ lt) = AllFuns-⊑ af lt
AllFuns-⊑ (af-⊔ af af₁) (ConjR2⊑ lt) = AllFuns-⊑ af₁ lt
AllFuns-⊑ af (Trans⊑ lt lt₁) = AllFuns-⊑ (AllFuns-⊑ af lt₁) lt

{-

  AllFuns v v₁ v₂ is equivalent to v ⊑ v₁ ↦ v₂.

-}

⊑↦→AllFuns : ∀{v v₁ v₂ : Value} → v ⊑ v₁ ↦ v₂ → AllFuns v v₁ v₂
⊑↦→AllFuns Bot⊑ = af-⊥
⊑↦→AllFuns (Fun⊑ lt lt₁) = af-fun lt lt₁
⊑↦→AllFuns (ConjL⊑ lt lt₁) = af-⊔ (⊑↦→AllFuns lt) (⊑↦→AllFuns lt₁)
⊑↦→AllFuns (Trans⊑ lt lt₁) = AllFuns-⊑ (⊑↦→AllFuns lt₁) lt

AllFuns→⊑↦ : ∀{v v₁ v₂ : Value} → AllFuns v v₁ v₂ → v ⊑ v₁ ↦ v₂
AllFuns→⊑↦ (af-fun x x₁) = Fun⊑ x x₁
AllFuns→⊑↦ (af-⊔ af af₁) = ConjL⊑ (AllFuns→⊑↦ af) (AllFuns→⊑↦ af₁)
AllFuns→⊑↦ af-⊥ = Bot⊑


{-

  The inequality v₁ ↦ v₂ ⊑ v says that something in v is a function
  whose domain is contained in v₁. It's difficult to say much 
  about the codomain and v₂ becaues of the Dist⊑ rule.

  (The most complete statement would be something like
   there are a collection of arrows inside v that together
   jive with v₁ ↦ v₂.)

-}

data SomeFun : Value → Value → Value → Set where
  sfv-fun : ∀{v₁ v₂ v₃ v₄ : Value}
         → v₃ ⊑ v₁
         → SomeFun v₁ v₂ (v₃ ↦ v₄) 
  sfv-⊔L : ∀{v₁ v₂ v₃ v₄ : Value}
       → SomeFun v₁ v₂ v₃
       → SomeFun v₁ v₂ (v₃ ⊔ v₄)
  sfv-⊔R : ∀{v₁ v₂ v₃ v₄ : Value}
       → SomeFun v₁ v₂ v₄
       → SomeFun v₁ v₂ (v₃ ⊔ v₄)

{-

  The SomeFun property is preserved going up.
  This makes it useful for inversion lemmas.

-}

SomeFun-⊑ : ∀{v v' v₁ v₂ : Value}
      → SomeFun v₁ v₂ v → v ⊑ v'
      → SomeFun v₁ v₂ v'
SomeFun-⊑ () Bot⊑
SomeFun-⊑ () Lit⊑
SomeFun-⊑ (sfv-fun x) (Fun⊑ lt lt₁) = sfv-fun (Trans⊑ lt x)
SomeFun-⊑ (sfv-fun x) Dist⊑ = sfv-⊔L (sfv-fun x)
SomeFun-⊑ (sfv-⊔L d) (ConjL⊑ lt lt₁) = SomeFun-⊑ d lt
SomeFun-⊑ (sfv-⊔R d) (ConjL⊑ lt lt₁) = SomeFun-⊑ d lt₁
SomeFun-⊑ d (ConjR1⊑ lt) = sfv-⊔L (SomeFun-⊑ d lt)
SomeFun-⊑ d (ConjR2⊑ lt) = sfv-⊔R (SomeFun-⊑ d lt)
SomeFun-⊑ d (Trans⊑ lt lt₁) = SomeFun-⊑ (SomeFun-⊑ d lt) lt₁


↦⊑→SomeFun : ∀{v₁ v₂ v : Value} → v₁ ↦ v₂ ⊑ v → SomeFun v₁ v₂ v
↦⊑→SomeFun (Fun⊑ lt lt₁) = sfv-fun lt
↦⊑→SomeFun Dist⊑ = sfv-⊔L (sfv-fun Refl⊑)
↦⊑→SomeFun (ConjR1⊑ lt) = sfv-⊔L (↦⊑→SomeFun lt)
↦⊑→SomeFun (ConjR2⊑ lt) = sfv-⊔R (↦⊑→SomeFun lt)
↦⊑→SomeFun (Trans⊑ lt lt₁) = SomeFun-⊑ (↦⊑→SomeFun lt) lt₁

{-

The other direction doesn't hold. That is,
SomeFun v₁ v₂ v does not imply v₁ ↦ v₂ ⊑ v.

-}

lit⊑↦→Bot : ∀{B : Base} {k : base-rep B}{ v₁ v₂ : Value}
          → lit k ⊑ v₁ ↦ v₂
          → Bot
lit⊑↦→Bot lt
    with AllFuns-⊑ (af-fun Refl⊑ Refl⊑) lt
... | ()

{-

  The inequality v ⊑ lit k says that everything in v is lit k.

-}

data AllLit : {B : Base} → base-rep B → Value → Set where
  al-lit : ∀{B : Base}{k : base-rep B}
         → AllLit k (lit k)
  al-⊔ : ∀{v₁ v₂}{B : Base}{k : base-rep B}
       → AllLit k v₁ → AllLit k v₂
       → AllLit k (v₁ ⊔ v₂)
  al-⊥ : ∀{B}{k : base-rep B} → AllLit k ⊥

{-

   The AllLit property is preserved going down.

-}

AllLit-⊑ : ∀{v v' : Value}{B}{k : base-rep B}
      → AllLit k v → v' ⊑ v
      → AllLit k v'
AllLit-⊑ al Bot⊑ = al-⊥
AllLit-⊑ al Lit⊑ = al
AllLit-⊑ () (Fun⊑ lt lt₁)
AllLit-⊑ (al-⊔ () al₁) Dist⊑
AllLit-⊑ al (ConjL⊑ lt lt₁) = al-⊔ (AllLit-⊑ al lt) (AllLit-⊑ al lt₁)
AllLit-⊑ (al-⊔ al al₁) (ConjR1⊑ lt) = AllLit-⊑ al lt
AllLit-⊑ (al-⊔ al al₁) (ConjR2⊑ lt) = AllLit-⊑ al₁ lt
AllLit-⊑ al (Trans⊑ lt lt₁) = AllLit-⊑ (AllLit-⊑ al lt₁) lt


⊑lit→AllLit : ∀{v}{B}{k : base-rep B} → v ⊑ lit k → AllLit k v
⊑lit→AllLit Bot⊑ = al-⊥
⊑lit→AllLit Lit⊑ = al-lit
⊑lit→AllLit (ConjL⊑ lt lt₁) = al-⊔ (⊑lit→AllLit lt) (⊑lit→AllLit lt₁)
⊑lit→AllLit (Trans⊑ lt lt₁) = AllLit-⊑ (⊑lit→AllLit lt₁) lt

AllLit→⊑lit : ∀{v}{B}{k : base-rep B} → AllLit k v → v ⊑ lit k
AllLit→⊑lit al-lit = Lit⊑
AllLit→⊑lit (al-⊔ al al₁) = ConjL⊑ (AllLit→⊑lit al) (AllLit→⊑lit al₁)
AllLit→⊑lit al-⊥ = Bot⊑


{-

  The inequality lit k ⊑ v says that something in v is lit k.

-}

data SomeLit : {B : Base} → base-rep B → Value → Set where
  slv-lit : ∀{B : Base}{k : base-rep B}
         → SomeLit k (lit k)
  slv-⊔L : ∀{v₁ v₂}{B : Base}{k : base-rep B}
       → SomeLit k v₁
       → SomeLit k (v₁ ⊔ v₂)
  slv-⊔R : ∀{v₁ v₂}{B : Base}{k : base-rep B}
       → SomeLit k v₂
       → SomeLit k (v₁ ⊔ v₂)

SomeLit-⊑ : ∀{v v' : Value}{B}{k : base-rep B}
      → SomeLit k v → v ⊑ v'
      → SomeLit k v'
SomeLit-⊑ (slv-lit) Lit⊑ = slv-lit 
SomeLit-⊑ (slv-⊔L d) (ConjL⊑ lt lt₁) = SomeLit-⊑ d lt
SomeLit-⊑ (slv-⊔R d) (ConjL⊑ lt lt₁) = SomeLit-⊑ d lt₁
SomeLit-⊑ d (ConjR1⊑ lt) = slv-⊔L (SomeLit-⊑ d lt)
SomeLit-⊑ d (ConjR2⊑ lt) = slv-⊔R (SomeLit-⊑ d lt)
SomeLit-⊑ d (Trans⊑ lt lt₁) = SomeLit-⊑ (SomeLit-⊑ d lt) lt₁

litk⊑→SomeLit : ∀{B}{k : base-rep B}{v : Value}
              → lit k ⊑ v → SomeLit k v
litk⊑→SomeLit Lit⊑ = slv-lit
litk⊑→SomeLit (ConjR1⊑ lt) = slv-⊔L (litk⊑→SomeLit lt)
litk⊑→SomeLit (ConjR2⊑ lt) = slv-⊔R (litk⊑→SomeLit lt)
litk⊑→SomeLit (Trans⊑ lt lt₁) = SomeLit-⊑ (litk⊑→SomeLit lt) lt₁

SomeLit→litk⊑ : ∀{B}{k : base-rep B}{v : Value}
              → SomeLit k v → lit k ⊑ v
SomeLit→litk⊑ slv-lit = Lit⊑
SomeLit→litk⊑ (slv-⊔L sl) = ConjR1⊑ (SomeLit→litk⊑ sl)
SomeLit→litk⊑ (slv-⊔R sl) = ConjR2⊑ (SomeLit→litk⊑ sl)


base-inv : ∀ {v}{B : Base}{k : base-rep B}
  → ℘ k v
    -------------------
  → AllLit k v
base-inv {B = Nat} (℘-base {.Nat}) = al-lit
base-inv {B = 𝔹} (℘-base {.𝔹}) = al-lit
base-inv (℘-⊔ pk pk₁) = al-⊔ (base-inv pk) (base-inv pk₁)
base-inv ℘-⊥ = al-⊥
base-inv (℘-⊑ pk lt) = AllLit-⊑ (base-inv pk) lt

prim-fun-inv : ∀{B}{P}{f : base-rep B → rep P}{v}
              → ℘ {B ⇒ P} f v
              → Λ℘{B}{P} f v
prim-fun-inv (℘-fun{f = f}{k = k} pfv lt1 lt2) {k'} lt3
    with ⊑lit→AllLit (Trans⊑ lt1 lt3)
... | al-lit = ℘-⊑ pfv lt2
prim-fun-inv (℘-⊔ pfv pfv₁) = ⟨ prim-fun-inv pfv , prim-fun-inv pfv₁ ⟩
prim-fun-inv ℘-⊥ = tt
prim-fun-inv (℘-⊑ pfv lt) = Λ℘-⊑ (prim-fun-inv pfv) lt

{-
prim-fun-inv2 : ∀{B}{P}{f : base-rep B → rep P}{v v₁ v₂}
              → ℘ {B ⇒ P} f v → SomeFun v₁ v₂ v 
              → v ⊑ ⊥ ⊎ Σ[ k ∈ base-rep B ] ℘ {P} (f k) v₂
prim-fun-inv2{f = f} p sf = {!!}
prim-fun-inv2{f = f} (℘-fun{k = k} pf) (sfv-fun lt1 lt2) =
  inj₂ ⟨ k , ℘-⊑ pf lt2 ⟩
prim-fun-inv2 (℘-⊔ pf pf₁) sf = {!!}
prim-fun-inv2 ℘-⊥ sf = inj₁ Bot⊑
prim-fun-inv2{f = f} (℘-⊑ pf lt) sf 
    with prim-fun-inv2{f = f} pf (SomeFun-⊑ sf lt)  
... | inj₁ lt2 =  inj₁ (Trans⊑ lt lt2)
... | inj₂ pfv2 = inj₂ pfv2
-}


℘k-litk : ∀{B}{k : base-rep B} → ℘ k (lit k)
℘k-litk {Nat} {k} = ℘-base
℘k-litk {𝔹} {k} = ℘-base

{-
prim-app-inv : ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v : Value}
             → ℘ {P} (f k) v
             → v ⊑ ⊥ ⊎ Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ]
               ℘ {B ⇒ P} f (v₁ ↦ v₂) × ℘ {` B} k v₃ × v₁ ⊑ v₃ × v ⊑ v₂
prim-app-inv{B}{P}{f}{k} (℘-base{B = B'}) =
  inj₂ ⟨ lit k , ⟨ lit (f k) , ⟨ lit k , ⟨ ℘-fun ℘-base ? ? , ⟨ ℘k-litk ,
            ⟨ Refl⊑ , Refl⊑ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
prim-app-inv {B}{B' ⇒ P}{f}{k} (℘-fun{k = k'}{v = v} pfk ? ?) =
  inj₂ ⟨ lit k , ⟨ lit k' ↦ v , ⟨ lit k , ⟨ ℘-fun (℘-fun pfk) , ⟨ ℘k-litk , ⟨ Refl⊑ , Refl⊑ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
prim-app-inv {B}{P}{f}{k} (℘-⊔ pfk pfk₁)
    with prim-app-inv{f = f}{k = k} pfk | prim-app-inv{f = f}{k = k} pfk₁
... | inj₁ lt1 | inj₁ lt2 = inj₁ (ConjL⊑ lt1 lt2)
... | inj₁ lt1 | inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt2 , lt3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 ,
                  ⟨ lt2 , (ConjL⊑ (Trans⊑ lt1 Bot⊑) lt3) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | inj₂  ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt3 , lt4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ | inj₁ lt2 =
      inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 ,
                  ⟨ lt3 , (ConjL⊑ lt4 (Trans⊑ lt2 Bot⊑)) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt3 , lt4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ v₃' , ⟨ d1' , ⟨ d2' , ⟨ lt3' , lt4' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      inj₂ ⟨ (v₁ ⊔ v₁') , ⟨ (v₂ ⊔ v₂') , ⟨ (v₃ ⊔ v₃') ,
            ⟨ (℘-⊑ (℘-⊔ d1 d1') Dist⊔↦⊔) ,
            ⟨ ((℘-⊔ d2 d2')) , ⟨ (ConjL⊑ (ConjR1⊑ lt3) (ConjR2⊑ lt3')) ,
            Conj⊑Conj lt4 lt4' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
prim-app-inv {B} {P} ℘-⊥ = inj₁ Bot⊑
prim-app-inv {B}{P}{f}{k} (℘-⊑ pfk lt)
    with prim-app-inv{B}{P}{f}{k} pfk
... | inj₁ lt' = inj₁ (Trans⊑ lt lt')
... | inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt1 , (Trans⊑ lt lt2) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ 
-}

{-

prim-fun-inv2 : ∀{B : Base}{P : Prim}{f : base-rep B → rep P}{v₁ v₂}
              → ℘ {B ⇒ P} f (v₁ ↦ v₂)
              → Σ[ k ∈ base-rep B ] lit k ⊑ v₁
prim-fun-inv2 (℘-fun{k = k} p) = ⟨ k , Lit⊑ ⟩
prim-fun-inv2 (℘-⊑ p (Fun⊑ lt lt₁))
    with prim-fun-inv2 p 
... | ⟨ k , lt2 ⟩ = ⟨ k , Trans⊑ lt2 lt ⟩
prim-fun-inv2 (℘-⊑ p Dist⊑) = {!!}
prim-fun-inv2 (℘-⊑ p (ConjR1⊑ lt)) = {!!}
prim-fun-inv2 (℘-⊑ p (ConjR2⊑ lt)) = {!!}
prim-fun-inv2 (℘-⊑ p (Trans⊑ lt lt₁)) = {!!}
-}
{-
prim-app-inv : ∀{B : Base}{P : Prim}{P' : Prim}{f : rep P}{k : rep P'}{v₁ v₂}
             → ℘ {P} f (v₁ ↦ v₂) → ℘ {P'} k v₁
               --------------------------------
             → Σ[ B ∈ Base ] Σ[ P'' ∈ Prim ] Σ[ k' ∈ rep P'' ]
               P ≡ B ⇒ P'' × P' ≡ ` B × f k ≡ k' ×
               ℘ {P''} k' v₂
prim-app-inv pf pk = {!!}
-}

app-inv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}{v : Value}
        → ℰ (M · N) γ v
        → Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ]
          ℰ M γ (v₁ ↦ v₂) × ℰ N γ v₃ × v₁ ⊑ v₃ × v ⊑ v₂
app-inv (ℰ-app{v₁ = v₁}{v₂ = v₂} d₁ d₂ lt) =
   ⟨ v₁ , ⟨ v₂ , ⟨ v₁ , ⟨ d₁ , ⟨ d₂ , ⟨ Refl⊑ , lt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
app-inv {Γ}{γ}{M}{N}{v} (ℰ-⊔ d₁ d₂)
    with app-inv d₁ | app-inv d₂
... | ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ v₁' , ⟨ v₂' , ⟨ v₃' , ⟨ M↓v12' , ⟨ N↓v3' , ⟨ v13' , vv2' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      let M↓⊔ = ℰ-⊔ M↓v12 M↓v12' in
      let N↓⊔ = ℰ-⊔ N↓v3 N↓v3' in
      ⟨ v₁ ⊔ v₁' , ⟨ v₂ ⊔ v₂' , ⟨ v₃ ⊔ v₃' ,
        ⟨ ℰ-⊑ M↓⊔ Dist⊔↦⊔ , ⟨ N↓⊔ , ⟨ H , I ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      where
      H = Conj⊑Conj v13 v13'
      I = Conj⊑Conj vv2 vv2'
app-inv {Γ}{γ}{M}{N}{v} (ℰ-⊑ d lt)
    with app-inv d
... | ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , Trans⊑ lt vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

infixl 7 _●_

_●_ : ∀{Γ} → Sem Γ → Sem Γ → Sem Γ
(F ● E) γ v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ] F γ (v₁ ↦ v₂) × E γ v₃ × v₁ ⊑ v₃ × v ⊑ v₂


Λ : ∀{Γ} → Sem (Γ , ★) → Sem Γ
Λ S' γ ⊥ = ⊤
Λ S' γ (lit x) = Bot
Λ S' γ (v₁ ↦ v₂) = S' (γ , v₁) v₂
Λ S' γ (v₁ ⊔ v₂) = (Λ S' γ v₁) × (Λ S' γ v₂)

sub-Λ : ∀{Γ}{M : Γ , ★ ⊢ ★}{γ v v'} → (Λ (ℰ M)) γ v → v' ⊑ v → (Λ (ℰ M)) γ v'
sub-Λ d Bot⊑ = tt
sub-Λ d Lit⊑ = d
sub-Λ d (Fun⊑ lt lt') = ℰ-⊑ (up-env d lt) lt'
sub-Λ d (ConjL⊑ lt lt₁) = ⟨ sub-Λ d lt , sub-Λ d lt₁ ⟩
sub-Λ d (ConjR1⊑ lt) = sub-Λ (proj₁ d) lt
sub-Λ d (ConjR2⊑ lt) = sub-Λ (proj₂ d) lt
sub-Λ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ M2 , M3 ⟩ Dist⊑ =
   ℰ-⊔ M2 M3
sub-Λ d (Trans⊑ x₁ x₂) = sub-Λ (sub-Λ d x₂) x₁


lam-inv : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → ℰ (ƛ M) γ v → Λ (ℰ M) γ v
lam-inv (ℰ-lam d) = d
lam-inv ℰ-⊥ = tt
lam-inv (ℰ-⊔ d₁ d₂) = ⟨ lam-inv d₁ , lam-inv d₂ ⟩
lam-inv {Γ}{γ}{M}{v = v₂} (ℰ-⊑{v₁ = v₁}{v₂ = v₂} d lt) = sub-Λ (lam-inv d) lt

inv-lam : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → Λ (ℰ M) γ v
        → ℰ (ƛ M) γ v
inv-lam {v = ⊥} d = ℰ-⊥
inv-lam {v = lit x} ()
inv-lam {v = v₁ ↦ v₂} d = ℰ-lam d
inv-lam {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ =
    let ih1 = inv-lam{v = v₁} d1 in
    let ih2 = inv-lam{v = v₂} d2 in
    ℰ-⊔ (inv-lam d1) (inv-lam d2)

lam-inv2 : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → Λ (ℰ M) γ v
        → (v ⊑ ⊥)
          ⊎ (Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] ℰ M (γ , v₁) v₂ × v₁ ↦ v₂ ⊑ v)
lam-inv2 {v = ⊥} d = inj₁ Bot⊑
lam-inv2 {v = lit x} ()
lam-inv2 {v = v₁ ↦ v₂} d = inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ d , Refl⊑ ⟩ ⟩ ⟩
lam-inv2 {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩
    with lam-inv2{v = v₁} d1 | lam-inv2{v = v₂} d2
... | inj₁ d1' | inj₁ d2' = inj₁ (ConjL⊑ d1' d2')
... | inj₁ lt1 | inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , lt2 ⟩ ⟩ ⟩ =
      inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , ConjR2⊑ lt2 ⟩ ⟩ ⟩
... | inj₂  ⟨ v₁' , ⟨ v₂' , ⟨ d' , lt2 ⟩ ⟩ ⟩ | _ =
      inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , ConjR1⊑ lt2 ⟩ ⟩ ⟩


{-

  Equational and compositional presentation of the semantics

-}

var-equiv : ∀{Γ}{γ : Env Γ}{x : Γ ∋ ★}
          → ℰ (` x) ≃ (λ γ v → v ⊑ nth x γ)
var-equiv = ⟨ var-inv , (λ lt → ℰ-var lt) ⟩

lit-equiv : ∀{Γ}{γ : Env Γ}{P : Prim}{p : rep P}
          → ℰ ($_ {Γ} {P} p) ≃ λ γ v → ℘ {P} p v
lit-equiv = ⟨ prim-inv , ℰ-lit ⟩

app-equiv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}
          → ℰ (M · N) ≃ (ℰ M) ● (ℰ N)
app-equiv{Γ}{γ}{M}{N} = ⟨ app-inv , G ⟩
   where G : ∀{γ v} → (ℰ M ● ℰ N) γ v → ℰ (M · N) γ v
         G {γ}{v} ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
           ℰ-app d1 (ℰ-⊑ d2 lt1) lt2

lam-equiv : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}
          → ℰ (ƛ M) ≃ Λ (ℰ M)
lam-equiv {Γ}{γ}{M}{v} = ⟨ lam-inv , inv-lam ⟩


