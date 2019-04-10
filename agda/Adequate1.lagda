\begin{code}
module Adequate1 where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.List using (List; _∷_; _++_; concat; map) renaming ([] to nil)
open import Data.List.NonEmpty using (List⁺; _∷_; _⁺++⁺_; toList) 
open import Data.Nat using (ℕ; suc; zero; _≤_)
open import Relation.Nullary using (Dec; yes; no)

open import Untyped
open import Denot_CBN_BCD
\end{code}

## Adequacy of the denotational semantics


\begin{code}
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where

  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)
\end{code}

\begin{code}
data Clos : Set

data ClosEnv : Context → Set where
  ∅ : ClosEnv ∅
  _,_ : ∀{Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
  
data Clos where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

kth : ∀{Γ} → (Γ ∋ ★) → ClosEnv Γ → Clos
kth () ∅
kth Z (ρ , v) = v
kth (S x) (ρ , v) = kth x ρ

data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{c}
        → kth x γ ≡ clos M δ
        → δ ⊢ M ⇓ c
          -----------
        → γ ⊢ ` x ⇓ c

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
        → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{L' : Δ , ★ ⊢ ★}{c}
       → γ ⊢ L ⇓ clos (ƛ L') δ   →   (δ , clos M γ) ⊢ L' ⇓ c
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ c

⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{c c' : Clos}
         → γ ⊢ M ⇓ c → γ ⊢ M ⇓ c'
         → c ≡ c'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''

AboveFun : Value → Set
AboveFun v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ↦ v₂ ⊑ v

AboveFun-⊑ : ∀{v v' : Value}
      → AboveFun v → v ⊑ v'
      → AboveFun v'
AboveFun-⊑ ⟨ v₁ , ⟨ v₂ , lt' ⟩ ⟩ lt = ⟨ v₁ , ⟨ v₂ , Trans⊑ lt' lt ⟩ ⟩


not-AboveFun-⊔-invL : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁
not-AboveFun-⊔-invL{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
  contradiction ⟨ v , ⟨ v' , ConjR1⊑ lt ⟩ ⟩ af12
  

not-AboveFun-⊔-invR : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₂
not-AboveFun-⊔-invR{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
  contradiction ⟨ v , ⟨ v' , ConjR2⊑ lt ⟩ ⟩ af12
  

not-AboveFun-⊔-inv : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁ × ¬ AboveFun v₂
not-AboveFun-⊔-inv af = ⟨ (not-AboveFun-⊔-invL af) , (not-AboveFun-⊔-invR af) ⟩


data Fun : Value → Set where
  fun : ∀{v₁ v v'} → v₁ ≡ (v ↦ v') → Fun v₁




atoms : Value → List Value
atoms (v ↦ v') = (v ↦ v') ∷ nil
atoms (v₁ ⊔ v₂) = atoms v₁ ++ atoms v₂
atoms ⊥ = nil

dom : (v : Value) → Fun v → Value
dom ⊥ (fun ())
dom (v ↦ v') (fun eq) = v
dom (v ⊔ v') (fun ())

cod : (v : Value) → Fun v → Value
cod ⊥ (fun ())
cod (v ↦ v') (fun eq) = v'
cod (v ⊔ v') (fun ())


infix 5 _∈_

_∈_ : Value → List Value → Set
v ∈ nil = Bot
v ∈ (v' ∷ vs) = v ≡ v' ⊎ v ∈ vs


_∈⁺_ : Value → List⁺ Value → Set
v ∈⁺ (v' ∷ vs) = v ≡ v' ⊎ v ∈ vs

↦≡↦-inv : ∀{v v' u u' : Value}
        → _≡_ {a = lzero}{A = Value} (v ↦ v') (u ↦ u') → v ≡ u × v' ≡ u'
↦≡↦-inv refl = ⟨ refl , refl ⟩

⊔≡⊔-inv : ∀{v v' u u' : Value}
        → _≡_ {a = lzero}{A = Value} (v ⊔ v') (u ⊔ u') → v ≡ u × v' ≡ u'
⊔≡⊔-inv refl = ⟨ refl , refl ⟩

val≡? : (v : Value) → (v' : Value) → Dec (v ≡ v')
val≡? ⊥ ⊥ = yes refl
val≡? ⊥ (v' ↦ v'') = no (λ ())
val≡? ⊥ (v' ⊔ v'') = no (λ ())
val≡? (v ↦ v₁) ⊥ = no (λ ())
val≡? (v ↦ v₁) (v' ↦ v'')
    with val≡? v v' | val≡? v₁ v''
... | yes a | yes b rewrite a | b = yes refl
... | yes a | no b = no λ x → b (proj₂ (↦≡↦-inv x))
... | no a | _ = no λ x → a (proj₁ (↦≡↦-inv x))
val≡? (v ↦ v₁) (v' ⊔ v'') = no (λ ())
val≡? (v ⊔ v₁) ⊥ = no (λ ())
val≡? (v ⊔ v₁) (v' ↦ v'') = no (λ ())
val≡? (v ⊔ v₁) (v' ⊔ v'')
    with val≡? v v' | val≡? v₁ v''
... | yes a | yes b rewrite a | b = yes refl
... | yes a | no b = no λ x → b (proj₂ (⊔≡⊔-inv x))
... | no a | _ = no λ x → a (proj₁ (⊔≡⊔-inv x))

∈++ : ∀{ls1 ls2 v} → v ∈ (ls1 ++ ls2) → v ∈ ls1 ⊎ v ∈ ls2
∈++ {nil} m = inj₂ m
∈++ {x ∷ ls1} (inj₁ refl) = inj₁ (inj₁ refl)
∈++ {x ∷ ls1} (inj₂ y)
    with ∈++ {ls1} y
... | inj₁ a = inj₁ (inj₂ a)
... | inj₂ b = inj₂ b

∈++⁺ : ∀{ls1 ls2 v} → v ∈⁺ (ls1 ⁺++⁺ ls2) → v ∈⁺ ls1 ⊎ v ∈⁺ ls2
∈++⁺ {x ∷ ls1} (inj₁ refl) = inj₁ (inj₁ refl)
∈++⁺ {x ∷ ls1} (inj₂ y)
    with ∈++ {ls1} y
... | inj₁ a = inj₁ (inj₂ a)
... | inj₂ b = inj₂ b

∈++-tail⁺ : ∀{ls1 ls2 : List⁺ Value}{v}
          → v ∈ List⁺.tail (ls1 ⁺++⁺ ls2)
          → v ∈ List⁺.tail ls1 ⊎ v ∈⁺ ls2
∈++-tail⁺ {head ∷ tail} {head₁ ∷ tail₁} {v} m
    with ∈++{ls1 = tail}{ls2 = head₁ ∷ tail₁} m
... | inj₁ x = inj₁ x
... | inj₂ (inj₁ y) = inj₂ (inj₁ y)
... | inj₂ (inj₂ y) = inj₂ (inj₂ y)

∈++-L : ∀{ls1 ls2 x} →  x ∈ ls1  →  x ∈ (ls1 ++ ls2)
∈++-L {nil} ()
∈++-L {x ∷ ls1} (inj₁ refl) = inj₁ refl
∈++-L {x ∷ ls1} (inj₂ y) = inj₂ (∈++-L y)

∈++-R : ∀{ls1 ls2 x} →  x ∈ ls2  →  x ∈ (ls1 ++ ls2)
∈++-R {nil} m = m
∈++-R {x ∷ ls1} m = inj₂ (∈++-R m)

∈++-L⁺ : ∀{ls1 ls2 x} →  x ∈⁺ ls1  →  x ∈⁺ (ls1 ⁺++⁺ ls2)
∈++-L⁺ {x ∷ ls1} (inj₁ refl) = inj₁ refl
∈++-L⁺ {x ∷ ls1} (inj₂ y) = inj₂ (∈++-L y)

∈++-R⁺ : ∀{ls1 ls2 x} →  x ∈⁺ ls2  →  x ∈⁺ (ls1 ⁺++⁺ ls2)
∈++-R⁺ {x ∷ ls1} m = inj₂ (∈++-R m)


Funs : List Value → Set
Funs vs = (∀{v} → v ∈ vs → Fun v)

doms : (vs : List Value) → Funs vs → List Value
doms nil af = nil
doms (v ∷ vs) af = dom v (af (inj₁ refl)) ∷ doms vs λ {v₁} z → af (inj₂ z)

doms⁺ : (vs : List⁺ Value) → Funs (toList vs) → List⁺ Value
doms⁺ (v ∷ vs) af = dom v (af (inj₁ refl)) ∷ doms vs λ {v₁} z → af (inj₂ z)

cods : (vs : List Value) → Funs vs → List Value
cods nil af = nil
cods (v ∷ vs) af = cod v (af (inj₁ refl)) ∷ cods vs λ {v₁} z → af (inj₂ z)

cods⁺ : (vs : List⁺ Value) → Funs (toList vs) → List⁺ Value
cods⁺ (v ∷ vs) af = cod v (af (inj₁ refl)) ∷ cods vs λ {v₁} z → af (inj₂ z)

atomic-sub-R : ∀{A B C} →  A ⊑ B  →  C ∈ atoms A  →  C ⊑ B
atomic-sub-R Bot⊑ ()
atomic-sub-R{C = v₁'} (ConjL⊑{v₁ = v₁}{v₂ = v₂} lt lt₁) a
    with ∈++{ls1 = atoms v₁} a
... | inj₁ v₁'∈v₁ = atomic-sub-R lt v₁'∈v₁
... | inj₂ v₁'∈v₂ = atomic-sub-R lt₁ v₁'∈v₂
atomic-sub-R (ConjR1⊑ lt) a = ConjR1⊑ (atomic-sub-R lt a)
atomic-sub-R (ConjR2⊑ lt) a = ConjR2⊑ (atomic-sub-R lt a)
atomic-sub-R (Trans⊑ lt lt₁) a = Trans⊑ (atomic-sub-R lt a) lt₁
atomic-sub-R (Fun⊑ lt lt₁) (inj₁ refl) = Fun⊑ lt lt₁
atomic-sub-R (Fun⊑ lt lt₁) (inj₂ ())
atomic-sub-R Dist⊑ (inj₁ refl) = Dist⊑
atomic-sub-R Dist⊑ (inj₂ ())


atomic-sub-trans : ∀{A B C : Value} →  A ∈ atoms B  →  B ⊑ C  →  A ⊑ C
atomic-sub-trans () Bot⊑
atomic-sub-trans ab (ConjL⊑{v₁ = v₁}{v₂ = v₂} bc bc₁)
    with ∈++{ls1 = atoms v₁} ab
... | inj₁ ab' = atomic-sub-trans ab' bc
... | inj₂ ab' =  atomic-sub-trans ab' bc₁
atomic-sub-trans ab (ConjR1⊑ bc) = ConjR1⊑ (atomic-sub-trans ab bc)
atomic-sub-trans ab (ConjR2⊑ bc) = ConjR2⊑ (atomic-sub-trans ab bc)
atomic-sub-trans ab (Trans⊑ bc bc₁) = Trans⊑ (atomic-sub-trans ab bc) bc₁
atomic-sub-trans (inj₁ refl) (Fun⊑ bc bc₁) = Fun⊑ bc bc₁
atomic-sub-trans (inj₂ ()) (Fun⊑ bc bc₁)
atomic-sub-trans (inj₁ refl) Dist⊑ = Dist⊑
atomic-sub-trans (inj₂ ()) Dist⊑


atomic-fun-sub : ∀{B C D E : Value} →  B ⊑ C  →  (D ↦ E) ∈ atoms B
               → Σ[ A ∈ Value ] Σ[ A' ∈ Value ] (A ↦ A') ∈ atoms C
atomic-fun-sub Bot⊑ ()
atomic-fun-sub (ConjL⊑{v₁ = A}{v₂ = A'} bc bc₁) deb
    with ∈++{ls1 = atoms A} deb
... | inj₁ dea = atomic-fun-sub bc dea
... | inj₂ dea = atomic-fun-sub bc₁ dea
atomic-fun-sub (ConjR1⊑ bc) deb 
    with atomic-fun-sub bc deb
... | ⟨ D' , ⟨ E' , m' ⟩ ⟩ = ⟨ D' , ⟨ E' , ∈++-L m' ⟩ ⟩
atomic-fun-sub (ConjR2⊑ bc) deb
    with atomic-fun-sub bc deb
... | ⟨ D' , ⟨ E' , m' ⟩ ⟩ = ⟨ D' , ⟨ E' , ∈++-R m' ⟩ ⟩
atomic-fun-sub (Trans⊑ bc bc₁) deb
    with atomic-fun-sub bc deb
... | ⟨ D' , ⟨ E' , deb' ⟩ ⟩ = atomic-fun-sub bc₁ deb'
atomic-fun-sub (Fun⊑{v₃ = v₃}{v₄ = v₄} bc bc₁) (inj₁ refl) =
    ⟨ v₃ , ⟨ v₄ , inj₁ refl ⟩ ⟩
atomic-fun-sub (Fun⊑ bc bc₁) (inj₂ ())
atomic-fun-sub (Dist⊑{v₁ = v₁}{v₂ = v₂}) (inj₁ refl) =
   ⟨ v₁ , ⟨ v₂ , inj₁ refl ⟩ ⟩
atomic-fun-sub Dist⊑ (inj₂ ())


atomic-sub-funL : ∀{A B C} → A ↦ B ⊑ C
                → Σ[ D ∈ Value ] Σ[ E ∈ Value ] (D ↦ E) ∈ atoms C
atomic-sub-funL (ConjR1⊑ lt)
    with atomic-sub-funL lt
... | ⟨ D , ⟨ E , m ⟩ ⟩ = ⟨ D , ⟨ E , (∈++-L m) ⟩ ⟩
atomic-sub-funL (ConjR2⊑ lt)
    with atomic-sub-funL lt
... | ⟨ D , ⟨ E , m ⟩ ⟩ = ⟨ D , ⟨ E , (∈++-R m) ⟩ ⟩
atomic-sub-funL (Trans⊑ lt lt₁) 
    with atomic-sub-funL lt
... | ⟨ D , ⟨ E , m ⟩ ⟩ =
    atomic-fun-sub lt₁ m
atomic-sub-funL (Fun⊑{v₃ = v₃}{v₄ = v₄} lt lt₁) =
    ⟨ v₃ , ⟨ v₄ , inj₁ refl ⟩ ⟩
atomic-sub-funL{A} (Dist⊑ {v₂ = v₂}) =
    ⟨ A , ⟨ v₂ , inj₁ refl ⟩ ⟩

fun∈-sub : ∀{u v v' : Value}
         → v ↦ v' ∈ atoms u
         → v ↦ v' ⊑ u
fun∈-sub {⊥} ()
fun∈-sub {u ↦ u'} (inj₁ refl) = Refl⊑
fun∈-sub {u ↦ u'} (inj₂ ())
fun∈-sub {u₁ ⊔ u₂} m
    with ∈++{ls1 = atoms u₁} m
... | inj₁ x = ConjR1⊑ (fun∈-sub x)
... | inj₂ x = ConjR2⊑ (fun∈-sub x)

⨆-list : Value → List Value → Value
⨆-list v nil = v
⨆-list v₁ (v₂ ∷ vs) = v₁ ⊔ (⨆-list v₂ vs)

concat-nil : _≡_ {a = lzero}{A = List Value} (concat nil) nil
concat-nil = refl

++-nil : ∀{ls : List Value} → _≡_ {a = lzero}{A = List Value} (ls ++ nil) ls
++-nil {nil} = refl
++-nil {x ∷ ls} rewrite ++-nil {ls} = refl

atoms-fun-id : ∀{A : Value} → Fun A → atoms A ≡ (A ∷ nil)
atoms-fun-id {.(_ ↦ _)} (fun refl) = refl

atoms⨆-list-funs : ∀{L : List Value}{A : Value}
    → Fun A → Funs L
    → atoms (⨆-list A L) ≡ atoms A ++ L
atoms⨆-list-funs {nil} {A} fa fl rewrite ++-nil{atoms A} = refl
atoms⨆-list-funs {B ∷ L} {A} fa fl 
    rewrite atoms⨆-list-funs {L}{B} (fl (inj₁ refl)) (λ {v} z → fl (inj₂ z))
    | atoms-fun-id{B} (fl (inj₁ refl)) = refl

atoms⨆-list : ∀{L : List Value}{A : Value}
    → atoms (⨆-list A L) ≡ atoms A ++ concat (Data.List.map atoms L)
atoms⨆-list {nil}{A} rewrite concat-nil | ++-nil{atoms A} = refl
atoms⨆-list {x ∷ L} rewrite atoms⨆-list {L}{x} = refl

⨆ : List⁺ Value → Value
⨆ (v ∷ vs) = ⨆-list v vs

atoms⨆ : ∀{L : List⁺ Value}
       → atoms (⨆ L) ≡ concat (Data.List.map atoms (toList L))
atoms⨆ {A ∷ L} = atoms⨆-list {L}{A}

atoms⨆-funs : ∀{L : List⁺ Value}
       → Funs (toList L)
       → atoms (⨆ L) ≡ toList L
atoms⨆-funs {A ∷ L'} f
  with atoms⨆-list-funs{L'}{A} (f (inj₁ refl)) λ {v} z → f (inj₂ z)
... | eq rewrite atoms-fun-id{A} (f (inj₁ refl)) = eq


funs-atoms-sub : ∀{A B : Value}
   → Funs (atoms B)  →  A ⊑ B
     ------------------------
   → Funs (atoms A)
funs-atoms-sub f Bot⊑ ()
funs-atoms-sub f (ConjL⊑{v₁ = C}{v₂ = D} ab ab₁) m
    with ∈++{ls1 = atoms C} m
... | inj₁ x = funs-atoms-sub f ab x  
... | inj₂ x = funs-atoms-sub f ab₁ x  
funs-atoms-sub{A} f (ConjR1⊑{v₁ = C}{v₂ = D} ab) m =
   funs-atoms-sub (λ {v₁} x → f {v₁} (∈++-L x)) ab m
funs-atoms-sub f (ConjR2⊑{v₁ = C}{v₂ = D} ab) m =
   funs-atoms-sub (λ {v₁} x → f {v₁} (∈++-R x)) ab m
funs-atoms-sub f (Trans⊑ ab ab₁) m = funs-atoms-sub (funs-atoms-sub f ab₁) ab m
funs-atoms-sub f (Fun⊑ ab ab₁) (inj₁ refl) = fun refl
funs-atoms-sub f (Fun⊑ ab ab₁) (inj₂ ())
funs-atoms-sub f Dist⊑ (inj₁ refl) = fun refl
funs-atoms-sub f Dist⊑ (inj₂ ())


sub-fun-atoms : ∀{Γ : List⁺ Value}{A B : Value}
              → Funs (toList Γ) →  A ⊑ ⨆ Γ → Funs (atoms A)
sub-fun-atoms{Γ}{A}{B} fg lt = funs-atoms-sub y lt
  where x : atoms (⨆ Γ) ≡ toList Γ
        x = atoms⨆-funs{Γ} fg 
        y : Funs (atoms (⨆ Γ))
        y rewrite x = fg 

{-

  Theorem 14.1.7 of Barendregt et al. (2013)

-}

⊔⊑-inv : ∀{A B C : Value}
       → A ⊔ B ⊑ C
       → A ⊑ C
⊔⊑-inv (ConjL⊑ abc abc₁) = abc
⊔⊑-inv (ConjR1⊑ abc) = ConjR1⊑ (⊔⊑-inv abc)
⊔⊑-inv (ConjR2⊑ abc) = ConjR2⊑ (⊔⊑-inv abc)
⊔⊑-inv (Trans⊑ abc abc₁) = Trans⊑ (⊔⊑-inv abc) abc₁

⊔⊑-invR : ∀{A B C : Value}
       → A ⊔ B ⊑ C
       → B ⊑ C
⊔⊑-invR (ConjL⊑ lt lt₁) = lt₁
⊔⊑-invR (ConjR1⊑ lt) = ConjR1⊑ (⊔⊑-invR lt)
⊔⊑-invR (ConjR2⊑ lt) = ConjR2⊑ (⊔⊑-invR lt)
⊔⊑-invR (Trans⊑ lt lt₁) = Trans⊑ (⊔⊑-invR lt) lt₁

infix 3 _≈_
_≈_ : (A : Value) → (B : Value) → Set
A ≈ B = A ⊑ B × B ⊑ A

Refl≈ : ∀ {v} → v ≈ v
Refl≈ = ⟨ Refl⊑ , Refl⊑ ⟩

Trans≈ : ∀ {A B C} → A ≈ B → B ≈ C → A ≈ C
Trans≈ ⟨ ab , ba ⟩ ⟨ bc , cb ⟩ = ⟨ (Trans⊑ ab bc) , (Trans⊑ cb ba) ⟩

Assoc⊑ : ∀ {A B C} → (A ⊔ B) ⊔ C ⊑ A ⊔ (B ⊔ C)
Assoc⊑ = ConjL⊑ (⊔⊑⊔ Refl⊑ (ConjR1⊑ Refl⊑)) (ConjR2⊑ (ConjR2⊑ Refl⊑))

Assoc⊑L : ∀ {A B C} → A ⊔ (B ⊔ C) ⊑ (A ⊔ B) ⊔ C
Assoc⊑L = ConjL⊑ (ConjR1⊑ (ConjR1⊑ Refl⊑))
   (ConjL⊑ (ConjR1⊑ (ConjR2⊑ Refl⊑)) (ConjR2⊑ Refl⊑))

Assoc≈ : ∀ {A B C} → (A ⊔ B) ⊔ C ≈ A ⊔ (B ⊔ C)
Assoc≈ = ⟨ Assoc⊑ , Assoc⊑L ⟩

Assoc≈L : ∀ {A B C} → A ⊔ (B ⊔ C) ≈ (A ⊔ B) ⊔ C
Assoc≈L = ⟨ Assoc⊑L , Assoc⊑ ⟩

⊔≈⊔ : ∀ {v₁ v₂ v₃ v₄}
      → v₁ ≈ v₃  →  v₂ ≈ v₄
        -----------------------
      → (v₁ ⊔ v₂) ≈ (v₃ ⊔ v₄)
⊔≈⊔ d₁ d₂ = ⟨ ConjL⊑ (ConjR1⊑ (proj₁ d₁)) (ConjR2⊑ (proj₁ d₂)) ,
              ConjL⊑ (ConjR1⊑ (proj₂ d₁)) (ConjR2⊑ (proj₂ d₂)) ⟩


dom-fun : ∀{A fg fg'} → dom A fg ≡ dom A fg'
dom-fun {.(_ ↦ _)}{fun refl} {fun refl}  = refl

cod-fun : ∀{A fg fg'} → cod A fg ≡ cod A fg'
cod-fun {.(_ ↦ _)}{fun refl} {fun refl}  = refl

doms-fun : ∀{Γ}{fg fg' : Funs Γ} → (doms Γ fg) ≡ (doms Γ fg')
doms-fun {nil} {fg} {fg'} = refl
doms-fun {A ∷ Γ} {fg} {fg'} = cong₂ _∷_ (dom-fun{A}) doms-fun

cods-fun : ∀{Γ}{fg fg' : Funs Γ} → (cods Γ fg) ≡ (cods Γ fg')
cods-fun {nil} {fg} {fg'} = refl
cods-fun {A ∷ Γ} {fg} {fg'} = cong₂ _∷_ (cod-fun{A}) cods-fun

doms++ : ∀{Γ₁ Γ₂ : List Value}
       → (f1 : Funs Γ₁) → (f2 : Funs Γ₂) → (f12 : Funs (Γ₁ ++ Γ₂))
       → (doms (Γ₁ ++ Γ₂) f12) ≡ (doms Γ₁ f1) ++ (doms Γ₂ f2)
doms++ {nil} {Γ₂} f1 f2 f12 = doms-fun
doms++ {A ∷ Γ₁} {Γ₂} f1 f2 f12 =
  cong₂ _∷_ (dom-fun{A}) (doms++ (λ {v} z → f1 (inj₂ z)) f2
                                 (λ {v} z → f12 (inj₂ z)))


cods++ : ∀{Γ₁ Γ₂ : List Value}
       → (f1 : Funs Γ₁) → (f2 : Funs Γ₂) → (f12 : Funs (Γ₁ ++ Γ₂))
       → (cods (Γ₁ ++ Γ₂) f12) ≡ (cods Γ₁ f1) ++ (cods Γ₂ f2)
cods++ {nil} {Γ₂} f1 f2 f12 = cods-fun
cods++ {A ∷ Γ₁} {Γ₂} f1 f2 f12 =
  cong₂ _∷_ (cod-fun{A}) (cods++ (λ {v} z → f1 (inj₂ z)) f2
                                 (λ {v} z → f12 (inj₂ z)))


doms++⁺ : ∀{Γ₁ Γ₂ : List⁺ Value}
       → (f1 : Funs (toList Γ₁)) → (f2 : Funs (toList Γ₂))
       → (f12 : Funs (toList (Γ₁ ⁺++⁺ Γ₂)))
       → (doms⁺ (Γ₁ ⁺++⁺ Γ₂) f12) ≡ (doms⁺ Γ₁ f1) ⁺++⁺ (doms⁺ Γ₂ f2)
doms++⁺ {A ∷ Γ₁}{B ∷ Γ₂} f1 f2 f12 =
  cong₂ _∷_ (dom-fun{A}) (doms++{Γ₁}{B ∷ Γ₂} (λ {v} z → f1 (inj₂ z))
                           f2 (λ {v} z → f12 (inj₂ z)))


cods++⁺ : ∀{Γ₁ Γ₂ : List⁺ Value}
       → (f1 : Funs (toList Γ₁)) → (f2 : Funs (toList Γ₂))
       → (f12 : Funs (toList (Γ₁ ⁺++⁺ Γ₂)))
       → (cods⁺ (Γ₁ ⁺++⁺ Γ₂) f12) ≡ (cods⁺ Γ₁ f1) ⁺++⁺ (cods⁺ Γ₂ f2)
cods++⁺ {A ∷ Γ₁}{B ∷ Γ₂} f1 f2 f12 =
  cong₂ _∷_ (cod-fun{A}) (cods++{Γ₁}{B ∷ Γ₂} (λ {v} z → f1 (inj₂ z))
                           f2 (λ {v} z → f12 (inj₂ z)))


⨆++ : ∀{Γ₁ : List Value}{Γ₂ : List Value}{A B : Value}
        → ⨆-list A (Γ₁ ++ (B ∷ Γ₂)) ≈ (⨆-list A Γ₁) ⊔ (⨆-list B Γ₂)
⨆++ {nil} = Refl≈
⨆++ {A' ∷ Γ₁} = Trans≈ (⊔≈⊔ Refl≈ (⨆++ {Γ₁})) Assoc≈L 


⨆++⁺ : ∀{Γ₁ Γ₂ : List⁺ Value}
        → ⨆ (Γ₁ ⁺++⁺ Γ₂) ≈ ⨆ Γ₁ ⊔ ⨆ Γ₂
⨆++⁺ {A ∷ Γ₁} {B ∷ Γ₂} = ⨆++{Γ₁}{Γ₂}


⨆doms++⁺ : ∀{Γ₁ Γ₂ : List⁺ Value}
          {fg : Funs (toList (Γ₁ ⁺++⁺ Γ₂))}
          {fg1 : Funs (toList Γ₁)} {fg2 : Funs (toList Γ₂)}
        → ⨆ (doms⁺ (Γ₁ ⁺++⁺ Γ₂) fg) ≈ ⨆ (doms⁺ Γ₁ fg1) ⊔ ⨆ (doms⁺ Γ₂ fg2)
⨆doms++⁺ {Γ₁} {Γ₂} {fg} {fg1} {fg2}
    rewrite cong ⨆ (doms++⁺ fg1 fg2 fg) =
      ⨆++⁺ {doms⁺ Γ₁ fg1}{doms⁺ Γ₂ fg2}


⨆cods++⁺ : ∀{Γ₁ Γ₂ : List⁺ Value}
          {fg : Funs (toList (Γ₁ ⁺++⁺ Γ₂))}
          {fg1 : Funs (toList Γ₁)} {fg2 : Funs (toList Γ₂)}
        → ⨆ (cods⁺ (Γ₁ ⁺++⁺ Γ₂) fg) ≈ ⨆ (cods⁺ Γ₁ fg1) ⊔ ⨆ (cods⁺ Γ₂ fg2)
⨆cods++⁺ {Γ₁} {Γ₂} {fg} {fg1} {fg2}
    rewrite cong ⨆ (cods++⁺ fg1 fg2 fg) =
      ⨆++⁺ {cods⁺ Γ₁ fg1}{cods⁺ Γ₂ fg2}


factor⁺ : (A : Value) → (Γ : List⁺ Value) → (B' : Value) → (C' : Value)→ Set
factor⁺ A Γ B' C' = Σ[ f ∈ Funs (toList Γ) ] 
                    (∀{B} → B ∈⁺ Γ → B ∈ atoms A) ×
                    (⨆ (doms⁺ Γ f) ⊑ B') × (C' ⊑ ⨆ (cods⁺ Γ f))

factor : (A : Value) → (A₁ : Value) (A₂ : Value) → (Γ : List Value)
       → (B' : Value) → (C' : Value)→ Set
factor A A₁ A₂ Γ B' C' = Σ[ f ∈ Funs Γ ] 
   (∀{A₃} → A₃ ∈ Γ → A₃ ∈ atoms A) ×
   (⨆-list A₁ (doms Γ f) ⊑ B') ×
   (C' ⊑ ⨆-list A₂ (cods Γ f))

funs-append : ∀{ls1 ls2} → Funs ls1 → Funs ls2 → Funs (ls1 ++ ls2)
funs-append {nil} {ls2} f1 f2 = f2
funs-append {x ∷ ls1} {ls2} f1 f2 {.x} (inj₁ refl) = f1 (inj₁ refl)
funs-append {x ∷ ls1} {ls2} f1 f2 {v} (inj₂ y) = funs-append (λ {v₁} z → f1 (inj₂ z)) f2 y

funs-append⁺ : ∀{ls1 ls2 : List⁺ Value} → Funs (toList ls1) → Funs (toList ls2) → Funs (toList (ls1 ⁺++⁺ ls2))
funs-append⁺ {x ∷ ls1} {ls2} f1 f2 {.x} (inj₁ refl) = f1 (inj₁ refl)
funs-append⁺ {x ∷ ls1} {ls2} f1 f2 {v} (inj₂ y) = funs-append (λ {v₁} z → f1 (inj₂ z)) f2 y

sub-inv-trans : ∀{D₁}{D₂}{Γ'}{fg' : Funs Γ'}{A}{D}
              → D₁ ↦ D₂ ∈ atoms D → (∀{B} → B ∈ Γ' → B ∈ atoms D)
              → (∀{B' C'} → B' ↦ C' ∈ atoms D
                  → Σ[ Γ ∈ List⁺ Value ] factor⁺ A Γ B' C')
              → Σ[ Γ ∈ List⁺ Value ] Σ[ fg ∈ Funs (toList Γ) ]
                (∀{A₁} → A₁ ∈⁺ Γ → A₁ ∈ atoms A)
              × (⨆ (doms⁺ Γ fg) ⊑ ⨆-list D₁ (doms Γ' fg'))
              × (⨆-list D₂ (cods Γ' fg') ⊑ ⨆ (cods⁺ Γ fg))
sub-inv-trans {D₁}{D₂}{nil} {fg'} {A} {D} D₁↦D₂∈D Γ'⊆D IH = IH D₁↦D₂∈D
sub-inv-trans {D₁}{D₂}{D'' ∷ Γ''} {fg'} {A} {D} D₁↦D₂∈D Γ'⊆D IH
    with IH D₁↦D₂∈D
... | ⟨ Γ₁ , ⟨ fg1 , ⟨ Γ₁⊆A , ⟨ ⨆domΓ₁⊑D₁ , D₂⊑⨆codΓ₁ ⟩ ⟩ ⟩ ⟩
    with fg' (inj₁ refl)
... | (fun{v = D₃}{v' = D₄} refl)
    with sub-inv-trans {D₃}{D₄}{Γ''} {λ {v} z → fg' (inj₂ z)} {A} {D}
             (Γ'⊆D (inj₁ refl)) (λ {B} z → Γ'⊆D (inj₂ z)) IH
... | ⟨ Γ₂ , ⟨ fg2 , ⟨ Γ₂⊆A , ⟨ ⨆domΓ₂⊑D₃ , D₄⊑⨆codΓ₂ ⟩ ⟩ ⟩ ⟩ =
    let fg12 = funs-append⁺ fg1 fg2 in
    ⟨ (Γ₁ ⁺++⁺ Γ₂) , ⟨ fg12 , ⟨ Γ₁++Γ₂⊆A ,
    ⟨ Trans⊑ (proj₁ (⨆doms++⁺{Γ₁}{Γ₂}{fg12}{fg1}{fg2}))
             (⊔⊑⊔ ⨆domΓ₁⊑D₁ ⨆domΓ₂⊑D₃) ,
      Trans⊑ (⊔⊑⊔ D₂⊑⨆codΓ₁ D₄⊑⨆codΓ₂)
             ((proj₂ (⨆cods++⁺{Γ₁}{Γ₂}{fg12}{fg1}{fg2}))) ⟩ ⟩ ⟩ ⟩

    where Γ₁++Γ₂⊆A : (∀{A₁} → A₁ ∈⁺ (Γ₁ ⁺++⁺ Γ₂) → A₁ ∈ atoms A)
          Γ₁++Γ₂⊆A (inj₁ refl) = Γ₁⊆A (inj₁ refl)
          Γ₁++Γ₂⊆A (inj₂ y)
              with ∈++-tail⁺{ls1 = Γ₁} y
          ... | inj₁ x = Γ₁⊆A (inj₂ x)
          ... | inj₂ (inj₁ refl) = Γ₂⊆A (inj₁ refl)
          ... | inj₂ (inj₂ z) = Γ₂⊆A (inj₂ z)


sub-inv : ∀{A A' : Value}
        → A' ⊑ A
        → ∀{B' C'} → B' ↦ C' ∈ atoms A'
        → Σ[ Γ ∈ List⁺ Value ] factor⁺ A Γ B' C'
sub-inv Bot⊑ ()
sub-inv{A}{A'₁ ⊔ A'₂} (ConjL⊑ A'₁⊑A A'₂⊑A) {B'}{C'} m 
    with ∈++{ls1 = atoms A'₁} m
... | inj₁ B'↦C'∈A'₁ = sub-inv A'₁⊑A B'↦C'∈A'₁ 
... | inj₂ B'↦C'∈A'₂ = sub-inv A'₂⊑A B'↦C'∈A'₂ 
sub-inv{A₁ ⊔ A₂}{A'} (ConjR1⊑{v₁ = A₁}{v₂ = A₂} A'⊑A₁) {B'}{C'} m 
    with sub-inv A'⊑A₁ m  
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A₁ , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩
    where Γ⊆A : (∀{B} → B ∈⁺ Γ → B ∈ atoms (A₁ ⊔ A₂))
          Γ⊆A {B} B∈Γ = ∈++-L (Γ⊆A₁ {B} B∈Γ)
sub-inv{A₁ ⊔ A₂}{A'} (ConjR2⊑{v₁ = A₁}{v₂ = A₂} A'⊑A₂) {B'}{C'} m 
    with sub-inv A'⊑A₂ m  
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A₂ , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩
    where Γ⊆A : (∀{B} → B ∈⁺ Γ → B ∈ atoms (A₁ ⊔ A₂))
          Γ⊆A {B} B∈Γ = ∈++-R (Γ⊆A₂ {B} B∈Γ)
sub-inv{A}{A'} (Trans⊑{v₂ = D} A'⊑D D⊑A) {B'}{C'} B'↦C'∈A' 
    with sub-inv A'⊑D B'↦C'∈A'  
... | ⟨ D' ∷ Γ' , ⟨ fg' , ⟨ Γ'⊆D , ⟨ domΓ'⊑B' , C'⊑codΓ' ⟩ ⟩ ⟩ ⟩
    with fg' (inj₁ refl)
... | (fun{v = D₁}{v' = D₂} refl) 
    with sub-inv-trans {D₁}{D₂}{Γ'}{λ z → fg' (inj₂ z)}{A}{D}
                       (Γ'⊆D (inj₁ refl)) (λ {B} z → Γ'⊆D (inj₂ z))
                       (sub-inv D⊑A)
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ domΓ⊑domΓ' , codΓ'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ Trans⊑ domΓ⊑domΓ' domΓ'⊑B' ,
                             Trans⊑ C'⊑codΓ' codΓ'⊑codΓ ⟩ ⟩ ⟩ ⟩
sub-inv {A₁ ↦ A₂} {A'₁ ↦ A'₂} (Fun⊑ A₁⊑A'₁ A'₂⊑A₂) (inj₁ refl) =
  ⟨ A₁ ↦ A₂ ∷ nil , ⟨ F , ⟨ G , ⟨ A₁⊑A'₁ , A'₂⊑A₂ ⟩ ⟩ ⟩ ⟩
  where F : Funs (toList (A₁ ↦ A₂ ∷ nil))
        F (inj₁ refl) = fun refl
        F (inj₂ ())

        G : {B : Value} → B ∈⁺ (A₁ ↦ A₂ ∷ nil) → B ≡ A₁ ↦ A₂ ⊎ Bot
        G (inj₁ refl) = inj₁ refl
        G (inj₂ ())
        
sub-inv {A₁ ↦ A₂} {A'₁ ↦ A'₂} (Fun⊑ A₁⊑A'₁ A'₂⊑A₂) (inj₂ ())
sub-inv {A₁ ↦ A₂ ⊔ A₁ ↦ A₃} {A₁ ↦ (A₂ ⊔ A₃)} Dist⊑ (inj₁ refl) =
  ⟨ (A₁ ↦ A₂ ∷ A₁ ↦ A₃ ∷ nil) , ⟨ f , ⟨ g , ⟨ (ConjL⊑ Refl⊑ Refl⊑) ,
     ⊔⊑⊔ Refl⊑ Refl⊑ ⟩ ⟩ ⟩ ⟩

  where f : Funs (toList (A₁ ↦ A₂ ∷ A₁ ↦ A₃ ∷ nil))
        f (inj₁ refl) = fun refl
        f (inj₂ (inj₁ refl)) = fun refl
        f (inj₂ (inj₂ ())) 

        g : {B : Value} → B ∈⁺ (A₁ ↦ A₂ ∷ A₁ ↦ A₃ ∷ nil)
          → B ≡ A₁ ↦ A₂ ⊎ B ≡ A₁ ↦ A₃ ⊎ Bot
        g (inj₁ refl) = inj₁ refl
        g (inj₂ (inj₁ refl)) = inj₂ (inj₁ refl)
        g (inj₂ (inj₂ ()))

sub-inv {A₁ ↦ A₂ ⊔ A₁ ↦ A₃} {A₁ ↦ (A₂ ⊔ A₃)} Dist⊑ (inj₂ ())

lub-sub : ∀{Γ}{A B C}
        → A ∈ (C ∷ Γ) →  ⨆-list C Γ ⊑ B
        → A ⊑ B
lub-sub {nil} {A} {B} (inj₁ refl) lt = lt
lub-sub {nil} {A} {B} (inj₂ ()) lt
lub-sub {C' ∷ Γ} {A} {B} (inj₁ refl) lt = ⊔⊑-inv lt
lub-sub {C' ∷ Γ} {A} {B} (inj₂ y) lt =
   lub-sub {Γ}{A}{B} y (⊔⊑-invR lt)

fun∈→dom∈ : ∀{Γ}{f : Funs Γ}{D E} → (D ↦ E) ∈ Γ → D ∈ doms Γ f
fun∈→dom∈ {nil} ()
fun∈→dom∈ {.(_ ↦ _) ∷ Γ}{f} (inj₁ refl)
      with f (inj₁ refl)
... | fun x = inj₁ refl
fun∈→dom∈ {A ∷ Γ}{f} (inj₂ y) = inj₂ (fun∈→dom∈ {Γ}{λ {v} z → f (inj₂ z)} y)

fun∈→dom∈⁺ : ∀{Γ}{f : Funs (toList Γ)}{D E} → (D ↦ E) ∈⁺ Γ → D ∈⁺ doms⁺ Γ f
fun∈→dom∈⁺ {A ∷ Γ}{f} m = fun∈→dom∈ {A ∷ Γ} {f} m


sub-inv-fun : ∀{A B C : Value}
        → (A ↦ B) ⊑ C
        → Σ[ Γ ∈ List⁺ Value ] Σ[ f ∈ Funs (toList Γ) ] 
             (∀{D} → D ∈⁺ Γ → D ∈ atoms C)
           × (∀{D E} → (D ↦ E) ∈⁺ Γ → D ⊑ A)
           × (B ⊑ ⨆ (cods⁺ Γ f))
sub-inv-fun{A}{B}{C} abc
    with sub-inv abc {A}{B} (inj₁ refl)
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ G , cc ⟩ ⟩ ⟩ ⟩

   where G : ∀{D E} → (D ↦ E) ∈⁺ Γ → D ⊑ A
         G{D}{E} m = lub-sub (fun∈→dom∈⁺{f = f} m) db
         

Γ⊆A↦B : ∀{Γ}{A B} → (∀{D} → D ∈⁺ Γ → D ∈ atoms (A ↦ B))
      → List⁺.head Γ ≡ A ↦ B
Γ⊆A↦B {head ∷ tail} f
    with f (inj₁ refl)
... | inj₁ refl = refl
... | inj₂ ()


Γ⊆A↦B→codΓ≡B : ∀{Γ}{A B}{f : Funs Γ}
      → (∀{D} → D ∈ Γ → D ∈ atoms (A ↦ B))
      → (∀{D} → D ∈ (cods Γ f) → D ≡ B)
Γ⊆A↦B→codΓ≡B {nil} {A} {B} {f} g ()
Γ⊆A↦B→codΓ≡B {x ∷ Γ} {A} {B} {f} g (inj₁ refl)
    with f (inj₁ refl)
... | fun{v = v}{v' = v'} refl
    with g {v ↦ v'} (inj₁ refl)
... | inj₁ refl = refl
... | inj₂ ()
Γ⊆A↦B→codΓ≡B {C ∷ Γ} {A} {B} {f} g (inj₂ y) =
   Γ⊆A↦B→codΓ≡B {Γ} {A} {B} {λ {v} z → f (inj₂ z)}
              (λ {D} z → g (inj₂ z)) y


⨆-list-refl : ∀{Γ}{A} → (∀{D} → D ∈ Γ → D ≡ A)
            → ⨆-list A Γ ⊑ A
⨆-list-refl {nil} f = Refl⊑
⨆-list-refl {B ∷ Γ}{A} f rewrite f (inj₁ refl) =
   let ih = ⨆-list-refl {Γ}{A} G in 
   ConjL⊑ Refl⊑ ih
   where G : {D : Value} → D ∈ Γ → D ≡ A
         G m = f (inj₂ m)

↦⊑↦-inv : ∀{v₁ v₂ v₃ v₄}
        → v₁ ↦ v₂ ⊑ v₃ ↦ v₄
        → v₃ ⊑ v₁ × v₂ ⊑ v₄
↦⊑↦-inv{v₁}{v₂}{v₃}{v₄} lt
    with sub-inv-fun lt  
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with ⊔⊑-invR (⨆-list-refl {cods ((List⁺.head Γ) ∷ (List⁺.tail Γ)) f}
               (Γ⊆A↦B→codΓ≡B {f = f} Γ⊆v34))
... | y               
    with f (inj₁ refl)
... | fun{v}{v₃'}{v₄'} eq = 
    ⟨ G , Trans⊑ lt2 y ⟩

    where G : v₃ ⊑ v₁
          G rewrite Γ⊆A↦B {Γ} Γ⊆v34 = lt1 (inj₁ refl)


AboveFun-⊔ : ∀{v₁ v₂}
           → AboveFun (v₁ ⊔ v₂)
           → AboveFun v₁ ⊎ AboveFun v₂
AboveFun-⊔{v₁}{v₂} ⟨ v , ⟨ v' , v↦v'⊑v₁⊔v₂ ⟩ ⟩ 
    with sub-inv-fun v↦v'⊑v₁⊔v₂
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v₁⊔v₂ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with f (inj₁ refl)
... | fun{v = u}{v' = u'} eq rewrite eq
    with ∈++{ls1 = atoms v₁} (Γ⊆v₁⊔v₂ (inj₁ refl))
... | inj₁ x = inj₁ ⟨ u , ⟨ u' , (fun∈-sub x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ u , ⟨ u' , (fun∈-sub x) ⟩ ⟩


AboveFun⊥ : ¬ AboveFun ⊥
AboveFun⊥ ⟨ v₁ , ⟨ v₂ , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ = Γ⊆⊥ (inj₁ refl)


not-AboveFun-⊔ : ∀{v₁ v₂ : Value}
               → ¬ AboveFun v₁ → ¬ AboveFun v₂
               → ¬ AboveFun (v₁ ⊔ v₂)
not-AboveFun-⊔ af1 af2 af12
    with AboveFun-⊔ af12
... | inj₁ x = contradiction x af1
... | inj₂ x = contradiction x af2
  

AboveFun? : (v : Value) → Dec (AboveFun v)
AboveFun? ⊥ = no AboveFun⊥
AboveFun? (v ↦ v') = yes ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩
AboveFun? (v₁ ⊔ v₂)
    with AboveFun? v₁ | AboveFun? v₂
... | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ v' , (ConjR1⊑ lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ = yes ⟨ v , ⟨ v' , (ConjR2⊑ lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)


𝔼 : Value → Clos → Set

{-

  We define 𝕍 first by cases on the closure's term,
  then on the value. 

 -}
𝕍 : Value → Clos → Set
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ v') (clos (ƛ M) γ) =
     (∀{c : Clos} → 𝔼 v c → AboveFun v' → Σ[ c' ∈ Clos ]
           (γ , c) ⊢ M ⇓ c'  ×  𝕍 v' c')
𝕍 (v₁ ⊔ v₂) (clos (ƛ M) γ) = 𝕍 v₁ (clos (ƛ M) γ) × 𝕍 v₂ (clos (ƛ M) γ)

𝔼 v (clos M γ) = AboveFun v → Σ[ c ∈ Clos ] γ ⊢ M ⇓ c × 𝕍 v c

𝕍⇓-id : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{v}
      → 𝕍 v (clos M γ)
      → γ ⊢ M ⇓ clos M γ
𝕍⇓-id {M = ` x} {⊥} ()
𝕍⇓-id {M = ` x} {v ↦ v₁} ()
𝕍⇓-id {M = ` x} {v ⊔ v₁} ()
𝕍⇓-id {M = ƛ M} {v = v} vv = ⇓-lam
𝕍⇓-id {M = M · M₁} {⊥} ()
𝕍⇓-id {M = M · M₁} {v ↦ v₁} ()
𝕍⇓-id {M = M · M₁} {v ⊔ v₁} ()

𝕍→WHNF : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{v} → 𝕍 v (clos M γ) → WHNF M
𝕍→WHNF {M = ` x} {v} ()
𝕍→WHNF {M = ƛ M} {v} vc = ƛ_
𝕍→WHNF {M = M · M₁} {v} ()


not-AboveFun-𝕍 : ∀{v : Value}{Γ}{γ' : ClosEnv Γ}{M : Γ , ★ ⊢ ★ }
               → ¬ AboveFun v → 𝕍 v (clos (ƛ M) γ')
not-AboveFun-𝕍 {⊥} af = tt
not-AboveFun-𝕍 {v ↦ v'} af = ⊥-elim (contradiction ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩ af)
not-AboveFun-𝕍 {v₁ ⊔ v₂} af
    with not-AboveFun-⊔-inv af
... | ⟨ af1 , af2 ⟩ =
    ⟨ not-AboveFun-𝕍 af1 , not-AboveFun-𝕍 af2 ⟩


𝕍→𝔼 : ∀{c : Clos}{v : Value}
    → 𝕍 v c → 𝔼 v c
𝕍→𝔼 {clos (` x₁) x} {v} ()
𝕍→𝔼 {clos (M · M₁) x} {v} ()
𝕍→𝔼 {clos (ƛ M) x} {⊥} vc af = ⊥-elim (AboveFun⊥ af)
𝕍→𝔼 {clos (ƛ M) γ} {v ↦ v'} vnc f =
   ⟨ clos (ƛ M) γ , ⟨ (𝕍⇓-id{M = (ƛ M)}{v = v ↦ v'} vnc) , vnc ⟩ ⟩
𝕍→𝔼 {clos (ƛ M) γ} {v₁ ⊔ v₂} ⟨ vv1 , vv2 ⟩ f =
   ⟨ (clos (ƛ M) γ) , ⟨ ⇓-lam , ⟨ vv1 , vv2 ⟩ ⟩ ⟩

𝕍⊔-intro : ∀{c v₁ v₂} → 𝕍 v₁ c → 𝕍 v₂ c → 𝕍 (v₁ ⊔ v₂) c
𝕍⊔-intro {clos (` x₁) x} () v2c
𝕍⊔-intro {clos (ƛ M) x} v1c v2c = ⟨ v1c , v2c ⟩
𝕍⊔-intro {clos (M · M₁) x} () v2c

𝕍→lam : ∀{c v} → 𝕍 v c → Σ[ Γ ∈ Context ] Σ[ γ ∈ ClosEnv Γ ] Σ[ M ∈ Γ , ★ ⊢ ★ ]
                 c ≡ clos (ƛ M) γ
𝕍→lam {clos (` x₁) x} ()
𝕍→lam {clos {Γ} (ƛ M) x} vc = ⟨ Γ , ⟨ x , ⟨ M , refl ⟩ ⟩ ⟩
𝕍→lam {clos (M · M₁) x} ()

sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c

sub-𝔼 : ∀{c : Clos}{v v'} → 𝔼 v c → v' ⊑ v → 𝔼 v' c
sub-𝔼 {clos M x} {v} {v'} evc lt fv
    with evc (AboveFun-⊑ fv lt)
... | ⟨ c , ⟨ Mc , vvc ⟩ ⟩ =
      ⟨ c , ⟨ Mc , sub-𝕍 vvc lt ⟩ ⟩

sub-𝕍 {clos (` x₁) x} {v} vc Bot⊑ = vc
sub-𝕍 {clos (ƛ M) x} {v} vc Bot⊑ = tt
sub-𝕍 {clos (M · M₁) x} {v} vc Bot⊑ = vc
sub-𝕍 {clos (` x₁) x} {v} () (ConjL⊑ lt lt₁)
sub-𝕍 {clos (ƛ M) x} {v} vc (ConjL⊑ lt₁ lt₂) = ⟨ (sub-𝕍 vc lt₁) , sub-𝕍 vc lt₂ ⟩
sub-𝕍 {clos (M · M₁) x} {v} () (ConjL⊑ lt lt₁)
sub-𝕍 {clos (` x₁) x} {.(_ ⊔ _)} () (ConjR1⊑ lt)
sub-𝕍 {clos (ƛ M) x} {.(_ ⊔ _)} ⟨ vv1 , vv2 ⟩ (ConjR1⊑ lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos (M · M₁) x} {.(_ ⊔ _)} () (ConjR1⊑ lt)
sub-𝕍 {clos (` x₁) x} {.(_ ⊔ _)} () (ConjR2⊑ lt)
sub-𝕍 {clos (ƛ M) x} {.(_ ⊔ _)} ⟨ vv1 , vv2 ⟩ (ConjR2⊑ lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos (M · M₁) x} {.(_ ⊔ _)} () (ConjR2⊑ lt)
sub-𝕍 {c} {v} vc (Trans⊑{v₂ = v₂} lt lt₁) =
    sub-𝕍 {c} {v₂} (sub-𝕍 {c}{v} vc lt₁) lt
sub-𝕍 {clos (` x₁) x} {.(_ ↦ _)} () (Fun⊑ lt lt₁)
sub-𝕍 {clos (ƛ M) x} {.(_ ↦ _)} vc (Fun⊑ lt lt₁) ev1 sf
    with vc (sub-𝔼 ev1 lt) (AboveFun-⊑ sf lt₁)
... | ⟨ c , ⟨ Mc , v4 ⟩ ⟩ = ⟨ c , ⟨ Mc , sub-𝕍 v4 lt₁ ⟩ ⟩
sub-𝕍 {clos (M · M₁) x} {.(_ ↦ _)} () (Fun⊑ lt lt₁)
sub-𝕍 {clos (` x₁) x} {.(_ ↦ _ ⊔ _ ↦ _)} () Dist⊑
sub-𝕍 {clos (ƛ M) γ} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩
    Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    with AboveFun? v₂ | AboveFun? v₃
... | yes af2 | no naf3
    with vc12 ev1c af2
... | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩ 
    with 𝕍→lam 𝕍2c
... | ⟨ Γ' , ⟨ δ , ⟨ N , eq ⟩ ⟩ ⟩ rewrite eq =
      let 𝕍3c = not-AboveFun-𝕍{v₃}{Γ'}{δ}{N} naf3 in
      ⟨ clos (ƛ N) δ , ⟨ M⇓c2 , 𝕍⊔-intro 𝕍2c 𝕍3c ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | no naf2 | yes af3
    with vc13 ev1c af3
... | ⟨ c3 , ⟨ M⇓c3 , 𝕍3c ⟩ ⟩ 
    with 𝕍→lam 𝕍3c
... | ⟨ Γ' , ⟨ δ , ⟨ N , eq ⟩ ⟩ ⟩ rewrite eq =
      let 𝕍2c = not-AboveFun-𝕍{v₂}{Γ'}{δ}{N} naf2 in
      ⟨ clos (ƛ N) δ , ⟨ M⇓c3 , 𝕍⊔-intro 𝕍2c 𝕍3c ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | no naf2 | no naf3
    with AboveFun-⊔ ⟨ v , ⟨ v' , lt ⟩ ⟩
... | inj₁ af2 = ⊥-elim (contradiction af2 naf2)
... | inj₂ af3 = ⊥-elim (contradiction af3 naf3)
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | yes af2 | yes af3
    with vc12 ev1c af2 | vc13 ev1c af3
... | ⟨ clos N δ , ⟨ Mc1 , v4 ⟩ ⟩
    | ⟨ c2 , ⟨ Mc2 , v5 ⟩ ⟩ rewrite ⇓-determ Mc2 Mc1 with 𝕍→WHNF v4
... | ƛ_ =
      ⟨ clos N δ , ⟨ Mc1 , ⟨ v4 , v5 ⟩ ⟩ ⟩

sub-𝕍 {clos (M · M₁) x} {.(_ ↦ _ ⊔ _ ↦ _)} () Dist⊑ 


𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 ∅ ∅ = ⊤
𝔾 (γ , v) (γ' , c) = 𝔾 γ γ' × 𝔼 v c


𝔾-nth : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
         → 𝔾 γ γ' → 𝔼 (nth x γ) (kth x γ')
𝔾-nth {∅} {∅} {∅} {()} tt
𝔾-nth {Γ , ★} {γ , x} {γ' , x₁} {Z} ⟨ fst , snd ⟩ = snd
𝔾-nth {Γ , ★} {γ , x} {γ' , x₁} {S k} ⟨ fst , snd ⟩ = 𝔾-nth fst


kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ M ∈ Δ ⊢ ★ ]
                 kth x γ' ≡ clos M δ
kth-x{γ' = γ'}{x = x} with kth x γ'
... | clos{Γ = Δ} M δ = ⟨ Δ , ⟨ δ , ⟨ M , refl ⟩ ⟩ ⟩





soundness↓⇓ : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Γ ⊢ ★ }{v}
            → 𝔾 γ γ' → γ ⊢ M ↓ v → 𝔼 v (clos M γ')
soundness↓⇓ {Γ} {γ} {γ'} {`_ x} {v} g var sf 
    with kth-x{Γ}{γ'}{x} | 𝔾-nth{x = x} g
... | ⟨ Δ , ⟨ δ , ⟨ M , eq ⟩ ⟩ ⟩ | g' rewrite eq
    with g' sf
... | ⟨ c , ⟨ L⇓c , Vnc ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq L⇓c) , Vnc ⟩ ⟩
soundness↓⇓ {Γ} {γ} {γ'} {L · M} {v} g (↦-elim{v₁ = v₁} d₁ d₂) sf
    with soundness↓⇓ g d₁ ⟨ v₁ , ⟨ v , Refl⊑ ⟩ ⟩
... | ⟨ clos (` x) δ , ⟨ L⇓c , () ⟩ ⟩
... | ⟨ clos (L' · M') δ , ⟨ L⇓c , () ⟩ ⟩ 
... | ⟨ clos (ƛ L') δ , ⟨ L⇓c , Vc ⟩ ⟩
    with Vc {clos M γ'} (soundness↓⇓ g d₂) sf
... | ⟨ c' , ⟨ L'⇓c' , Vc' ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓c L'⇓c' , Vc' ⟩ ⟩
soundness↓⇓ {Γ} {γ} {γ'} {ƛ M} {v ↦ v'} g (↦-intro d) sf =
  ⟨ (clos (ƛ M) γ') , ⟨ ⇓-lam , G ⟩ ⟩
  where G : {c : Clos} → 𝔼 v c → AboveFun v'
          → Σ-syntax Clos (λ c' → ((γ' , c) ⊢ M ⇓ c') × 𝕍 v' c')
        G {c} evc sfv' =
           soundness↓⇓{Γ , ★}{γ , v}{γ' , c}{M}{v'} ⟨ g , evc ⟩ d sfv'
soundness↓⇓ {Γ} {γ} {γ'} {M} {⊥} g ⊥-intro sf = ⊥-elim (AboveFun⊥ sf)
soundness↓⇓ {Γ} {γ} {γ'} {M} {v₁ ⊔ v₂} g (⊔-intro d₁ d₂) af12
    with AboveFun? v₁ | AboveFun? v₂
soundness↓⇓ g (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) af12 | yes af1 | no naf2
    with soundness↓⇓ g d₁ af1 
... | ⟨ c1 , ⟨ M⇓c1 , 𝕍1c ⟩ ⟩
    with 𝕍→lam 𝕍1c
... | ⟨ Γ , ⟨ γ , ⟨ M , eq ⟩ ⟩ ⟩ rewrite eq =     
    let 𝕍2c = not-AboveFun-𝕍{v₂}{Γ}{γ}{M} naf2 in
    ⟨ clos (ƛ M) γ , ⟨ M⇓c1 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
soundness↓⇓ g (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) af12 | no naf1  | yes af2
    with soundness↓⇓ g d₂ af2
... | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩
    with 𝕍→lam 𝕍2c
... | ⟨ Γ , ⟨ γ , ⟨ M , eq ⟩ ⟩ ⟩ rewrite eq =     
    let 𝕍1c = not-AboveFun-𝕍{v₁}{Γ}{γ}{M} naf1 in
    ⟨ clos (ƛ M) γ , ⟨ M⇓c2 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
soundness↓⇓ g (⊔-intro d₁ d₂) af12 | no naf1  | no naf2
    with AboveFun-⊔ af12
... | inj₁ af1 = ⊥-elim (contradiction af1 naf1)
... | inj₂ af2 = ⊥-elim (contradiction af2 naf2)
soundness↓⇓ g (⊔-intro d₁ d₂) af12 | yes af1 | yes af2
    with soundness↓⇓ g d₁ af1 | soundness↓⇓ g d₂ af2 
... | ⟨ c1 , ⟨ M⇓c1 , 𝕍1c ⟩ ⟩ | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩
    rewrite ⇓-determ M⇓c2 M⇓c1 =
      ⟨ c1 , ⟨ M⇓c1 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
soundness↓⇓ {Γ} {γ} {γ'} {M} {v} g (sub d lt) sf 
    with soundness↓⇓ {Γ} {γ} {γ'} {M} g d (AboveFun-⊑ sf lt)
... | ⟨ c , ⟨ M⇓c , 𝕍c ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍c lt ⟩ ⟩
\end{code}


## Adequacy of the denotational semantics

\begin{code}
adequacy : ∀{M : ∅ ⊢ ★}{N : ∅ , ★ ⊢ ★}  →  ℰ M ≃ ℰ (ƛ N)
         →  Σ[ c ∈ Clos ] ∅ ⊢ M ⇓ c
adequacy{M}{N} eq 
    with soundness↓⇓ tt ((proj₂ eq) (↦-intro ⊥-intro)) ⟨ ⊥ , ⟨ ⊥ , Refl⊑ ⟩ ⟩
... | ⟨ c , ⟨ M⇓c , Vc ⟩ ⟩ = ⟨ c , M⇓c ⟩
\end{code}

