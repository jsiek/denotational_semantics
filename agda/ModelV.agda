open import Structures
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; cong-app)

import LambdaV
open LambdaV.ASTMod using (Var; Z; S_; extensionality)

module ModelV where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  Bot⊑ : ∀ {v} → ⊥ ⊑ v

  ConjL⊑ : ∀ {u v w}
      → v ⊑ u
      → w ⊑ u
        -----------
      → (v ⊔ w) ⊑ u

  ConjR1⊑ : ∀ {u v w}
     → u ⊑ v
       -----------
     → u ⊑ (v ⊔ w)

  ConjR2⊑ : ∀ {u v w}
     → u ⊑ w
       -----------
     → u ⊑ (v ⊔ w)

  Trans⊑ : ∀ {u v w}
     → u ⊑ v
     → v ⊑ w
       -----
     → u ⊑ w

  Fun⊑ : ∀ {v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)

  Dist⊑ : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

Refl⊑ : ∀ {v} → v ⊑ v
Refl⊑ {⊥} = Bot⊑
Refl⊑ {v ↦ v′} = Fun⊑ Refl⊑ Refl⊑
Refl⊑ {v₁ ⊔ v₂} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)

⊔⊑⊔ : ∀ {v w v′ w′}
      → v ⊑ v′  →  w ⊑ w′
        -----------------------
      → (v ⊔ w) ⊑ (v′ ⊔ w′)
⊔⊑⊔ d₁ d₂ = ConjL⊑ (ConjR1⊑ d₁) (ConjR2⊑ d₂)

Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
        → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v′ ↦ w′)
Dist⊔↦⊔ = Trans⊑ Dist⊑ (⊔⊑⊔ (Fun⊑ (ConjR1⊑ Refl⊑) Refl⊑)
                            (Fun⊑ (ConjR2⊑ Refl⊑) Refl⊑))

module LM = LambdaModelMod Value _⊑_ _⊔_
open LM

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ {Γ} D = record { E = F ;
                    up-env = λ {γ}{δ}{v} x x₁ → up-F {γ}{δ}{v} x x₁ ;
                    ⊑-closed = sub-F ;
                    ⊔-closed = λ {γ}{u}{v} x x₁ → F-⊔{γ}{u}{v} x x₁ }
   where
   F : Env Γ → Value → Set
   F γ (v ↦ w) = Denotation.E D (γ `, v) w
   F γ ⊥ = ⊤
   F γ (u ⊔ v) = (F γ u) × (F γ v)

   up-F : ∀ {γ δ : Env Γ} {v : Value} →
        F γ v → ((x : Var Γ) → γ x ⊑ δ x) → F δ v
   up-F {v = ⊥} Fγv γ⊑δ = tt
   up-F {γ}{δ} {v = v ↦ w} Fγv γ⊑δ =
      Denotation.up-env D Fγv b
      where b : (γ `, v) `⊑ (δ `, v)
            b Z = Refl⊑
            b (S x) = γ⊑δ x

   up-F {v = u ⊔ v} ⟨ fst , snd ⟩ γ⊑δ =
      ⟨ up-F{v = u} fst γ⊑δ , up-F{v = v} snd γ⊑δ ⟩

   sub-F : {γ : Env  Γ} {v w : Value} → F γ v → w ⊑ v → F γ w
   sub-F Fγv Bot⊑ = tt
   sub-F Fγv (ConjL⊑ wv wv₁) = ⟨ (sub-F Fγv wv) , (sub-F Fγv wv₁) ⟩
   sub-F Fγv (ConjR1⊑ wv) = sub-F (proj₁ Fγv) wv
   sub-F Fγv (ConjR2⊑ wv) = sub-F (proj₂ Fγv) wv
   sub-F Fγv (Trans⊑ wv wv₁) = sub-F (sub-F Fγv wv₁) wv
   sub-F {γ}{v ↦ w}{v' ↦ w'} Fγv (Fun⊑ wv wv₁) =
      let a = Denotation.up-env D Fγv b in
      Denotation.⊑-closed D a wv₁
      where b : (γ `, v) `⊑ (γ `, v')
            b Z = wv
            b (S x) = Refl⊑ 
   sub-F ⟨ Eγvw , Eγvw′ ⟩ Dist⊑ = Denotation.⊔-closed D Eγvw Eγvw′

   F-⊔ : ∀{γ : Env Γ} {u v : Value} → F γ u → F γ v → F γ u × F γ v
   F-⊔ d1 d2 = ⟨ d1 , d2 ⟩

infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ = record { E = app ;
                         up-env = up-env ;
                         ⊑-closed = ●-⊑ ;
                         ⊔-closed = ●-⊔ }
  where
  app : Env Γ → Value → Set
  app γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] Denotation.E D₁ γ (v ↦ w)
                                 × Denotation.E D₂ γ v 

  up-env : ∀{γ δ : Env Γ} {w : Value} → app γ w → γ `⊑ δ → app δ w
  up-env (inj₁ w⊑⊥) γ⊑δ = inj₁ w⊑⊥
  up-env (inj₂ ⟨ v , ⟨ Eγv↦w , Eγv ⟩ ⟩) γ⊑δ =
    inj₂ ⟨ v ,
         ⟨ Denotation.up-env D₁ Eγv↦w γ⊑δ ,
           Denotation.up-env D₂ Eγv γ⊑δ ⟩ ⟩

  ●-⊑ : ∀ {γ : Var Γ → Value} {v w : Value} → app γ v → w ⊑ v → app γ w
  ●-⊑ (inj₁ v⊑⊥) w⊑v = inj₁ (Trans⊑ w⊑v v⊑⊥)
  ●-⊑ {v = v}{w} (inj₂ ⟨ v' , ⟨ Eγv'↦v , Eγv' ⟩ ⟩) w⊑v =
    inj₂ ⟨ v' , ⟨ Denotation.⊑-closed D₁ Eγv'↦v lt , Eγv' ⟩ ⟩
    where lt : v' ↦ w ⊑ v' ↦ v
          lt = Fun⊑ Refl⊑ w⊑v

  ●-⊔ : ∀ {γ : Var Γ → Value} {u v : Value} → app γ u → app γ v → app γ (u ⊔ v)
  ●-⊔ (inj₁ u⊑⊥) (inj₁ v⊑⊥) = inj₁ (ConjL⊑ u⊑⊥ v⊑⊥)
  ●-⊔ {u = u}{v} (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ Eγv'↦v , Eγv' ⟩ ⟩) =
     inj₂ ⟨ v' , ⟨ Denotation.⊑-closed D₁ Eγv'↦v lt , Eγv' ⟩ ⟩
     where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
           lt = Fun⊑ Refl⊑ (ConjL⊑ (Trans⊑ u⊑⊥ Bot⊑) Refl⊑)
  ●-⊔ {u = u}{v} (inj₂ ⟨ v' , ⟨ Eγv'↦v , Eγv' ⟩ ⟩) (inj₁ u⊑⊥) =
     inj₂ ⟨ v' , ⟨ Denotation.⊑-closed D₁ Eγv'↦v lt , Eγv' ⟩ ⟩
     where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ u
           lt = Fun⊑ Refl⊑ (ConjL⊑ Refl⊑ (Trans⊑ u⊑⊥ Bot⊑))
  ●-⊔ {u = u}{v} (inj₂ ⟨ u₁ , ⟨ Eγu₁↦v , Eγu₁ ⟩ ⟩)
                 (inj₂ ⟨ v₁ , ⟨ Eγv₁↦v , Eγv₁ ⟩ ⟩) =
     let a = Denotation.⊔-closed D₁ Eγu₁↦v Eγv₁↦v in
     let b = Denotation.⊔-closed D₂ Eγu₁ Eγv₁ in
     inj₂ ⟨ (u₁ ⊔ v₁) , ⟨ Denotation.⊑-closed D₁ a Dist⊔↦⊔ , b ⟩ ⟩

var : {Γ : ℕ} → Var Γ → Denotation Γ
var {Γ} x = record { E = E ; up-env = up-env ;
                 ⊑-closed = λ {γ v w} x₁ x₂ → var-⊑ {γ}{v}{w} x₁ x₂ ;
                 ⊔-closed = λ {γ u v} x y → var-⊔ {γ}{u}{v} x y }
        where      
        E : Env Γ → Value → Set
        E ρ v = v ⊑ ρ x

        up-env : ∀ {γ δ : Env Γ} {v : Value} → v ⊑ γ x → γ `⊑ δ → v ⊑ δ x
        up-env v⊑γx γ⊑δ = Trans⊑ v⊑γx (γ⊑δ x)

        var-⊑ : ∀ {γ : Env Γ} {v w : Value} → v ⊑ γ x → w ⊑ v → w ⊑ γ x
        var-⊑ v⊑γx w⊑v = Trans⊑ w⊑v v⊑γx

        var-⊔ : ∀ {γ : Env Γ} {u v : Value} → u ⊑ γ x → v ⊑ γ x → (u ⊔ v) ⊑ γ x
        var-⊔ u⊑γx v⊑γx = ConjL⊑ u⊑γx v⊑γx

{-
retract : ∀{Γ}{f : Denotation (suc Γ)}{D : Denotation Γ}{γ}{v}
        → Denotation.E (_●_ (ℱ f)) γ v iff Denotation.E f γ v
retract {Γ}{D} = ?
-}

model : LambdaModel 
model = record { var = var ;
                 ℱ = ℱ ;
                 _●_ = _●_ ;
                 Refl⊑ = Refl⊑ ;
                 Trans⊑ = Trans⊑ ;
                 ConjL⊑ = ConjL⊑
                 }
