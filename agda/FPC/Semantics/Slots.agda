{-

  The values of a fixed frame (FPC/Language/Frame.agda), for the
  interpreters and machines whose values are typed: Slots V Δ I holds a
  value of V A for each initialized slot of type A (_∷_), and nothing
  for the others (∙_). A read of an initialized slot (read) always finds
  a value; a write (write) initializes its slot; restrict forgets the
  values of the slots that code which starts with fewer initialized
  slots (J ⊆ I) does not read.

-}

module FPC.Semantics.Slots where

open import FPC.Language.Type
open import FPC.Language.Frame
open import Framework.Membership using (_⊑_; ⊑-∋)
open import FPC.Framework.AllUtil using ([]; _∷_)

open import Data.Bool using (Bool; true; false)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)

infixr 5 _∷_
infix 5 ∙_

data Slots (V : Type → Set) : (Δ : Ctx) → Inits Δ → Set where
  [] : Slots V [] []
  _∷_ : ∀ {A Δ I} → V A → Slots V Δ I → Slots V (A ∷ Δ) (true ∷ I)
  ∙_ : ∀ {A Δ I} → Slots V Δ I → Slots V (A ∷ Δ) (false ∷ I)

module _ {V : Type → Set} where

  {- the frame with no slot initialized -}
  empty : ∀ Δ → Slots V Δ (none Δ)
  empty [] = []
  empty (A ∷ Δ) = ∙ empty Δ

  read : ∀ {Δ I A} → Slots V Δ I → (x : Δ ∋ A) → .(x ∈ I) → V A
  read (v ∷ φ) Z i = v
  read (∙ φ) Z ()
  read (v ∷ φ) (S x) i = read φ x i
  read (∙ φ) (S x) i = read φ x i

  write : ∀ {Δ I A} → Slots V Δ I → (x : Δ ∋ A) → V A → Slots V Δ (I ⊕ x)
  write (_ ∷ φ) Z v = v ∷ φ
  write (∙ φ) Z v = v ∷ φ
  write (u ∷ φ) (S x) v = u ∷ write φ x v
  write (∙ φ) (S x) v = ∙ write φ x v

  restrict : ∀ {Δ} {I J : Inits Δ} → .(J ⊆ I) → Slots V Δ I → Slots V Δ J
  restrict {J = []} p [] = []
  restrict {J = true ∷ J} p (v ∷ φ) = v ∷ restrict (proj₂ p) φ
  restrict {J = true ∷ J} p (∙ φ) = ⊥-elim (proj₁ p tt)
  restrict {J = false ∷ J} p (v ∷ φ) = ∙ restrict (proj₂ p) φ
  restrict {J = false ∷ J} p (∙ φ) = ∙ restrict (proj₂ p) φ

  {- the frame at the start of a body with parameters A ∷ B ∷ [] (an
     argument and an environment), the environment written first -}
  params : ∀ {Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) → V B → V A
    → Slots V Δ (initial p)
  params {Δ} p e w = write (write (empty Δ) (⊑-∋ p (S Z)) e) (⊑-∋ p Z) w
