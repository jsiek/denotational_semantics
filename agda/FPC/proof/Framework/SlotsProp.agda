{-

  Properties of the values of a fixed frame (FPC/Semantics/Slots.agda).

  * A read after a write to the same slot finds the value written
    (read-write), and a read of another initialized slot finds the old
    value, when the slot written was not initialized (read-write-other).
  * Two frames agree on the slots J (Agree J) when they hold the same
    values there. Writing the same value to a slot keeps frames in
    agreement (agree-write), a write to a slot that is not initialized
    keeps the frame in agreement with the old one (agree-fresh), and
    frames that agree on J are the same when restricted to J
    (restrict-ext).
  * So the frame that code starts with after writes to y and then x is
    the one it starts with after the write to x alone, when y was not
    initialized, and so the code does not read y (restrict-fresh).

-}

module FPC.proof.Framework.SlotsProp where

open import FPC.Language.Type
open import FPC.Language.Frame
open import FPC.Framework.AllUtil using ([]; _∷_)
open import FPC.Semantics.Slots
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Data.List using ([]; _∷_)

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;
  cong₂; trans; sym)

module _ {V : Type → Set} where

  read-write : ∀ {Δ I A} (φ : Slots V Δ I) (x : Δ ∋ A) (v : V A)
    → .(i : x ∈ I ⊕ x)
    → read (write φ x v) x i ≡ v
  read-write (u ∷ φ) Z v i = refl
  read-write (∙ φ) Z v i = refl
  read-write (u ∷ φ) (S x) v i = read-write φ x v i
  read-write (∙ φ) (S x) v i = read-write φ x v i

  {- a read of an initialized slot y, after a write to a slot x that was
     not -}
  read-write-other : ∀ {Δ I A B} (φ : Slots V Δ I) (x : Δ ∋ A) (v : V A)
    (y : Δ ∋ B)
    → .(yi : y ∈ I)
    → .(x ∉ I)
    → .(i : y ∈ I ⊕ x)
    → read (write φ x v) y i ≡ read φ y yi
  read-write-other (u ∷ φ) Z v Z yi xn i = ⊥-elim xn
  read-write-other (∙ φ) Z v Z yi xn i = ⊥-elim yi
  read-write-other (u ∷ φ) Z v (S y) yi xn i = refl
  read-write-other (∙ φ) Z v (S y) yi xn i = refl
  read-write-other (u ∷ φ) (S x) v Z yi xn i = refl
  read-write-other (∙ φ) (S x) v Z yi xn i = ⊥-elim yi
  read-write-other (u ∷ φ) (S x) v (S y) yi xn i =
    read-write-other φ x v y yi xn i
  read-write-other (∙ φ) (S x) v (S y) yi xn i =
    read-write-other φ x v y yi xn i

  {- frames that hold the same values in the slots J -}
  Agree : ∀ {Δ} {I I' : Inits Δ} (J : Inits Δ) → .(J ⊆ I) → .(J ⊆ I')
    → Slots V Δ I → Slots V Δ I' → Set
  Agree {Δ} J p p' φ ψ =
    ∀ {B} (z : Δ ∋ B) (j : z ∈ J)
    → read φ z (∈-⊆ z j p) ≡ read ψ z (∈-⊆ z j p')

  agree-refl : ∀ {Δ I} {J : Inits Δ} (φ : Slots V Δ I) .(p : J ⊆ I)
    → Agree J p p φ φ
  agree-refl φ p z j = refl

  agree-mono : ∀ {Δ I I'} {J J' : Inits Δ} {φ : Slots V Δ I}
    {ψ : Slots V Δ I'} .{p : J ⊆ I} .{p' : J ⊆ I'}
    → (q : J' ⊆ J)
    → Agree J p p' φ ψ
    → Agree J' (⊆-trans q p) (⊆-trans q p') φ ψ
  agree-mono q a z j = a z (∈-⊆ z j q)

  {- a write to a slot that is not initialized -}
  agree-fresh : ∀ {Δ I A} (φ : Slots V Δ I) (y : Δ ∋ A) (u : V A)
    → .(y ∉ I)
    → Agree I ⊆-refl (⊆-⊕ y) φ (write φ y u)
  agree-fresh φ y u yn z j = sym′ (read-write-other φ y u z j yn _)
    where
    sym′ : ∀ {a b : V _} → a ≡ b → b ≡ a
    sym′ refl = refl

  {- writing the same value to x -}
  agree-write : ∀ {Δ I I' A} {J : Inits Δ} (φ : Slots V Δ I)
    (ψ : Slots V Δ I') .(p : J ⊆ I) .(p' : J ⊆ I') (x : Δ ∋ A) (v : V A)
    → Agree J p p' φ ψ
    → Agree (J ⊕ x) (⊕-mono x p) (⊕-mono x p') (write φ x v) (write ψ x v)
  agree-write {J = c ∷ J} (u ∷ φ) (w ∷ ψ) p p' Z v a Z j = refl
  agree-write {J = c ∷ J} (u ∷ φ) (∙ ψ) p p' Z v a Z j = refl
  agree-write {J = c ∷ J} (∙ φ) (w ∷ ψ) p p' Z v a Z j = refl
  agree-write {J = c ∷ J} (∙ φ) (∙ ψ) p p' Z v a Z j = refl
  agree-write {J = c ∷ J} (u ∷ φ) (w ∷ ψ) p p' Z v a (S z) j = a (S z) j
  agree-write {J = c ∷ J} (u ∷ φ) (∙ ψ) p p' Z v a (S z) j = a (S z) j
  agree-write {J = c ∷ J} (∙ φ) (w ∷ ψ) p p' Z v a (S z) j = a (S z) j
  agree-write {J = c ∷ J} (∙ φ) (∙ ψ) p p' Z v a (S z) j = a (S z) j
  agree-write {J = c ∷ J} (u ∷ φ) (w ∷ ψ) p p' (S x) v a Z j =
    a Z j
  agree-write {J = c ∷ J} (u ∷ φ) (∙ ψ) p p' (S x) v a Z j =
    ⊥-elim (proj₁ p' j)
  agree-write {J = c ∷ J} (∙ φ) (w ∷ ψ) p p' (S x) v a Z j =
    ⊥-elim (proj₁ p j)
  agree-write {J = c ∷ J} (∙ φ) (∙ ψ) p p' (S x) v a Z j =
    ⊥-elim (proj₁ p j)
  agree-write {J = c ∷ J} (u ∷ φ) (w ∷ ψ) p p' (S x) v a (S z) j =
    agree-write φ ψ (proj₂ p) (proj₂ p') x v (λ z j → a (S z) j) z j
  agree-write {J = c ∷ J} (u ∷ φ) (∙ ψ) p p' (S x) v a (S z) j =
    agree-write φ ψ (proj₂ p) (proj₂ p') x v (λ z j → a (S z) j) z j
  agree-write {J = c ∷ J} (∙ φ) (w ∷ ψ) p p' (S x) v a (S z) j =
    agree-write φ ψ (proj₂ p) (proj₂ p') x v (λ z j → a (S z) j) z j
  agree-write {J = c ∷ J} (∙ φ) (∙ ψ) p p' (S x) v a (S z) j =
    agree-write φ ψ (proj₂ p) (proj₂ p') x v (λ z j → a (S z) j) z j

  {- frames that agree on J are the same restricted to J -}
  restrict-ext : ∀ {Δ I I'} {J : Inits Δ} (φ : Slots V Δ I)
    (ψ : Slots V Δ I') .(p : J ⊆ I) .(p' : J ⊆ I')
    → Agree J p p' φ ψ
    → restrict p φ ≡ restrict p' ψ
  restrict-ext {J = []} [] [] p p' a = refl
  restrict-ext {J = true ∷ J} (v ∷ φ) (w ∷ ψ) p p' a =
    cong₂ _∷_ (a Z tt) (restrict-ext φ ψ (proj₂ p) (proj₂ p') λ z j → a (S z) j)
  restrict-ext {J = true ∷ J} (v ∷ φ) (∙ ψ) p p' a = ⊥-elim (proj₁ p' tt)
  restrict-ext {J = true ∷ J} (∙ φ) ψ p p' a = ⊥-elim (proj₁ p tt)
  restrict-ext {J = false ∷ J} (v ∷ φ) (w ∷ ψ) p p' a =
    cong ∙_ (restrict-ext φ ψ (proj₂ p) (proj₂ p') λ z j → a (S z) j)
  restrict-ext {J = false ∷ J} (v ∷ φ) (∙ ψ) p p' a =
    cong ∙_ (restrict-ext φ ψ (proj₂ p) (proj₂ p') λ z j → a (S z) j)
  restrict-ext {J = false ∷ J} (∙ φ) (w ∷ ψ) p p' a =
    cong ∙_ (restrict-ext φ ψ (proj₂ p) (proj₂ p') λ z j → a (S z) j)
  restrict-ext {J = false ∷ J} (∙ φ) (∙ ψ) p p' a =
    cong ∙_ (restrict-ext φ ψ (proj₂ p) (proj₂ p') λ z j → a (S z) j)

  {- the frame after writes to y and x, restricted to J ⊆ I ⊕ x, is the
     one after the write to x alone, when y ∉ I -}
  restrict-fresh : ∀ {Δ I A B} {J : Inits Δ} (φ : Slots V Δ I) (y : Δ ∋ B)
    (u : V B) (x : Δ ∋ A) (v : V A)
    → .(y ∉ I)
    → (p : J ⊆ I ⊕ x)
    → .(p' : J ⊆ I ⊕ y ⊕ x)
    → restrict p' (write (write φ y u) x v) ≡ restrict p (write φ x v)
  restrict-fresh {I = I} {J = J} φ y u x v yn p p' =
    sym (restrict-ext (write φ x v) (write (write φ y u) x v) p p'
      (agree-mono {I = I ⊕ x} {I ⊕ y ⊕ x} {I ⊕ x} {J} {write φ x v}
        {write (write φ y u) x v} {⊕-mono x (⊆-refl {I = I})}
        {⊕-mono x (⊆-⊕ {I = I} y)} p
        (agree-write φ (write φ y u) (⊆-refl {I = I}) (⊆-⊕ y) x v
          (agree-fresh φ y u yn))))

  {- the start of a body holds its argument and environment -}
  params-arg : ∀ {Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) (e : V B) (w : V A)
    → .(i : ⊑-∋ p Z ∈ initial p)
    → read (params p e w) (⊑-∋ p Z) i ≡ w
  params-arg {Δ} p e w i =
    read-write (write (empty Δ) (⊑-∋ p (S Z)) e) (⊑-∋ p Z) w i

  params-env : ∀ {Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) (e : V B) (w : V A)
    → .(i : ⊑-∋ p (S Z) ∈ initial p)
    → read (params p e w) (⊑-∋ p (S Z)) i ≡ e
  params-env {Δ} p e w i =
    trans
      (read-write-other (write (empty Δ) (⊑-∋ p (S Z)) e) (⊑-∋ p Z) w
        (⊑-∋ p (S Z)) (∈-⊕ {I = none Δ} (⊑-∋ p (S Z))) (params-fresh p) i)
      (read-write (empty Δ) (⊑-∋ p (S Z)) e _)

  restrict-id : ∀ {Δ I} (φ : Slots V Δ I) .(p : I ⊆ I) → restrict p φ ≡ φ
  restrict-id [] p = refl
  restrict-id (v ∷ φ) p = cong (v ∷_) (restrict-id φ (proj₂ p))
  restrict-id (∙ φ) p = cong ∙_ (restrict-id φ (proj₂ p))
