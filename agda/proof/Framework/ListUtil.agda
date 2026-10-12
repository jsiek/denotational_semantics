{-

  Lemmas about the list operations of Framework/ListUtil.agda.

-}

module proof.Framework.ListUtil where

open import Framework.ListUtil public

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; [_]; length; replicate; reverse)
open import Data.List.Properties using (++-assoc; reverse-++; unfold-reverse; reverse-involutive; length-reverse)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

private variable
  A B : Set

‼-< : ∀ (vs : List A) x → x < length vs → Σ[ v ∈ A ] vs ‼ x ≡ just v
‼-< (v ∷ vs) zero _ = v , refl
‼-< (v ∷ vs) (suc x) (s≤s x<) = ‼-< vs x x<

‼-snoc-< : ∀ (vs : List A) v k → k < length vs → (vs ∷ʳ v) ‼ k ≡ vs ‼ k
‼-snoc-< (u ∷ vs) v zero _ = refl
‼-snoc-< (u ∷ vs) v (suc k) (s≤s k<) = ‼-snoc-< vs v k k<

‼-snoc-length : ∀ (vs : List A) v → (vs ∷ʳ v) ‼ length vs ≡ just v
‼-snoc-length [] v = refl
‼-snoc-length (u ∷ vs) v = ‼-snoc-length vs v

‼-≥ : ∀ (vs : List A) k → length vs ≤ k → vs ‼ k ≡ nothing
‼-≥ [] k _ = refl
‼-≥ (u ∷ vs) (suc k) (s≤s le) = ‼-≥ vs k le

‼-++ : ∀ (ws : List A) {a zs} → (ws ++ a ∷ zs) ‼ length ws ≡ just a
‼-++ [] = refl
‼-++ (w ∷ ws) = ‼-++ ws

‼-just : ∀ (vs : List A) x {v} → vs ‼ x ≡ just v → x < length vs
‼-just (u ∷ vs) zero _ = s≤s z≤n
‼-just (u ∷ vs) (suc x) e = s≤s (‼-just vs x e)

replicate-‼ : ∀ n {a : A} x → x < n → replicate n a ‼ x ≡ just a
replicate-‼ (suc n) zero _ = refl
replicate-‼ (suc n) (suc x) (s≤s x<) = replicate-‼ n x x<

replicate-‼-just : ∀ n {a b : A} x → replicate n a ‼ x ≡ just b → b ≡ a
replicate-‼-just (suc n) zero refl = refl
replicate-‼-just (suc n) (suc x) e = replicate-‼-just n x e

‼-split : ∀ (vs : List A) k {b} → vs ‼ k ≡ just b → Σ[ xs ∈ List A ] Σ[ ys ∈ List A ] vs ≡ xs ++ b ∷ ys × length xs ≡ k
‼-split (x ∷ vs) zero refl = [] , vs , refl , refl
‼-split (x ∷ vs) (suc k) e with ‼-split vs k e
... | xs , ys , refl , refl = x ∷ xs , ys , refl , refl

{- element k of the reverse of a list, counting from its end -}
reverse-‼-split : ∀ (vs : List A) k {b} → reverse vs ‼ k ≡ just b
  → Σ[ xs ∈ List A ] Σ[ ys ∈ List A ] vs ≡ xs ++ b ∷ ys × length ys ≡ k
reverse-‼-split vs k {b} e with ‼-split (reverse vs) k e
... | xs , ys , e' , refl =
  reverse ys , reverse xs
  , trans (sym (reverse-involutive vs))
      (trans (cong reverse e')
        (trans (reverse-++ xs (b ∷ ys))
          (trans (cong (_++ reverse xs) (unfold-reverse b ys)) (++-assoc (reverse ys) [ b ] (reverse xs)))))
  , length-reverse xs

reverse-‼-suffix : ∀ (xs : List A) b ys → reverse (xs ++ b ∷ ys) ‼ length ys ≡ just b
reverse-‼-suffix xs b ys =
  trans (cong (_‼ length ys)
          (trans (reverse-++ xs (b ∷ ys))
            (trans (cong (_++ reverse xs) (unfold-reverse b ys)) (++-assoc (reverse ys) [ b ] (reverse xs)))))
        (trans (cong (λ m → (reverse ys ++ b ∷ reverse xs) ‼ m) (sym (length-reverse ys))) (‼-++ (reverse ys)))

length-snoc : ∀ (vs : List A) v → length (vs ∷ʳ v) ≡ suc (length vs)
length-snoc [] v = refl
length-snoc (u ∷ vs) v = cong suc (length-snoc vs v)

module _ {R : A → B → Set} where

  has-length-pw : ∀ n {vs ws} → Pointwise R vs ws → has-length n vs ≡ has-length n ws
  has-length-pw zero [] = refl
  has-length-pw zero (_ ∷ _) = refl
  has-length-pw (suc n) [] = refl
  has-length-pw (suc n) (_ ∷ rs) = has-length-pw n rs

  proj-pw : ∀ {n} (i : Fin n) {vs ws} → Pointwise R vs ws → M.Pointwise R (proj i vs) (proj i ws)
  proj-pw zero [] = M.nothing
  proj-pw (suc i) [] = M.nothing
  proj-pw (suc i) (r ∷ rs) = proj-pw i rs
  proj-pw {n = suc n} zero {_ ∷ vs} {_ ∷ ws} (r ∷ rs) rewrite has-length-pw n rs
    with has-length n ws
  ... | true = M.just r
  ... | false = M.nothing

