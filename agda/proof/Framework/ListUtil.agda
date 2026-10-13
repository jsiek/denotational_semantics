{-

  Lemmas about the list operations of Framework/ListUtil.agda.

-}

module proof.Framework.ListUtil where

open import Framework.ListUtil public

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; [_]; length; replicate; reverse)
import Data.List
import Data.Maybe
open import Data.List.Properties using (++-assoc; reverse-++; unfold-reverse; reverse-involutive; length-reverse; reverse-map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Framework.abt.Sig using (■)
open import Framework.abt.AbstractBindingTree using (ABT; Args)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil)

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

  ‼-pw : ∀ {xs ys} → Pointwise R xs ys → ∀ k → M.Pointwise R (xs ‼ k) (ys ‼ k)
  ‼-pw [] k = M.nothing
  ‼-pw (r ∷ rs) zero = M.just r
  ‼-pw (r ∷ rs) (suc k) = ‼-pw rs k

  proj-pw : ∀ {n} (i : Fin n) {vs ws} → Pointwise R vs ws → M.Pointwise R (proj i vs) (proj i ws)
  proj-pw zero [] = M.nothing
  proj-pw (suc i) [] = M.nothing
  proj-pw (suc i) (r ∷ rs) = proj-pw i rs
  proj-pw {n = suc n} zero {_ ∷ vs} {_ ∷ ws} (r ∷ rs) rewrite has-length-pw n rs
    with has-length n ws
  ... | true = M.just r
  ... | false = M.nothing


{- projecting from a mapped list -}
has-length-map : ∀ (f : A → B) n (vs : List A) → has-length n (Data.List.map f vs) ≡ has-length n vs
has-length-map f zero [] = refl
has-length-map f zero (_ ∷ _) = refl
has-length-map f (suc n) [] = refl
has-length-map f (suc n) (v ∷ vs) = has-length-map f n vs

proj-map : ∀ (f : A → B) {n} (i : Fin n) (vs : List A) → proj i (Data.List.map f vs) ≡ Data.Maybe.map f (proj i vs)
proj-map f zero [] = refl
proj-map f (suc i) [] = refl
proj-map f (suc i) (v ∷ vs) = proj-map f i vs
proj-map f {suc n} zero (v ∷ vs) rewrite has-length-map f n vs with has-length n vs
... | true = refl
... | false = refl

‼-map : ∀ (f : A → B) (xs : List A) k → Data.List.map f xs ‼ k ≡ Data.Maybe.map f (xs ‼ k)
‼-map f [] k = refl
‼-map f (x ∷ xs) zero = refl
‼-map f (x ∷ xs) (suc k) = ‼-map f xs k

{- element k of the reverse of a mapped list (a table of definitions) -}
reverse-map-‼ : ∀ (f : A → B) (xs : List A) k
  → reverse (Data.List.map f xs) ‼ k ≡ Data.Maybe.map f (reverse xs ‼ k)
reverse-map-‼ f xs k = trans (cong (_‼ k) (sym (reverse-map f xs))) (‼-map f (reverse xs) k)

‼-any : ∀ (xs : List A) k {x} → xs ‼ k ≡ just x → Any (x ≡_) xs
‼-any (y ∷ xs) zero refl = here refl
‼-any (y ∷ xs) (suc k) eq = there (‼-any xs k eq)

{- listing the result of a map over the subterms of a tuple, given the
   defining equation of the map -}
args→list-hom : ∀ {Op sig Op' sig'} (f : ABT Op sig → ABT Op' sig')
  (g : ∀ {n} → Args Op sig (replicate n ■) → Args Op' sig' (replicate n ■))
  → (∀ {n} M (as : Args Op sig (replicate n ■)) → g (M ,, as) ≡ f M ,, g as)
  → ∀ {n} (as : Args Op sig (replicate n ■)) → args→list (g as) ≡ Data.List.map f (args→list as)
args→list-hom f g cons {zero} Nil = refl
args→list-hom f g cons {suc n} (M ,, as) rewrite cons M as = cong (f M ∷_) (args→list-hom f g cons as)
