open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Framework.abt.Sig using (Sig)
open import Framework.abt.Var using (Var)

{-
  Renaming the variables of a term. A cleared argument (∁) cannot see the
  variables around it, so renaming leaves it unchanged.
-}
module Framework.Syntax.Rename (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
  renaming (ABT to AST)

{- the renaming for the body of a binder -}
ext : (Var → Var) → Var → Var
ext r zero = zero
ext r (suc x) = suc (r x)

rename : (Var → Var) → AST → AST
rename-arg : ∀ {b} → (Var → Var) → Arg b → Arg b
rename-args : ∀ {bs} → (Var → Var) → Args bs → Args bs

rename r (` x) = ` (r x)
rename r (op ⦅ args ⦆) = op ⦅ rename-args r args ⦆

rename-arg r (ast M) = ast (rename r M)
rename-arg r (bind a) = bind (rename-arg (ext r) a)
rename-arg r (clear a) = clear a

rename-args r nil = nil
rename-args r (cons a args) = cons (rename-arg r a) (rename-args r args)

{- shift every variable up by one, to put a term under one more binder -}
shift : AST → AST
shift = rename suc

{- Renaming lemmas ----------------------------------------------------------------}

private
  Pw : (Var → Var) → (Var → Var) → Set
  Pw f g = ∀ x → f x ≡ g x

ext-cong : ∀ {f g} → Pw f g → Pw (ext f) (ext g)
ext-cong eq zero = refl
ext-cong eq (suc x) = cong suc (eq x)

rename-cong : ∀ {f g} → Pw f g → ∀ M → rename f M ≡ rename g M
rename-cong-arg : ∀ {f g b} → Pw f g → (a : Arg b) → rename-arg f a ≡ rename-arg g a
rename-cong-args : ∀ {f g bs} → Pw f g → (as : Args bs) → rename-args f as ≡ rename-args g as
rename-cong eq (` x) = cong `_ (eq x)
rename-cong eq (op ⦅ as ⦆) = cong (op ⦅_⦆) (rename-cong-args eq as)
rename-cong-arg eq (ast M) = cong ast (rename-cong eq M)
rename-cong-arg eq (bind a) = cong bind (rename-cong-arg (ext-cong eq) a)
rename-cong-arg eq (clear a) = refl
rename-cong-args eq nil = refl
rename-cong-args eq (cons a as) = cong₂ cons (rename-cong-arg eq a) (rename-cong-args eq as)

rename-fuse : ∀ f g M → rename f (rename g M) ≡ rename (λ x → f (g x)) M
rename-fuse-arg : ∀ f g {b} (a : Arg b)
  → rename-arg f (rename-arg g a) ≡ rename-arg (λ x → f (g x)) a
rename-fuse-args : ∀ f g {bs} (as : Args bs)
  → rename-args f (rename-args g as) ≡ rename-args (λ x → f (g x)) as
rename-fuse f g (` x) = refl
rename-fuse f g (op ⦅ as ⦆) = cong (op ⦅_⦆) (rename-fuse-args f g as)
rename-fuse-arg f g (ast M) = cong ast (rename-fuse f g M)
rename-fuse-arg f g (bind a) =
  cong bind (trans (rename-fuse-arg (ext f) (ext g) a) (rename-cong-arg ext-fuse a))
  where ext-fuse : Pw (λ x → ext f (ext g x)) (ext (λ x → f (g x)))
        ext-fuse zero = refl
        ext-fuse (suc x) = refl
rename-fuse-arg f g (clear a) = refl
rename-fuse-args f g nil = refl
rename-fuse-args f g (cons a as) = cong₂ cons (rename-fuse-arg f g a) (rename-fuse-args f g as)

rename-id : ∀ M → rename (λ x → x) M ≡ M
rename-id-arg : ∀ {f b} → Pw f (λ x → x) → (a : Arg b) → rename-arg f a ≡ a
rename-id-args : ∀ {f bs} → Pw f (λ x → x) → (as : Args bs) → rename-args f as ≡ as
rename-id (` x) = refl
rename-id (op ⦅ as ⦆) = cong (op ⦅_⦆) (rename-id-args (λ x → refl) as)
rename-id-arg eq (ast M) = cong ast (trans (rename-cong eq M) (rename-id M))
rename-id-arg eq (bind a) = cong bind (rename-id-arg (λ { zero → refl ; (suc x) → cong suc (eq x) }) a)
rename-id-arg eq (clear a) = refl
rename-id-args eq nil = refl
rename-id-args eq (cons a as) = cong₂ cons (rename-id-arg eq a) (rename-id-args eq as)
