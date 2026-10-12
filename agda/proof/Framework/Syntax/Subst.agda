open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-pred; m≤n⇒m<n∨m≡n)
open import Data.List using (List; replicate)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Framework.abt.Sig using (Sig; ■)
open import Framework.abt.Var using (Var)

{-
  Lemmas about substitution (Framework/Syntax/Subst.agda): congruence,
  identity, renaming as a substitution, and the fusion of renamings and
  substitutions, after the σ-calculus.
-}
module proof.Framework.Syntax.Subst (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
  renaming (ABT to AST)
open import proof.Framework.Syntax.Rename Op sig using (ext; rename; rename-arg; rename-args; rename-fuse)
open import Framework.Syntax.Subst Op sig public

infix 4 _≗_
_≗_ : Subst → Subst → Set
σ ≗ τ = ∀ x → σ x ≡ τ x

exts-cong : ∀ {σ τ} → σ ≗ τ → exts σ ≗ exts τ
exts-cong eq zero = refl
exts-cong eq (suc x) = cong (rename suc) (eq x)

sub-cong : ∀ {σ τ} → σ ≗ τ → ∀ M → sub σ M ≡ sub τ M
sub-cong-arg : ∀ {σ τ b} → σ ≗ τ → (a : Arg b) → sub-arg σ a ≡ sub-arg τ a
sub-cong-args : ∀ {σ τ bs} → σ ≗ τ → (as : Args bs) → sub-args σ as ≡ sub-args τ as
sub-cong eq (` x) = eq x
sub-cong eq (op ⦅ as ⦆) = cong (op ⦅_⦆) (sub-cong-args eq as)
sub-cong-arg eq (ast M) = cong ast (sub-cong eq M)
sub-cong-arg eq (bind a) = cong bind (sub-cong-arg (exts-cong eq) a)
sub-cong-arg eq (clear a) = refl
sub-cong-args eq nil = refl
sub-cong-args eq (cons a as) = cong₂ cons (sub-cong-arg eq a) (sub-cong-args eq as)

sub-id : ∀ M → sub ids M ≡ M
sub-id-arg : ∀ {σ b} → σ ≗ ids → (a : Arg b) → sub-arg σ a ≡ a
sub-id-args : ∀ {σ bs} → σ ≗ ids → (as : Args bs) → sub-args σ as ≡ as
sub-id (` x) = refl
sub-id (op ⦅ as ⦆) = cong (op ⦅_⦆) (sub-id-args (λ x → refl) as)
sub-id-arg eq (ast M) = cong ast (trans (sub-cong eq M) (sub-id M))
sub-id-arg eq (bind a) = cong bind (sub-id-arg (λ { zero → refl ; (suc x) → cong (rename suc) (eq x) }) a)
sub-id-arg eq (clear a) = refl
sub-id-args eq nil = refl
sub-id-args eq (cons a as) = cong₂ cons (sub-id-arg eq a) (sub-id-args eq as)

{- renaming is substitution by variables -}
rename-sub : ∀ r M → rename r M ≡ sub (λ x → ` r x) M
rename-sub-arg : ∀ r {σ b} → σ ≗ (λ x → ` r x) → (a : Arg b) → rename-arg r a ≡ sub-arg σ a
rename-sub-args : ∀ r {σ bs} → σ ≗ (λ x → ` r x) → (as : Args bs)
  → rename-args r as ≡ sub-args σ as
rename-sub r (` x) = refl
rename-sub r (op ⦅ as ⦆) = cong (op ⦅_⦆) (rename-sub-args r (λ x → refl) as)
rename-sub-arg r eq (ast M) = cong ast (trans (rename-sub r M) (sym (sub-cong eq M)))
rename-sub-arg r eq (bind a) =
  cong bind (rename-sub-arg (ext r) (λ { zero → refl ; (suc x) → cong (rename suc) (eq x) }) a)
rename-sub-arg r eq (clear a) = refl
rename-sub-args r eq nil = refl
rename-sub-args r eq (cons a as) = cong₂ cons (rename-sub-arg r eq a) (rename-sub-args r eq as)

{- substituting after renaming -}
ren-sub : ∀ τ r M → sub τ (rename r M) ≡ sub (λ x → τ (r x)) M
ren-sub-arg : ∀ τ r {b} (a : Arg b) → sub-arg τ (rename-arg r a) ≡ sub-arg (λ x → τ (r x)) a
ren-sub-args : ∀ τ r {bs} (as : Args bs)
  → sub-args τ (rename-args r as) ≡ sub-args (λ x → τ (r x)) as
ren-sub τ r (` x) = refl
ren-sub τ r (op ⦅ as ⦆) = cong (op ⦅_⦆) (ren-sub-args τ r as)
ren-sub-arg τ r (ast M) = cong ast (ren-sub τ r M)
ren-sub-arg τ r (bind a) =
  cong bind (trans (ren-sub-arg (exts τ) (ext r) a)
                   (sub-cong-arg (λ { zero → refl ; (suc x) → refl }) a))
ren-sub-arg τ r (clear a) = refl
ren-sub-args τ r nil = refl
ren-sub-args τ r (cons a as) = cong₂ cons (ren-sub-arg τ r a) (ren-sub-args τ r as)

{- renaming after substituting -}
sub-ren : ∀ r σ M → rename r (sub σ M) ≡ sub (λ x → rename r (σ x)) M
sub-ren-arg : ∀ r σ {b} (a : Arg b) → rename-arg r (sub-arg σ a) ≡ sub-arg (λ x → rename r (σ x)) a
sub-ren-args : ∀ r σ {bs} (as : Args bs)
  → rename-args r (sub-args σ as)
    ≡ sub-args (λ x → rename r (σ x)) as
sub-ren r σ (` x) = refl
sub-ren r σ (op ⦅ as ⦆) = cong (op ⦅_⦆) (sub-ren-args r σ as)
sub-ren-arg r σ (ast M) = cong ast (sub-ren r σ M)
sub-ren-arg r σ (bind a) =
  cong bind (trans (sub-ren-arg (ext r) (exts σ) a) (sub-cong-arg eq a))
  where eq : (λ x → rename (ext r) (exts σ x)) ≗ exts (λ x → rename r (σ x))
        eq zero = refl
        eq (suc x) = trans (rename-fuse (ext r) suc (σ x)) (sym (rename-fuse suc r (σ x)))
sub-ren-arg r σ (clear a) = refl
sub-ren-args r σ nil = refl
sub-ren-args r σ (cons a as) = cong₂ cons (sub-ren-arg r σ a) (sub-ren-args r σ as)

{- substituting twice -}
sub-sub : ∀ τ σ M → sub τ (sub σ M) ≡ sub (λ x → sub τ (σ x)) M
sub-sub-arg : ∀ τ σ {b} (a : Arg b) → sub-arg τ (sub-arg σ a) ≡ sub-arg (λ x → sub τ (σ x)) a
sub-sub-args : ∀ τ σ {bs} (as : Args bs) → sub-args τ (sub-args σ as) ≡ sub-args (λ x → sub τ (σ x)) as
sub-sub τ σ (` x) = refl
sub-sub τ σ (op ⦅ as ⦆) = cong (op ⦅_⦆) (sub-sub-args τ σ as)
sub-sub-arg τ σ (ast M) = cong ast (sub-sub τ σ M)
sub-sub-arg τ σ (bind a) =
  cong bind (trans (sub-sub-arg (exts τ) (exts σ) a) (sub-cong-arg eq a))
  where eq : (λ x → sub (exts τ) (exts σ x)) ≗ exts (λ x → sub τ (σ x))
        eq zero = refl
        eq (suc x) = trans (ren-sub (exts τ) suc (σ x)) (sym (sub-ren suc τ (σ x)))
sub-sub-arg τ σ (clear a) = refl
sub-sub-args τ σ nil = refl
sub-sub-args τ σ (cons a as) = cong₂ cons (sub-sub-arg τ σ a) (sub-sub-args τ σ as)

{- substituting into a shifted term, and into the body of a binder -}
sub-shift : ∀ M σ N → sub (M • σ) (rename suc N) ≡ sub σ N
sub-shift M σ N = ren-sub (M • σ) suc N

sub-exts : ∀ M τ σ N → sub (M • τ) (sub (exts σ) N) ≡ sub (M • (λ x → sub τ (σ x))) N
sub-exts M τ σ N = trans (sub-sub (M • τ) (exts σ) N) (sub-cong eq N)
  where eq : (λ x → sub (M • τ) (exts σ x)) ≗ (M • (λ x → sub τ (σ x)))
        eq zero = refl
        eq (suc x) = sub-shift M τ (σ x)

{- the substitution of the body of a binder, then the bound value -}
exts-[] : ∀ V σ N → sub (exts σ) N [ V ] ≡ sub (V • σ) N
exts-[] V σ N = trans (sub-exts V ids σ N) (sub-cong (λ { zero → refl ; (suc x) → sub-id (σ x) }) N)

{- substitution commutes with going under a binder -}
exts-sub-comm : ∀ τ σ → (λ x → sub (exts τ) (exts σ x)) ≗ exts (λ x → sub τ (σ x))
exts-sub-comm τ σ zero = refl
exts-sub-comm τ σ (suc x) = trans (ren-sub (exts τ) suc (σ x)) (sym (sub-ren suc τ (σ x)))

{- extending by the operands of a tuple -}
extend-skip : ∀ {n} (Ms : Args (replicate n ■)) σ x → extend Ms σ (n + x) ≡ σ x
extend-skip {zero} nil σ x = refl
extend-skip {suc n} (cons (ast M) Ms) σ x =
  trans (cong (extend Ms (M • σ)) (sym (+-suc n x))) (extend-skip Ms (M • σ) (suc x))

extend-sub : ∀ τ {n} (Ms : Args (replicate n ■)) σ σ' k → k < n
  → extend (sub-args τ Ms) σ' k ≡ sub τ (extend Ms σ k)
extend-sub τ {suc n} (cons (ast M) Ms) σ σ' k k< with m≤n⇒m<n∨m≡n (≤-pred k<)
... | inj₁ k<n = extend-sub τ Ms (M • σ) (sub τ M • σ') k k<n
... | inj₂ refl =
  trans (subst (λ y → extend (sub-args τ Ms) (sub τ M • σ') y ≡ sub τ M) (+-identityʳ n)
               (extend-skip (sub-args τ Ms) (sub τ M • σ') 0))
        (cong (sub τ) (sym (subst (λ y → extend Ms (M • σ) y ≡ M) (+-identityʳ n)
                                  (extend-skip Ms (M • σ) 0))))

{- substituting under a binder into a shifted term -}
exts-shift : ∀ σ M → sub (exts σ) (rename suc M) ≡ rename suc (sub σ M)
exts-shift σ M = trans (ren-sub (exts σ) suc M) (sym (sub-ren suc σ M))
