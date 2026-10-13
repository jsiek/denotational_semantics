{-

  Syntactic facts about simplify (Compiler/Simplify.agda), used by both
  of its proofs: the values (SV, where a variable stands for a value),
  which value and small recognize and substitution keeps, and what the
  known values that simplify inspects are.

-}

module proof.Compiler.Simplify where

open import Compiler.Simplify public

open import Language.ISWIM
open import Language.Prim using (Out; int; bool)
open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.Syntax.Subst Op sig using (Subst; sub; sub-args; exts)
import proof.Framework.Syntax.Subst Op sig as SS
open import Framework.Syntax.Rename Op sig using (rename)
open import Framework.ListUtil using (proj; args→list; has-length)

open import Data.Bool using (true; false; _∧_)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (replicate)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

{- Values ----------------------------------------------------------------------}

data SV : AST → Set
data SVs : ∀ {n} → Args (replicate n ■) → Set

data SV where
  var : ∀ x → SV (` x)
  lam : ∀ {N} → SV (lam ⦅ ⟩ N ,, Nil ⦆)
  lit : ∀ {B k} → SV (lit B k ⦅ Nil ⦆)
  tuple : ∀ {n as} → SVs as → SV (tuple n ⦅ as ⦆)
  inl : ∀ {V} → SV V → SV (inl-op ⦅ V ,, Nil ⦆)
  inr : ∀ {V} → SV V → SV (inr-op ⦅ V ,, Nil ⦆)

infixr 5 _∷_
data SVs where
  [] : SVs Nil
  _∷_ : ∀ {n V} {as : Args (replicate n ■)} → SV V → SVs as → SVs (V ,, as)

∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true {true} {true} refl = refl , refl

value-sv : ∀ M → value M ≡ true → SV M
values-sv : ∀ {n} (as : Args (replicate n ■)) → values as ≡ true → SVs as
value-sv (` x) _ = var x
value-sv (lam ⦅ ⟩ N ,, Nil ⦆) _ = lam
value-sv (lit B k ⦅ Nil ⦆) _ = lit
value-sv (tuple n ⦅ as ⦆) e = tuple (values-sv as e)
value-sv (inl-op ⦅ M ,, Nil ⦆) e = inl (value-sv M e)
value-sv (inr-op ⦅ M ,, Nil ⦆) e = inr (value-sv M e)
value-sv (app ⦅ _ ⦆) ()
value-sv (get i ⦅ _ ⦆) ()
value-sv (case-op ⦅ _ ⦆) ()
value-sv (prim p ⦅ _ ⦆) ()
values-sv {zero} Nil _ = []
values-sv {suc n} (M ,, as) e with ∧-true {value M} e
... | e₁ , e₂ = value-sv M e₁ ∷ values-sv as e₂

atom-sv : ∀ M → atom M ≡ true → SV M
atom-sv (` x) _ = var x
atom-sv (lit B k ⦅ Nil ⦆) _ = lit
atom-sv (tuple zero ⦅ Nil ⦆) _ = tuple []
atom-sv (tuple (suc n) ⦅ _ ⦆) ()
atom-sv (lam ⦅ _ ⦆) ()
atom-sv (app ⦅ _ ⦆) ()
atom-sv (get i ⦅ _ ⦆) ()
atom-sv (inl-op ⦅ _ ⦆) ()
atom-sv (inr-op ⦅ _ ⦆) ()
atom-sv (case-op ⦅ _ ⦆) ()
atom-sv (prim p ⦅ _ ⦆) ()

small-sv : ∀ M → small M ≡ true → SV M
small-sv (inl-op ⦅ M ,, Nil ⦆) e = inl (atom-sv M e)
small-sv (inr-op ⦅ M ,, Nil ⦆) e = inr (atom-sv M e)
small-sv (` x) e = atom-sv (` x) e
small-sv (lam ⦅ as ⦆) e = atom-sv (lam ⦅ as ⦆) e
small-sv (app ⦅ as ⦆) e = atom-sv (app ⦅ as ⦆) e
small-sv (lit B k ⦅ as ⦆) e = atom-sv (lit B k ⦅ as ⦆) e
small-sv (tuple n ⦅ as ⦆) e = atom-sv (tuple n ⦅ as ⦆) e
small-sv (get i ⦅ as ⦆) e = atom-sv (get i ⦅ as ⦆) e
small-sv (case-op ⦅ as ⦆) e = atom-sv (case-op ⦅ as ⦆) e
small-sv (prim p ⦅ as ⦆) e = atom-sv (prim p ⦅ as ⦆) e

prim-term-sv : ∀ o → SV (prim-term o)
prim-term-sv (int n) = lit
prim-term-sv (bool true) = inl (tuple [])
prim-term-sv (bool false) = inr (tuple [])

{- substitution by values keeps values -}
sv-sub : ∀ {σ V} → (∀ x → SV (σ x)) → SV V → SV (sub σ V)
svs-sub : ∀ {σ n} {as : Args (replicate n ■)} → (∀ x → SV (σ x)) → SVs as → SVs (sub-args σ as)
sv-sub h (var x) = h x
sv-sub h lam = lam
sv-sub h lit = lit
sv-sub h (tuple vs) = tuple (svs-sub h vs)
sv-sub h (inl v) = inl (sv-sub h v)
sv-sub h (inr v) = inr (sv-sub h v)
svs-sub h [] = []
svs-sub h (v ∷ vs) = sv-sub h v ∷ svs-sub h vs

sv-rename : ∀ r {V} → SV V → SV (rename r V)
sv-rename r {V} v = subst SV (sym (SS.rename-sub r V)) (sv-sub (λ x → var (r x)) v)

{- Known values -----------------------------------------------------------------}

{- a known integer is a literal -}
int-of-just : ∀ {K n} → SV K → int-of (just K) ≡ just n → K ≡ lit Int n ⦅ Nil ⦆
int-of-just (lit {Int}) refl = refl

{- a component of a known tuple of values -}
component-just : ∀ {n m} (i : Fin n) {Ks : Args (replicate m ■)} {K}
  → SVs Ks → proj i (args→list Ks) ≡ just K → SV K
component-just zero [] ()
component-just (suc i) [] ()
component-just (suc i) (v ∷ vs) e = component-just i vs e
component-just {suc n} zero {_ ,, Ks} (v ∷ vs) e with has-length n (args→list Ks)
component-just {suc n} zero {_ ,, Ks} (v ∷ vs) refl | true = v
component-just {suc n} zero {_ ,, Ks} (v ∷ vs) () | false
