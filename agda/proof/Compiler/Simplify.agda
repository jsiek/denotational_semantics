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
open import Framework.Syntax.Uses Op sig using (bound; bound-args)
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Compiler.EncloseScope using (Closed)
open import Data.Nat using (_≤_; _⊔_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ≤-trans; m≤n+m∸n)
open import Data.Unit using (tt)

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

{- what simplify's tests on known values found -}
comp-inv : ∀ {n} (i : Fin n) k {K} → component i k ≡ just K
  → Σ[ m ∈ ℕ ] Σ[ Ks ∈ Args (replicate m ■) ] k ≡ just (tuple m ⦅ Ks ⦆) × proj i (args→list Ks) ≡ just K
comp-inv i (just (tuple m ⦅ Ks ⦆)) e = m , Ks , refl , e

int-inv : ∀ k {n} → int-of k ≡ just n → k ≡ just (lit Int n ⦅ Nil ⦆)
int-inv (just (lit Int n ⦅ Nil ⦆)) refl = refl

branch-inl : ∀ k {K} → branch k ≡ just (true , K) → k ≡ just (inl-op ⦅ K ,, Nil ⦆) × small K ≡ true
branch-inl (just (inl-op ⦅ K ,, Nil ⦆)) e with small K in s | e
... | true | refl = refl , s
branch-inl (just (inr-op ⦅ K ,, Nil ⦆)) e with small K | e
... | true | ()

branch-inr : ∀ k {K} → branch k ≡ just (false , K) → k ≡ just (inr-op ⦅ K ,, Nil ⦆) × small K ≡ true
branch-inr (just (inr-op ⦅ K ,, Nil ⦆)) e with small K in s | e
... | true | refl = refl , s
branch-inr (just (inl-op ⦅ K ,, Nil ⦆)) e with small K | e
... | true | ()

{- a closed program is well scoped -}
private
  l : ∀ m n {o} → m ⊔ n ≤ o → m ≤ o
  l m n = m⊔n≤o⇒m≤o m n
  r : ∀ m n {o} → m ⊔ n ≤ o → n ≤ o
  r m n = m⊔n≤o⇒n≤o m n
  bind≤ : ∀ m {k} → m ∸ 1 ≤ k → m ≤ suc k
  bind≤ m le = ≤-trans (m≤n+m∸n m 1) (s≤s le)

bound-ws : ∀ {k} M → bound M ≤ k → WS k M
bound-ws-args : ∀ {k n} (as : Args (replicate n ■)) → bound-args as ≤ k → WS-args k as
bound-ws (` x) le = le
bound-ws (lam ⦅ ⟩ N ,, Nil ⦆) le = bound-ws N (bind≤ (bound N) (l (bound N ∸ 1) 0 le)) , tt
bound-ws (app ⦅ L ,, M ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le) , bound-ws M (l (bound M) 0 (r (bound L) (bound M ⊔ 0) le)) , tt
bound-ws (lit B k ⦅ Nil ⦆) le = tt
bound-ws (tuple n ⦅ as ⦆) le = bound-ws-args as le
bound-ws (get i ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (inl-op ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (inr-op ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le)
  , bound-ws M (bind≤ (bound M) (l (bound M ∸ 1) _ le₁))
  , bound-ws N (bind≤ (bound N) (l (bound N ∸ 1) 0 (r (bound M ∸ 1) _ le₁)))
  , tt
  where le₁ = r (bound L) ((bound M ∸ 1) ⊔ ((bound N ∸ 1) ⊔ 0)) le
bound-ws (prim p ⦅ L ,, M ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le) , bound-ws M (l (bound M) 0 (r (bound L) (bound M ⊔ 0) le)) , tt
bound-ws-args {n = zero} Nil le = tt
bound-ws-args {n = suc n} (M ,, as) le = bound-ws M (l (bound M) (bound-args as) le) , bound-ws-args as (r (bound M) (bound-args as) le)

closed-ws : ∀ {M} → Closed M → WS 0 M
closed-ws {M} c = bound-ws M (subst (_≤ 0) (sym c) z≤n)

{- value recognizes values -}
sv-value : ∀ {V} → SV V → value V ≡ true
svs-values : ∀ {n} {as : Args (replicate n ■)} → SVs as → values as ≡ true
sv-value (var x) = refl
sv-value lam = refl
sv-value lit = refl
sv-value (tuple vs) = svs-values vs
sv-value (inl v) = sv-value v
sv-value (inr v) = sv-value v
svs-values [] = refl
svs-values (v ∷ vs) rewrite sv-value v = svs-values vs

small-value : ∀ T → small T ≡ true → value T ≡ true
small-value T s = sv-value (small-sv T s)
