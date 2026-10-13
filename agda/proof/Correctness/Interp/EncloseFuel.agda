{-

  Correctness of the enclose pass (ISWIM → Clos2), clock for clock (see
  the design note in Clock.agda): for every clock, a term and its
  enclosure, in related environments, both time out, both go wrong, or
  return related values. Enclose maps each application to one
  application, so the two interpreters call functions in lock step.

  Values are related (_≈_) when they agree, except that an ISWIM closure
  of N and environment ρ is related to a Clos2 closure of enclose N whose
  captured values agree with ρ on every variable N uses (Agree).

  Agree M k ρ₁ ρ₂ says that M, under k binders, finds related values in
  ρ₁ and ρ₂ for the variables it uses, and that the Clos2 environment ρ₂
  covers the bound of M, so that every variable a closure captures is
  defined. The end theorem is for closed programs.

-}

module proof.Correctness.Interp.EncloseFuel where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import proof.Framework.Syntax.Uses Op sig
open import Compiler.Optimize using (bind-n-ast)
open import Compiler.Enclose
open import proof.Compiler.EncloseScope using (Closed)
open import Semantics.Observation
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import proof.Framework.ListUtil using (_‼_; ‼-<; proj-pw)
open import proof.Semantics.Interp.Clock
import Semantics.Interp.ISWIM as S
import Semantics.Interp.Clos2 as T

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-pred; m≤m⊔n; m≤n⊔m; +-monoʳ-≤; m≤n+m∸n;
         +-identityʳ; +-suc; n≤1+n; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂)

{- The relation -----------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → T.Val → Set
Lookup : ℕ → S.Env → T.Env → Set
data Agree (M : AST) (k : ℕ) (ρ₁ : S.Env) (ρ₂ : T.Env) : Set

data _≈_ where
  clo≈ : ∀ {N ρ vs} → Agree N 1 ρ vs → S.clo N ρ ≈ T.clos (enclose N) vs
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

Lookup x ρ₁ ρ₂ =
  Σ[ v ∈ S.Val ] Σ[ w ∈ T.Val ] (ρ₁ ‼ x ≡ just v) × (ρ₂ ‼ x ≡ just w) × v ≈ w

data Agree M k ρ₁ ρ₂ where
  agree : (∀ x → Uses (k + x) M → Lookup x ρ₁ ρ₂) → bound M ≤ k + length ρ₂ → Agree M k ρ₁ ρ₂

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ T.obs-list ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

{- related operands give related results of a primitive -}
prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (S.prim? p v₁ v₂) (T.prim? p w₁ w₂)
prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (T.obs w₁) (T.obs w₂)
... | nothing = M.nothing
... | just (int n) = M.just const≈
... | just (bool true) = M.just (inl≈ (tup≈ []))
... | just (bool false) = M.just (inr≈ (tup≈ []))

{- Agreement of environments ---------------------------------------------------}

agree-ext : ∀ {M ρ₁ ρ₂ v w} → v ≈ w → Agree M 1 ρ₁ ρ₂ → Agree M 0 (v ∷ ρ₁) (w ∷ ρ₂)
agree-ext {M} {ρ₁} {ρ₂} {v} {w} r (agree look b) = agree look' b
  where
  look' : ∀ x → Uses x M → Lookup x (v ∷ ρ₁) (w ∷ ρ₂)
  look' zero _ = v , w , refl , refl , r
  look' (suc x) u = look x u

{- a subterm M' of M, under k binders -}
agree-sub : ∀ {k M M' ρ₁ ρ₂} → (∀ x → Uses (k + x) M' → Uses x M)
  → bound M' ≤ k + bound M → Agree M 0 ρ₁ ρ₂ → Agree M' k ρ₁ ρ₂
agree-sub {k} sub b (agree look b₀) = agree (λ x u → look x (sub x u)) (≤-trans b (+-monoʳ-≤ k b₀))

⊔-left : ∀ {m n} → m ≤ m ⊔ n
⊔-left {m} {n} = m≤m⊔n m n

⊔-right : ∀ {k m n} → m ≤ k ⊔ (m ⊔ n)
⊔-right {k} {m} {n} = ≤-trans (m≤m⊔n m n) (m≤n⊔m k _)

body-bind : ∀ m N → T.body m (bind-n-ast m N) ≡ N
body-bind zero N = refl
body-bind (suc m) N = body-bind m N

{- evaluating the captured variables ` (j - 1) , ... , ` 0 -}
capture : ∀ ck j {vs ρ} → j ≤ length ρ
  → Σ[ vs' ∈ List T.Val ] T.eval-args ck ρ vs (fv-vars j) ≡ ret vs'
      × length vs' ≡ j + length vs
      × (∀ x → x < j → vs' ‼ x ≡ ρ ‼ x)
      × (∀ x → vs' ‼ (j + x) ≡ vs ‼ x)
capture ck zero {vs} j≤ = vs , refl , refl , (λ x ()) , (λ x → refl)
capture ck (suc j) {vs} {ρ} j< with ‼-< ρ j j<
... | v , eq rewrite eq with capture ck j {v ∷ vs} {ρ} (≤-trans (n≤1+n j) j<)
...   | vs' , ev , len , pre , suf = vs' , ev , trans len (+-suc j _) , pre' , suf'
  where
  pre' : ∀ x → x < suc j → vs' ‼ x ≡ ρ ‼ x
  pre' x x< with m≤n⇒m<n∨m≡n (≤-pred x<)
  ... | inj₁ x<j = pre x x<j
  ... | inj₂ refl = trans (subst (λ y → vs' ‼ y ≡ just v) (+-identityʳ x) (suf 0)) (sym eq)

  suf' : ∀ x → vs' ‼ (suc j + x) ≡ vs ‼ x
  suf' x = trans (cong (vs' ‼_) (sym (+-suc j x))) (suf (suc x))

{- Clock for clock ---------------------------------------------------------------}

run≈ : ∀ ck {ρ₁ ρ₂} M → Agree M 0 ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (enclose M))
args≈ : ∀ ck {n ρ₁ ρ₂ vs ws} (args : Args (replicate n ■)) → Agree (tuple n ⦅ args ⦆) 0 ρ₁ ρ₂
  → Pointwise _≈_ vs ws
  → RelResult (Pointwise _≈_) (S.eval-args ck ρ₁ vs args) (T.eval-args ck ρ₂ ws (enc-args args))
apply≈ : ∀ ck {ρ₁ ρ₂ f g} M → Agree M 0 ρ₁ ρ₂ → f ≈ g
  → RelResult _≈_ (S.apply ck ρ₁ M f) (T.apply ck ρ₂ (enclose M) g)
call≈ : ∀ ck {ρ₁ ρ₂} N → Agree N 0 ρ₁ ρ₂
  → RelResult _≈_ (S.call ck N ρ₁) (T.call ck (enclose N) ρ₂)
branch≈ : ∀ ck {ρ₁ ρ₂ v w} M N → Agree M 1 ρ₁ ρ₂ → Agree N 1 ρ₁ ρ₂ → v ≈ w
  → RelResult _≈_ (S.branch ck ρ₁ M N v) (T.branch ck ρ₂ (enclose M) (enclose N) w)

run≈ ck {ρ₁} {ρ₂} (` x) (agree look _) with look x refl
... | v , w , e₁ , e₂ , r rewrite e₁ | e₂ = ret r
run≈ ck {ρ₁} {ρ₂} (lam ⦅ ⟩ N ,, Nil ⦆) (agree look b)
  with capture ck (bound N ∸ 1) {[]} {ρ₂} (≤-trans (m≤m⊔n (bound N ∸ 1) 0) b)
... | vs' , ev , len , pre , suf rewrite ev | body-bind (bound N ∸ 1) (enclose N) =
  ret (clo≈ (agree look' b'))
  where
  look' : ∀ x → Uses (suc x) N → Lookup x ρ₁ vs'
  look' x u with look x (inj₁ u)
  ... | v , w , e₁ , e₂ , r = v , w , e₁ , trans (pre x (<-∸1 (uses-bound (suc x) N u))) e₂ , r

  b' : bound N ≤ 1 + length vs'
  b' rewrite len | +-identityʳ (bound N ∸ 1) = m≤n+m∸n (bound N) 1
run≈ ck (app ⦅ L ,, M ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub (λ x → inj₁) ⊔-left ag))
           (apply≈ ck M (agree-sub (λ x u → inj₂ (inj₁ u)) (⊔-right {bound L}) ag))
run≈ ck (lit B k ⦅ Nil ⦆) ag = ret const≈
run≈ ck (tuple n ⦅ args ⦆) ag = bind-rel (args≈ ck args ag []) (λ rs → ret (tup≈ (reverse⁺ rs)))
run≈ ck (get i ⦅ M ,, Nil ⦆) ag = bind-rel (run≈ ck M (agree-sub (λ x → inj₁) ⊔-left ag)) get≈
  where
  get≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (S.project i v) (T.project i w)
  get≈ (tup≈ rs) = from-maybe-rel (proj-pw i rs)
  get≈ (clo≈ _) = wrong
  get≈ const≈ = wrong
  get≈ (inl≈ _) = wrong
  get≈ (inr≈ _) = wrong
run≈ ck (inl-op ⦅ M ,, Nil ⦆) ag =
  bind-rel (run≈ ck M (agree-sub (λ x → inj₁) ⊔-left ag)) (λ r → ret (inl≈ r))
run≈ ck (inr-op ⦅ M ,, Nil ⦆) ag =
  bind-rel (run≈ ck M (agree-sub (λ x → inj₁) ⊔-left ag)) (λ r → ret (inr≈ r))
run≈ ck (prim p ⦅ L ,, M ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub (λ x → inj₁) ⊔-left ag)) λ r →
  bind-rel (run≈ ck M (agree-sub (λ x u → inj₂ (inj₁ u)) (⊔-right {bound L}) ag)) λ s →
  from-maybe-rel (prim≈ p r s)
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub (λ x → inj₁) ⊔-left ag))
    (branch≈ ck M N
      (agree-sub (λ x u → inj₂ (inj₁ u))
                 (≤-trans (m≤n+m∸n (bound M) 1) (s≤s (⊔-right {bound L}))) ag)
      (agree-sub (λ x u → inj₂ (inj₂ (inj₁ u)))
                 (≤-trans (m≤n+m∸n (bound N) 1)
                   (s≤s (≤-trans (m≤m⊔n (bound N ∸ 1) 0)
                     (≤-trans (m≤n⊔m (bound M ∸ 1) _) (m≤n⊔m (bound L) _))))) ag))

args≈ ck {zero} Nil ag rs = ret rs
args≈ ck {suc n} (M ,, args) ag rs =
  bind-rel (run≈ ck M (agree-sub (λ x → inj₁) ⊔-left ag))
           (λ r → args≈ ck args (agree-sub (λ x → inj₂) (m≤n⊔m (bound M) _) ag) (r ∷ rs))

apply≈ ck M ag (clo≈ {N} agN) = bind-rel (run≈ ck M ag) (λ r → call≈ ck N (agree-ext r agN))
apply≈ ck M ag const≈ = wrong
apply≈ ck M ag (tup≈ _) = wrong
apply≈ ck M ag (inl≈ _) = wrong
apply≈ ck M ag (inr≈ _) = wrong

call≈ zero N ag = timeout
call≈ (suc ck) N ag = run≈ ck N ag

branch≈ ck M N agM agN (inl≈ r) = run≈ ck M (agree-ext r agM)
branch≈ ck M N agM agN (inr≈ r) = run≈ ck N (agree-ext r agN)
branch≈ ck M N agM agN (clo≈ _) = wrong
branch≈ ck M N agM agN const≈ = wrong
branch≈ ck M N agM agN (tup≈ _) = wrong

{- The end theorem -------------------------------------------------------------}

agree-closed : ∀ M → Closed M → Agree M 0 [] []
agree-closed M c = agree (λ x u → ⊥-elim (x<0 (subst (x <_) c (uses-bound x M u)))) (subst (_≤ 0) (sym c) z≤n)
  where x<0 : ∀ {x} → x < 0 → ⊥
        x<0 ()

enclose-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M c = clocked _≈_ obs≈ (λ ck → run≈ ck M (agree-closed M c))
