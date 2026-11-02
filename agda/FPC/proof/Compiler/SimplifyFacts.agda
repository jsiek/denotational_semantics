{-

  Syntactic facts about simplify (Mu/Compiler/Simplify.agda), used by
  its four proofs, as for the untyped simplify
  (proof/Compiler/SimplifyFacts.agda): the values (SV, where a variable
  stands for a value), which value and small recognize and renaming and
  substitution keep, and what the known values that simplify inspects
  are.

-}

module Mu.proof.Compiler.SimplifyFacts where

open import Mu.Compiler.Simplify public

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Mu.Language.FPC
open import Mu.Language.FPCSubst using (Kit; Sub; trav; travs; ren)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Integer using (ℤ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (does)

{- Values ----------------------------------------------------------------------}

data SV {Γ} : ∀ {A} → Tm Γ A → Set
data SVs {Γ} : ∀ {Δ} → All (Tm Γ) Δ → Set

data SV {Γ} where
  var : ∀ {A} (x : Γ ∋ A) → SV (` x)
  lam : ∀ {A B} {N : Tm (A ∷ Γ) B} → SV (lam N)
  lit : ∀ {B c} → SV (lit B c)
  tuple : ∀ {Δ} {Ms : All (Tm Γ) Δ} → SVs Ms → SV (tuple Ms)
  inl : ∀ {A B} {V : Tm Γ A} → SV V → SV (inl {B = B} V)
  inr : ∀ {A B} {V : Tm Γ B} → SV V → SV (inr {A = A} V)
  fold : ∀ {A} {V : Tm Γ (unroll A)} → SV V → SV (fold {A = A} V)

infixr 5 _∷_
data SVs {Γ} where
  [] : SVs []
  _∷_ : ∀ {A Δ} {V : Tm Γ A} {Ms : All (Tm Γ) Δ} → SV V → SVs Ms → SVs (V ∷ Ms)

∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true {true} {true} refl = refl , refl

value-sv : ∀ {Γ A} (M : Tm Γ A) → value M ≡ true → SV M
values-sv : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) → values Ms ≡ true → SVs Ms
value-sv (` x) _ = var x
value-sv (lam N) _ = lam
value-sv (lit B c) _ = lit
value-sv (tuple Ms) e = tuple (values-sv Ms e)
value-sv (inl M) e = inl (value-sv M e)
value-sv (inr M) e = inr (value-sv M e)
value-sv (fold M) e = fold (value-sv M e)
values-sv [] _ = []
values-sv (M ∷ Ms) e with ∧-true {value M} e
... | e₁ , e₂ = value-sv M e₁ ∷ values-sv Ms e₂

atom-sv : ∀ {Γ A} (M : Tm Γ A) → atom M ≡ true → SV M
atom-sv (` x) _ = var x
atom-sv (lit B c) _ = lit
atom-sv (tuple []) _ = tuple []
atom-sv (tuple (_ ∷ _)) ()
atom-sv (lam _) ()
atom-sv (app _ _) ()
atom-sv (get _ _) ()
atom-sv (inl _) ()
atom-sv (inr _) ()
atom-sv (case _ _ _) ()
atom-sv (prim _ _ _) ()
atom-sv (let′ _ _) ()
atom-sv (fold _) ()
atom-sv (unfold _) ()

small-sv : ∀ {Γ A} (M : Tm Γ A) → small M ≡ true → SV M
small-sv (inl M) e = inl (atom-sv M e)
small-sv (inr M) e = inr (atom-sv M e)
small-sv (` x) e = atom-sv (` x) e
small-sv (lit B c) e = atom-sv (lit B c) e
small-sv (tuple Ms) e = atom-sv (tuple Ms) e
small-sv (lam N) e = atom-sv (lam N) e
small-sv (app L M) e = atom-sv (app L M) e
small-sv (get i M) e = atom-sv (get i M) e
small-sv (case L M N) e = atom-sv (case L M N) e
small-sv (prim p L M) e = atom-sv (prim p L M) e
small-sv (let′ M N) e = atom-sv (let′ M N) e
small-sv (fold M) e = atom-sv (fold M) e
small-sv (unfold M) e = atom-sv (unfold M) e

prim-term-sv : ∀ {Γ} p n m → SV (prim-term {Γ} p n m)
prim-term-sv sub n m = lit
prim-term-sv eq n m with does (n ≟ m)
... | true = inl (tuple [])
... | false = inr (tuple [])

{- a traversal by variables or values keeps values -}
sv-trav : ∀ {𝒦 Γ Δ A} {σ : Sub 𝒦 Γ Δ} → (∀ {B} (x : Γ ∋ B) → SV (Kit.tm 𝒦 (σ x))) → {V : Tm Γ A} → SV V → SV (trav 𝒦 σ V)
svs-trav : ∀ {𝒦 Γ Δ Δ'} {σ : Sub 𝒦 Γ Δ} → (∀ {B} (x : Γ ∋ B) → SV (Kit.tm 𝒦 (σ x))) → {Vs : All (Tm Γ) Δ'} → SVs Vs → SVs (travs 𝒦 σ Vs)
sv-trav h (var x) = h x
sv-trav h lam = lam
sv-trav h lit = lit
sv-trav h (tuple vs) = tuple (svs-trav h vs)
sv-trav h (inl v) = inl (sv-trav h v)
sv-trav h (inr v) = inr (sv-trav h v)
sv-trav h (fold v) = fold (sv-trav h v)
svs-trav h [] = []
svs-trav h (v ∷ vs) = sv-trav h v ∷ svs-trav h vs

sv-ren : ∀ {Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) {V : Tm Γ A} → SV V → SV (ren r V)
sv-ren r = sv-trav (λ x → var (r x))

{- value recognizes values -}
sv-value : ∀ {Γ A} {V : Tm Γ A} → SV V → value V ≡ true
svs-values : ∀ {Γ Δ} {Vs : All (Tm Γ) Δ} → SVs Vs → values Vs ≡ true
sv-value (var x) = refl
sv-value lam = refl
sv-value lit = refl
sv-value (tuple vs) = svs-values vs
sv-value (inl v) = sv-value v
sv-value (inr v) = sv-value v
sv-value (fold v) = sv-value v
svs-values [] = refl
svs-values (v ∷ vs) rewrite sv-value v = svs-values vs

small-value : ∀ {Γ A} (T : Tm Γ A) → small T ≡ true → value T ≡ true
small-value T s = sv-value (small-sv T s)

{- Known values -----------------------------------------------------------------}

{- a component of a known tuple of values -}
svs-lookup : ∀ {Γ Δ A} {Ks : All (Tm Γ) Δ} → SVs Ks → (i : Δ ∋ A) → SV (lookup Ks i)
svs-lookup (v ∷ vs) Z = v
svs-lookup (v ∷ vs) (S i) = svs-lookup vs i

{- what simplify's tests on known values found -}
{- (each takes the operand's type generically, with an equation to the
   expected one, as the tests do) -}
int-inv : ∀ {Γ A} (k : Maybe (Known Γ A)) {n} → int-of k ≡ just n
  → Σ[ e ∈ base Int ≡ A ] k ≡ just (val (subst (Tm Γ) e (lit Int n)))
int-inv (just (val (lit Int n))) refl = refl , refl

comp-inv : ∀ {Γ C Δ A} (i : Δ ∋ A) (k : Maybe (Known Γ C)) (e : C ≡ tup Δ) {K} → component i k e ≡ just K
  → Σ[ Ks ∈ All (Tm Γ) Δ ] subst (λ C → Maybe (Known Γ C)) e k ≡ just (val (tuple Ks)) × lookup Ks i ≡ K
comp-inv i (just (val (tuple Ks))) refl refl = Ks , refl , refl

branch-inl : ∀ {Γ C A B} (k : Maybe (Known Γ C)) (e : C ≡ A ⊹ B) {K} → branch k e ≡ just (inj₁ K)
  → subst (λ C → Maybe (Known Γ C)) e k ≡ just (val (inl K)) × small K ≡ true
branch-inl (just (val (inl K))) refl e with small K in s | e
... | true | refl = refl , s
branch-inl (just (val (inr K))) refl e with small K | e
... | true | ()

branch-inr : ∀ {Γ C A B} (k : Maybe (Known Γ C)) (e : C ≡ A ⊹ B) {K} → branch k e ≡ just (inj₂ K)
  → subst (λ C → Maybe (Known Γ C)) e k ≡ just (val (inr K)) × small K ≡ true
branch-inr (just (val (inr K))) refl e with small K in s | e
... | true | refl = refl , s
branch-inr (just (val (inl K))) refl e with small K | e
... | true | ()

unfold-inv : ∀ {Γ C A} (k : Maybe (Known Γ C)) (e : C ≡ μ A) {K} → unfolded k e ≡ just K
  → subst (λ C → Maybe (Known Γ C)) e k ≡ just (val (fold K))
unfold-inv (just (val (fold K))) refl refl = refl
