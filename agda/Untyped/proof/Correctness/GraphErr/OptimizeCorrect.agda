{-

  Correctness of the optimize pass (Clos2 → Clos2) in the graph model with
  errors (Semantics/GraphErr/Clos2.agda).

  As in the graph model (proof/Correctness/Graph/OptimizeCorrect.agda),
  optimize renames variables (by r) and drops the free variables that a
  closure's code does not use, and the denotation is unchanged:
  ⟦ M ⟧ ρ ≃ ⟦ optimize r M ⟧ ρ' when ρ and ρ' agree through r on the
  variables M uses.

  A closure binds its free variables, left to right, so dropping one
  keeps the meaning only when that variable is a set of values: then its
  bind is the left unit (≫=-val-β). A dropped free variable is a
  variable, so the precondition is on the environment: the term is well
  scoped (WS k) and every variable below k is a set of values. This holds
  under the binders, which bind values, inside a closure's code when its
  free variables have values, and vacuously for a closed program
  (enclose's output is WS 0). A kept free variable is bound on both
  sides (≫=-≃).

-}

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim
open import Untyped.Language.Clos2
open import Untyped.proof.Semantics.GraphErr.Clos2
open import Untyped.Compiler.Optimize
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import proof.Framework.GraphModel.Env using (Env)
import Language.ISWIM as ISWIM
open import Compiler.Simplify using (simplify)
open import Untyped.Compiler.Enclose using (enclose)
open import Compiler.EncloseScope using (Closed)
open import Untyped.proof.Compiler.EncloseScope using (enclose-closed)
open import proof.Compiler.SimplifyScope using (simplify-closed)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; ≤-pred)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

module Untyped.proof.Correctness.GraphErr.OptimizeCorrect where

{- Helpers --------------------------------------------------------------------}

init₀ : Env Value
init₀ = λ _ → ⌈ ω ⌉

unbind-bind : ∀ m (N : AST) → unbind-n m (bind-n-ast m N) ≡ N
unbind-bind zero N = refl
unbind-bind (suc m) N = unbind-bind m N

{- the variables below k are sets of values -}
Vals : ℕ → Env Value → Set
Vals k ρ = ∀ x → x < k → Val (ρ x)

{- the positions below n + m of a pushed environment hold components of Ds,
   or the first m of σ -}
push-P : ∀ (P : 𝒫 Value → Set) n m (Ds : Results (𝒫 Value) (replicate n ■)) σ
  → (∀ i → P (nthD Ds i)) → (∀ k → k < m → P (σ k)) → ∀ j → j < n + m → P (push Ds σ j)
push-P P zero m Ds σ ps qs j j< = qs j j<
push-P P (suc n) m ⟨ D , Ds ⟩ σ ps qs j j< =
  push-P P n (suc m) Ds (D • σ) (λ i → ps (suc i)) qs' j (subst (j <_) (sym (+-suc n m)) j<)
  where
  qs' : ∀ k → k < suc m → P ((D • σ) k)
  qs' zero _ = ps zero
  qs' (suc k) (s≤s k<) = qs k k<

push-con : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) σ
  → (∀ i → Con (nthD Ds i)) → Con-env σ → Con-env (push Ds σ)
push-con zero _ σ _ c = c
push-con (suc n) ⟨ D , Ds ⟩ σ cs c = push-con n Ds (D • σ) (λ i → cs (suc i)) (Con-• (cs zero) c)

{- What pruning a closure's free variables preserves --------------------------}

{- every position that the code uses is renumbered to the same set -}
PushRel : ∀ n m → (ℕ → Set) → Results (𝒫 Value) (replicate n ■) → Results (𝒫 Value) (replicate m ■)
  → (ℕ → ℕ) → (ℕ → ℕ) → Set₁
PushRel n m U Xs Xs' idx b = ∀ ρ₁ ρ₂ → (∀ k → U (n + k) → ρ₁ k ≃ ρ₂ (b k))
  → ∀ j → U j → push Xs ρ₁ j ≃ push Xs' ρ₂ (idx j)

{- binding the free variables and binding the kept ones are the same,
   for continuations that are the same on such values -}
PruneOK : ∀ n (U : ℕ → Set) (fvs : Args (replicate n ■)) (P : Pruned) (b : ℕ → ℕ) (ρ ρ' : Env Value) → Set₁
PruneOK n U fvs P b ρ ρ' = ∀ {K K'}
  → (∀ {Xs Xs'} → AllVal n Xs → (∀ i → Con (nthD Xs i)) → PushRel n (count P) U Xs Xs' (index P) b → K Xs ≃ K' Xs')
  → binds n (⟦ fvs ⟧₊ ρ) K ≃ binds (count P) (⟦ kept P ⟧₊ ρ') K'

⌊⌋-≃ : ∀ {D E} → D ≃ E → ⌊ D ⌋ ≃ ⌊ E ⌋
⌊⌋-≃ ⟨ D⊆ , E⊆ ⟩ = ⟨ ⌊⌋-mono D⊆ , ⌊⌋-mono E⊆ ⟩

keep-ok : ∀ {n U} {M M' : AST} {fvs : Args (replicate n ■)} {P b ρ ρ'}
  → ⟦ M ⟧ ρ ≃ ⟦ M' ⟧ ρ' → Con (⟦ M ⟧ ρ)
  → PruneOK n U fvs P (keep-base b) ρ ρ'
  → PruneOK (suc n) U (M ,, fvs) (keep M' P) b ρ ρ'
keep-ok {n} {U} {M} {M'} {fvs} {P} {b} {ρ} {ρ'} M≃ cM ok {K} {K'} hK =
  ≫=-≃ {F = λ X → binds n (⟦ fvs ⟧₊ ρ) (λ Xs → K ⟨ X , Xs ⟩)}
       {F' = λ X → binds (count P) (⟦ kept P ⟧₊ ρ') (λ Xs → K' ⟨ X , Xs ⟩)} M≃ λ cv _ → ok {λ Xs → K ⟨ ⌊ ⟦ M ⟧ ρ ⌋ , Xs ⟩} {λ Xs' → K' ⟨ ⌊ ⟦ M' ⟧ ρ' ⌋ , Xs' ⟩}
    λ vXs cXs h → hK (λ { zero → ⌊⌋-val cv ; (suc i) → vXs i }) (λ { zero → Con-⊆ cM ⌊⌋-⊆ ; (suc i) → cXs i })
      (λ ρ₁ ρ₂ bse j u → h (⌊ ⟦ M ⟧ ρ ⌋ • ρ₁) (⌊ ⟦ M' ⟧ ρ' ⌋ • ρ₂) (bse' ρ₁ ρ₂ bse) j u)
  where
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (⌊ ⟦ M ⟧ ρ ⌋ • ρ₁) k ≃ (⌊ ⟦ M' ⟧ ρ' ⌋ • ρ₂) (keep-base b k)
  bse' ρ₁ ρ₂ bse zero _ = ⌊⌋-≃ M≃
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)

{- under a binder -}
rel-ext : ∀ B {r} {ρ ρ' : Env Value} {X} → (∀ x → Uses (suc x) B → ρ x ≃ ρ' (r x))
  → ∀ x → Uses x B → (X • ρ) x ≃ (X • ρ') (ext-var r x)
rel-ext B rx zero _ = ≃-refl
rel-ext B rx (suc x) u = rx x u

vals-ext : ∀ {k ρ X} → Val X → Vals k ρ → Vals (suc k) (X • ρ)
vals-ext vX V zero _ = vX
vals-ext vX V (suc x) (s≤s x<) = V x x<

{- The main lemma -------------------------------------------------------------}

opt-correct : ∀ (M : AST) r k ρ ρ' → WS k M → Vals k ρ → Con-env ρ
  → (∀ x → Uses x M → ρ x ≃ ρ' (r x))
  → ⟦ M ⟧ ρ ≃ ⟦ optimize r M ⟧ ρ'

opt-body-correct : ∀ r k m (a : Arg (ν-n k (ν ■))) ρ ρ' → WS-arg m a → Vals (k + suc m) ρ → Con-env ρ
  → (∀ x → Uses x (unbind-n k a) → ρ x ≃ ρ' (r x))
  → ⟦ unbind-n k a ⟧ ρ ≃ ⟦ opt-body r k a ⟧ ρ'

opt-args-correct : ∀ {n} (args : Args (replicate n ■)) r k ρ ρ' → WS-args k args → Vals k ρ → Con-env ρ
  → (∀ x → UsesArgs x args → ρ x ≃ ρ' (r x))
  → ∀ i → nthD (⟦ args ⟧₊ ρ) i ≃ nthD (⟦ opt-args r args ⟧₊ ρ') i

prune-ok : ∀ n r k {U : ℕ → Set} (dec : ∀ j → Dec (U j)) (fvs : Args (replicate n ■))
  (b : ℕ → ℕ) ρ ρ' → WS-args k fvs → Vals k ρ → Con-env ρ → (∀ x → UsesArgs x fvs → ρ x ≃ ρ' (r x))
  → PruneOK n U fvs (prune n r dec fvs b) b ρ ρ'

opt-correct (` x) r k ρ ρ' ws V c rel = rel x refl
opt-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) r k ρ ρ' ⟨ wsa , wsf ⟩ V c rel =
  prune-ok n r k (λ j → uses? (suc j) N) fvs (λ k → k) ρ ρ' wsf V c (λ x u → rel x (inj₂ u))
    λ {Xs} {Xs'} vXs cXs h → Λᵐ-≃ (body≃ Xs Xs' vXs cXs h)
  where
  N = unbind-n n a
  P = prune n r (λ j → uses? (suc j) N) fvs (λ k → k)
  m = count P
  N' = opt-body (ext-var (index P)) n a

  {- applying the closure to U runs the same body on the same free variables -}
  body≃ : ∀ Xs Xs' → AllVal n Xs → (∀ i → Con (nthD Xs i)) → PushRel n m (λ j → Uses (suc j) N) Xs Xs' (index P) (λ k → k)
    → BodyEq (apply-n n (⟦ a ⟧ₐ init₀) Xs) (apply-n m (⟦ bind-n-ast m N' ⟧ₐ init₀) Xs')
  body≃ Xs Xs' vXs cXs h U neU cU nU
    rewrite apply-push n a init₀ Xs (mem U)
          | apply-push m (bind-n-ast m N') init₀ Xs' (mem U)
          | unbind-bind m N' =
    opt-body-correct (ext-var (index P)) n 0 a (mem U • push Xs init₀) (mem U • push Xs' init₀)
      wsa V' (Con-• (≈⇒Con cU) (push-con n Xs init₀ cXs (λ _ → Con-⌈⌉ ω))) rel₁
    where
    V' : Vals (n + 1) (mem U • push Xs init₀)
    V' zero _ = noerr-val U neU nU
    V' (suc j) j< = push-P Val n 0 Xs init₀ vXs (λ _ ()) j (lt j<)
      where
      lt : ∀ {j} → suc j < n + 1 → j < n + 0
      lt j< rewrite +-identityʳ n | +-comm n 1 = ≤-pred j<
    rel₁ : ∀ x → Uses x N → (mem U • push Xs init₀) x ≃ (mem U • push Xs' init₀) (ext-var (index P) x)
    rel₁ zero _ = ≃-refl
    rel₁ (suc j) u = h init₀ init₀ (λ k _ → ≃-refl) j u
opt-correct (app ⦅ L ,, M ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , _ ⟩ ⟩ V c rel =
  ⋆ᵐ-≃ (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
       (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₂ (inj₁ u))))
opt-correct (lit B k′ ⦅ Nil ⦆) r k ρ ρ' ws V c rel = ≃-refl
opt-correct (tuple n ⦅ args ⦆) r k ρ ρ' ws V c rel = 𝒯ᵐ-≃ n (opt-args-correct args r k ρ ρ' ws V c rel)
opt-correct (get i ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  projᵐ-≃ i (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (inl-op ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  inlᵐ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (inr-op ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  inrᵐ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ V c rel =
  𝒞ᵐ-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ optimize (ext-var r) M ⟧ (X • ρ')}
       {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ optimize (ext-var r) N ⟧ (X • ρ')}
       (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
       (λ W ne cW n → opt-correct M (ext-var r) (suc k) _ _ wM (vals-ext (noerr-val W ne n) V)
                       (Con-• (≈⇒Con cW) c) (rel-ext M (λ x u → rel x (inj₂ (inj₁ u)))))
       (λ W ne cW n → opt-correct N (ext-var r) (suc k) _ _ wN (vals-ext (noerr-val W ne n) V)
                       (Con-• (≈⇒Con cW) c) (rel-ext N (λ x u → rel x (inj₂ (inj₂ (inj₁ u))))))
opt-correct (prim p ⦅ L ,, M ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , _ ⟩ ⟩ V c rel =
  primᵐ-≃ p (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
            (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₂ (inj₁ u))))
opt-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) r k ρ ρ' ⟨ wM , ⟨ wN , _ ⟩ ⟩ V c rel =
  letᵐ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
         (λ W ne cW n → opt-correct N (ext-var r) (suc k) _ _ wN (vals-ext (noerr-val W ne n) V)
                          (Con-• (≈⇒Con cW) c) (rel-ext N (λ x u → rel x (inj₂ (inj₁ u)))))

opt-body-correct r zero m (bind (ast N)) ρ ρ' ws V c rel = opt-correct N r (suc m) ρ ρ' ws V c rel
opt-body-correct r (suc k) m (bind a) ρ ρ' ws V c rel =
  opt-body-correct r k (suc m) a ρ ρ' ws (subst (λ j → Vals j ρ) (sym (+-suc k (suc m))) V) c rel

opt-args-correct {suc n} (M ,, args) r k ρ ρ' ⟨ wM , ws ⟩ V c rel zero =
  opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u))
opt-args-correct {suc n} (M ,, args) r k ρ ρ' ⟨ wM , ws ⟩ V c rel (suc i) =
  opt-args-correct args r k ρ ρ' ws V c (λ x u → rel x (inj₂ u)) i

prune-ok zero r k dec Nil b ρ ρ' ws V c rel hK = hK (λ ()) (λ ()) (λ ρ₁ ρ₂ bse j u → bse j u)
prune-ok (suc n) r k {U} dec ((` y) ,, fvs) b ρ ρ' ⟨ y< , ws ⟩ V c rel {K} {K'} hK with dec n
... | yes _ =
  keep-ok {M = ` y} {` (r y)} (rel y (inj₁ refl)) (c y)
          (prune-ok n r k dec fvs (keep-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u))) hK
... | no ¬u =
  ≃-trans (≫=-val-β {F = λ X → binds n (⟦ fvs ⟧₊ ρ) (λ Xs → K ⟨ X , Xs ⟩)} (V y y<))
    (ok {λ Xs → K ⟨ ⌊ ρ y ⌋ , Xs ⟩} {K'}
      λ vXs cXs h → hK (λ { zero → ⌊⌋-val (Val⇒Conv (V y y<)) ; (suc i) → vXs i })
                       (λ { zero → Con-⊆ (c y) ⌊⌋-⊆ ; (suc i) → cXs i })
                       (λ ρ₁ ρ₂ bse j u → h (⌊ ρ y ⌋ • ρ₁) ρ₂ (bse' ρ₁ ρ₂ bse) j u))
  where
  ok = prune-ok n r k dec fvs (drop-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u))
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (⌊ ρ y ⌋ • ρ₁) k ≃ ρ₂ (drop-base b k)
  bse' ρ₁ ρ₂ bse zero uk = ⊥-elim (¬u (subst U (+-identityʳ n) uk))
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)
prune-ok (suc n) r k dec ((op ⦅ args ⦆) ,, fvs) b ρ ρ' ⟨ wM , ws ⟩ V c rel =
  keep-ok {M = op ⦅ args ⦆} {optimize r (op ⦅ args ⦆)} (opt-correct (op ⦅ args ⦆) r k ρ ρ' wM V c (λ x u → rel x (inj₁ u))) (Clos2ᵐ-con-env (op ⦅ args ⦆) c)
          (prune-ok n r k dec fvs (keep-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u)))

{- The end theorems ------------------------------------------------------------}

{- a well-scoped program (no variable is free) -}
optimize-correct : ∀ (M : AST) → WS 0 M → ⟦ M ⟧ ρ₀ ≃ ⟦ optimize-program M ⟧ ρ₀
optimize-correct M ws = opt-correct M (λ x → x) 0 ρ₀ ρ₀ ws (λ x ()) (λ _ → Con-⌈⌉ ω) (λ x _ → ≃-refl)

{- the input of optimize in the compiler -}
optimize-correct-compile : ∀ (M : ISWIM.AST) → Closed M
  → ⟦ enclose (simplify M) ⟧ ρ₀ ≃ ⟦ optimize-program (enclose (simplify M)) ⟧ ρ₀
optimize-correct-compile M c = optimize-correct (enclose (simplify M)) (enclose-closed (simplify M) (simplify-closed M c))
