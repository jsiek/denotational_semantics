{-

  Correctness of the optimize pass (Clos2 → Clos2) in the graph model with
  errors (Semantics/GraphErr/Clos2.agda).

  As in the graph model (proof/Correctness/Graph/OptimizeCorrect.agda),
  optimize renames variables (by r) and drops the free variables that a
  closure's code does not use, and the denotation is unchanged:
  ⟦ M ⟧ ρ ≃ ⟦ optimize r M ⟧ ρ' when ρ and ρ' agree through r on the
  variables M uses.

  With errors, a closure is an error when one of its free variables is,
  so dropping a free variable keeps the meaning only when that variable
  has a value and holds no ω. A dropped free variable is a variable, so
  the precondition is on the environment: the term is well scoped (WS k)
  and every variable below k has a value in a consistent environment
  (hence holds no ω). This holds under the binders, which bind values
  without ω, inside a closure's code when its free variables have values,
  and vacuously for a closed program (enclose's output is WS 0).

-}

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim
open import Language.Clos2
open import proof.Semantics.GraphErr.Clos2
open import Compiler.Optimize
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import proof.Framework.GraphModel.Env using (Env)
import Language.ISWIM as ISWIM
open import Compiler.Simplify using (simplify)
open import Compiler.Enclose using (enclose)
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.EncloseScope using (enclose-closed)
open import proof.Compiler.SimplifyScope using (simplify-closed)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

module proof.Correctness.GraphErr.OptimizeCorrect where

{- Helpers --------------------------------------------------------------------}

init₀ : Env Value
init₀ = λ _ → ⌈ ω ⌉

unbind-bind : ∀ m (N : AST) → unbind-n m (bind-n-ast m N) ≡ N
unbind-bind zero N = refl
unbind-bind (suc m) N = unbind-bind m N

{- the variables below k have values -}
Vals : ℕ → Env Value → Set
Vals k ρ = ∀ x → x < k → val∈ (ρ x)

{- the positions below n + m of a pushed environment hold components of Ds,
   or the first m of σ -}
push-P : ∀ (P : 𝒫 Value → Set) n m (Ds : Results (𝒫 Value) (replicate n ■)) σ
  → (∀ i → P (nthD Ds i)) → (∀ k → k < m → P (σ k)) → ∀ j → j < n + m → P (push Ds σ j)
push-P P zero m Ds σ ps qs j j< = qs j j<
push-P P (suc n) m ⟨ D , Ds ⟩ σ ps qs j j< =
  push-P P n (suc m) Ds (D • σ) (λ i → ps (suc i)) qs' j (subst (j <_) (sym' (+-suc n m)) j<)
  where
  sym' : ∀ {a b : ℕ} → a ≡ b → b ≡ a
  sym' refl = refl
  qs' : ∀ k → k < suc m → P ((D • σ) k)
  qs' zero _ = ps zero
  qs' (suc k) (s≤s k<) = qs k k<

push-con : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) σ
  → (∀ i → Con (nthD Ds i)) → Con-env σ → Con-env (push Ds σ)
push-con zero _ σ _ c = c
push-con (suc n) ⟨ D , Ds ⟩ σ cs c = push-con n Ds (D • σ) (λ i → cs (suc i)) (Con-• (cs zero) c)

args-con : ∀ {n} (fvs : Args (replicate n ■)) ρ → Con-env ρ → ∀ i → Con (nthD (⟦ fvs ⟧₊ ρ) i)
args-con {suc n} (M ,, fvs) ρ c zero = Clos2ᵉ-con-env M c
args-con {suc n} (M ,, fvs) ρ c (suc i) = args-con fvs ρ c i

noerr-val : ∀ V → V ≢ [] → NoErr V → val∈ (mem V)
noerr-val [] ne _ = ⊥-elim (ne refl)
noerr-val (v ∷ V) _ n = ⟨ v , ⟨ here refl , (λ { refl → n (here refl) }) ⟩ ⟩

{- What pruning a closure's free variables preserves --------------------------}

record PruneOK n (U : ℕ → Set) (fvs : Args (replicate n ■)) (P : Pruned) (b : ℕ → ℕ)
    (ρ ρ' : Env Value) : Set₁ where
  field
    {- the kept free variables err, and have values, exactly when all of them do -}
    errs→ : errs n (⟦ fvs ⟧₊ ρ) → errs (count P) (⟦ kept P ⟧₊ ρ')
    errs← : errs (count P) (⟦ kept P ⟧₊ ρ') → errs n (⟦ fvs ⟧₊ ρ)
    vals→ : vals n (⟦ fvs ⟧₊ ρ) → vals (count P) (⟦ kept P ⟧₊ ρ')
    vals← : vals (count P) (⟦ kept P ⟧₊ ρ') → vals n (⟦ fvs ⟧₊ ρ)
    {- every position that the code uses is renumbered to the same set -}
    push≃ : ∀ ρ₁ ρ₂ → (∀ k → U (n + k) → ρ₁ k ≃ ρ₂ (b k))
      → ∀ j → U j → push (⟦ fvs ⟧₊ ρ) ρ₁ j ≃ push (⟦ kept P ⟧₊ ρ') ρ₂ (index P j)

keep-ok : ∀ {n U} {M M' : AST} {fvs : Args (replicate n ■)} {P b ρ ρ'}
  → ⟦ M ⟧ ρ ≃ ⟦ M' ⟧ ρ'
  → PruneOK n U fvs P (keep-base b) ρ ρ'
  → PruneOK (suc n) U (M ,, fvs) (keep M' P) b ρ ρ'
keep-ok {n} {U} {M} {M'} {fvs} {P} {b} {ρ} {ρ'} M≃ ok = record
  { errs→ = λ { (inj₁ ω∈) → inj₁ (proj₁ M≃ ω ω∈)
              ; (inj₂ ⟨ v , e ⟩) → inj₂ ⟨ val∈-mono (proj₁ M≃) v , PruneOK.errs→ ok e ⟩ }
  ; errs← = λ { (inj₁ ω∈) → inj₁ (proj₂ M≃ ω ω∈)
              ; (inj₂ ⟨ v , e ⟩) → inj₂ ⟨ val∈-mono (proj₂ M≃) v , PruneOK.errs← ok e ⟩ }
  ; vals→ = λ { vs zero → val∈-mono (proj₁ M≃) (vs zero)
              ; vs (suc i) → PruneOK.vals→ ok (λ i → vs (suc i)) i }
  ; vals← = λ { vs zero → val∈-mono (proj₂ M≃) (vs zero)
              ; vs (suc i) → PruneOK.vals← ok (λ i → vs (suc i)) i }
  ; push≃ = λ ρ₁ ρ₂ bse j u →
      PruneOK.push≃ ok (⟦ M ⟧ ρ • ρ₁) (⟦ M' ⟧ ρ' • ρ₂) (bse' ρ₁ ρ₂ bse) j u
  }
  where
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (⟦ M ⟧ ρ • ρ₁) k ≃ (⟦ M' ⟧ ρ' • ρ₂) (keep-base b k)
  bse' ρ₁ ρ₂ bse zero _ = M≃
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)

{- under a binder -}
rel-ext : ∀ B {r} {ρ ρ' : Env Value} {X} → (∀ x → Uses (suc x) B → ρ x ≃ ρ' (r x))
  → ∀ x → Uses x B → (X • ρ) x ≃ (X • ρ') (ext-var r x)
rel-ext B rx zero _ = ≃-refl
rel-ext B rx (suc x) u = rx x u

vals-ext : ∀ {k ρ X} → val∈ X → Vals k ρ → Vals (suc k) (X • ρ)
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
opt-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) r k ρ ρ' ⟨ wsa , wsf ⟩ V c rel = ⟨ G , H ⟩
  where
  N = unbind-n n a
  P = prune n r (λ j → uses? (suc j) N) fvs (λ k → k)
  ok = prune-ok n r k (λ j → uses? (suc j) N) fvs (λ k → k) ρ ρ' wsf V c (λ x u → rel x (inj₂ u))
  Ds = ⟦ fvs ⟧₊ ρ
  Ds' = ⟦ kept P ⟧₊ ρ'
  m = count P
  N' = opt-body (ext-var (index P)) n a

  {- applying the closure to U runs the same body on the same free variables -}
  body≃ : ∀ U → U ≢ [] → U ≈ U → NoErr U → vals n Ds
    → apply-n n (⟦ a ⟧ₐ init₀) Ds (mem U) ≃ apply-n m (⟦ bind-n-ast m N' ⟧ₐ init₀) Ds' (mem U)
  body≃ U neU cU nU vs
    rewrite apply-push n a init₀ Ds (mem U)
          | apply-push m (bind-n-ast m N') init₀ Ds' (mem U)
          | unbind-bind m N' =
    opt-body-correct (ext-var (index P)) n 0 a (mem U • push Ds init₀) (mem U • push Ds' init₀)
      wsa V' (Con-• (≈⇒Con cU) (push-con n Ds init₀ (args-con fvs ρ c) (λ _ → Con-⌈⌉ ω)))
      rel₁
    where
    V' : Vals (n + 1) (mem U • push Ds init₀)
    V' zero _ = noerr-val U neU nU
    V' (suc j) j< = push-P val∈ n 0 Ds init₀ vs (λ _ ()) j (lt j j<)
      where
      lt : ∀ j → suc j < n + 1 → j < n + 0
      lt j j< rewrite +-identityʳ n = pred< (subst (suc j <_) (+-comm1 n) j<)
        where
        open import Data.Nat.Properties using (+-comm)
        +-comm1 : ∀ n → n + 1 ≡ suc n
        +-comm1 n = +-comm n 1
        pred< : ∀ {a b} → suc a < suc b → a < b
        pred< (s≤s x) = x
    rel₁ : ∀ x → Uses x N → (mem U • push Ds init₀) x ≃ (mem U • push Ds' init₀) (ext-var (index P) x)
    rel₁ zero _ = ≃-refl
    rel₁ (suc j) u = PruneOK.push≃ ok init₀ init₀ (λ k _ → ≃-refl) j u

  G : ⟦ clos-op n ⦅ ! clear a ,, fvs ⦆ ⟧ ρ ⊆ ⟦ optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆) ⟧ ρ'
  G w (inj₁ ⟨ refl , e ⟩) = inj₁ ⟨ refl , PruneOK.errs→ ok e ⟩
  G ν (inj₂ ⟨ vs , tt ⟩) = inj₂ ⟨ PruneOK.vals→ ok vs , tt ⟩
  G (U ↦ x) (inj₂ ⟨ vs , ⟨ x∈ , r' ⟩ ⟩) =
    inj₂ ⟨ PruneOK.vals→ ok vs
         , ⟨ proj₁ (body≃ U (proj₁ r') (proj₁ (proj₂ r')) (proj₂ (proj₂ r')) vs) x x∈ , r' ⟩ ⟩

  H : ⟦ optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆) ⟧ ρ' ⊆ ⟦ clos-op n ⦅ ! clear a ,, fvs ⦆ ⟧ ρ
  H w (inj₁ ⟨ refl , e ⟩) = inj₁ ⟨ refl , PruneOK.errs← ok e ⟩
  H ν (inj₂ ⟨ vs' , tt ⟩) = inj₂ ⟨ PruneOK.vals← ok vs' , tt ⟩
  H (U ↦ x) (inj₂ ⟨ vs' , ⟨ x∈ , r' ⟩ ⟩) =
    inj₂ ⟨ vs , ⟨ proj₂ (body≃ U (proj₁ r') (proj₁ (proj₂ r')) (proj₂ (proj₂ r')) vs) x x∈ , r' ⟩ ⟩
    where vs = PruneOK.vals← ok vs'
opt-correct (app ⦅ L ,, M ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , _ ⟩ ⟩ V c rel =
  ⋆ᵉ-≃ (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
       (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₂ (inj₁ u))))
opt-correct (lit B k′ ⦅ Nil ⦆) r k ρ ρ' ws V c rel = ≃-refl
opt-correct (tuple n ⦅ args ⦆) r k ρ ρ' ws V c rel = 𝒯ᵉ-≃ n (opt-args-correct args r k ρ ρ' ws V c rel)
opt-correct (get i ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  projᵉ-≃ i (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (inl-op ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  inlᵉ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (inr-op ⦅ M ,, Nil ⦆) r k ρ ρ' ⟨ wM , _ ⟩ V c rel =
  inrᵉ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
opt-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ V c rel =
  𝒞ᵉ-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ optimize (ext-var r) M ⟧ (X • ρ')}
       {λ X → ⟦ N ⟧ (X • ρ)} {λ X → ⟦ optimize (ext-var r) N ⟧ (X • ρ')}
       (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
       (λ v W cW n → opt-correct M (ext-var r) (suc k) _ _ wM (vals-ext (noerr-val (v ∷ W) (λ ()) n) V)
                       (Con-• (≈⇒Con cW) c) (rel-ext M (λ x u → rel x (inj₂ (inj₁ u)))))
       (λ v W cW n → opt-correct N (ext-var r) (suc k) _ _ wN (vals-ext (noerr-val (v ∷ W) (λ ()) n) V)
                       (Con-• (≈⇒Con cW) c) (rel-ext N (λ x u → rel x (inj₂ (inj₂ (inj₁ u))))))
opt-correct (prim p ⦅ L ,, M ,, Nil ⦆) r k ρ ρ' ⟨ wL , ⟨ wM , _ ⟩ ⟩ V c rel =
  primᵉ-≃ p (opt-correct L r k ρ ρ' wL V c (λ x u → rel x (inj₁ u)))
            (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₂ (inj₁ u))))
opt-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) r k ρ ρ' ⟨ wM , ⟨ wN , _ ⟩ ⟩ V c rel =
  letᵉ-≃ (opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
         (λ W ne cW n → opt-correct N (ext-var r) (suc k) _ _ wN (vals-ext (noerr-val W ne n) V)
                          (Con-• (≈⇒Con cW) c) (rel-ext N (λ x u → rel x (inj₂ (inj₁ u)))))

opt-body-correct r zero m (bind (ast N)) ρ ρ' ws V c rel = opt-correct N r (suc m) ρ ρ' ws V c rel
opt-body-correct r (suc k) m (bind a) ρ ρ' ws V c rel =
  opt-body-correct r k (suc m) a ρ ρ' ws (subst (λ j → Vals j ρ) (sym (+-suc k (suc m))) V) c rel

opt-args-correct {suc n} (M ,, args) r k ρ ρ' ⟨ wM , ws ⟩ V c rel zero =
  opt-correct M r k ρ ρ' wM V c (λ x u → rel x (inj₁ u))
opt-args-correct {suc n} (M ,, args) r k ρ ρ' ⟨ wM , ws ⟩ V c rel (suc i) =
  opt-args-correct args r k ρ ρ' ws V c (λ x u → rel x (inj₂ u)) i

prune-ok zero r k dec Nil b ρ ρ' ws V c rel = record
  { errs→ = λ () ; errs← = λ () ; vals→ = λ _ () ; vals← = λ _ ()
  ; push≃ = λ ρ₁ ρ₂ bse j u → bse j u }
prune-ok (suc n) r k {U} dec ((` y) ,, fvs) b ρ ρ' ⟨ y< , ws ⟩ V c rel with dec n
... | yes _ =
  keep-ok (rel y (inj₁ refl))
          (prune-ok n r k dec fvs (keep-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u)))
... | no ¬u = record
  { errs→ = λ { (inj₁ ω∈) → ⊥-elim (cl ω ω∈ refl) ; (inj₂ ⟨ _ , e ⟩) → PruneOK.errs→ ok e }
  ; errs← = λ e → inj₂ ⟨ V y y< , PruneOK.errs← ok e ⟩
  ; vals→ = λ vs → PruneOK.vals→ ok (λ i → vs (suc i))
  ; vals← = λ { vs' zero → V y y< ; vs' (suc i) → PruneOK.vals← ok vs' i }
  ; push≃ = λ ρ₁ ρ₂ bse j u → PruneOK.push≃ ok (ρ y • ρ₁) ρ₂ (bse' ρ₁ ρ₂ bse) j u
  }
  where
  cl = con-val-clean (c y) (V y y<)
  ok = prune-ok n r k dec fvs (drop-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u))
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (ρ y • ρ₁) k ≃ ρ₂ (drop-base b k)
  bse' ρ₁ ρ₂ bse zero uk = ⊥-elim (¬u (subst U (+-identityʳ n) uk))
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)
prune-ok (suc n) r k dec ((op ⦅ args ⦆) ,, fvs) b ρ ρ' ⟨ wM , ws ⟩ V c rel =
  keep-ok (opt-correct (op ⦅ args ⦆) r k ρ ρ' wM V c (λ x u → rel x (inj₁ u)))
          (prune-ok n r k dec fvs (keep-base b) ρ ρ' ws V c (λ x u → rel x (inj₂ u)))

{- The end theorems ------------------------------------------------------------}

{- a well-scoped program (no variable is free) -}
optimize-correct : ∀ (M : AST) → WS 0 M → ⟦ M ⟧ ρ₀ ≃ ⟦ optimize-program M ⟧ ρ₀
optimize-correct M ws = opt-correct M (λ x → x) 0 ρ₀ ρ₀ ws (λ x ()) (λ _ → Con-⌈⌉ ω) (λ x _ → ≃-refl)

{- the input of optimize in the compiler -}
optimize-correct-compile : ∀ (M : ISWIM.AST) → Closed M
  → ⟦ enclose (simplify M) ⟧ ρ₀ ≃ ⟦ optimize-program (enclose (simplify M)) ⟧ ρ₀
optimize-correct-compile M c = optimize-correct (enclose (simplify M)) (enclose-closed (simplify M) (simplify-closed M c))
