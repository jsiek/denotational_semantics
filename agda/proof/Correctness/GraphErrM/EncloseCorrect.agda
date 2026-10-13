{-

  Correctness of the enclose pass (ISWIM → Clos2) in the graph model with
  errors (Semantics/GraphErr/{ISWIM,Clos2}.agda).

  As in the graph model (proof/Correctness/Graph/EncloseCorrect.agda),
  ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂ when the environments agree on the
  variables M uses. What changes is the closure: a Clos2 closure first
  evaluates its free variables, and is an error if one of them is. So
  the captured variables, ` (m - 1) , ... , ` 0, all those below the
  bound of the function, must have values and no errors in ρ₂ (Vals),
  which holds under the binders (they bind no ω) and, for a closed
  program, vacuously: no variable is below its bound, 0.

-}

module proof.Correctness.GraphErrM.EncloseCorrect where

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErrM.Prim
open import Language.ISWIM
open import proof.Framework.Syntax.Uses Op sig
open import proof.Semantics.GraphErrM.ISWIM
open import proof.Semantics.GraphErrM.Clos2 as S2 using (apply-n; apply-n-pres; push; apply-push; push-plus) renaming
  (⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧ₐ₂; ⟦_⟧₊ to ⟦_⟧₊₂; ⟦⟧-monotone-arg to ⟦⟧-monotone-arg₂)
import Language.Clos2 as L2
open import Compiler.Optimize using (bind-n-ast)
open import Compiler.Enclose
open import Compiler.EncloseScope using (Closed)
open import proof.Framework.GraphModel.Env using (Env)

open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; _∸_; _+_; _⊔_)
open import Data.Nat.Properties
  using (+-identityʳ; +-suc; ≤-antisym; ≤-pred; ≮⇒≥; m≤m⊔n; m≤n⊔m; <-≤-trans; <-trans; n≮0; n<1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Unit using (tt; ⊤)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- a set of values without errors -}
Vals : 𝒫 Value → Set
Vals D = Conv D × Clean D

{- Binding the free variables one at a time ------------------------------------}

init₀ : Env Value
init₀ = λ _ → ⌈ ω ⌉

unbind-bind : ∀ m (N : L2.AST) → L2.unbind-n m (bind-n-ast m N) ≡ N
unbind-bind zero N = refl
unbind-bind (suc m) N = unbind-bind m N

{- binding ` (n - 1) , ... , ` 0 one at a time puts ρ k at position k -}
push-vars : ∀ n (ρ σ : Env Value) k → k < n → push (⟦ fv-vars n ⟧₊₂ ρ) σ k ≡ ρ k
push-vars (suc n) ρ σ k k<sn with k <? n
... | yes k<n = push-vars n ρ (ρ n • σ) k k<n
... | no ¬k<n =
  trans (cong (push (⟦ fv-vars n ⟧₊₂ ρ) (ρ n • σ)) (trans k≡n (sym (+-identityʳ n))))
        (trans (push-plus n _ (ρ n • σ) 0) (cong ρ (sym k≡n)))
  where
  k≡n : k ≡ n
  k≡n = ≤-antisym (≤-pred k<sn) (≮⇒≥ ¬k<n)

{- the captured free variables have values, and no errors -}
fv-vars-vals : ∀ m (ρ : Env Value) → (∀ k → k < m → Vals (ρ k)) → ∀ i → Conv (nthD (⟦ fv-vars m ⟧₊₂ ρ) i)
fv-vars-vals (suc m) ρ V zero = proj₁ (V m (n<1+n m))
fv-vars-vals (suc m) ρ V (suc i) = fv-vars-vals m ρ (λ k k< → V k (<-trans k< (n<1+n m))) i

fv-vars-clean : ∀ m (ρ : Env Value) → (∀ k → k < m → Vals (ρ k)) → ∀ i → Clean (nthD (⟦ fv-vars m ⟧₊₂ ρ) i)
fv-vars-clean (suc m) ρ V zero = proj₂ (V m (n<1+n m))
fv-vars-clean (suc m) ρ V (suc i) = fv-vars-clean m ρ (λ k k< → V k (<-trans k< (n<1+n m))) i

{- bounds of subterms -}
<-⊔ˡ : ∀ {x a} b → x < a → x < a ⊔ b
<-⊔ˡ {a = a} b x< = <-≤-trans x< (m≤m⊔n a b)

<-⊔ʳ : ∀ {x} a {b} → x < b → x < a ⊔ b
<-⊔ʳ a {b} x< = <-≤-trans x< (m≤n⊔m a b)

{- under a binder -}
rel-ext : ∀ B {ρ₁ ρ₂ : Env Value} {X} → (∀ x → Uses (suc x) B → ρ₁ x ≃ ρ₂ x)
  → ∀ x → Uses x B → (X • ρ₁) x ≃ (X • ρ₂) x
rel-ext B r zero _ = ≃-refl
rel-ext B r (suc x) u = r x u

vals-ext : ∀ B {ρ₂ : Env Value} {X} → Vals X → (∀ x → x < bound B ∸ 1 → Vals (ρ₂ x))
  → ∀ x → x < bound B → Vals ((X • ρ₂) x)
vals-ext B VX V zero _ = VX
vals-ext B VX V (suc x) x< = V x (<-∸1 x<)

noerr-vals : ∀ V → V ≢ [] → NoErr V → Vals (mem V)
noerr-vals [] ne n = ⊥-elim (ne refl)
noerr-vals (v ∷ V) ne n =
  ⟨ ⟨ v , ⟨ here refl , (λ { refl → n (here refl) }) ⟩ ⟩ , (λ { .ω ω∈ refl → n ω∈ }) ⟩

{- The main lemma -------------------------------------------------------------}

enc-correct : ∀ (M : AST) ρ₁ ρ₂ → (∀ x → x < bound M → Vals (ρ₂ x)) → (∀ x → Uses x M → ρ₁ x ≃ ρ₂ x)
  → ⟦ M ⟧ ρ₁ ≃ ⟦ enclose M ⟧₂ ρ₂

enc-args-correct : ∀ {n} (args : Args (replicate n ■)) ρ₁ ρ₂
  → (∀ x → x < bound-args args → Vals (ρ₂ x)) → (∀ x → UsesArgs x args → ρ₁ x ≃ ρ₂ x)
  → ∀ i → nthD (⟦ args ⟧₊ ρ₁) i ≃ nthD (⟦ enc-args args ⟧₊₂ ρ₂) i

enc-correct (` x) ρ₁ ρ₂ V rel = rel x refl
enc-correct (lam ⦅ ⟩ N ,, Nil ⦆) ρ₁ ρ₂ V rel = G
  where
  m = bound N ∸ 1
  Ds = ⟦ fv-vars m ⟧₊₂ ρ₂
  Vm : ∀ k → k < m → Vals (ρ₂ k)
  Vm k k< = V k (<-⊔ˡ 0 k<)

  {- the body finds its free variables where it found them before -}
  body≃ : ∀ U → U ≢ [] → NoErr U → ⟦ N ⟧ (mem U • ρ₁)
              ≃ apply-n m (⟦ bind-n-ast m (enclose N) ⟧ₐ₂ init₀) Ds (mem U)
  body≃ U neU nU rewrite apply-push m (bind-n-ast m (enclose N)) init₀ Ds (mem U)
                      | unbind-bind m (enclose N) =
    enc-correct N (mem U • ρ₁) (mem U • push Ds init₀) V' rel'
    where
    V' : ∀ x → x < bound N → Vals ((mem U • push Ds init₀) x)
    V' zero _ = noerr-vals U neU nU
    V' (suc k) k< = subst Vals (sym (push-vars m ρ₂ init₀ k (<-∸1 k<))) (Vm k (<-∸1 k<))
    rel' : ∀ x → Uses x N → (mem U • ρ₁) x ≃ (mem U • push Ds init₀) x
    rel' zero _ = ≃-refl
    rel' (suc k) u =
      ≃-trans (rel k (inj₁ u))
              (≃-reflexive (sym (push-vars m ρ₂ init₀ k (<-∸1 (uses-bound (suc k) N u)))))

  F = ⟦ bind-n-ast m (enclose N) ⟧ₐ₂ init₀
  K = λ Xs → Λᵐ ⟨ apply-n m F Xs , ptt ⟩
  mK : Rel⊆ m K K
  mK {Xs} {Ys} Xs⊆ = lower (mono (Λᵐ-good {⊤}) ⟨ apply-n m F Xs , ptt ⟩ ⟨ apply-n m F Ys , ptt ⟩
    ⟨ apply-n-pres _⊆_ m F F Xs Ys (⟦⟧-monotone-arg₂ {{S2.Clos2ᵐ-Semantics}} (bind-n-ast m (enclose N)) (λ _ _ z → z)) Xs⊆ , ptt ⟩)
  G = ≃-trans (Λᵐ-≃ (λ U ne _ n → body≃ U ne n))
        (≃-sym (binds-β m mK (λ i → ⟨ fv-vars-clean m ρ₂ Vm i , (let ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = fv-vars-vals m ρ₂ Vm i in ⟨ d , d∈ ⟩) ⟩)))
enc-correct (app ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ V rel =
  ⋆ᵐ-≃ (enc-correct L ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ _ x<)) (λ x u → rel x (inj₁ u)))
       (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ʳ (bound L) (<-⊔ˡ 0 x<))) (λ x u → rel x (inj₂ (inj₁ u))))
enc-correct (lit B k ⦅ Nil ⦆) ρ₁ ρ₂ V rel = ≃-refl
enc-correct (tuple n ⦅ args ⦆) ρ₁ ρ₂ V rel = 𝒯ᵐ-≃ n (enc-args-correct args ρ₁ ρ₂ V rel)
enc-correct (get i ⦅ M ,, Nil ⦆) ρ₁ ρ₂ V rel =
  projᵐ-≃ i (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ 0 x<)) (λ x u → rel x (inj₁ u)))
enc-correct (inl-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ V rel =
  inlᵐ-≃ (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ 0 x<)) (λ x u → rel x (inj₁ u)))
enc-correct (inr-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ V rel =
  inrᵐ-≃ (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ 0 x<)) (λ x u → rel x (inj₁ u)))
enc-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ V rel =
  𝒞ᵐ-≃ {F = λ X → ⟦ M ⟧ (X • ρ₁)} {λ X → ⟦ enclose M ⟧₂ (X • ρ₂)}
       {λ X → ⟦ N ⟧ (X • ρ₁)} {λ X → ⟦ enclose N ⟧₂ (X • ρ₂)}
       (enc-correct L ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ _ x<)) (λ x u → rel x (inj₁ u)))
       (λ W ne _ n → enc-correct M _ _
          (vals-ext M (noerr-vals W ne n) (λ x x< → V x (<-⊔ʳ (bound L) (<-⊔ˡ _ x<))))
          (rel-ext M (λ x u → rel x (inj₂ (inj₁ u)))))
       (λ W ne _ n → enc-correct N _ _
          (vals-ext N (noerr-vals W ne n)
             (λ x x< → V x (<-⊔ʳ (bound L) (<-⊔ʳ (bound M ∸ 1) (<-⊔ˡ 0 x<)))))
          (rel-ext N (λ x u → rel x (inj₂ (inj₂ (inj₁ u))))))
enc-correct (prim p ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ V rel =
  primᵐ-≃ p (enc-correct L ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ _ x<)) (λ x u → rel x (inj₁ u)))
            (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ʳ (bound L) (<-⊔ˡ 0 x<))) (λ x u → rel x (inj₂ (inj₁ u))))
enc-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ V rel =
  letᵐ-≃ (enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ _ x<)) (λ x u → rel x (inj₁ u)))
         (λ W ne _ n → enc-correct N _ _
            (vals-ext N (noerr-vals W ne n) (λ x x< → V x (<-⊔ʳ (bound M) (<-⊔ˡ 0 x<))))
            (rel-ext N (λ x u → rel x (inj₂ (inj₁ u)))))

enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ V rel zero =
  enc-correct M ρ₁ ρ₂ (λ x x< → V x (<-⊔ˡ _ x<)) (λ x u → rel x (inj₁ u))
enc-args-correct {suc n} (M ,, args) ρ₁ ρ₂ V rel (suc i) =
  enc-args-correct args ρ₁ ρ₂ (λ x x< → V x (<-⊔ʳ (bound M) x<)) (λ x u → rel x (inj₂ u)) i

{- The end theorem: closed programs ----------------------------------------------}

enclose-correct : ∀ (M : AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
enclose-correct M c = enc-correct M ρ₀ ρ₀ (λ x x< → ⊥-elim (n≮0 (subst (x <_) c x<))) (λ x _ → ≃-refl)
