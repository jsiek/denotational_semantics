{-

  Correctness of the enclose pass (ISWIM → Clos2), in Scott domains.

  ISWIM and Clos2 have the same values, and enclose only changes where a
  function's body finds its free variables: in the surrounding
  environment in ISWIM, and among the values its closure captured in
  Clos2. So the pass preserves meanings exactly, ⟦ M ⟧ ρ₁ = ⟦ enclose M ⟧₂ ρ₂,
  when the environments agree on the variables M uses, and every value
  of ρ₂ is defined (as Clos2 closures are strict in their free
  variables). A function (or a branch of a case) is strict, so its body
  needs to agree only on defined arguments, which keep ρ₂ defined.

  As the graph-model proof (proof/Correctness/Graph/EncloseCorrect.agda),
  with equality of values in place of equality of sets.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Data.Nat using (_<_; _<?_; _∸_; _+_)
open import Data.Nat.Properties using (+-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥; +-suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary using (Dec; yes; no)

open import Framework.abt.GSubst using (_•_)
open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil
open import Language.ISWIM
import Language.Clos2 as C
open import proof.Framework.Syntax.Uses Op sig
open import Compiler.Optimize using (bind-n-ast)
open import Compiler.Enclose

module proof.Correctness.Scott.EncloseCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; tuple to tupleᵈ)
open import Framework.Scott.Semantics pt fe pe using (Res; Ress; toPow; nthᶜ; tupleᶜ)
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Semantics.Scott.ISWIM pt fe pe
open import Semantics.Scott.Clos2 pt fe pe
  renaming (⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧ₐ₂; ⟦_⟧₊ to ⟦_⟧₊₂) using (apply-n)

private
 ≡→＝ : {X : 𝓤 ̇ } {x y : X} → x Eq.≡ y → x ＝ y
 ≡→＝ Eq.refl = refl

{- environments, and environments of defined values -}
Env' : 𝓤₁ ̇
Env' = ⟨ Env ⟩

defined-env : Env' → 𝓤₀ ̇
defined-env ρ = (x : ℕ) → defined (ρ x)

{- The captured free variables ----------------------------------------------}

{- n values, and all of them defined -}
all-defined : (n : ℕ) → ⟨ Ress (replicate n ■) ⟩ → 𝓤₀ ̇
all-defined zero _ = 𝟙
all-defined (succ n) (d , ds) = defined d × all-defined n ds

all-defined-at : (n : ℕ) (ds : ⟨ Ress (replicate n ■) ⟩) → all-defined n ds
  → (i : Fin n) → defined (nthᶜ n i · ds)
all-defined-at (succ n) (d , ds) (h , _) zero = h
all-defined-at (succ n) (d , ds) (_ , h) (suc i) = all-defined-at n ds h i

{- bind n values one at a time, the last one ending up first -}
push : (n : ℕ) → ⟨ Ress (replicate n ■) ⟩ → Env' → Env'
push zero _ ρ = ρ
push (succ n) (d , ds) ρ = push n ds (d • ρ)

push-defined : (n : ℕ) (ds : ⟨ Ress (replicate n ■) ⟩) (ρ : Env')
  → all-defined n ds → defined-env ρ → defined-env (push n ds ρ)
push-defined zero _ ρ _ h = h
push-defined (succ n) (d , ds) ρ (hd , hds) h = push-defined n ds (d • ρ) hds h'
 where
  h' : defined-env (d • ρ)
  h' zero = hd
  h' (succ x) = h x

push-plus : (n : ℕ) (ds : ⟨ Ress (replicate n ■) ⟩) (ρ : Env') (j : ℕ) → push n ds ρ (n + j) ＝ ρ j
push-plus zero _ ρ j = refl
push-plus (succ n) (d , ds) ρ j =
 ap (push n ds (d • ρ)) (≡→＝ (Eq.sym (+-suc n j))) ∙ push-plus n ds (d • ρ) (succ j)

{- the values of ` (n - 1) , ... , ` 0 -}
fv-vars-defined : (m : ℕ) (ρ : Env') → defined-env ρ → all-defined m (⟦ fv-vars m ⟧₊₂ · ρ)
fv-vars-defined zero ρ h = ⋆
fv-vars-defined (succ m) ρ h = h m , fv-vars-defined m ρ h

{- binding them one at a time puts ρ k at position k -}
push-vars : (n : ℕ) (ρ σ : Env') (k : ℕ) → k < n → push n (⟦ fv-vars n ⟧₊₂ · ρ) σ k ＝ ρ k
push-vars (succ n) ρ σ k k<sn = by-cases (k <? n)
 where
  by-cases : Dec (k < n) → push n (⟦ fv-vars n ⟧₊₂ · ρ) (ρ n • σ) k ＝ ρ k
  by-cases (yes k<n) = push-vars n ρ (ρ n • σ) k k<n
  by-cases (no ¬k<n) =
   ap (push n (⟦ fv-vars n ⟧₊₂ · ρ) (ρ n • σ)) (≡→＝ (Eq.trans k≡n (Eq.sym (+-identityʳ n))))
   ∙ push-plus n (⟦ fv-vars n ⟧₊₂ · ρ) (ρ n • σ) 0 ∙ ap ρ (≡→＝ (Eq.sym k≡n))
   where
    k≡n : k Eq.≡ n
    k≡n = ≤-antisym (≤-pred k<sn) (≮⇒≥ ¬k<n)

{- applying the meaning of a body under k binders to k values -}
apply-push : (k : ℕ) (a : C.Arg (ν-n k (ν ■))) (ρ : Env') (ds : ⟨ Ress (replicate k ■) ⟩) (d : ⟨ 𝔻 ⟩)
  → apply-n k · (⟦ a ⟧ₐ₂ · ρ , ds) · d ＝ ⟦ C.unbind-n k a ⟧₂ · (d • push k ds ρ)
apply-push zero (C.bind (C.ast N)) ρ _ d = refl
apply-push (succ k) (C.bind a) ρ (d' , ds) d = apply-push k a (d' • ρ) ds d

unbind-bind : (m : ℕ) (N : C.AST) → C.unbind-n m (bind-n-ast m N) ＝ N
unbind-bind zero N = refl
unbind-bind (succ m) N = unbind-bind m N

{- The main lemma -----------------------------------------------------------}

enc-correct : (M : AST) (ρ₁ ρ₂ : Env') → defined-env ρ₂ → ((x : ℕ) → Uses x M → ρ₁ x ＝ ρ₂ x)
  → ⟦ M ⟧ · ρ₁ ＝ ⟦ enclose M ⟧₂ · ρ₂

enc-args-correct : {n : ℕ} (args : Args (replicate n ■)) (ρ₁ ρ₂ : Env') → defined-env ρ₂
  → ((x : ℕ) → UsesArgs x args → ρ₁ x ＝ ρ₂ x)
  → ⟦ args ⟧₊ · ρ₁ ＝ ⟦ enc-args args ⟧₊₂ · ρ₂

{- a strict body: it agrees on defined arguments -}
enc-body : (N : AST) (ρ₁ ρ₂ : Env') → defined-env ρ₂ → ((x : ℕ) → Uses (succ x) N → ρ₁ x ＝ ρ₂ x)
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ₁) ＝ ⟦ enclose N ⟧₂ · (d • ρ₂)
enc-body N ρ₁ ρ₂ h rel d hd = enc-correct N (d • ρ₁) (d • ρ₂) h' rel'
 where
  h' : defined-env (d • ρ₂)
  h' zero = hd
  h' (succ x) = h x
  rel' : (x : ℕ) → Uses x N → (d • ρ₁) x ＝ (d • ρ₂) x
  rel' zero _ = refl
  rel' (succ x) u = rel x u

enc-correct (` x) ρ₁ ρ₂ h rel = rel x Eq.refl
enc-correct (lam ⦅ ⟩ N ,, Nil ⦆) ρ₁ ρ₂ h rel =
 Λ-cong (⟦ bind (ast N) ⟧ₐ · ρ₁) g₂ body ∙ (guard-defined m (toPow m · ds) ds-defined (Λ · g₂)) ⁻¹
 where
  m = bound N ∸ 1
  ds = ⟦ fv-vars m ⟧₊₂ · ρ₂
  σ = push m ds (λ _ → ω)
  g₂ = apply-n m · (⟦ bind-n-ast m (enclose N) ⟧ₐ₂ · (λ _ → ω) , ds)
  ds-defined : (i : Fin m) → defined ((toPow m · ds) i)
  ds-defined = all-defined-at m ds (fv-vars-defined m ρ₂ h)
  σ-defined : defined-env σ
  σ-defined = push-defined m ds (λ _ → ω) (fv-vars-defined m ρ₂ h) (λ _ → ω-defined)
  body : (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ₁) ＝ g₂ · d
  body d hd = enc-body N ρ₁ σ σ-defined
                (λ k u → rel k (inj₁ u) ∙ push-vars m ρ₂ (λ _ → ω) k (<-∸1 (uses-bound (succ k) N u)) ⁻¹)
                d hd
              ∙ ap (λ - → ⟦ - ⟧₂ · (d • σ)) (unbind-bind m (enclose N)) ⁻¹
              ∙ apply-push m (bind-n-ast m (enclose N)) (λ _ → ω) ds d ⁻¹
enc-correct (app ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap₂ (λ a b → appᵈ · a · b) (enc-correct L ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
                           (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₂ (inj₁ u))))
enc-correct (lit B k ⦅ Nil ⦆) ρ₁ ρ₂ h rel = refl
enc-correct (tuple n ⦅ args ⦆) ρ₁ ρ₂ h rel =
 ap (λ - → tupleᶜ n · -) (enc-args-correct args ρ₁ ρ₂ h rel)
enc-correct (get i ⦅ M ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap (λ - → proj i · -) (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
enc-correct (inl-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap (λ - → inl · -) (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
enc-correct (inr-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap (λ - → inr · -) (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
enc-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap₂ (λ a b → cases · a · b)
   (enc-correct L ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
   (ap₂ _,_ (strict-cong (⟦ bind (ast M) ⟧ₐ · ρ₁) (⟦ C.bind (C.ast (enclose M)) ⟧ₐ₂ · ρ₂)
               (enc-body M ρ₁ ρ₂ h (λ x u → rel x (inj₂ (inj₁ u)))))
            (strict-cong (⟦ bind (ast N) ⟧ₐ · ρ₁) (⟦ C.bind (C.ast (enclose N)) ⟧ₐ₂ · ρ₂)
               (enc-body N ρ₁ ρ₂ h (λ x u → rel x (inj₂ (inj₂ (inj₁ u)))))))
enc-correct (prim p ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ h rel =
 ap₂ (λ a b → primD p · a · b) (enc-correct L ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
                               (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₂ (inj₁ u))))

enc-args-correct {zero} Nil ρ₁ ρ₂ h rel = refl
enc-args-correct {succ n} (M ,, args) ρ₁ ρ₂ h rel =
 ap₂ _,_ (enc-correct M ρ₁ ρ₂ h (λ x u → rel x (inj₁ u)))
         (enc-args-correct args ρ₁ ρ₂ h (λ x u → rel x (inj₂ u)))

{- The end theorem ------------------------------------------------------------}

{- the environment of a closed program: every variable means ω -}
ρ₀ : Env'
ρ₀ = λ _ → ω

enclose-correct-closed : (M : AST) → ⟦ M ⟧ · ρ₀ ＝ ⟦ enclose M ⟧₂ · ρ₀
enclose-correct-closed M = enc-correct M ρ₀ ρ₀ (λ _ → ω-defined) (λ _ _ → refl)
