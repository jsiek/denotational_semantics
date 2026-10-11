{-

  Correctness of the globalize pass (Clos4 → Clos5), clock for clock (see
  the design note in Clock.agda): for every clock, a term and its
  globalization, in related environments, both time out, both go wrong,
  or return related values. Globalize maps each application to one
  application, so the two interpreters call functions in lock step.

  As in the CompCert-style proof (Operational/Correctness/GlobalizeSim.agda),
  which shares the lemmas about growing tables (Compile/GlobalizeTable.agda)
  with this one, the Clos5 interpreter
  runs with the table D that the pass made for the whole program, and the
  relation is indexed by D. A subterm M is compiled to proj₁ (glob M ds)
  for the table ds made before it, and the table made after it,
  proj₂ (glob M ds), only grows into D (_⊑_). Code fun N is related to a
  code pointer code k when the table made by globalizing N, with N's own
  definition on top, is part of D: then looking up k in D finds the
  globalized N (global-⊑). Environments are related pointwise, so there
  is no precondition.

-}

module Compiler.Functional.Correctness.GlobalizeFuel where

open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos4
open import Compiler.Lang.Clos5 using (global)
open import Compiler.Compile.Globalize
open import Compiler.Observation
open import Compiler.Lang.ListUtil using (_‼_; proj-pw)
open import Compiler.Compile.GlobalizeTable
  using (_⊑_; ⊑-refl; ⊑-trans; ∷-⊑; glob-grows; glob-grows-args; global-⊑)
open import Compiler.Functional.Clock
import Compiler.Functional.Interp.Clos4 as S
import Compiler.Functional.Interp.Clos5 as T

open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (just)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

{- The relation, for the final table D --------------------------------------------}

module Rel (D : Defs) where

  infix 4 _≈_

  data _≈_ : S.Val → T.Val → Set where
    fun≈ : ∀ {N ds} → proj₁ (glob N ds) ∷ proj₂ (glob N ds) ⊑ D
      → S.fun N ≈ T.code (length (proj₂ (glob N ds)))
    pair≈ : ∀ {v v' w w'} → v ≈ v' → w ≈ w' → S.pair v w ≈ T.pair v' w'
    const≈ : ∀ {B k} → S.const B k ≈ T.const B k
    tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
    inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
    inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

  _≈ρ_ : S.Env → T.Env → Set
  _≈ρ_ = Pointwise _≈_

  {- Related values are observed alike -}
  obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ T.obs w
  obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ T.obs-list ws
  obs≈ (fun≈ _) = refl
  obs≈ (pair≈ _ _) = refl
  obs≈ const≈ = refl
  obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈-list [] = refl
  obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

  lookup-pw : ∀ x {ρ₁ ρ₂} → ρ₁ ≈ρ ρ₂ → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ x)
  lookup-pw x [] = M.nothing
  lookup-pw zero (r ∷ rs) = M.just r
  lookup-pw (suc x) (r ∷ rs) = lookup-pw x rs

  {- the destructors, on related values -}
  first≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (S.first v) (T.first w)
  first≈ (pair≈ r _) = ret r
  first≈ (fun≈ _) = wrong
  first≈ const≈ = wrong
  first≈ (tup≈ _) = wrong
  first≈ (inl≈ _) = wrong
  first≈ (inr≈ _) = wrong

  second≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (S.second v) (T.second w)
  second≈ (pair≈ _ r) = ret r
  second≈ (fun≈ _) = wrong
  second≈ const≈ = wrong
  second≈ (tup≈ _) = wrong
  second≈ (inl≈ _) = wrong
  second≈ (inr≈ _) = wrong

  {- Clock for clock -------------------------------------------------------------}

  {- M, globalized after the table ds, with the table it makes part of D -}
  run≈ : ∀ ck {ρ₁ ρ₂} M ds → proj₂ (glob M ds) ⊑ D → ρ₁ ≈ρ ρ₂
    → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval D ck ρ₂ (proj₁ (glob M ds)))
  args≈ : ∀ ck {n ρ₁ ρ₂ vs ws} (args : Args (replicate n ■)) ds
    → proj₂ (glob-args args ds) ⊑ D → ρ₁ ≈ρ ρ₂ → Pointwise _≈_ vs ws
    → RelResult (Pointwise _≈_) (S.eval-args ck ρ₁ vs args)
                                (T.eval-args D ck ρ₂ ws (proj₁ (glob-args args ds)))
  apply≈ : ∀ ck {ρ₁ ρ₂ f g} M N ds → proj₂ (glob N (proj₂ (glob M ds))) ⊑ D → ρ₁ ≈ρ ρ₂
    → f ≈ g → RelResult _≈_ (S.apply ck ρ₁ M N f)
                (T.apply D ck ρ₂ (proj₁ (glob M ds)) (proj₁ (glob N (proj₂ (glob M ds)))) g)
  call≈ : ∀ ck {ρ₁ ρ₂} N ds (q : proj₁ (glob N ds) ∷ proj₂ (glob N ds) ⊑ D) → ρ₁ ≈ρ ρ₂
    → RelResult _≈_ (S.call ck N ρ₁) (T.call D ck (global D (length (proj₂ (glob N ds)))) ρ₂)
  branch≈ : ∀ ck {ρ₁ ρ₂ v w} M N ds → proj₂ (glob N (proj₂ (glob M ds))) ⊑ D → ρ₁ ≈ρ ρ₂
    → v ≈ w → RelResult _≈_ (S.branch ck ρ₁ M N v)
                (T.branch D ck ρ₂ (proj₁ (glob M ds)) (proj₁ (glob N (proj₂ (glob M ds)))) w)

  run≈ ck (` x) ds p ρ = from-maybe-rel (lookup-pw x ρ)
  run≈ ck (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds p ρ = ret (fun≈ p)
  run≈ ck (app ⦅ L ,, M ,, N ,, Nil ⦆) ds p ρ =
    bind-rel (run≈ ck L ds (⊑-trans (glob-grows M _) (⊑-trans (glob-grows N _) p)) ρ)
             (apply≈ ck M N _ p ρ)
  run≈ ck (lit B k ⦅ Nil ⦆) ds p ρ = ret const≈
  run≈ ck (pair-op ⦅ L ,, M ,, Nil ⦆) ds p ρ =
    bind-rel (run≈ ck L ds (⊑-trans (glob-grows M _) p) ρ) λ r →
    bind-rel (run≈ ck M _ p ρ) λ r' → ret (pair≈ r r')
  run≈ ck (fst-op ⦅ M ,, Nil ⦆) ds p ρ = bind-rel (run≈ ck M ds p ρ) first≈
  run≈ ck (snd-op ⦅ M ,, Nil ⦆) ds p ρ = bind-rel (run≈ ck M ds p ρ) second≈
  run≈ ck (tuple n ⦅ args ⦆) ds p ρ = bind-rel (args≈ ck args ds p ρ []) (λ rs → ret (tup≈ (reverse⁺ rs)))
  run≈ ck (get i ⦅ M ,, Nil ⦆) ds p ρ = bind-rel (run≈ ck M ds p ρ) get≈
    where
    get≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (S.project i v) (T.project i w)
    get≈ (tup≈ rs) = from-maybe-rel (proj-pw i rs)
    get≈ (fun≈ _) = wrong
    get≈ (pair≈ _ _) = wrong
    get≈ const≈ = wrong
    get≈ (inl≈ _) = wrong
    get≈ (inr≈ _) = wrong
  run≈ ck (inl-op ⦅ M ,, Nil ⦆) ds p ρ = bind-rel (run≈ ck M ds p ρ) (λ r → ret (inl≈ r))
  run≈ ck (inr-op ⦅ M ,, Nil ⦆) ds p ρ = bind-rel (run≈ ck M ds p ρ) (λ r → ret (inr≈ r))
  run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ds p ρ =
    bind-rel (run≈ ck L ds (⊑-trans (glob-grows M _) (⊑-trans (glob-grows N _) p)) ρ)
             (branch≈ ck M N _ p ρ)
  run≈ ck (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ds p ρ =
    bind-rel (run≈ ck M ds (⊑-trans (glob-grows N _) p) ρ) λ r → run≈ ck N _ p (r ∷ ρ)

  args≈ ck {zero} Nil ds p ρ rs = ret rs
  args≈ ck {suc n} (M ,, args) ds p ρ rs =
    bind-rel (run≈ ck M ds (⊑-trans (glob-grows-args args _) p) ρ)
             (λ r → args≈ ck args _ p ρ (r ∷ rs))

  apply≈ ck M N ds p ρ (fun≈ {N'} {ds'} q) =
    bind-rel (run≈ ck M ds (⊑-trans (glob-grows N _) p) ρ) λ e →
    bind-rel (run≈ ck N _ p ρ) λ w → call≈ ck N' ds' q (w ∷ e ∷ [])
  apply≈ ck M N ds p ρ (pair≈ _ _) = wrong
  apply≈ ck M N ds p ρ const≈ = wrong
  apply≈ ck M N ds p ρ (tup≈ _) = wrong
  apply≈ ck M N ds p ρ (inl≈ _) = wrong
  apply≈ ck M N ds p ρ (inr≈ _) = wrong

  {- calling code k finds the globalized body in D -}
  call≈ ck N ds q ρ rewrite global-⊑ q = go ck
    where
    go : ∀ ck → RelResult _≈_ (S.call ck N _) (T.call D ck (just (proj₁ (glob N ds))) _)
    go zero = timeout
    go (suc ck) = run≈ ck N ds (∷-⊑ q) ρ

  branch≈ ck M N ds p ρ (inl≈ r) = run≈ ck M ds (⊑-trans (glob-grows N _) p) (r ∷ ρ)
  branch≈ ck M N ds p ρ (inr≈ r) = run≈ ck N _ p (r ∷ ρ)
  branch≈ ck M N ds p ρ (fun≈ _) = wrong
  branch≈ ck M N ds p ρ (pair≈ _ _) = wrong
  branch≈ ck M N ds p ρ const≈ = wrong
  branch≈ ck M N ds p ρ (tup≈ _) = wrong

{- The end theorem, for any program, with no precondition ----------------------------}

globalize-correct : ∀ M → Equivalent (S.sem M) (T.sem (globalize M))
globalize-correct M = clocked _≈_ obs≈ (λ ck → run≈ ck M [] ⊑-refl [])
  where open Rel (proj₂ (glob M []))
