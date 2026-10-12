{-

  Correctness of the globalize pass (Clos4 → Clos5) by a forward simulation
  between their machines (see the design note in Smallstep.agda).

  The machines run in lock step. The Clos5 machine runs with the table of
  global definitions D that the pass produced for the whole program, and
  the relation is indexed by D.

  The pass threads the table through the term, so a subterm M is compiled
  to proj₁ (glob M ds) for the table ds made before it, and the table
  proj₂ (glob M ds) made after it only grows into D (_⊑_: D extends it with
  newer definitions). So a Clos4 term M is related to a Clos5 term
  (M ↝ M') when M' = proj₁ (glob M ds) for some ds with
  proj₂ (glob M ds) ⊑ D. Code fun N is related to a code pointer code k when
  the table made by globalizing N, with N's own definition on top, is part
  of D: then k is the position of that definition, and looking it up in D
  finds the globalized N (global-⊑), however much the table grew afterwards.

  States, continuations, and the other values are related frame by frame,
  and environments pointwise. There is no precondition: the whole program
  M is related to the main expression of globalize M with D the table it
  makes, and an unbound variable is unbound on both sides.

-}

module Compiler.Operational.Correctness.GlobalizeSim where

open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos4
import Compiler.Lang.Clos5 as C
open import Compiler.Compile.Globalize
open import Compiler.Compile.GlobalizeTable
open import Compiler.Observation
open import Compiler.Operational.Smallstep
open import Compiler.Operational.Simulation
open import ListUtil
import Compiler.Operational.Machine.Clos4 as S
import Compiler.Operational.Machine.Clos5 as T

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; length; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Compiler.Lang.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

{- The simulation relation, for the final table D --------------------------------}

module Rel (D : Defs) where

  infix 4 _↝_ _≈_ _≈k_ _~_

  {- M' is M globalized, with the definitions it makes in D -}
  data _↝_ : AST → C.AST → Set where
    glob↝ : ∀ {M ds} → proj₂ (glob M ds) ⊑ D → M ↝ proj₁ (glob M ds)

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

  data _≈k_ : S.Cont → T.Cont → Set where
    halt : S.halt ≈k T.halt
    appF : ∀ {M M' N N' ρ₁ ρ₂ κ₁ κ₂} → M ↝ M' → N ↝ N' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.appF M N ρ₁ κ₁ ≈k T.appF M' N' ρ₂ κ₂
    appE : ∀ {f f' N N' ρ₁ ρ₂ κ₁ κ₂} → f ≈ f' → N ↝ N' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.appE f N ρ₁ κ₁ ≈k T.appE f' N' ρ₂ κ₂
    appA : ∀ {f f' e e' κ₁ κ₂} → f ≈ f' → e ≈ e' → κ₁ ≈k κ₂
      → S.appA f e κ₁ ≈k T.appA f' e' κ₂
    pairL : ∀ {M M' ρ₁ ρ₂ κ₁ κ₂} → M ↝ M' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.pairL M ρ₁ κ₁ ≈k T.pairL M' ρ₂ κ₂
    pairR : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.pairR v κ₁ ≈k T.pairR w κ₂
    fstK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.fstK κ₁ ≈k T.fstK κ₂
    sndK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.sndK κ₁ ≈k T.sndK κ₂
    tupK : ∀ {vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws → Pointwise _↝_ Ms Ms'
      → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂ → S.tupK vs Ms ρ₁ κ₁ ≈k T.tupK ws Ms' ρ₂ κ₂
    getK : ∀ {n} {i : Fin n} {κ₁ κ₂} → κ₁ ≈k κ₂ → S.getK i κ₁ ≈k T.getK i κ₂
    inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inlK κ₁ ≈k T.inlK κ₂
    inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inrK κ₁ ≈k T.inrK κ₂
    caseK : ∀ {M M' N N' ρ₁ ρ₂ κ₁ κ₂} → M ↝ M' → N ↝ N' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.caseK M N ρ₁ κ₁ ≈k T.caseK M' N' ρ₂ κ₂
    letK : ∀ {N N' ρ₁ ρ₂ κ₁ κ₂} → N ↝ N' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.letK N ρ₁ κ₁ ≈k T.letK N' ρ₂ κ₂
    primL : ∀ {p M M' ρ₁ ρ₂ κ₁ κ₂} → M ↝ M' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.primL p M ρ₁ κ₁ ≈k T.primL p M' ρ₂ κ₂
    primR : ∀ {p v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.primR p v κ₁ ≈k T.primR p w κ₂

  data _~_ : S.State → T.State → Set where
    eval~ : ∀ {M M' ρ₁ ρ₂ κ₁ κ₂} → M ↝ M' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
      → S.eval M ρ₁ κ₁ ~ T.eval M' ρ₂ κ₂
    ret~ : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.ret v κ₁ ~ T.ret w κ₂

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

  {- related operands give related results of a primitive -}
  prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (S.prim? p v₁ v₂) (T.prim? p w₁ w₂)
  prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (T.obs w₁) (T.obs w₂)
  ... | nothing = M.nothing
  ... | just (int n) = M.just const≈
  ... | just (bool true) = M.just (inl≈ (tup≈ []))
  ... | just (bool false) = M.just (inr≈ (tup≈ []))

  {- a subterm, whose table is extended by the rest of the term -}
  sub↝ : ∀ {M ds ds'} → proj₂ (glob M ds) ⊑ ds' → ds' ⊑ D → M ↝ proj₁ (glob M ds)
  sub↝ p q = glob↝ (⊑-trans p q)

  glob-list : ∀ {n} (args : Args (replicate n ■)) ds → proj₂ (glob-args args ds) ⊑ D
    → Pointwise _↝_ (args→list args) (args→list (proj₁ (glob-args args ds)))
  glob-list {zero} Nil ds p = []
  glob-list {suc n} (M ,, args) ds p =
    sub↝ (glob-grows-args args _) p ∷ glob-list args (proj₂ (glob M ds)) p

{- The simulation, for any Clos5 program with table D ---------------------------}

module _ (D : Defs) (M₀ : C.AST) where
  open Rel D

  L₂ = T.sem (C.program D M₀)

  one : ∀ {s s'} → T.step D s ≡ next s' → Plus L₂ s s'
  one eq = plus eq ε

  {- answering a lookup or a projection -}
  ret?-answers : ∀ {mv mw κ₁ κ₂ s₂} → M.Pointwise _≈_ mv mw → κ₁ ≈k κ₂
    → T.step D s₂ ≡ T.ret? mw κ₂ → Answers L₂ _~_ (S.ret? mv κ₁) s₂
  ret?-answers (M.just r) κ eq = steps (one eq) (ret~ r κ)
  ret?-answers M.nothing κ eq = stops eq

  lookup-pw : ∀ x {ρ₁ ρ₂} → ρ₁ ≈ρ ρ₂ → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ x)
  lookup-pw x [] = M.nothing
  lookup-pw zero (r ∷ rs) = M.just r
  lookup-pw (suc x) (r ∷ rs) = lookup-pw x rs

  tuple-next~ : ∀ {vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → Pointwise _↝_ Ms Ms' → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → S.tuple-next vs Ms ρ₁ κ₁ ~ T.tuple-next ws Ms' ρ₂ κ₂
  tuple-next~ rs [] ρ κ = ret~ (tup≈ (reverse⁺ rs)) κ
  tuple-next~ rs (g ∷ gs) ρ κ = eval~ g ρ (tupK rs gs ρ κ)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (S.step s₁) s₂
  sim (eval~ {M = ` x} (glob↝ p) ρ κ) = ret?-answers (lookup-pw x ρ) κ refl
  sim (eval~ {M = fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (ret~ (fun≈ p) κ)
  sim (eval~ {M = app ⦅ L ,, M ,, N ,, Nil ⦆} (glob↝ {ds = ds} p) ρ κ) =
    steps (one refl)
      (eval~ (sub↝ (⊑-trans (glob-grows M d₁) (glob-grows N (proj₂ (glob M d₁)))) p)
             ρ (appF (sub↝ (glob-grows N _) p) (glob↝ p) ρ κ))
    where d₁ = proj₂ (glob L ds)
  sim (eval~ {M = lit B k ⦅ Nil ⦆} (glob↝ p) ρ κ) = steps (one refl) (ret~ const≈ κ)
  sim (eval~ {M = pair-op ⦅ L ,, M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (sub↝ (glob-grows M _) p) ρ (pairL (glob↝ p) ρ κ))
  sim (eval~ {M = fst-op ⦅ M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (glob↝ p) ρ (fstK κ))
  sim (eval~ {M = snd-op ⦅ M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (glob↝ p) ρ (sndK κ))
  sim (eval~ {M = tuple n ⦅ args ⦆} (glob↝ {ds = ds} p) ρ κ) =
    steps (one refl) (tuple-next~ [] (glob-list args ds p) ρ κ)
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (glob↝ p) ρ (getK κ))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (glob↝ p) ρ (inlK κ))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (glob↝ p) ρ (inrK κ))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} (glob↝ {ds = ds} p) ρ κ) =
    steps (one refl)
      (eval~ (sub↝ (⊑-trans (glob-grows M d₁) (glob-grows N (proj₂ (glob M d₁)))) p)
             ρ (caseK (sub↝ (glob-grows N _) p) (glob↝ p) ρ κ))
    where d₁ = proj₂ (glob L ds)
  sim (eval~ {M = let-op ⦅ M ,, ⟩ N ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (sub↝ (glob-grows N _) p) ρ (letK (glob↝ p) ρ κ))
  sim (eval~ {M = prim q ⦅ L ,, M ,, Nil ⦆} (glob↝ p) ρ κ) =
    steps (one refl) (eval~ (sub↝ (glob-grows M _) p) ρ (primL (glob↝ p) ρ κ))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r (appF gM gN ρ κ)) = steps (one refl) (eval~ gM ρ (appE r gN ρ κ))
  sim (ret~ r (appE f gN ρ κ)) = steps (one refl) (eval~ gN ρ (appA f r κ))
  sim (ret~ {w = w} r (appA {e' = e'} {κ₂ = κ₂} (fun≈ p) e κ)) =
    steps (one (cong (λ m → T.call m w e' κ₂) (global-⊑ p)))
          (eval~ (glob↝ (∷-⊑ p)) (r ∷ e ∷ []) κ)
  sim (ret~ r (appA (pair≈ _ _) e κ)) = stops refl
  sim (ret~ r (appA const≈ e κ)) = stops refl
  sim (ret~ r (appA (tup≈ _) e κ)) = stops refl
  sim (ret~ r (appA (inl≈ _) e κ)) = stops refl
  sim (ret~ r (appA (inr≈ _) e κ)) = stops refl
  sim (ret~ r (pairL gM ρ κ)) = steps (one refl) (eval~ gM ρ (pairR r κ))
  sim (ret~ r (pairR r' κ)) = steps (one refl) (ret~ (pair≈ r' r) κ)
  sim (ret~ (pair≈ r _) (fstK κ)) = steps (one refl) (ret~ r κ)
  sim (ret~ (fun≈ _) (fstK κ)) = stops refl
  sim (ret~ const≈ (fstK κ)) = stops refl
  sim (ret~ (tup≈ _) (fstK κ)) = stops refl
  sim (ret~ (inl≈ _) (fstK κ)) = stops refl
  sim (ret~ (inr≈ _) (fstK κ)) = stops refl
  sim (ret~ (pair≈ _ r) (sndK κ)) = steps (one refl) (ret~ r κ)
  sim (ret~ (fun≈ _) (sndK κ)) = stops refl
  sim (ret~ const≈ (sndK κ)) = stops refl
  sim (ret~ (tup≈ _) (sndK κ)) = stops refl
  sim (ret~ (inl≈ _) (sndK κ)) = stops refl
  sim (ret~ (inr≈ _) (sndK κ)) = stops refl
  sim (ret~ r (tupK rs gs ρ κ)) = steps (one refl) (tuple-next~ (r ∷ rs) gs ρ κ)
  sim (ret~ (tup≈ rs) (getK {i = i} κ)) = ret?-answers (proj-pw i rs) κ refl
  sim (ret~ (fun≈ _) (getK κ)) = stops refl
  sim (ret~ (pair≈ _ _) (getK κ)) = stops refl
  sim (ret~ const≈ (getK κ)) = stops refl
  sim (ret~ (inl≈ _) (getK κ)) = stops refl
  sim (ret~ (inr≈ _) (getK κ)) = stops refl
  sim (ret~ r (inlK κ)) = steps (one refl) (ret~ (inl≈ r) κ)
  sim (ret~ r (inrK κ)) = steps (one refl) (ret~ (inr≈ r) κ)
  sim (ret~ (inl≈ r) (caseK gM gN ρ κ)) = steps (one refl) (eval~ gM (r ∷ ρ) κ)
  sim (ret~ (inr≈ r) (caseK gM gN ρ κ)) = steps (one refl) (eval~ gN (r ∷ ρ) κ)
  sim (ret~ (fun≈ _) (caseK _ _ _ κ)) = stops refl
  sim (ret~ (pair≈ _ _) (caseK _ _ _ κ)) = stops refl
  sim (ret~ const≈ (caseK _ _ _ κ)) = stops refl
  sim (ret~ (tup≈ _) (caseK _ _ _ κ)) = stops refl
  sim (ret~ r (letK gN ρ κ)) = steps (one refl) (eval~ gN (r ∷ ρ) κ)
  sim (ret~ r (primL gM ρ κ)) = steps (one refl) (eval~ gM ρ (primR r κ))
  sim (ret~ s (primR {p} r κ)) = ret?-answers (prim≈ p r s) κ refl

{- The end theorem -------------------------------------------------------------}

{- for any program, with no precondition -}

globalize-fsim : ∀ M → FSim (S.sem M) (T.sem (globalize M))
globalize-fsim M =
  plus-simulation _~_ (eval~ (glob↝ ⊑-refl) [] halt) (sim D (proj₁ (glob M [])))
  where D = proj₂ (glob M [])
        open Rel D

globalize-correct : ∀ M → Equivalent (S.sem M) (T.sem (globalize M))
globalize-correct M = equivalent (globalize-fsim M)
