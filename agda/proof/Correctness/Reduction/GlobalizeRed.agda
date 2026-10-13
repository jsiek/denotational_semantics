{-

  Correctness of the globalize pass (Clos4 → Clos5) by a forward
  simulation between their reduction semantics (see the design note in
  Semantics/Reduction/Smallstep.agda).

  The two reductions run in lock step. The Clos5 program runs with the
  table of global definitions D that the pass produced for the whole
  program, and the relation is indexed by D.

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-subst), except for code: fun N is related to a reference k to a
  definition N' of D when N is related to N'. The code of a function,
  which no substitution enters, is related through the compilation
  function: the pass threads the table through the term, so a subterm M
  is compiled to proj₁ (glob M ds) for the table ds made before it, and
  M is related to it when the table made after it only grows into D
  (glob≈, with the lemmas about growing tables shared with the CEK
  proof, proof/Compiler/GlobalizeTable.agda).

  No precondition is needed: a free variable goes wrong in both.

-}

module proof.Correctness.Reduction.GlobalizeRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos4
import Language.Clos5 as C
open import Compiler.Globalize
open import proof.Compiler.GlobalizeTable
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-wrong
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Clos4 as S
import proof.Semantics.Reduction.Clos5 as T
import proof.Framework.Syntax.Subst Op sig as SS
import proof.Framework.Syntax.Subst C.Op C.sig as TS
import proof.Framework.Syntax.SubstRel Op sig C.Op C.sig as SubstRel
open SS using (sub; sub-args; exts; ids)
open import proof.Framework.ListUtil using (proj-pw)

open import Data.Fin using (Fin)
open import Data.List using (List; []; replicate; _∷_)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

module _ (D : Defs) where

  {- The relation on terms, for the final table D ---------------------------------}

  infix 4 _≈_
  data _≈_ : AST → C.AST → Set where
    var≈ : ∀ {x} → ` x ≈ C.` x
    fun≈ : ∀ {k N N'} → C.global D k ≡ just N' → N ≈ N'
      → fun-op ⦅ cons (clear (bind (bind (ast N)))) Nil ⦆ ≈ C.fun-ref k C.⦅ Nil ⦆
    app≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
      → app ⦅ L ,, M ,, N ,, Nil ⦆ ≈ C.app C.⦅ L' ,, M' ,, N' ,, Nil ⦆
    lit≈ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈ C.lit B k C.⦅ Nil ⦆
    pair≈ : ∀ {L L' M M'} → L ≈ L' → M ≈ M' → pair-op ⦅ L ,, M ,, Nil ⦆ ≈ C.pair-op C.⦅ L' ,, M' ,, Nil ⦆
    fst≈ : ∀ {M M'} → M ≈ M' → fst-op ⦅ M ,, Nil ⦆ ≈ C.fst-op C.⦅ M' ,, Nil ⦆
    snd≈ : ∀ {M M'} → M ≈ M' → snd-op ⦅ M ,, Nil ⦆ ≈ C.snd-op C.⦅ M' ,, Nil ⦆
    tuple≈ : ∀ {n as as'} → Pw _≈_ {n} as as' → tuple n ⦅ as ⦆ ≈ C.tuple n C.⦅ as' ⦆
    get≈ : ∀ {n} {i : Fin n} {M M'} → M ≈ M' → get i ⦅ M ,, Nil ⦆ ≈ C.get i C.⦅ M' ,, Nil ⦆
    inl≈ : ∀ {M M'} → M ≈ M' → inl-op ⦅ M ,, Nil ⦆ ≈ C.inl-op C.⦅ M' ,, Nil ⦆
    inr≈ : ∀ {M M'} → M ≈ M' → inr-op ⦅ M ,, Nil ⦆ ≈ C.inr-op C.⦅ M' ,, Nil ⦆
    case≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
      → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ C.case-op C.⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆
    prim≈ : ∀ {p L L' M M'} → L ≈ L' → M ≈ M' → prim p ⦅ L ,, M ,, Nil ⦆ ≈ C.prim p C.⦅ L' ,, M' ,, Nil ⦆
    let≈ : ∀ {M M' N N'} → M ≈ M' → N ≈ N' → let-op ⦅ M ,, ⟩ N ,, Nil ⦆ ≈ C.let-op C.⦅ M' ,, ⟩ N' ,, Nil ⦆

  {- the operands of an operator, related -}
  GR : ∀ {bs} → Args bs → C.Args bs → Set
  GRa : ∀ {b} → Arg b → C.Arg b → Set
  GR nil C.nil = ⊤
  GR (cons a as) (C.cons a' as') = GRa a a' × GR as as'
  GRa (ast M) (C.ast M') = M ≈ M'
  GRa (bind a) (C.bind a') = GRa a a'
  GRa (clear a) (C.clear a') = GRa a a'

  {- a term is related to its globalization, when the table it makes grows into D -}
  glob≈ : ∀ M ds → proj₂ (glob M ds) ⊑ D → M ≈ proj₁ (glob M ds)
  glob≈a : ∀ {b} (a : Arg b) ds → proj₂ (glob-arg a ds) ⊑ D → GRa a (proj₁ (glob-arg a ds))
  glob≈s : ∀ {bs} (as : Args bs) ds → proj₂ (glob-args as ds) ⊑ D → GR as (proj₁ (glob-args as ds))
  glob≈ (` x) ds p = var≈
  glob≈ (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds p = fun≈ (global-⊑ p) (glob≈ N ds (∷-⊑ p))
  glob≈ (app ⦅ as@(L ,, M ,, N ,, Nil) ⦆) ds p with glob≈s as ds p
  ... | r , s , t , _ = app≈ r s t
  glob≈ (lit B k ⦅ Nil ⦆) ds p = lit≈
  glob≈ (pair-op ⦅ as@(L ,, M ,, Nil) ⦆) ds p with glob≈s as ds p
  ... | r , s , _ = pair≈ r s
  glob≈ (fst-op ⦅ as@(M ,, Nil) ⦆) ds p = fst≈ (proj₁ (glob≈s as ds p))
  glob≈ (snd-op ⦅ as@(M ,, Nil) ⦆) ds p = snd≈ (proj₁ (glob≈s as ds p))
  glob≈ (tuple n ⦅ as ⦆) ds p = tuple≈ (pw n as (glob≈s as ds p))
    where pw : ∀ n (as : Args (replicate n ■)) {as'} → GR as as' → Pw _≈_ as as'
          pw zero nil {C.nil} _ = []
          pw (suc n) (cons (ast M) as) {C.cons (C.ast M') as'} (r , rs) = r ∷ pw n as rs
  glob≈ (get i ⦅ as@(M ,, Nil) ⦆) ds p = get≈ (proj₁ (glob≈s as ds p))
  glob≈ (inl-op ⦅ as@(M ,, Nil) ⦆) ds p = inl≈ (proj₁ (glob≈s as ds p))
  glob≈ (inr-op ⦅ as@(M ,, Nil) ⦆) ds p = inr≈ (proj₁ (glob≈s as ds p))
  glob≈ (case-op ⦅ as@(L ,, ⟩ M ,, ⟩ N ,, Nil) ⦆) ds p with glob≈s as ds p
  ... | r , s , t , _ = case≈ r s t
  glob≈ (prim q ⦅ as@(L ,, M ,, Nil) ⦆) ds p with glob≈s as ds p
  ... | r , s , _ = prim≈ r s
  glob≈ (let-op ⦅ as@(M ,, ⟩ N ,, Nil) ⦆) ds p with glob≈s as ds p
  ... | r , s , _ = let≈ r s
  glob≈a (ast M) ds p = glob≈ M ds p
  glob≈a (bind a) ds p = glob≈a a ds p
  glob≈a (clear a) ds p = glob≈a a ds p
  glob≈s nil ds p = tt
  glob≈s (cons a as) ds p = glob≈a a ds (⊑-trans (glob-grows-args as _) p) , glob≈s as _ p

  {- Closure under substitution -------------------------------------------------}

  module Kit (P : SS.Subst → TS.Subst → Set) (p≈ : ∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x)
    (pok : ∀ {σ σ'} → P σ σ' → ⊤) (pexts : ∀ {σ σ'} → P σ σ' → P (exts σ) (TS.exts σ')) where

    ≈-sub : ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → sub σ M ≈ TS.sub σ' M'
    ≈-subs : ∀ {σ σ' n as as'} → P σ σ' → Pw _≈_ {n} as as' → Pw _≈_ (sub-args σ as) (TS.sub-args σ' as')
    ≈-sub p var≈ = p≈ p _
    ≈-sub p (fun≈ e r) = fun≈ e r
    ≈-sub p (app≈ r s t) = app≈ (≈-sub p r) (≈-sub p s) (≈-sub p t)
    ≈-sub p lit≈ = lit≈
    ≈-sub p (pair≈ r s) = pair≈ (≈-sub p r) (≈-sub p s)
    ≈-sub p (fst≈ r) = fst≈ (≈-sub p r)
    ≈-sub p (snd≈ r) = snd≈ (≈-sub p r)
    ≈-sub p (tuple≈ rs) = tuple≈ (≈-subs p rs)
    ≈-sub p (get≈ r) = get≈ (≈-sub p r)
    ≈-sub p (inl≈ r) = inl≈ (≈-sub p r)
    ≈-sub p (inr≈ r) = inr≈ (≈-sub p r)
    ≈-sub p (case≈ r s t) = case≈ (≈-sub p r) (≈-sub (pexts p) s) (≈-sub (pexts p) t)
    ≈-sub p (prim≈ r s) = prim≈ (≈-sub p r) (≈-sub p s)
    ≈-sub p (let≈ r s) = let≈ (≈-sub p r) (≈-sub (pexts p) s)
    ≈-subs p [] = []
    ≈-subs p (r ∷ rs) = ≈-sub p r ∷ ≈-subs p rs

  open SubstRel.Closure _≈_ var≈ (λ _ _ → ⊤) (λ _ → tt) (λ _ → tt) Kit.≈-sub using (≈-subst)

  {- The simulation -----------------------------------------------------------------}

  Ans′ = Ans (T.red D) T.Value _≈_

  vr : ∀ {V} → T.Value V → T.red D V ≡ val
  vr = T.value-red

  obs≈ : ∀ {M M'} → M ≈ M' → S.obs M ≡ T.obs M'
  obs≈s : ∀ {n as as'} → Pw _≈_ {n} as as' → S.obs-args as ≡ T.obs-args as'
  obs≈ var≈ = refl
  obs≈ (fun≈ _ _) = refl
  obs≈ (app≈ _ _ _) = refl
  obs≈ lit≈ = refl
  obs≈ (pair≈ _ _) = refl
  obs≈ (fst≈ _) = refl
  obs≈ (snd≈ _) = refl
  obs≈ (tuple≈ rs) = cong o-tuple (obs≈s rs)
  obs≈ (get≈ _) = refl
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (case≈ _ _ _) = refl
  obs≈ (prim≈ _ _) = refl
  obs≈ (let≈ _ _) = refl
  obs≈s [] = refl
  obs≈s (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈s rs)

  ret?-ans : ∀ {M mv mw X} → M.Pointwise _≈_ mv mw → T.red D X ≡ T.ret? mw → Ans′ M (S.ret? mv) X
  ret?-ans (M.just r) e = to (one e) r
  ret?-ans M.nothing e = wrong ε e

  {- a call, once its operands are values -}
  call-step : ∀ {F E W r} → T.Value F → T.Value E → T.Value W → T.call D F E W ≡ r
    → T.red D (C.app C.⦅ F ,, E ,, W ,, Nil ⦆) ≡ r
  call-step v v' w e rewrite vr v | vr v' | vr w = e

  one≈ : ∀ {V V'} → V ≈ V' → T.Value V' → ∀ x → (V • ids) x ≈ (V' TS.• TS.ids) x
  one≈ r v zero = r
  one≈ r v (suc x) = var≈

  sim : ∀ {M M'} → M ≈ M' → Ans′ M (S.red M) M'
  sims : ∀ {n as as'} → Pw _≈_ {n} as as' → Ans (T.red-args D) T.Values (Pw _≈_) as (S.red-args as) as'
  sim var≈ = wrong ε refl
  sim (fun≈ e r) = val ε T.fun (fun≈ e r)
  sim (app≈ {L} {L'} {M} {M'} {N} {N'} r s t) =
    ans-in (frame _ (λ _ → refl)) (λ r' → app≈ r' s t) (sim r)
      λ v r' → ans-in (frame {g = λ X → C.app C.⦅ _ ,, X ,, N' ,, Nil ⦆} _ (λ X → val-in (vr v)))
                      (λ s' → app≈ r' s' t) (sim s)
        λ v' s' → ans-in (frame {g = λ X → C.app C.⦅ _ ,, _ ,, X ,, Nil ⦆} _
                                (λ X → trans (val-in (vr v)) (val-in (vr v'))))
                         (app≈ r' s') (sim t) (call-sim v v' r' s')
    where
    call-sim : ∀ {F F' E E' W W'} → T.Value F' → T.Value E' → F ≈ F' → E ≈ E' → T.Value W' → W ≈ W'
      → Ans′ (app ⦅ F ,, E ,, W ,, Nil ⦆) (S.call F E W) (C.app C.⦅ F' ,, E' ,, W' ,, Nil ⦆)
    call-sim v v' (fun≈ e r) s' w t' =
      to (one (call-step v v' w (cong (λ x → T.call? x _ _) e)))
         (≈-subst ((λ { zero → t' ; (suc zero) → s' ; (suc (suc x)) → var≈ }) , tt) r)
    call-sim v@(T.pair _ _) v' (pair≈ _ _) s' w t' = wrong ε (call-step v v' w refl)
    call-sim v@T.lit v' lit≈ s' w t' = wrong ε (call-step v v' w refl)
    call-sim v@(T.tuple _) v' (tuple≈ _) s' w t' = wrong ε (call-step v v' w refl)
    call-sim v@(T.inl _) v' (inl≈ _) s' w t' = wrong ε (call-step v v' w refl)
    call-sim v@(T.inr _) v' (inr≈ _) s' w t' = wrong ε (call-step v v' w refl)
  sim lit≈ = val ε T.lit lit≈
  sim (pair≈ r s) =
    ans-in (frame _ (λ _ → refl)) (λ r' → pair≈ r' s) (sim r)
      λ v r' → ans-in (frame {g = λ X → C.pair-op C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (vr v))) (pair≈ r') (sim s)
        λ v' s' → val ε (T.pair v v') (pair≈ r' s')
  sim (fst≈ r) = ans-in (frame _ (λ _ → refl)) fst≈ (sim r) fst-sim
    where
    fst-sim : ∀ {M V'} → T.Value V' → M ≈ V' → Ans′ (fst-op ⦅ M ,, Nil ⦆) (S.fst? M) (C.fst-op C.⦅ V' ,, Nil ⦆)
    fst-sim v@(T.pair _ _) (pair≈ r s) = to (one (val-in (vr v))) r
    fst-sim T.fun (fun≈ _ _) = wrong ε refl
    fst-sim T.lit lit≈ = wrong ε refl
    fst-sim v@(T.tuple _) (tuple≈ _) = wrong ε (val-in (vr v))
    fst-sim v@(T.inl _) (inl≈ _) = wrong ε (val-in (vr v))
    fst-sim v@(T.inr _) (inr≈ _) = wrong ε (val-in (vr v))
  sim (snd≈ r) = ans-in (frame _ (λ _ → refl)) snd≈ (sim r) snd-sim
    where
    snd-sim : ∀ {M V'} → T.Value V' → M ≈ V' → Ans′ (snd-op ⦅ M ,, Nil ⦆) (S.snd? M) (C.snd-op C.⦅ V' ,, Nil ⦆)
    snd-sim v@(T.pair _ _) (pair≈ r s) = to (one (val-in (vr v))) s
    snd-sim T.fun (fun≈ _ _) = wrong ε refl
    snd-sim T.lit lit≈ = wrong ε refl
    snd-sim v@(T.tuple _) (tuple≈ _) = wrong ε (val-in (vr v))
    snd-sim v@(T.inl _) (inl≈ _) = wrong ε (val-in (vr v))
    snd-sim v@(T.inr _) (inr≈ _) = wrong ε (val-in (vr v))
  sim (tuple≈ rs) = ans-in (frame _ (λ _ → refl)) tuple≈ (sims rs) (λ vs rs' → val ε (T.tuple vs) (tuple≈ rs'))
  sim (get≈ {i = i} r) = ans-in (frame _ (λ _ → refl)) get≈ (sim r) get-sim
    where
    get-sim : ∀ {M V'} → T.Value V' → M ≈ V' → Ans′ (get i ⦅ M ,, Nil ⦆) (S.get? i M) (C.get i C.⦅ V' ,, Nil ⦆)
    get-sim v@(T.tuple _) (tuple≈ rs) = ret?-ans (proj-pw {R = _≈_} i (pw-list rs)) (val-in (vr v))
    get-sim T.fun (fun≈ _ _) = wrong ε refl
    get-sim v@(T.pair _ _) (pair≈ _ _) = wrong ε (val-in (vr v))
    get-sim T.lit lit≈ = wrong ε refl
    get-sim v@(T.inl _) (inl≈ _) = wrong ε (val-in (vr v))
    get-sim v@(T.inr _) (inr≈ _) = wrong ε (val-in (vr v))
  sim (inl≈ r) = ans-in (frame _ (λ _ → refl)) inl≈ (sim r) (λ v r' → val ε (T.inl v) (inl≈ r'))
  sim (inr≈ r) = ans-in (frame _ (λ _ → refl)) inr≈ (sim r) (λ v r' → val ε (T.inr v) (inr≈ r'))
  sim (case≈ {M = M} {M'} {N} {N'} r s t) = ans-in (frame _ (λ _ → refl)) (λ r' → case≈ r' s t) (sim r) case-sim
    where
    case-sim : ∀ {L V'} → T.Value V' → L ≈ V'
      → Ans′ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (S.case? L M N) (C.case-op C.⦅ V' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆)
    case-sim v@(T.inl v₁) (inl≈ r') = to (one (val-in (vr v))) (≈-subst (one≈ r' v₁ , tt) s)
    case-sim v@(T.inr v₁) (inr≈ r') = to (one (val-in (vr v))) (≈-subst (one≈ r' v₁ , tt) t)
    case-sim T.fun (fun≈ _ _) = wrong ε refl
    case-sim v@(T.pair _ _) (pair≈ _ _) = wrong ε (val-in (vr v))
    case-sim T.lit lit≈ = wrong ε refl
    case-sim v@(T.tuple _) (tuple≈ _) = wrong ε (val-in (vr v))
  sim (prim≈ {p} r s) =
    ans-in (frame _ (λ _ → refl)) (λ r' → prim≈ r' s) (sim r)
      λ v r' → ans-in (frame {g = λ X → C.prim p C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (vr v))) (prim≈ r') (sim s)
        λ v' s' → ret?-ans (out≈ (obs≈ r') (obs≈ s')) (trans (val-in (vr v)) (val-in (vr v')))
    where
    out≈ : ∀ {o₁ o₁' o₂ o₂'} → o₁ ≡ o₁' → o₂ ≡ o₂'
      → M.Pointwise _≈_ (map S.out (δ? p o₁ o₂)) (map T.out (δ? p o₁' o₂'))
    out≈ {o₁} {_} {o₂} refl refl with δ? p o₁ o₂
    ... | nothing = M.nothing
    ... | just (int n) = M.just lit≈
    ... | just (bool true) = M.just (inl≈ (tuple≈ []))
    ... | just (bool false) = M.just (inr≈ (tuple≈ []))
  sim (let≈ r s) =
    ans-in (frame _ (λ _ → refl)) (λ r' → let≈ r' s) (sim r)
      λ v r' → to (one (val-in (vr v))) (≈-subst (one≈ r' v , tt) s)
  sims [] = val ε T.[] []
  sims (r ∷ rs) =
    ans-in (frame _ (λ _ → refl)) (λ r' → r' ∷ rs) (sim r)
      λ v r' → ans-in (frame {g = λ Xs → _ ,, Xs} _ (λ X → val-in (vr v))) (r' ∷_) (sims rs)
        λ vs rs' → val ε (v T.∷ vs) (r' ∷ rs')

{- The end theorem: for every Clos4 program ----------------------------------}

globalize-correct : ∀ M → Equivalent (S.sem M) (T.sem (globalize M))
globalize-correct M =
  red-equivalent T.value-red (_≈_ D) (sim D) (λ m _ _ → obs≈ D m) (glob≈ D M [] ⊑-refl)
  where D = proj₂ (glob M [])
