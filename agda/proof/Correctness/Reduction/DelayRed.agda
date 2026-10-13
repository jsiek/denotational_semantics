{-

  Correctness of the delay pass (Clos3 → Clos4) by a forward simulation
  between their reduction semantics (see the design note in
  Semantics/Reduction/Smallstep.agda).

  delay turns a closure into a pair of code and the tuple of its free
  variables, and an application app L M into

    let x = L' in app (fst x) (snd x) (shift M')

  so calling a closure takes three more steps in Clos4: the let, fst and
  snd, which come before the operand is evaluated.

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-subst), with the cases of delay: a closure is related to the pair of
  the code of a related body and the tuple of related free variables, an
  application to its let, and an application of a closure value to the
  call that the let, fst and snd lead to (call≈), where the target waits
  for the operand. Since delay does not look at variables, it is a
  relation between any terms, and the code of a closure, which no
  substitution enters, is related by the relation itself: the
  compilation function is the relation on code (del: M ≈ delay M).

  No precondition is needed: a free variable goes wrong in both.

-}

module proof.Correctness.Reduction.DelayRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos3
import Language.Clos4 as C
open import Compiler.Delay using (delay; del-map-args)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-wrong
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Clos3 as S
import proof.Semantics.Reduction.Clos4 as T
import proof.Framework.Syntax.Subst Op sig as SS
import proof.Framework.Syntax.Subst C.Op C.sig as TS
import Framework.Syntax.Rename Op sig as SR
import Framework.Syntax.Rename C.Op C.sig as TR
import proof.Framework.Syntax.SubstRel Op sig C.Op C.sig as SubstRel
open SS using (sub; sub-args; exts; ids)
open import proof.Framework.ListUtil using (proj-pw)

open import Data.Fin using (Fin)
open import Data.List using (replicate; _∷_)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

{- The relation on terms -------------------------------------------------------}

{- the code of a function, and what follows the let-bound closure -}
fun : C.AST → C.AST
fun N = C.fun-op C.⦅ C.cons (C.clear (C.bind (C.bind (C.ast N)))) C.nil ⦆

app-body : C.AST → C.AST
app-body M = C.app C.⦅ C.fst-op C.⦅ C.` 0 ,, Nil ⦆ ,, C.snd-op C.⦅ C.` 0 ,, Nil ⦆ ,, TR.rename suc M ,, Nil ⦆

infix 4 _≈_
data _≈_ : AST → C.AST → Set where
  var≈ : ∀ {x} → ` x ≈ C.` x
  clos≈ : ∀ {n N N' Fs Fs'} → N ≈ N' → Pw _≈_ {n} Fs Fs'
    → clos-op n ⦅ cons (clear (bind (bind (ast N)))) Fs ⦆ ≈ C.pair-op C.⦅ fun N' ,, C.tuple n C.⦅ Fs' ⦆ ,, Nil ⦆
  app≈ : ∀ {L L' M M'} → L ≈ L' → M ≈ M' → app ⦅ L ,, M ,, Nil ⦆ ≈ C.let-op C.⦅ L' ,, ⟩ app-body M' ,, Nil ⦆
  call≈ : ∀ {n N N' Vs Vs' M M'} → N ≈ N' → Pw _≈_ {n} Vs Vs' → S.Values Vs → T.Values Vs' → M ≈ M'
    → app ⦅ clos-op n ⦅ cons (clear (bind (bind (ast N)))) Vs ⦆ ,, M ,, Nil ⦆
      ≈ C.app C.⦅ fun N' ,, C.tuple n C.⦅ Vs' ⦆ ,, M' ,, Nil ⦆
  lit≈ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈ C.lit B k C.⦅ Nil ⦆
  tuple≈ : ∀ {n as as'} → Pw _≈_ {n} as as' → tuple n ⦅ as ⦆ ≈ C.tuple n C.⦅ as' ⦆
  get≈ : ∀ {n} {i : Fin n} {M M'} → M ≈ M' → get i ⦅ M ,, Nil ⦆ ≈ C.get i C.⦅ M' ,, Nil ⦆
  inl≈ : ∀ {M M'} → M ≈ M' → inl-op ⦅ M ,, Nil ⦆ ≈ C.inl-op C.⦅ M' ,, Nil ⦆
  inr≈ : ∀ {M M'} → M ≈ M' → inr-op ⦅ M ,, Nil ⦆ ≈ C.inr-op C.⦅ M' ,, Nil ⦆
  case≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ C.case-op C.⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆
  prim≈ : ∀ {p L L' M M'} → L ≈ L' → M ≈ M' → prim p ⦅ L ,, M ,, Nil ⦆ ≈ C.prim p C.⦅ L' ,, M' ,, Nil ⦆
  let≈ : ∀ {M M' N N'} → M ≈ M' → N ≈ N' → let-op ⦅ M ,, ⟩ N ,, Nil ⦆ ≈ C.let-op C.⦅ M' ,, ⟩ N' ,, Nil ⦆

{- delay is related: the compilation function is the relation on code -}
del : ∀ M → M ≈ delay M
dels : ∀ {n} (as : Args (replicate n ■)) → Pw _≈_ as (del-map-args as)
del (` x) = var≈
del (clos-op n ⦅ cons (clear (bind (bind (ast N)))) Fs ⦆) = clos≈ (del N) (dels Fs)
del (app ⦅ L ,, M ,, Nil ⦆) = app≈ (del L) (del M)
del (lit B k ⦅ Nil ⦆) = lit≈
del (tuple n ⦅ as ⦆) = tuple≈ (dels as)
del (get i ⦅ M ,, Nil ⦆) = get≈ (del M)
del (inl-op ⦅ M ,, Nil ⦆) = inl≈ (del M)
del (inr-op ⦅ M ,, Nil ⦆) = inr≈ (del M)
del (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = case≈ (del L) (del M) (del N)
del (prim p ⦅ L ,, M ,, Nil ⦆) = prim≈ (del L) (del M)
del (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = let≈ (del M) (del N)
dels {zero} Nil = []
dels {suc n} (M ,, as) = del M ∷ dels as

{- Closure under substitution -------------------------------------------------}

{- substituting by any P-related substitutions, where P is preserved under
   binders: first for renamings, then for all substitutions -}
module Kit (P : SS.Subst → TS.Subst → Set) (p≈ : ∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x)
  (pexts : ∀ {σ σ'} → P σ σ' → P (exts σ) (TS.exts σ')) where

  ≈-sub : ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → sub σ M ≈ TS.sub σ' M'
  ≈-subs : ∀ {σ σ' n as as'} → P σ σ' → Pw _≈_ {n} as as' → Pw _≈_ (sub-args σ as) (TS.sub-args σ' as')
  ≈-sub p var≈ = p≈ p _
  ≈-sub p (clos≈ r rs) = clos≈ r (≈-subs p rs)
  ≈-sub {σ} {σ'} p (app≈ {L} {L'} {M} {M'} r s) =
    subst (λ X → sub σ (app ⦅ L ,, M ,, Nil ⦆) ≈ C.let-op C.⦅ TS.sub σ' L' ,, ⟩ X ,, Nil ⦆)
          (cong (λ Z → C.app C.⦅ C.fst-op C.⦅ C.` 0 ,, Nil ⦆ ,, C.snd-op C.⦅ C.` 0 ,, Nil ⦆ ,, Z ,, Nil ⦆)
                (sym (TS.exts-shift σ' M')))
          (app≈ (≈-sub p r) (≈-sub p s))
  ≈-sub p (call≈ r rs vs vs' s) =
    call≈ r (≈-subs p rs) (S.values-sub _ vs) (T.values-sub _ vs') (≈-sub p s)
  ≈-sub p lit≈ = lit≈
  ≈-sub p (tuple≈ rs) = tuple≈ (≈-subs p rs)
  ≈-sub p (get≈ r) = get≈ (≈-sub p r)
  ≈-sub p (inl≈ r) = inl≈ (≈-sub p r)
  ≈-sub p (inr≈ r) = inr≈ (≈-sub p r)
  ≈-sub p (case≈ r s t) = case≈ (≈-sub p r) (≈-sub (pexts p) s) (≈-sub (pexts p) t)
  ≈-sub p (prim≈ r s) = prim≈ (≈-sub p r) (≈-sub p s)
  ≈-sub p (let≈ r s) = let≈ (≈-sub p r) (≈-sub (pexts p) s)
  ≈-subs p [] = []
  ≈-subs p (r ∷ rs) = ≈-sub p r ∷ ≈-subs p rs

open SubstRel.Closure _≈_ var≈ (λ _ _ → ⊤) (λ _ → tt) (λ _ → tt) (λ P p≈ _ → Kit.≈-sub P p≈)
  using (≈-rename; ≈-subst; ≈-[])

{- The simulation -----------------------------------------------------------------}

Ans′ = Ans T.red T.Value _≈_

{- a target value is related to a source value -}
≈-value : ∀ {V V'} → T.Value V' → V ≈ V' → S.Value V
≈-values : ∀ {n as as'} → T.Values as' → Pw _≈_ {n} as as' → S.Values as
≈-value T.fun ()
≈-value (T.pair _ (T.tuple vs)) (clos≈ r rs) = S.clos (≈-values vs rs)
≈-value T.lit lit≈ = S.lit
≈-value (T.tuple vs) (tuple≈ rs) = S.tuple (≈-values vs rs)
≈-value (T.inl v) (inl≈ r) = S.inl (≈-value v r)
≈-value (T.inr v) (inr≈ r) = S.inr (≈-value v r)
≈-values T.[] [] = S.[]
≈-values (v T.∷ vs) (r ∷ rs) = ≈-value v r S.∷ ≈-values vs rs

obs≈ : ∀ {M M'} → M ≈ M' → S.obs M ≡ T.obs M'
obs≈s : ∀ {n as as'} → Pw _≈_ {n} as as' → S.obs-args as ≡ T.obs-args as'
obs≈ var≈ = refl
obs≈ (clos≈ _ _) = refl
obs≈ (app≈ _ _) = refl
obs≈ (call≈ _ _ _ _ _) = refl
obs≈ lit≈ = refl
obs≈ (tuple≈ rs) = cong o-tuple (obs≈s rs)
obs≈ (get≈ _) = refl
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (case≈ _ _ _) = refl
obs≈ (prim≈ _ _) = refl
obs≈ (let≈ _ _) = refl
obs≈s [] = refl
obs≈s (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈s rs)

{- the let, fst and snd that take a closure apart -}
let-fst-snd : ∀ {n N' as M'} → T.Values {n} as
  → let V = C.pair-op C.⦅ fun N' ,, C.tuple n C.⦅ as ⦆ ,, Nil ⦆ in
    Star* T.red (C.let-op C.⦅ V ,, ⟩ app-body M' ,, Nil ⦆)
                (C.app C.⦅ fun N' ,, C.tuple n C.⦅ as ⦆ ,, TS.sub (V TS.• TS.ids) (TR.rename suc M') ,, Nil ⦆)
let-fst-snd {n} {N'} {as} {M'} vs = s₁ ◅ s₂ ◅ s₃ ◅ ε
  where
  V = C.pair-op C.⦅ fun N' ,, C.tuple n C.⦅ as ⦆ ,, Nil ⦆
  Z = TS.sub (V TS.• TS.ids) (TR.rename suc M')
  s₁ : T.red (C.let-op C.⦅ V ,, ⟩ app-body M' ,, Nil ⦆)
       ≡ to (C.app C.⦅ C.fst-op C.⦅ V ,, Nil ⦆ ,, C.snd-op C.⦅ V ,, Nil ⦆ ,, Z ,, Nil ⦆)
  s₁ rewrite T.values-red vs = refl
  s₂ : T.red (C.app C.⦅ C.fst-op C.⦅ V ,, Nil ⦆ ,, C.snd-op C.⦅ V ,, Nil ⦆ ,, Z ,, Nil ⦆)
       ≡ to (C.app C.⦅ fun N' ,, C.snd-op C.⦅ V ,, Nil ⦆ ,, Z ,, Nil ⦆)
  s₂ rewrite T.values-red vs = refl
  s₃ : T.red (C.app C.⦅ fun N' ,, C.snd-op C.⦅ V ,, Nil ⦆ ,, Z ,, Nil ⦆)
       ≡ to (C.app C.⦅ fun N' ,, C.tuple n C.⦅ as ⦆ ,, Z ,, Nil ⦆)
  s₃ rewrite T.values-red vs = refl

{- fst of a value that is not a pair goes wrong -}
fst-wrong : ∀ {V' Y Z} → T.Value V' → T.fst? V' ≡ wrong
  → T.red (C.app C.⦅ C.fst-op C.⦅ V' ,, Nil ⦆ ,, Y ,, Z ,, Nil ⦆) ≡ wrong
fst-wrong v e rewrite T.value-red v | e = refl

sim : ∀ {M M'} → M ≈ M' → Ans′ M (S.red M) M'
sims : ∀ {n as as'} → Pw _≈_ {n} as as' → Ans T.red-args T.Values (Pw _≈_) as (S.red-args as) as'

{- calling a closure: the operand, then the body -}
call-ans : ∀ {n N N' Vs Vs' M M'} → N ≈ N' → Pw _≈_ {n} Vs Vs' → T.Values Vs' → M ≈ M'
  → Ans′ (app ⦅ clos-op n ⦅ cons (clear (bind (bind (ast N)))) Vs ⦆ ,, M ,, Nil ⦆)
         (S.app? (clos-op n ⦅ cons (clear (bind (bind (ast N)))) Vs ⦆) (S.red M) M)
         (C.app C.⦅ fun N' ,, C.tuple n C.⦅ Vs' ⦆ ,, M' ,, Nil ⦆)
call-ans r rs vs s =
  ans-in (frame {g = λ X → C.app C.⦅ _ ,, _ ,, X ,, Nil ⦆} _ (λ X → val-in (T.value-red (T.tuple vs))))
         (call≈ r rs (≈-values vs rs) vs) (sim s)
    λ w s' → to (one (trans (val-in (T.value-red (T.tuple vs))) (val-in (T.value-red w))))
                (≈-subst ((λ { zero → s' ; (suc zero) → tuple≈ rs ; (suc (suc x)) → var≈ }) , tt) r)

sim var≈ = wrong ε refl
sim (clos≈ {n} {N' = N'} r rs) =
  ans-in (frame-∘ (frame {redT = T.red-args} {redU = T.red} {g = λ Xs → C.tuple n C.⦅ Xs ⦆} _ (λ _ → refl))
                  (frame {g = λ X → C.pair-op C.⦅ fun N' ,, X ,, Nil ⦆} _ (λ _ → refl)))
         (clos≈ r) (sims rs) (λ vs rs' → val ε (T.pair T.fun (T.tuple vs)) (clos≈ r rs'))
sim (app≈ {M = M} {M' = M'} r s) =
  ans-in (frame _ (λ _ → refl)) (λ r' → app≈ r' s) (sim r) app-sim
  where
  {- the let, then fst and snd of a closure: anything else goes wrong at fst -}
  app-sim : ∀ {L V'} → T.Value V' → L ≈ V' → Ans′ (app ⦅ L ,, M ,, Nil ⦆) (S.app? L (S.red M) M) (C.let-op C.⦅ V' ,, ⟩ app-body M' ,, Nil ⦆)
  app-sim v@(T.pair T.fun (T.tuple vs)) (clos≈ r' rs) =
    ans-star (let-fst-snd vs) (subst (λ Z → Ans′ _ _ (C.app C.⦅ _ ,, _ ,, Z ,, Nil ⦆))
                                     (sym (trans (TS.sub-shift _ TS.ids M') (TS.sub-id M'))) (call-ans r' rs vs s))
  app-sim T.lit lit≈ = wrong (refl ◅ ε) refl
  app-sim v@(T.tuple _) (tuple≈ _) = wrong (val-in (T.value-red v) ◅ ε) (fst-wrong v refl)
  app-sim v@(T.inl _) (inl≈ _) = wrong (val-in (T.value-red v) ◅ ε) (fst-wrong v refl)
  app-sim v@(T.inr _) (inr≈ _) = wrong (val-in (T.value-red v) ◅ ε) (fst-wrong v refl)
sim (call≈ r rs svs vs s) =
  ans-skip (S.value-red (S.clos svs)) (call-ans r rs vs s)
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ (λ _ → refl)) tuple≈ (sims rs) (λ vs rs' → val ε (T.tuple vs) (tuple≈ rs'))
sim (get≈ {i = i} r) = ans-in (frame _ (λ _ → refl)) get≈ (sim r) get-sim
  where
  get-sim : ∀ {M V'} → T.Value V' → M ≈ V' → Ans′ (get i ⦅ M ,, Nil ⦆) (S.get? i M) (C.get i C.⦅ V' ,, Nil ⦆)
  get-sim v@(T.tuple _) (tuple≈ rs) = ret?-ans (proj-pw {R = _≈_} i (pw-list rs)) (val-in (T.value-red v))
  get-sim T.fun ()
  get-sim v@(T.pair _ _) (clos≈ _ _) = wrong ε (val-in (T.value-red v))
  get-sim T.lit lit≈ = wrong ε refl
  get-sim v@(T.inl _) (inl≈ _) = wrong ε (val-in (T.value-red v))
  get-sim v@(T.inr _) (inr≈ _) = wrong ε (val-in (T.value-red v))
sim (inl≈ r) = ans-in (frame _ (λ _ → refl)) inl≈ (sim r) (λ v r' → val ε (T.inl v) (inl≈ r'))
sim (inr≈ r) = ans-in (frame _ (λ _ → refl)) inr≈ (sim r) (λ v r' → val ε (T.inr v) (inr≈ r'))
sim (case≈ {M = M} {M'} {N} {N'} r s t) = ans-in (frame _ (λ _ → refl)) (λ r' → case≈ r' s t) (sim r) case-sim
  where
  case-sim : ∀ {L V'} → T.Value V' → L ≈ V'
    → Ans′ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (S.case? L M N) (C.case-op C.⦅ V' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆)
  case-sim v@(T.inl _) (inl≈ r') =
    to (one (val-in (T.value-red v))) (≈-[] tt r' s)
  case-sim v@(T.inr _) (inr≈ r') =
    to (one (val-in (T.value-red v))) (≈-[] tt r' t)
  case-sim T.fun ()
  case-sim v@(T.pair _ _) (clos≈ _ _) = wrong ε (val-in (T.value-red v))
  case-sim T.lit lit≈ = wrong ε refl
  case-sim v@(T.tuple _) (tuple≈ _) = wrong ε (val-in (T.value-red v))
sim (prim≈ {p} r s) =
  ans-in (frame _ (λ _ → refl)) (λ r' → prim≈ r' s) (sim r)
    λ v r' → ans-in (frame {g = λ X → C.prim p C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (T.value-red v))) (prim≈ r') (sim s)
      λ v' s' → ret?-ans (out≈ (obs≈ r') (obs≈ s')) (trans (val-in (T.value-red v)) (val-in (T.value-red v')))
  where
  out≈ : ∀ {o₁ o₁' o₂ o₂'} → o₁ ≡ o₁' → o₂ ≡ o₂'
    → M.Pointwise _≈_ (map S.out (δ? p o₁ o₂)) (map T.out (δ? p o₁' o₂'))
  out≈ {o₁} {_} {o₂} refl refl with δ? p o₁ o₂
  ... | nothing = M.nothing
  ... | just (int n) = M.just lit≈
  ... | just (bool true) = M.just (inl≈ (tuple≈ []))
  ... | just (bool false) = M.just (inr≈ (tuple≈ []))
sim (let≈ r s) = ans-in (frame _ (λ _ → refl)) (λ r' → let≈ r' s) (sim r)
  λ v r' → to (one (val-in (T.value-red v))) (≈-[] tt r' s)
sims [] = val ε T.[] []
sims (r ∷ rs) = ans-cons T.red-args (λ _ _ → refl) T.value-red rs (sim r) (sims rs)

{- The end theorem: for every Clos3 program ----------------------------------}

delay-correct : ∀ M → Equivalent (S.sem M) (T.sem (delay M))
delay-correct M = red-equivalent T.value-red _≈_ sim (λ m _ _ → obs≈ m) (del M)
