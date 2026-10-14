{-

  Correctness of the concretize pass (Clos2 → Clos3) by a forward
  simulation between their reduction semantics (see the design note in
  Semantics/Reduction/Smallstep.agda).

  A Clos2 closure binds its free variables one at a time; the Clos3
  closure binds the tuple of them, and its code projects each free
  variable from the tuple. Applying them substitutes the values of the
  free variables in the Clos2 body, and their tuple in the Clos3 body,
  so where the source has a value V the target has a projection
  get i ⦅ tuple ⦅ Vs' ⦆ ⦆, which takes one more step (prj≈).

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-subst), with prj≈, and with closures related by their free
  variables and by their code, the target's being concretize of the
  source's (the compilation function is the relation on code). Applying
  related closures gives related terms by the fundamental lemma (conc):
  sub τ M is related to sub τ' (concretize φ M) when τ is related to τ'
  through φ.

  The precondition: the program is well scoped (which optimize keeps).
  A variable of a closure's code beyond its parameters becomes a
  different variable in the two languages (in Clos3, variable 2), and
  substitution moves both, so it would not stay related; the machines
  look up both in the closure's environment and fail alike.

-}

module Untyped.proof.Correctness.Reduction.ConcretizeRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.Syntax.SigUtil using (ν-n)
open import Untyped.Language.Clos2
import Untyped.Language.Clos3 as C
open import Untyped.Compiler.Concretize
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import Semantics.Reduction.Smallstep using (Equivalent)
import Untyped.proof.Semantics.Reduction.Clos2 as S
import Untyped.proof.Semantics.Reduction.Clos3 as T
import proof.Framework.Syntax.Subst Op sig as SS
import proof.Framework.Syntax.Subst C.Op C.sig as TS
import Framework.Syntax.Rename C.Op C.sig as TR
import proof.Framework.Syntax.SubstRel Op sig C.Op C.sig as SubstRel
open SS using (sub; sub-args; exts; ids; extend)
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import proof.Framework.Syntax.ScopeSubst Op sig using (module Unbind)
open import proof.Framework.ListUtil using (proj; has-length; args→list; proj-pw; proj-map)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (replicate; _∷_)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _<?_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m≤n⇒m<n∨m≡n)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Language.Prim using (int; bool)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- The relation on terms -------------------------------------------------------}

infix 4 _≈_
data _≈_ : AST → C.AST → Set where
  var≈ : ∀ {x} → ` x ≈ C.` x
  prj≈ : ∀ {n} {i : Fin n} {V V' Vs'} → V ≈ V' → proj i (args→list Vs') ≡ just V' → T.Values Vs'
    → V ≈ C.get i C.⦅ C.tuple n C.⦅ Vs' ⦆ ,, Nil ⦆
  clos≈ : ∀ {n a Fs Fs'} → WS (suc n) (unbind-n n a) → Pw _≈_ {n} Fs Fs'
    → clos-op n ⦅ cons (clear a) Fs ⦆
      ≈ C.clos-op n C.⦅ C.cons (C.clear (C.bind (C.bind (C.ast (conc-body n n a))))) Fs' ⦆
  app≈ : ∀ {L L' M M'} → L ≈ L' → M ≈ M' → app ⦅ L ,, M ,, Nil ⦆ ≈ C.app C.⦅ L' ,, M' ,, Nil ⦆
  lit≈ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈ C.lit B k C.⦅ Nil ⦆
  tuple≈ : ∀ {n as as'} → Pw _≈_ {n} as as' → tuple n ⦅ as ⦆ ≈ C.tuple n C.⦅ as' ⦆
  get≈ : ∀ {n} {i : Fin n} {M M'} → M ≈ M' → get i ⦅ M ,, Nil ⦆ ≈ C.get i C.⦅ M' ,, Nil ⦆
  inl≈ : ∀ {M M'} → M ≈ M' → inl-op ⦅ M ,, Nil ⦆ ≈ C.inl-op C.⦅ M' ,, Nil ⦆
  inr≈ : ∀ {M M'} → M ≈ M' → inr-op ⦅ M ,, Nil ⦆ ≈ C.inr-op C.⦅ M' ,, Nil ⦆
  case≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ C.case-op C.⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆
  prim≈ : ∀ {p L L' M M'} → L ≈ L' → M ≈ M' → prim p ⦅ L ,, M ,, Nil ⦆ ≈ C.prim p C.⦅ L' ,, M' ,, Nil ⦆
  let≈ : ∀ {M M' N N'} → M ≈ M' → N ≈ N' → let-op ⦅ M ,, ⟩ N ,, Nil ⦆ ≈ C.let-op C.⦅ M' ,, ⟩ N' ,, Nil ⦆

{- Closure under substitution -------------------------------------------------}

module Kit (P : SS.Subst → TS.Subst → Set) (p≈ : ∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x)
  (pok : ∀ {σ σ'} → P σ σ' → ⊤) (pexts : ∀ {σ σ'} → P σ σ' → P (exts σ) (TS.exts σ')) where

  ≈-sub : ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → sub σ M ≈ TS.sub σ' M'
  ≈-subs : ∀ {σ σ' n as as'} → P σ σ' → Pw _≈_ {n} as as' → Pw _≈_ (sub-args σ as) (TS.sub-args σ' as')
  ≈-sub p var≈ = p≈ p _
  ≈-sub {σ' = σ'} p (prj≈ {i = i} r e vs) = prj≈ (≈-sub p r) (TS.sub-proj σ' i e) (T.values-sub σ' vs)
  ≈-sub p (clos≈ w rs) = clos≈ w (≈-subs p rs)
  ≈-sub p (app≈ r s) = app≈ (≈-sub p r) (≈-sub p s)
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

open SubstRel.Closure _≈_ var≈ (λ _ _ → ⊤) (λ _ → tt) (λ _ → tt) Kit.≈-sub using (≈-rename; ≈-[])

{- The fundamental lemma --------------------------------------------------------}

ref-shift : ∀ r → ref-ast (shift-ref r) ≡ TR.rename suc (ref-ast r)
ref-shift (var x) = refl
ref-shift (prj i x) = refl

{- under a binder -}
under : ∀ {k τ τ'} φ → (∀ x → x < k → τ x ≈ TS.sub τ' (ref-ast (φ x)))
  → ∀ x → x < suc k → exts τ x ≈ TS.sub (TS.exts τ') (ref-ast (ext-ref φ x))
under φ h zero _ = var≈
under {τ' = τ'} φ h (suc x) (s≤s x<) rewrite ref-shift (φ x) | TS.exts-shift τ' (ref-ast (φ x)) = ≈-rename suc (h x x<)

conc : ∀ {k τ τ'} φ M → WS k M → (∀ x → x < k → τ x ≈ TS.sub τ' (ref-ast (φ x)))
  → sub τ M ≈ TS.sub τ' (concretize φ M)
concs : ∀ {k τ τ' n} φ (as : Args (replicate n ■)) → WS-args k as
  → (∀ x → x < k → τ x ≈ TS.sub τ' (ref-ast (φ x))) → Pw _≈_ (sub-args τ as) (TS.sub-args τ' (conc-args φ as))
conc φ (` x) w h = h x w
conc φ (clos-op n ⦅ cons (clear a) Fs ⦆) (wa , ws) h =
  clos≈ (ws-unbind₀ n a wa) (concs φ Fs ws h)
  where open Unbind unbind-n (λ _ → refl) (λ _ _ → refl)
conc φ (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h = app≈ (conc φ L wL h) (conc φ M wM h)
conc φ (lit B k ⦅ Nil ⦆) w h = lit≈
conc φ (tuple n ⦅ as ⦆) w h = tuple≈ (concs φ as w h)
conc φ (get i ⦅ M ,, Nil ⦆) (w , _) h = get≈ (conc φ M w h)
conc φ (inl-op ⦅ M ,, Nil ⦆) (w , _) h = inl≈ (conc φ M w h)
conc φ (inr-op ⦅ M ,, Nil ⦆) (w , _) h = inr≈ (conc φ M w h)
conc φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) h =
  case≈ (conc φ L wL h) (conc (ext-ref φ) M wM (under φ h)) (conc (ext-ref φ) N wN (under φ h))
conc φ (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h = prim≈ (conc φ L wL h) (conc φ M wM h)
conc φ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) h = let≈ (conc φ M wM h) (conc (ext-ref φ) N wN (under φ h))
concs {n = zero} φ Nil w h = []
concs {n = suc n} φ (M ,, as) (w , ws) h = conc φ M w h ∷ concs φ as ws h

conc-body-eq : ∀ n k (a : Arg (ν-n k (ν ■))) → conc-body n k a ≡ concretize (fv-ref n) (unbind-n k a)
conc-body-eq n zero (bind (ast N)) = refl
conc-body-eq n (suc k) (bind a) = conc-body-eq n k a

{- free variable k of the body is component fv-index n k of the tuple -}
fv-proj : ∀ {n Fs Fs'} → Pw _≈_ {n} Fs Fs' → ∀ ρ k (k< : k < n)
  → Σ[ V' ∈ C.AST ] proj (fv-index n k k<) (args→list Fs') ≡ just V' × extend Fs ρ k ≈ V'
fv-proj {suc n} {F ,, Fs} {F' ,, Fs'} (r ∷ rs) ρ k k< with k <? n
... | yes k<n = fv-proj rs (F • ρ) k k<n
... | no k≮n rewrite has-length-args Fs' = F' , refl , subst (_≈ F') (sym (skip k<)) r
  where skip : k < suc n → extend Fs (F • ρ) k ≡ F
        skip (s≤s k≤n) with m≤n⇒m<n∨m≡n k≤n
        ... | inj₁ k<n = ⊥-elim (k≮n k<n)
        ... | inj₂ refl = SS.extend-top Fs F ρ

{- The simulation -----------------------------------------------------------------}

Ans′ = Ans T.red T.Value _≈_

obs≈ : ∀ {M M'} → T.Value M' → M ≈ M' → S.obs M ≡ T.obs M'
obs≈s : ∀ {n as as'} → T.Values as' → Pw _≈_ {n} as as' → S.obs-args as ≡ T.obs-args as'
obs≈ (T.clos _) (clos≈ _ _) = refl
obs≈ T.lit lit≈ = refl
obs≈ (T.tuple vs) (tuple≈ rs) = cong o-tuple (obs≈s vs rs)
obs≈ (T.inl v) (inl≈ r) = cong o-inl (obs≈ v r)
obs≈ (T.inr v) (inr≈ r) = cong o-inr (obs≈ v r)
obs≈s T.[] [] = refl
obs≈s (v T.∷ vs) (r ∷ rs) = cong₂ _∷_ (obs≈ v r) (obs≈s vs rs)

sim : ∀ {M M'} → M ≈ M' → Ans′ M (S.red M) M'
sims : ∀ {n as as'} → Pw _≈_ {n} as as' → Ans T.red-args T.Values (Pw _≈_) as (S.red-args as) as'
sim var≈ = error ε refl
sim (prj≈ r e vs) = ans-step (trans (val-in (T.value-red (T.tuple vs))) (cong ret? e)) (sim r)
sim (clos≈ w rs) = ans-in (frame _ (λ _ → refl)) (clos≈ w) (sims rs) (λ vs rs' → val ε (T.clos vs) (clos≈ w rs'))
sim (app≈ r s) = ans-in (frame _ (λ _ → refl)) (λ r' → app≈ r' s) (sim r) (λ v r' → app-sim v r' s)
  where
  app-sim : ∀ {L V' M M'} → T.Value V' → L ≈ V' → M ≈ M'
    → Ans′ (app ⦅ L ,, M ,, Nil ⦆) (S.app? L (S.red M) M) (C.app C.⦅ V' ,, M' ,, Nil ⦆)
  app-sim v@(T.clos vs) (clos≈ {n} {a} {Fs} {Fs'} w rs) s =
    ans-in (frame {g = λ X → C.app C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (T.value-red v))) (app≈ (clos≈ w rs)) (sim s)
      λ v' s' → to (one (trans (val-in (T.value-red v)) (val-in (T.value-red v')))) (β s')
    where
    β : ∀ {M W'} → M ≈ W'
      → sub (M • extend Fs ids) (unbind-n n a) ≈ TS.sub (W' TS.• C.tuple n C.⦅ Fs' ⦆ TS.• TS.ids) (conc-body n n a)
    β {M} {W'} s' = subst (λ B → sub (M • extend Fs ids) (unbind-n n a) ≈ TS.sub (W' TS.• C.tuple n C.⦅ Fs' ⦆ TS.• TS.ids) B)
                          (sym (conc-body-eq n n a)) (conc (fv-ref n) (unbind-n n a) w body)
      where
      body : ∀ x → x < suc n → (M • extend Fs ids) x ≈ TS.sub (W' TS.• C.tuple n C.⦅ Fs' ⦆ TS.• TS.ids) (ref-ast (fv-ref n x))
      body zero _ = s'
      body (suc k) (s≤s k<) with k <? n
      ... | yes k<n with fv-proj rs ids k k<n
      ...   | V' , e , r = prj≈ r e vs
      body (suc k) (s≤s k<) | no k≮n = ⊥-elim (k≮n k<)
  app-sim T.lit lit≈ s = error ε refl
  app-sim v@(T.tuple _) (tuple≈ _) s = error ε (val-in (T.value-red v))
  app-sim v@(T.inl _) (inl≈ _) s = error ε (val-in (T.value-red v))
  app-sim v@(T.inr _) (inr≈ _) s = error ε (val-in (T.value-red v))
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ (λ _ → refl)) tuple≈ (sims rs) (λ vs rs' → val ε (T.tuple vs) (tuple≈ rs'))
sim (get≈ {i = i} r) = ans-in (frame _ (λ _ → refl)) get≈ (sim r) get-sim
  where
  get-sim : ∀ {M V'} → T.Value V' → M ≈ V' → Ans′ (get i ⦅ M ,, Nil ⦆) (S.get? i M) (C.get i C.⦅ V' ,, Nil ⦆)
  get-sim v@(T.tuple _) (tuple≈ rs) = ret?-ans (proj-pw {R = _≈_} i (pw-list rs)) (val-in (T.value-red v))
  get-sim v@(T.clos _) (clos≈ _ _) = error ε (val-in (T.value-red v))
  get-sim T.lit lit≈ = error ε refl
  get-sim v@(T.inl _) (inl≈ _) = error ε (val-in (T.value-red v))
  get-sim v@(T.inr _) (inr≈ _) = error ε (val-in (T.value-red v))
sim (inl≈ r) = ans-in (frame _ (λ _ → refl)) inl≈ (sim r) (λ v r' → val ε (T.inl v) (inl≈ r'))
sim (inr≈ r) = ans-in (frame _ (λ _ → refl)) inr≈ (sim r) (λ v r' → val ε (T.inr v) (inr≈ r'))
sim (case≈ {M = M} {M'} {N} {N'} r s t) = ans-in (frame _ (λ _ → refl)) (λ r' → case≈ r' s t) (sim r) case-sim
  where
  case-sim : ∀ {L V'} → T.Value V' → L ≈ V'
    → Ans′ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (S.case? L M N) (C.case-op C.⦅ V' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆)
  case-sim v@(T.inl _) (inl≈ r') = to (one (val-in (T.value-red v))) (≈-[] tt r' s)
  case-sim v@(T.inr _) (inr≈ r') = to (one (val-in (T.value-red v))) (≈-[] tt r' t)
  case-sim v@(T.clos _) (clos≈ _ _) = error ε (val-in (T.value-red v))
  case-sim T.lit lit≈ = error ε refl
  case-sim v@(T.tuple _) (tuple≈ _) = error ε (val-in (T.value-red v))
sim (prim≈ {p} r s) =
  ans-in (frame _ (λ _ → refl)) (λ r' → prim≈ r' s) (sim r)
    λ v r' → ans-in (frame {g = λ X → C.prim p C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (T.value-red v))) (prim≈ r') (sim s)
      λ v' s' → ret?-ans (out≈ (obs≈ v r') (obs≈ v' s')) (trans (val-in (T.value-red v)) (val-in (T.value-red v')))
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

{- The end theorem: for well-scoped programs ------------------------------------}

concretize-correct : ∀ M → WS 0 M → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M w =
  red-equivalent T.value-red _≈_ sim (λ m _ v → obs≈ v m)
    (subst₂ _≈_ (SS.sub-id M) (TS.sub-id (concretize var M)) (conc var M w (λ x ())))
