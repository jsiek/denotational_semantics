{-

  Correctness of cast insertion (ISWIM → ISWIMᵀ) by a forward simulation
  between their machines (see the design note in Semantics/CEK/Smallstep.agda).

  An ISWIM value v is related to an ISWIMᵀ value of type Any, dyn G x,
  when x has the flat type G of v's kind (_≈_): a closure of N and ρ to
  a closure of cast (ext r) N under an environment related to ρ through
  the renaming r (Env≈), a tuple to a tuple of pointwise related
  components, and so on. Continuations are related frame by frame, the
  typed ones wrapped in the injK/projK frames that cast inserts; a
  primitive's primL/primR frames are related to the letK frames of the
  lets that bind its operands.

  Every source step is matched by one or more target steps (the inject,
  project and let steps): the target skips its intermediate states. Where
  the source stops with an error, on an operand of the wrong kind, the
  target stops at the corresponding project, at once, or (for a
  primitive) after a few steps that load the operands (runs).

-}

module proof.Correctness.Typed.CEK.CastSim where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
import Language.Typed.ISWIM as I
open import Compiler.Typed.Cast
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import Framework.ListUtil using (_‼_; proj; args→list)
open import Framework.VecUtil using (toVec; collected)
open import proof.Correctness.Typed.CEK.CastSimLemmas using (length→has-length; δ?-nothing₁; δ?-nothing₂; proj-just-length)
import Semantics.CEK.ISWIM as S
import Semantics.CEK.Typed.ISWIM as T
open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; sub; eq; δ)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<) renaming (zero to fz; suc to fs)
import Data.Integer as Z
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺; Pointwise-length)
open import Data.List.Properties using (length-reverse)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
import Data.Nat as N
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup; toList; fromList)
open import Data.Vec.Properties using (toList∘fromList; length-toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; does)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : S.Val → T.Val Any → Set
Env≈ : ∀ {k k'} → (Fin k → Fin k') → S.Env → T.Env k' → Set

data _≈_ where
  clo≈ : ∀ {k k' N w ρ ρ'} {r : Fin k → Fin k'} → Env≈ r ρ ρ'
    → S.clo N ρ ≈ T.dyn fun (T.clo (cast (ext r) N w) ρ')
  const≈ : ∀ {B c} → S.const B c ≈ T.dyn (base B) (T.const c)
  tup≈ : ∀ {n vs} {ws : Vec (T.Val Any) n} → Pointwise _≈_ vs (toList ws) → S.tup vs ≈ T.dyn (tup n) (T.tup ws)
  inl≈ : ∀ {v v'} → v ≈ v' → S.inl v ≈ T.dyn sum (T.inl v')
  inr≈ : ∀ {v v'} → v ≈ v' → S.inr v ≈ T.dyn sum (T.inr v')

Env≈ {k} r ρ ρ' = ∀ x (lt : x < k) → Σ[ v ∈ S.Val ] ρ ‼ x ≡ just v × v ≈ lookup ρ' (r (fromℕ< lt))

{- the body of the lets of a primitive -}
pbody : ∀ {k} p → I.Tm (suc (suc k)) Any
pbody p = I.inject (out-flat p) (I.prim p (I.project tint (I.` fs fz)) (I.project tint (I.` fz)))

data _≈k_ : S.Cont → T.Cont Any → Set where
  halt : S.halt ≈k T.halt
  appL : ∀ {k k' M ρ ρ' κ κ'} {r : Fin k → Fin k'} (w : WS k M) → Env≈ r ρ ρ' → κ ≈k κ'
    → S.appL M ρ κ ≈k T.projK tfun (T.appL (cast r M w) ρ' κ')
  appR : ∀ {v f κ κ'} → v ≈ T.dyn fun f → κ ≈k κ' → S.appR v κ ≈k T.appR f κ'
  tupK : ∀ {k k' n j vs vs' ρ ρ' κ κ'} {r : Fin k → Fin k'} (Ms : Args (replicate j ■)) {ws : WS-args k Ms}
    {e : length vs' N.+ suc j ≡ n} → Pointwise _≈_ vs vs' → Env≈ r ρ ρ' → κ ≈k κ'
    → S.tupK vs (args→list Ms) ρ κ ≈k T.tupK vs' (casts r Ms ws) ρ' e (T.injK (tup n) κ')
  getK : ∀ {n} {i : Fin (suc n)} {κ κ'} → κ ≈k κ' → S.getK i κ ≈k T.projK (ttup n) (T.getK i κ')
  inlK : ∀ {κ κ'} → κ ≈k κ' → S.inlK κ ≈k T.inlK (T.injK sum κ')
  inrK : ∀ {κ κ'} → κ ≈k κ' → S.inrK κ ≈k T.inrK (T.injK sum κ')
  caseK : ∀ {k k' M N ρ ρ' κ κ'} {r : Fin k → Fin k'} (wM : WS (suc k) M) (wN : WS (suc k) N)
    → Env≈ r ρ ρ' → κ ≈k κ'
    → S.caseK M N ρ κ ≈k T.projK tsum (T.caseK (cast (ext r) M wM) (cast (ext r) N wN) ρ' κ')
  primL : ∀ {k k' p M ρ ρ' κ κ'} {r : Fin k → Fin k'} (w : WS k M) → Env≈ r ρ ρ' → κ ≈k κ'
    → S.primL p M ρ κ ≈k T.letK (I.let′ (cast (λ x → fs (r x)) M w) (pbody p)) ρ' κ'
  primR : ∀ {k p v v' κ κ'} {ρ' : T.Env k} → v ≈ v' → κ ≈k κ' → S.primR p v κ ≈k T.letK (pbody p) (v' ∷ ρ') κ'
  letK : ∀ {k k' N ρ ρ' κ κ'} {r : Fin k → Fin k'} (w : WS (suc k) N) → Env≈ r ρ ρ' → κ ≈k κ'
    → S.letK N ρ κ ≈k T.letK (cast (ext r) N w) ρ' κ'

data _~_ : S.State → T.State → Set where
  eval~ : ∀ {k k' M ρ ρ' κ κ'} {r : Fin k → Fin k'} (w : WS k M) → Env≈ r ρ ρ' → κ ≈k κ'
    → S.eval M ρ κ ~ T.eval (cast r M w) ρ' κ'
  ret~ : ∀ {v v' κ κ'} → v ≈ v' → κ ≈k κ' → S.ret v κ ~ T.ret v' κ'

{- Lemmas ----------------------------------------------------------------------}

obs≈ : ∀ {v v'} → v ≈ v' → S.obs v ≡ T.obs v'
obs≈-list : ∀ {n vs} {ws : Vec (T.Val Any) n} → Pointwise _≈_ vs (toList ws) → S.obs-list vs ≡ T.obs-vec ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list {ws = []} [] = refl
obs≈-list {ws = _ ∷ _} (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

env-ext : ∀ {k k' ρ ρ' v v'} {r : Fin k → Fin k'} → Env≈ r ρ ρ' → v ≈ v' → Env≈ (ext r) (v ∷ ρ) (v' ∷ ρ')
env-ext E r zero _ = _ , refl , r
env-ext E r (suc x) (s≤s lt) = E x lt

toList-toVec : ∀ {A : Set} {n} (xs : List A) (e : length xs ≡ n) → toList (toVec xs e) ≡ xs
toList-toVec xs refl = toList∘fromList xs

collected≈ : ∀ {n vs vs'} (e : length vs' N.+ 0 ≡ n) → Pointwise _≈_ vs vs'
  → Pointwise _≈_ (reverse vs) (toList (collected vs' e))
collected≈ {vs' = vs'} e rs = subst (Pointwise _≈_ _) (sym eqn) (reverse⁺ rs)
  where eqn : toList (collected vs' e) ≡ reverse vs'
        eqn = toList-toVec (reverse vs') (trans (length-reverse vs') (trans (sym (+-identityʳ _)) e))

proj≈ : ∀ {n} (i : Fin n) {vs} {ws : Vec (T.Val Any) n} → Pointwise _≈_ vs (toList ws)
  → Σ[ v ∈ S.Val ] proj i vs ≡ just v × v ≈ lookup ws i
proj≈ (fs i) {ws = _ ∷ _} (_ ∷ rs) = proj≈ i rs
proj≈ {suc n} fz {v ∷ vs} {_ ∷ ws} (r ∷ rs)
  rewrite length→has-length n vs (trans (Pointwise-length rs) (length-toList ws)) = v , refl , r

{- the only error of the typed machine -}
project-ok : ∀ t (x : T.Val ⟪ flat t ⟫) (κ : T.Cont ⟪ flat t ⟫) → T.step (T.ret (T.dyn (flat t) x) (T.projK t κ)) ≡ next (T.ret x κ)
project-ok t x κ with flat t ≟F flat t
... | yes refl = refl
... | no ne = ⊥-elim (ne refl)

project-bad : ∀ {H t} → H ≢ flat t → (x : T.Val ⟪ H ⟫) (κ : T.Cont ⟪ flat t ⟫) → T.step (T.ret (T.dyn H x) (T.projK t κ)) ≡ stop o-error
project-bad {H} {t} ne x κ with H ≟F flat t
... | yes e = ⊥-elim (ne e)
... | no _ = refl

{- the kind errors of ISWIM, where the typed machine's project fails -}
proj-bad : ∀ {m n} (i : Fin n) {vs} {ws : Vec (T.Val Any) m} → m ≢ n → Pointwise _≈_ vs (toList ws)
  → proj i vs ≡ nothing
proj-bad i {vs} {ws} ne rs with proj i vs in e
... | nothing = refl
... | just _ = ⊥-elim (ne (trans (sym (trans (Pointwise-length rs) (length-toList ws))) (proj-just-length i vs e)))

notint : ∀ {v H} {x : T.Val ⟪ H ⟫} → v ≈ T.dyn H x → H ≢ base Int → ∀ n → S.obs v ≢ o-const Int n
notint const≈ ne n refl = ne refl

prim≈ : ∀ p n m → S.out (δ p n m) ≈ T.dyn (out-flat p) (T.δᵀ p n m)
prim≈ sub n m = const≈
prim≈ eq n m with does (n Z.≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

{- The simulation, for any ISWIMᵀ program P -------------------------------------}

module _ (P : I.Tm 0 Any) where

  L₂ = T.sem P

  R : ℕ → S.State → T.State → Set
  R _ = _~_

  infixr 5 _▷_
  _▷_ : ∀ {s₁ s s'} → Step L₂ s s' → Reach L₂ _~_ s₁ s' → Reach L₂ _~_ s₁ s
  st ▷ (t , σ , m) = t , st ◅ σ , m

  done : ∀ {s₁ s} → s₁ ~ s → Reach L₂ _~_ s₁ s
  done m = _ , ε , m

  go : ∀ {i s₁ s s'} → Step L₂ s s' → Reach L₂ _~_ s₁ s' → Answers≺ L₂ R i (next s₁) s
  go = after≺ {j = 0}

  tuple-next~ : ∀ {k k' n j vs vs' ρ ρ' κ κ'} {r : Fin k → Fin k'} (Ms : Args (replicate j ■)) (ws : WS-args k Ms)
    {e : length vs' N.+ j ≡ n} → Pointwise _≈_ vs vs' → Env≈ r ρ ρ' → κ ≈k κ'
    → Reach L₂ _~_ (S.tuple-next vs (args→list Ms) ρ κ) (T.tuple-next vs' (casts r Ms ws) ρ' e (T.injK (tup n) κ'))
  tuple-next~ {j = zero} Nil _ {e} rs E κ = refl ▷ done (ret~ (tup≈ (collected≈ e rs)) κ)
  tuple-next~ {j = suc j} (M ,, Ms) (w , ws) rs E κ = done (eval~ w E (tupK Ms rs E κ))

  sim : ∀ {i s₁ s₂} → s₁ ~ s₂ → Answers≺ L₂ R i (S.step s₁) s₂
  sim (eval~ {M = ` x} w E κ) with E x w
  ... | v , e , r = answers-at (cong (λ m → S.ret? m _) e) (go refl (done (ret~ r κ)))
  sim (eval~ {M = lam ⦅ ⟩ N ,, Nil ⦆} (w , _) E κ) = go refl (refl ▷ refl ▷ done (ret~ (clo≈ E) κ))
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} (wL , wM , _) E κ) = go refl (refl ▷ done (eval~ wL E (appL wM E κ)))
  sim (eval~ {M = lit B c ⦅ Nil ⦆} _ E κ) = go refl (refl ▷ refl ▷ done (ret~ const≈ κ))
  sim (eval~ {M = tuple n ⦅ Ms ⦆} ws E κ) = go refl (refl ▷ tuple-next~ Ms ws [] E κ)
  sim (eval~ {M = get {suc n} i ⦅ M ,, Nil ⦆} (w , _) E κ) = go refl (refl ▷ done (eval~ w E (getK κ)))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} (w , _) E κ) = go refl (refl ▷ done (eval~ w E (inlK κ)))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} (w , _) E κ) = go refl (refl ▷ done (eval~ w E (inrK κ)))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} (wL , wM , wN , _) E κ) =
    go refl (refl ▷ done (eval~ wL E (caseK wM wN E κ)))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} (wL , wM , _) E κ) = go refl (done (eval~ wL E (primL wM E κ)))
  sim (eval~ {M = let-op ⦅ M ,, ⟩ N ,, Nil ⦆} (wM , wN , _) E κ) = go refl (done (eval~ wM E (letK wN E κ)))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r@(clo≈ _) (appL w E κ)) = go refl (refl ▷ done (eval~ w E (appR r κ)))
  sim (ret~ const≈ (appL w E κ)) = stops refl
  sim (ret~ (tup≈ _) (appL w E κ)) = stops refl
  sim (ret~ (inl≈ _) (appL w E κ)) = stops refl
  sim (ret~ (inr≈ _) (appL w E κ)) = stops refl
  sim (ret~ r (appR (clo≈ E) κ)) = go refl (done (eval~ _ (env-ext E r) κ))
  sim (ret~ r (tupK Ms rs E κ)) = go refl (tuple-next~ Ms _ (r ∷ rs) E κ)
  sim (ret~ (tup≈ {n = m} rs) (getK {n} {i} κ)) with m N.≟ suc n
  ... | yes refl with proj≈ i rs
  ...   | v , e , r = answers-at (cong (λ x → S.ret? x _) e) (go (project-ok _ _ _) (refl ▷ done (ret~ r κ)))
  sim (ret~ (tup≈ rs) (getK {i = i} κ)) | no ne =
    answers-at (cong (λ x → S.ret? x _) (proj-bad i ne rs)) (stops (project-bad (λ { refl → ne refl }) _ _))
  sim (ret~ (clo≈ _) (getK κ)) = stops refl
  sim (ret~ const≈ (getK κ)) = stops refl
  sim (ret~ (inl≈ _) (getK κ)) = stops refl
  sim (ret~ (inr≈ _) (getK κ)) = stops refl
  sim (ret~ r (inlK κ)) = go refl (refl ▷ done (ret~ (inl≈ r) κ))
  sim (ret~ r (inrK κ)) = go refl (refl ▷ done (ret~ (inr≈ r) κ))
  sim (ret~ (inl≈ r) (caseK wM wN E κ)) = go refl (refl ▷ done (eval~ wM (env-ext E r) κ))
  sim (ret~ (inr≈ r) (caseK wM wN E κ)) = go refl (refl ▷ done (eval~ wN (env-ext E r) κ))
  sim (ret~ (clo≈ _) (caseK _ _ _ κ)) = stops refl
  sim (ret~ const≈ (caseK _ _ _ κ)) = stops refl
  sim (ret~ (tup≈ _) (caseK _ _ _ κ)) = stops refl
  sim (ret~ r (primL w E κ)) = go refl (refl ▷ done (eval~ w E (primR r κ)))
  sim (ret~ {v' = T.dyn H₂ y} s (primR {p = p} {v' = T.dyn H₁ x} r κ)) with H₁ ≟F base Int | H₂ ≟F base Int
  ... | no ne | _ = answers-at (cong (λ m → S.ret? (map S.out m) _) (δ?-nothing₁ p _ _ (notint r ne)))
    (runs (plus refl (refl ◅ refl ◅ refl ◅ refl ◅ ε)) (project-bad ne x _))
  sim (ret~ {v' = T.dyn _ y} s (primR {p = p} const≈ κ)) | yes refl | no ne = answers-at (cong (λ m → S.ret? (map S.out m) _) (δ?-nothing₂ p (o-const Int _) _ (notint s ne)))
    (runs (plus refl (refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ ε)) (project-bad ne y _))
  sim (ret~ const≈ (primR {p = p} const≈ κ)) | yes refl | yes refl =
    go refl (refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ refl ▷ done (ret~ (prim≈ p _ _) κ))
  sim (ret~ r (letK w E κ)) = go refl (done (eval~ w (env-ext E r) κ))

{- The end theorem -------------------------------------------------------------}

cast-correct : ∀ (M : AST) (w : WS 0 M) → Equivalent (S.sem M) (T.sem (cast-program M w))
cast-correct M w = equivalent (record { match = R P ; init = 0 , eval~ w (λ _ ()) halt ; sim = sim P })
  where P = cast-program M w
