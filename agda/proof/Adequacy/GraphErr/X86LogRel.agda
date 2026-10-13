{-

  Adequacy of the graph model with errors (Semantics/GraphErr/X86.agda)
  for the X86 machine: every element of the denotation of a well-formed
  program is witnessed by a run of the machine of its global definitions
  ds, and ω by a run that stops with an error.

  As in Adequacy/X86LogRel.agda, a logical relation 𝕍 d v relates
  denotational values to machine values, and the code of a definition,
  Λ X. Λ Y. …, is related to code k when the machine runs definition k on
  values related to X and Y, on any stack, to a result related to the
  body's (Res). What is new is that a result w may be ω: Res S w says that
  S errs on every stack when w = ω (Err), and otherwise returns a value
  related to w (Ret). A location is related to what the machine holds
  there (𝕄): ω to an unset location, any other element to a related value;
  so is the flag (Fl). The fundamental lemma (adequate) has a case for
  each check of the machine: e.g. a write errs when its value is ω or its
  slot is beyond the frame, and a call errs when its code, %rdi or %rsi is
  unset, its code is not code, or the callee errs. A run cannot both
  return and err (Ret-Err), so a call whose result has a value holds no ω
  (calls-err).

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse)
open import Language.X86 using (Body)

module proof.Adequacy.GraphErr.X86LogRel (ds : List Body) where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; δ; sub; eq; int; bool)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩) renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD)
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim using (primᵉ; IsInt) renaming (out to dout)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
  hiding (Body)
open import Semantics.GraphErr.X86
  renaming (Regs to SRegs; code to codeD; run to runD; put to putD; call to callD; args to argsD;
            read to readD; zeros to zerosD; _[_↦_] to _[_↦ₛ_]; flag to flagD)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Next; next; stop)
open import proof.Framework.ListUtil using (_‼_; proj; has-length)
open import Semantics.CEK.Values using (obs-list)
open import Semantics.CEK.X86
  using (Val; code; pair; const; tup; obs; out; prim?; Frame; State; Stack; halt; retK; run; step; block-at; global; get-field; build; is-inl; cmp; bit; zeros; arg; args; halt?; regs; upd; goto; callq?; back; test)
  renaming (read to readM; put to putM; call to callM; Regs to MRegs; _[_↦_] to _[_↦ₘ_])
import Semantics.CEK.X86 as T using (inl; inr)
open import proof.Adequacy.Common using (ShapeOf; ShapeAt; has-length→length; length→has-length)
open import proof.Adequacy.GraphErr.LogRel using (δ?-nothing₁; δ?-nothing₂)
open import proof.Adequacy.GraphErr.X86WF
open import proof.Adequacy.GraphErr.X86Common ds
open import proof.Adequacy.GraphErr.X86Soundness using (_≟R_; ↦ₘ-here; ↦ₘ-other; ≔-here; ≔-other; args-inv; length-obs-list)

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (0ℤ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _∸_; _+_; s≤s)
open import Data.Nat.Properties using (≤-pred; m≤n⇒m<n∨m≡n)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; ¬_)

{- Runs to a return, and to an error ------------------------------------------------}

Fam : Set
Fam = Stack → State

{- from S stk, the machine returns v to stk -}
Ret : Fam → Val → Set
Ret S v = ∀ stk → Σ[ bs ∈ List Block ] Σ[ f ∈ Maybe Bool ] Σ[ φ ∈ Frame ] Σ[ ρ ∈ MRegs ]
  (S stk ↠ run [] retq bs stk f φ ρ) × ρ rax ≡ just v

{- from S stk, the machine stops with an error -}
Err : Fam → Set
Err S = ∀ stk → Σ[ t ∈ State ] (S stk ↠ t) × step ds t ≡ stop o-error

obs≢err : ∀ v → obs v ≢ o-error
obs≢err (code k) ()
obs≢err (pair v w) ()
obs≢err (const B k) ()
obs≢err (tup vs) ()
obs≢err (T.inl v) ()
obs≢err (T.inr v) ()

stop-inj : ∀ {o o'} → stop {S = State} o ≡ stop o' → o ≡ o'
stop-inj refl = refl

Ret-det : ∀ {S v₁ v₂} → Ret S v₁ → Ret S v₂ → v₁ ≡ v₂
Ret-det r₁ r₂ with r₁ halt | r₂ halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ₁ , e₁ ⟩ ⟩ ⟩ ⟩ ⟩ | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ₂ , e₂ ⟩ ⟩ ⟩ ⟩ ⟩
    with ↠-final-det τ₁ τ₂ (cong halt? e₁) (cong halt? e₂)
... | refl with trans (sym e₁) e₂
... | refl = refl

{- a run does not both return and err -}
Ret-Err : ∀ {S v} → Ret S v → Err S → ⊥
Ret-Err {v = v} r er with r halt | er halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ₁ , e₁ ⟩ ⟩ ⟩ ⟩ ⟩ | ⟨ t , ⟨ τ₂ , st ⟩ ⟩ with ↠-final-det τ₁ τ₂ (cong halt? e₁) st
... | refl = obs≢err v (stop-inj (trans (sym (cong halt? e₁)) st))

{- The logical relation ----------------------------------------------------------}

{- the start of a definition with locals n, blocks bs and start b, called on e and a -}
Callee : ℕ → List Block → Block → Val → Val → Fam
Callee n bs b e a stk = run (Block.instrs b) (Block.jump b) bs stk nothing (zeros (2 + (n ∸ 2))) (regs nothing (just e) (just a))

𝕍 : Value → Val → Set
𝕍code : List Value → Value → ℕ → Set
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set

𝕍 (dconst {B} k) v = v ≡ const B k
𝕍 ν (code k) = ⊤
𝕍 (X ↦ w) (code k) = 𝕍code X w k
𝕍 ⦅ u₁ , u₂ ⦆ (pair v w) = 𝕍 u₁ v × 𝕍 u₂ w
𝕍 ⟨⟩ (tup vs) = vs ≡ []
𝕍 (tup[ i ] d) (tup vs) = 𝕍At i d vs
𝕍 (left d) (T.inl v) = 𝕍 d v
𝕍 (right d) (T.inr v) = 𝕍 d v
𝕍 _ _ = ⊥

{- the entries of code, Λ X. Λ Y. N: definition k runs on values related
   to X and Y to a result related to w -}
𝕍code X ν k = ⊤
𝕍code X (Y ↦ w) k = ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a
  → Σ[ n ∈ ℕ ] Σ[ bs ∈ List Block ] Σ[ b ∈ Block ] global ds k ≡ just (body n bs b)
    × ((w ≡ ω × Err (Callee n bs b e a)) ⊎ (Σ[ v ∈ Val ] Ret (Callee n bs b e a) v × 𝕍 w v))
𝕍code X _ k = ⊥

𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

𝕍At {suc n} zero d (v ∷ vs) = length vs ≡ n × 𝕍 d v
𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
𝕍At _ d [] = ⊥

{- ω means an error, any other value a return of a related value -}
Res : Fam → Value → Set
Res S w = (w ≡ ω × Err S) ⊎ (Σ[ v ∈ Val ] Ret S v × 𝕍 w v)

𝕍-ω : ∀ {v} → 𝕍 ω v → ⊥
𝕍-ω {code k} ()
𝕍-ω {pair v w} ()
𝕍-ω {const B k} ()
𝕍-ω {tup vs} ()
𝕍-ω {T.inl v} ()
𝕍-ω {T.inr v} ()

Res-step : ∀ {S S' w} → (∀ stk → step ds (S stk) ≡ next (S' stk)) → Res S' w → Res S w
Res-step st (inj₁ ⟨ refl , er ⟩) = inj₁ ⟨ refl , (λ stk → let ⟨ t , ⟨ τ , e ⟩ ⟩ = er stk in ⟨ t , ⟨ st stk ∷↠ τ , e ⟩ ⟩) ⟩
Res-step st (inj₂ ⟨ v , ⟨ r , rv ⟩ ⟩) =
  inj₂ ⟨ v , ⟨ (λ stk → let ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ = r stk in ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ st stk ∷↠ τ , e ⟩ ⟩ ⟩ ⟩ ⟩) , rv ⟩ ⟩

Res-stop : ∀ {S} → (∀ stk → step ds (S stk) ≡ stop o-error) → Res S ω
Res-stop st = inj₁ ⟨ refl , (λ stk → ⟨ _ , ⟨ done , st stk ⟩ ⟩) ⟩

𝕍s-∈ : ∀ V {v d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

all→𝕍s : ∀ V {v} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
all→𝕍s [] all = tt
all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

𝕍At-proj : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → Σ[ v ∈ Val ] proj i vs ≡ just v × 𝕍 d v
𝕍At-proj {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ rewrite length→has-length n vs len = ⟨ v , ⟨ refl , r ⟩ ⟩
𝕍At-proj (suc i) d (v ∷ vs) r = 𝕍At-proj i d vs r

𝕍At-length : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → length vs ≡ n
𝕍At-length {suc n} zero d (v ∷ vs) ⟨ len , _ ⟩ = cong suc len
𝕍At-length (suc i) d (v ∷ vs) r = cong suc (𝕍At-length i d vs r)

proj-just-length : ∀ {n} (i : Fin n) (vs : List Val) {v} → proj i vs ≡ just v → length vs ≡ n
proj-just-length {suc n} zero (v ∷ vs) e with has-length n vs in h
proj-just-length {suc n} zero (v ∷ vs) refl | true = cong suc (has-length→length n vs h)
proj-just-length {suc n} zero (v ∷ vs) () | false
proj-just-length (suc i) (v ∷ vs) e = cong suc (proj-just-length i vs e)

proj-nothing-[] : ∀ {n} (i : Fin n) → proj {A = Val} i [] ≡ nothing
proj-nothing-[] zero = refl
proj-nothing-[] (suc i) = refl

𝕍-out : ∀ r → 𝕍 (dout r) (out r)
𝕍-out (int k) = refl
𝕍-out (bool true) = refl
𝕍-out (bool false) = refl

{- related values are observed in the shape of the denotational value -}
𝕍-shape : ∀ d v → 𝕍 d v → ShapeOf (obs v) d
𝕍At-shape : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → ShapeAt i (obs-list vs) d
𝕍-shape (dconst k) (const B k) refl = refl
𝕍-shape ν (code k) r = tt
𝕍-shape (X ↦ w) (code k) r = tt
𝕍-shape ⦅ u₁ , u₂ ⦆ (pair v w) r = tt
𝕍-shape ⟨⟩ (tup []) refl = refl
𝕍-shape (tup[ i ] d) (tup vs) r = 𝕍At-shape i d vs r
𝕍-shape (left d) (T.inl v) r = 𝕍-shape d v r
𝕍-shape (right d) (T.inr v) r = 𝕍-shape d v r
𝕍At-shape {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ = ⟨ trans (length-obs-list vs) len , 𝕍-shape d v r ⟩
𝕍At-shape (suc i) d (v ∷ vs) r = 𝕍At-shape i d vs r

{- The kinds of related values ----------------------------------------------------}

𝕍-code : ∀ d k → 𝕍 d (code k) → IsFun d
𝕍-code ν k r = tt
𝕍-code (V ↦ w) k r = tt

𝕍-pair : ∀ d v w → 𝕍 d (pair v w) → IsPair d
𝕍-pair ⦅ p , q ⦆ v w r = tt

𝕍-inl : ∀ d v → 𝕍 d (T.inl v) → IsInj d
𝕍-inl (left d) v r = tt

𝕍-inr : ∀ d v → 𝕍 d (T.inr v) → IsInj d
𝕍-inr (right d) v r = tt

notint-obs : ∀ d v → 𝕍 d v → ¬ IsInt d → ∀ n → obs v ≢ o-const Int n
notint-obs (dconst k) (const B k) refl ni n refl = ni tt
notint-obs d (code k) r ni n ()
notint-obs d (pair v w) r ni n ()
notint-obs d (tup vs) r ni n ()
notint-obs d (T.inl v) r ni n ()
notint-obs d (T.inr v) r ni n ()

get-wrong : ∀ {n} (i : Fin n) d vs → 𝕍 d (tup vs) → ¬ IsTup n d → proj i vs ≡ nothing
get-wrong i ⟨⟩ vs refl nt = proj-nothing-[] i
get-wrong i (tup[ j ] e) vs r nt with proj i vs in p
... | just v = ⊥-elim (nt (trans (sym (𝕍At-length j e vs r)) (proj-just-length i vs p)))
... | nothing = refl

{- a field that a related value of the wrong kind lacks -}
field-wrong : ∀ fl d v → 𝕍 d v → d ≢ ω → ω ∈ field′ fl ⌈ d ⌉ → get-field fl v ≡ nothing
field-wrong fstₛ d (pair v w) r d≢ (inj₁ ⟨ _ , refl ⟩) = ⊥-elim (𝕍-ω {v} (proj₁ r))
field-wrong fstₛ d (pair v w) r d≢ (inj₂ ⟨ _ , inj₁ refl ⟩) = ⊥-elim (d≢ refl)
field-wrong fstₛ d (pair v w) r d≢ (inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ refl , ⟨ _ , np ⟩ ⟩ ⟩ ⟩) = ⊥-elim (np (𝕍-pair d v w r))
field-wrong fstₛ d (code k) r d≢ _ = refl
field-wrong fstₛ d (const B k) r d≢ _ = refl
field-wrong fstₛ d (tup vs) r d≢ _ = refl
field-wrong fstₛ d (T.inl v) r d≢ _ = refl
field-wrong fstₛ d (T.inr v) r d≢ _ = refl
field-wrong sndₛ d (pair v w) r d≢ (inj₁ ⟨ _ , refl ⟩) = ⊥-elim (𝕍-ω {w} (proj₂ r))
field-wrong sndₛ d (pair v w) r d≢ (inj₂ ⟨ _ , inj₁ refl ⟩) = ⊥-elim (d≢ refl)
field-wrong sndₛ d (pair v w) r d≢ (inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ refl , ⟨ _ , np ⟩ ⟩ ⟩ ⟩) = ⊥-elim (np (𝕍-pair d v w r))
field-wrong sndₛ d (code k) r d≢ _ = refl
field-wrong sndₛ d (const B k) r d≢ _ = refl
field-wrong sndₛ d (tup vs) r d≢ _ = refl
field-wrong sndₛ d (T.inl v) r d≢ _ = refl
field-wrong sndₛ d (T.inr v) r d≢ _ = refl
field-wrong (getₛ i) d (tup vs) r d≢ (inj₁ refl) = let ⟨ v' , ⟨ _ , r' ⟩ ⟩ = 𝕍At-proj i ω vs r in ⊥-elim (𝕍-ω {v'} r')
field-wrong (getₛ i) d (tup vs) r d≢ (inj₂ ⟨ _ , inj₁ refl ⟩) = ⊥-elim (d≢ refl)
field-wrong (getₛ i) d (tup vs) r d≢ (inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ refl , ⟨ _ , nt ⟩ ⟩ ⟩ ⟩) = get-wrong i d vs r nt
field-wrong (getₛ i) d (code k) r d≢ _ = refl
field-wrong (getₛ i) d (pair v w) r d≢ _ = refl
field-wrong (getₛ i) d (const B k) r d≢ _ = refl
field-wrong (getₛ i) d (T.inl v) r d≢ _ = refl
field-wrong (getₛ i) d (T.inr v) r d≢ _ = refl
field-wrong payload d (T.inl v) r d≢ (inj₁ ⟨ _ , ne ⟩) = ⊥-elim (ne refl)
field-wrong payload d (T.inl v) r d≢ (inj₂ (inj₁ ⟨ _ , ne ⟩)) = ⊥-elim (ne refl)
field-wrong payload d (T.inl v) r d≢ (inj₂ (inj₂ ⟨ _ , inj₁ refl ⟩)) = ⊥-elim (d≢ refl)
field-wrong payload d (T.inl v) r d≢ (inj₂ (inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ refl , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) = ⊥-elim (ni (𝕍-inl d v r))
field-wrong payload d (T.inr v) r d≢ (inj₁ ⟨ _ , ne ⟩) = ⊥-elim (ne refl)
field-wrong payload d (T.inr v) r d≢ (inj₂ (inj₁ ⟨ _ , ne ⟩)) = ⊥-elim (ne refl)
field-wrong payload d (T.inr v) r d≢ (inj₂ (inj₂ ⟨ _ , inj₁ refl ⟩)) = ⊥-elim (d≢ refl)
field-wrong payload d (T.inr v) r d≢ (inj₂ (inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ refl , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) = ⊥-elim (ni (𝕍-inr d v r))
field-wrong payload d (code k) r d≢ _ = refl
field-wrong payload d (pair v w) r d≢ _ = refl
field-wrong payload d (const B k) r d≢ _ = refl
field-wrong payload d (tup vs) r d≢ _ = refl

{- Related locations ---------------------------------------------------------------}

{- a location holds a value related to every element of D other than ω,
   and is unset if D holds ω -}
𝕄 : 𝒫 Value → Maybe Val → Set
𝕄 D m = ∀ d → d ∈ D → (d ≡ ω × m ≡ nothing) ⊎ (Σ[ v ∈ Val ] m ≡ just v × 𝕍 d v)

Fl : 𝒫 Value → Maybe Bool → Set
Fl F f = ∀ d → d ∈ F → (d ≡ ω × f ≡ nothing) ⊎ (Σ[ b ∈ Bool ] f ≡ just b × 𝕍 d (bit b))

𝕄-ω : ∀ {D m} → 𝕄 D m → ω ∈ D → m ≡ nothing
𝕄-ω h ω∈ with h ω ω∈
... | inj₁ ⟨ _ , e ⟩ = e
... | inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩ = ⊥-elim (𝕍-ω {v} r)

𝕄-val : ∀ {D m} → 𝕄 D m → ∀ d → d ∈ D → d ≢ ω → Σ[ v ∈ Val ] m ≡ just v × 𝕍 d v
𝕄-val h d d∈ d≢ with h d d∈
... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d≢ e)
... | inj₂ r = r

Fl-ω : ∀ {F f} → Fl F f → ω ∈ F → f ≡ nothing
Fl-ω h ω∈ with h ω ω∈
... | inj₁ ⟨ _ , e ⟩ = e
... | inj₂ ⟨ b , ⟨ _ , r ⟩ ⟩ = ⊥-elim (𝕍-ω {bit b} r)

init-𝕄 : 𝕄 init nothing
init-𝕄 _ refl = inj₁ ⟨ refl , refl ⟩

init-Fl : Fl init nothing
init-Fl _ refl = inj₁ ⟨ refl , refl ⟩

{- the frame, on its slots, and the registers -}
𝔽 : Store → Frame → Set
𝔽 σ φ = ∀ x → x < length φ → 𝕄 (σ x) (φ ‼ x)

ℝ : SRegs → MRegs → Set
ℝ ρs ρm = ∀ g → 𝕄 (ρs g) (ρm g)

{- the entries of the table below K are related to the code pointers -}
𝕋 : ℕ → Table → Set
𝕋 K T = ∀ k → k < K → ∀ d → d ∈ T k → 𝕍 d (code k)

bind≡ : ∀ {A B : Set} {m : Maybe A} {x} {f : A → Maybe B} → m ≡ just x → (m >>= f) ≡ f x
bind≡ refl = refl

bind-none : ∀ {A B : Set} {m : Maybe A} {f : A → Maybe B} → m ≡ nothing → (m >>= f) ≡ nothing
bind-none refl = refl

noω : ∀ {V d} → NoErr V → d ∈ mem V → d ≢ ω
noω noe d∈ refl = noe d∈

{- Operations ----------------------------------------------------------------------}

ℬ-𝕄 : ∀ B k → 𝕄 (ℬ B k ptt) (just (const B k))
ℬ-𝕄 B k (dconst k') ⟨ refl , refl ⟩ = inj₂ ⟨ const B k , ⟨ refl , refl ⟩ ⟩

{- a primitive fails on ω or on values that are not two integers -}
Bad : Prim → Maybe Val → Maybe Val → Set
Bad p mu mw = mu ≡ nothing ⊎ mw ≡ nothing ⊎ (Σ[ u ∈ Val ] Σ[ w ∈ Val ] mu ≡ just u × mw ≡ just w × δ? p (obs u) (obs w) ≡ nothing)

prim-cases : ∀ p {D E mu mw} → 𝕄 D mu → 𝕄 E mw → ∀ d → d ∈ primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩
  → (d ≡ ω × Bad p mu mw)
    ⊎ (Σ[ n ∈ _ ] Σ[ m ∈ _ ] mu ≡ just (const Int n) × mw ≡ just (const Int m) × d ≡ dout (δ p n m))
prim-cases p hD hE d (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩)
    with 𝕄-val hD (dconst n) n∈ (λ ()) | 𝕄-val hE (dconst m) m∈ (λ ())
... | ⟨ _ , ⟨ e₁ , refl ⟩ ⟩ | ⟨ _ , ⟨ e₂ , refl ⟩ ⟩ = inj₂ ⟨ n , ⟨ m , ⟨ e₁ , ⟨ e₂ , refl ⟩ ⟩ ⟩ ⟩
prim-cases p hD hE d (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩) = inj₁ ⟨ refl , inj₁ (𝕄-ω hD ω∈) ⟩
prim-cases p hD hE d (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₁ ω∈ ⟩) ⟩) = inj₁ ⟨ refl , inj₂ (inj₁ (𝕄-ω hE ω∈)) ⟩
prim-cases p hD hE d (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ ⟨ _ , () ⟩ ⟩) ⟩)
prim-cases p hD hE d (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ c , ⟨ c∈ , ⟨ c≢ , ni ⟩ ⟩ ⟩ , ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ ⟩) ⟩)
    with 𝕄-val hD c c∈ c≢ | 𝕄-val hE e e∈ e≢
... | ⟨ u , ⟨ eu , ru ⟩ ⟩ | ⟨ w , ⟨ ew , _ ⟩ ⟩ =
  inj₁ ⟨ refl , inj₂ (inj₂ ⟨ u , ⟨ w , ⟨ eu , ⟨ ew , δ?-nothing₁ p (obs u) (obs w) (notint-obs c u ru ni) ⟩ ⟩ ⟩ ⟩) ⟩
prim-cases p hD hE d (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ c , ⟨ c∈ , c≢ ⟩ ⟩ , ⟨ e , ⟨ e∈ , ⟨ e≢ , ni ⟩ ⟩ ⟩ ⟩) ⟩)
    with 𝕄-val hD c c∈ c≢ | 𝕄-val hE e e∈ e≢
... | ⟨ u , ⟨ eu , _ ⟩ ⟩ | ⟨ w , ⟨ ew , rw ⟩ ⟩ =
  inj₁ ⟨ refl , inj₂ (inj₂ ⟨ u , ⟨ w , ⟨ eu , ⟨ ew , δ?-nothing₂ p (obs u) (obs w) (notint-obs e w rw ni) ⟩ ⟩ ⟩ ⟩) ⟩

sub-none : ∀ md ma → Bad sub md ma → (ma >>= λ w → md >>= λ u → prim? sub u w) ≡ nothing
sub-none md nothing _ = refl
sub-none nothing (just w) _ = refl
sub-none (just u) (just w) (inj₁ ())
sub-none (just u) (just w) (inj₂ (inj₁ ()))
sub-none (just u) (just w) (inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ refl , ⟨ refl , e ⟩ ⟩ ⟩ ⟩)) rewrite e = refl

cmp-none : ∀ m₁ m₂ → Bad eq m₁ m₂ → (m₁ >>= λ v → m₂ >>= λ w → cmp v w) ≡ nothing
cmp-none nothing m₂ _ = refl
cmp-none (just v) nothing _ = refl
cmp-none (just v) (just w) (inj₁ ())
cmp-none (just v) (just w) (inj₂ (inj₁ ()))
cmp-none (just v) (just w) (inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ refl , ⟨ refl , e ⟩ ⟩ ⟩ ⟩)) rewrite e = refl

sub-𝕄 : ∀ {Dd Da md ma} → 𝕄 Dd md → 𝕄 Da ma
  → 𝕄 (primᵉ sub ⟨ Dd , ⟨ Da , ptt ⟩ ⟩) (ma >>= λ w → md >>= λ u → prim? sub u w)
sub-𝕄 {md = md} {ma} hd ha x x∈ with prim-cases sub hd ha x x∈
... | inj₁ ⟨ refl , bad ⟩ = inj₁ ⟨ refl , sub-none md ma bad ⟩
... | inj₂ ⟨ n , ⟨ m , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ = inj₂ ⟨ out (δ sub n m) , ⟨ refl , 𝕍-out (δ sub n m) ⟩ ⟩

cmp-Fl : ∀ {D₁ D₂ m₁ m₂} → 𝕄 D₁ m₁ → 𝕄 D₂ m₂
  → Fl (primᵉ eq ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩) (m₁ >>= λ v → m₂ >>= λ w → cmp v w)
cmp-Fl {m₁ = m₁} {m₂} h₁ h₂ x x∈ with prim-cases eq h₁ h₂ x x∈
... | inj₁ ⟨ refl , bad ⟩ = inj₁ ⟨ refl , cmp-none m₁ m₂ bad ⟩
... | inj₂ ⟨ n , ⟨ m , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ = inj₂ ⟨ _ , ⟨ refl , 𝕍-out (δ eq n m) ⟩ ⟩

notinj-isinl : ∀ v d → 𝕍 d v → ¬ IsInj d → is-inl v ≡ nothing
notinj-isinl (T.inl v) d r ni = ⊥-elim (ni (𝕍-inl d v r))
notinj-isinl (T.inr v) d r ni = ⊥-elim (ni (𝕍-inr d v r))
notinj-isinl (code k) d r ni = refl
notinj-isinl (pair v w) d r ni = refl
notinj-isinl (const B k) d r ni = refl
notinj-isinl (tup vs) d r ni = refl

isinl-Fl : ∀ {D m} → 𝕄 D m → Fl (isinlᵉ D) (m >>= is-inl)
isinl-Fl h _ (inj₁ ⟨ u , ⟨ u∈ , refl ⟩ ⟩) with 𝕄-val h (left u) u∈ (λ ())
... | ⟨ T.inl v , ⟨ refl , _ ⟩ ⟩ = inj₂ ⟨ true , ⟨ refl , refl ⟩ ⟩
isinl-Fl h _ (inj₂ (inj₁ ⟨ u , ⟨ u∈ , refl ⟩ ⟩)) with 𝕄-val h (right u) u∈ (λ ())
... | ⟨ T.inr v , ⟨ refl , _ ⟩ ⟩ = inj₂ ⟨ false , ⟨ refl , refl ⟩ ⟩
isinl-Fl h _ (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₁ ⟨ refl , bind-none (𝕄-ω h ω∈) ⟩
isinl-Fl h _ (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) with 𝕄-val h d d∈ d≢
... | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₁ ⟨ refl , trans (bind≡ e) (notinj-isinl v d r ni) ⟩

{- ω in a field: ω in the operand, or an element of it that has no such field -}
field-ω-inv : ∀ fl {D} → ω ∈ field′ fl D → ω ∈ D ⊎ (Σ[ d ∈ Value ] d ∈ D × d ≢ ω × ω ∈ field′ fl ⌈ d ⌉)
field-ω-inv fstₛ (inj₁ ⟨ v , p∈ ⟩) = inj₂ ⟨ _ , ⟨ p∈ , ⟨ (λ ()) , inj₁ ⟨ v , refl ⟩ ⟩ ⟩ ⟩
field-ω-inv fstₛ (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = inj₁ ω∈
field-ω-inv fstₛ (inj₂ ⟨ _ , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , np ⟩ ⟩ ⟩ ⟩) = inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ refl , ⟨ d≢ , np ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
field-ω-inv sndₛ (inj₁ ⟨ u , p∈ ⟩) = inj₂ ⟨ _ , ⟨ p∈ , ⟨ (λ ()) , inj₁ ⟨ u , refl ⟩ ⟩ ⟩ ⟩
field-ω-inv sndₛ (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = inj₁ ω∈
field-ω-inv sndₛ (inj₂ ⟨ _ , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , np ⟩ ⟩ ⟩ ⟩) = inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ refl , ⟨ d≢ , np ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
field-ω-inv (getₛ i) (inj₁ t∈) = inj₂ ⟨ _ , ⟨ t∈ , ⟨ (λ ()) , inj₁ refl ⟩ ⟩ ⟩
field-ω-inv (getₛ i) (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = inj₁ ω∈
field-ω-inv (getₛ i) (inj₂ ⟨ _ , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , nt ⟩ ⟩ ⟩ ⟩) = inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ refl , ⟨ d≢ , nt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
field-ω-inv payload (inj₁ ⟨ _ , ne ⟩) = ⊥-elim (ne refl)
field-ω-inv payload (inj₂ (inj₁ ⟨ _ , ne ⟩)) = ⊥-elim (ne refl)
field-ω-inv payload (inj₂ (inj₂ ⟨ _ , inj₁ ω∈ ⟩)) = inj₁ ω∈
field-ω-inv payload (inj₂ (inj₂ ⟨ _ , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) =
  inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ refl , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩) ⟩ ⟩ ⟩

field-none : ∀ fl {D m} → 𝕄 D m → ω ∈ field′ fl D → (m >>= get-field fl) ≡ nothing
field-none fl h ω∈ with field-ω-inv fl ω∈
... | inj₁ ω∈D = bind-none (𝕄-ω h ω∈D)
... | inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , w ⟩ ⟩ ⟩ with 𝕄-val h d d∈ d≢
...   | ⟨ v , ⟨ e , r ⟩ ⟩ = trans (bind≡ e) (field-wrong fl d v r d≢ w)

field-𝕄 : ∀ fl {D m} → 𝕄 D m → 𝕄 (field′ fl D) (m >>= get-field fl)
field-𝕄 fstₛ h x (inj₁ ⟨ y , xy∈ ⟩) with 𝕄-val h ⦅ x , y ⦆ xy∈ (λ ())
... | ⟨ pair v w , ⟨ refl , ⟨ r , _ ⟩ ⟩ ⟩ = inj₂ ⟨ v , ⟨ refl , r ⟩ ⟩
field-𝕄 fstₛ h x x∈@(inj₂ ⟨ refl , _ ⟩) = inj₁ ⟨ refl , field-none fstₛ h x∈ ⟩
field-𝕄 sndₛ h y (inj₁ ⟨ x , xy∈ ⟩) with 𝕄-val h ⦅ x , y ⦆ xy∈ (λ ())
... | ⟨ pair v w , ⟨ refl , ⟨ _ , r ⟩ ⟩ ⟩ = inj₂ ⟨ w , ⟨ refl , r ⟩ ⟩
field-𝕄 sndₛ h x x∈@(inj₂ ⟨ refl , _ ⟩) = inj₁ ⟨ refl , field-none sndₛ h x∈ ⟩
field-𝕄 (getₛ i) h x (inj₁ x∈) with 𝕄-val h (tup[ i ] x) x∈ (λ ())
... | ⟨ tup vs , ⟨ refl , r ⟩ ⟩ with 𝕍At-proj i x vs r
...   | ⟨ v , ⟨ e , r' ⟩ ⟩ = inj₂ ⟨ v , ⟨ e , r' ⟩ ⟩
field-𝕄 (getₛ i) h x x∈@(inj₂ ⟨ refl , _ ⟩) = inj₁ ⟨ refl , field-none (getₛ i) h x∈ ⟩
field-𝕄 payload h x (inj₁ ⟨ x∈ , _ ⟩) with 𝕄-val h (left x) x∈ (λ ())
... | ⟨ T.inl v , ⟨ refl , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ refl , r ⟩ ⟩
field-𝕄 payload h x (inj₂ (inj₁ ⟨ x∈ , _ ⟩)) with 𝕄-val h (right x) x∈ (λ ())
... | ⟨ T.inr v , ⟨ refl , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ refl , r ⟩ ⟩
field-𝕄 payload h x x∈@(inj₂ (inj₂ ⟨ refl , _ ⟩)) = inj₁ ⟨ refl , field-none payload h x∈ ⟩

{- the objects that build makes, of their arity -}
Arity : Shape → ℕ → Set
Arity pairₛ n = n ≡ 2
Arity tupleₛ n = ⊤
Arity inlₛ n = n ≡ 1
Arity inrₛ n = n ≡ 1

build-arity : ∀ sh us {w} → build sh us ≡ just w → Arity sh (length us)
build-arity pairₛ (u ∷ v ∷ []) _ = refl
build-arity tupleₛ us _ = tt
build-arity inlₛ (u ∷ []) _ = refl
build-arity inrₛ (u ∷ []) _ = refl

nothing-if : ∀ (m : Maybe Val) → (∀ w → m ≡ just w → ⊥) → m ≡ nothing
nothing-if nothing _ = refl
nothing-if (just w) h = ⊥-elim (h w refl)

arity-none : ∀ {φ ρm} sh as → (Arity sh (length as) → ⊥) → args φ ρm [] as (build sh) ≡ nothing
arity-none sh as ¬ar = nothing-if _ λ w e →
  let ⟨ us , ⟨ es , eb ⟩ ⟩ = args-inv [] as e in
  ¬ar (subst (Arity sh) (sym (Pointwise-length es)) (build-arity sh us eb))

{- Related states ------------------------------------------------------------------}

module _ {K : ℕ} {T : Table} (𝕋T : 𝕋 K T) where

  𝒪-𝕄 : ∀ {n σ ρs φ ρm} a → OK (_< K) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → 𝕄 (𝒪 T n σ ρs a) (arg φ ρm a)
  𝒪-𝕄 {n} {φ = φ} (loc (var x)) _ refl F G with x <? length φ
  ... | yes x< = F x x<
  ... | no ¬x< = subst (𝕄 init) (sym (‼-out φ x ¬x<)) init-𝕄
  𝒪-𝕄 (loc (reg g)) _ _ F G = G g
  𝒪-𝕄 (imm B k) _ _ F G = ℬ-𝕄 B k
  𝒪-𝕄 (label k) k< _ F G d d∈ = inj₂ ⟨ code k , ⟨ refl , 𝕋T k k< d d∈ ⟩ ⟩

  {- the operands of alloc, when each has a value -}
  args-run : ∀ {n σ ρs φ ρm} as acc (k : List Val → Maybe Val) → All (OK (_< K)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → vals (length as) (𝒪s T n σ ρs as)
    → Σ[ vs ∈ List Val ] args φ ρm acc as k ≡ k (reverse acc ++ vs) × length vs ≡ length as
       × (∀ j x → x ∈ nthD (𝒪s T n σ ρs as) j → 𝕍At j x vs)
  args-run [] acc k _ _ _ _ _ = ⟨ [] , ⟨ cong k (sym (++-identityʳ (reverse acc))) , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
  args-run {φ = φ} {ρm} (a ∷ as) acc k (o ∷ os) nφ F G vs with vs zero
  ... | ⟨ x₀ , ⟨ x₀∈ , x₀≢ ⟩ ⟩ with 𝕄-val (𝒪-𝕄 a o nφ F G) x₀ x₀∈ x₀≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ with args-run as (v ∷ acc) k os nφ F G (λ j → vs (suc j))
  ... | ⟨ us , ⟨ e , ⟨ len , rs ⟩ ⟩ ⟩ =
    ⟨ v ∷ us , ⟨ trans (bind≡ ea) (trans e (cong k (trans (cong (_++ us) (unfold-reverse v acc)) (++-assoc (reverse acc) [ v ] us))))
              , ⟨ cong suc len , G' ⟩ ⟩ ⟩
    where
    G' : ∀ j x → x ∈ nthD (𝒪s T _ _ _ (a ∷ as)) j → 𝕍At j x (v ∷ us)
    G' zero x x∈ with 𝒪-𝕄 a o nφ F G x x∈
    ... | inj₁ ⟨ _ , e' ⟩ with trans (sym ea) e'
    ...   | ()
    G' zero x x∈ | inj₂ ⟨ _ , ⟨ e' , r ⟩ ⟩ with trans (sym ea) e'
    ...   | refl = ⟨ len , r ⟩
    G' (suc j) x x∈ = rs j x x∈

  {- the operands of alloc, one of which errs -}
  args-errs : ∀ {n σ ρs φ ρm} as acc (k : List Val → Maybe Val) → All (OK (_< K)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → errs (length as) (𝒪s T n σ ρs as) → args φ ρm acc as k ≡ nothing
  args-errs (a ∷ as) acc k (o ∷ os) nφ F G (inj₁ ω∈) = bind-none (𝕄-ω (𝒪-𝕄 a o nφ F G) ω∈)
  args-errs (a ∷ as) acc k (o ∷ os) nφ F G (inj₂ ⟨ ⟨ x , ⟨ x∈ , x≢ ⟩ ⟩ , er ⟩) with 𝕄-val (𝒪-𝕄 a o nφ F G) x x∈ x≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ = trans (bind≡ ea) (args-errs as (v ∷ acc) k os nφ F G er)

  object-𝕄 : ∀ {n σ ρs φ ρm} sh as → All (OK (_< K)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → 𝕄 (object T n σ ρs sh as) (args φ ρm [] as (build sh))
  object-𝕄 pairₛ (a ∷ b ∷ []) (oa ∷ ob ∷ []) nφ F G ⦅ u , w ⦆ ⟨ u∈ , ⟨ w∈ , ⟨ u≢ , w≢ ⟩ ⟩ ⟩
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) u u∈ u≢ | 𝕄-val (𝒪-𝕄 b ob nφ F G) w w∈ w≢
  ... | ⟨ v₁ , ⟨ e₁ , r₁ ⟩ ⟩ | ⟨ v₂ , ⟨ e₂ , r₂ ⟩ ⟩ = inj₂ ⟨ pair v₁ v₂ , ⟨ trans (bind≡ e₁) (bind≡ e₂) , ⟨ r₁ , r₂ ⟩ ⟩ ⟩
  object-𝕄 pairₛ (a ∷ b ∷ []) os nφ F G ω er = inj₁ ⟨ refl , args-errs (a ∷ b ∷ []) [] (build pairₛ) os nφ F G er ⟩
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ (a ∷ []) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ (a ∷ []) (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ (a ∷ b ∷ c ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ (a ∷ b ∷ c ∷ as) (λ ()) ⟩
  object-𝕄 tupleₛ as os nφ F G ω er = inj₁ ⟨ refl , args-errs as [] (build tupleₛ) os nφ F G er ⟩
  object-𝕄 tupleₛ [] [] nφ F G ⟨⟩ tt = inj₂ ⟨ tup [] , ⟨ refl , refl ⟩ ⟩
  object-𝕄 tupleₛ (a ∷ as) os nφ F G (tup[ i ] x) ⟨ refl , ⟨ x∈ , vs ⟩ ⟩ with args-run (a ∷ as) [] (build tupleₛ) os nφ F G vs
  ... | ⟨ us , ⟨ e , ⟨ _ , rs ⟩ ⟩ ⟩ = inj₂ ⟨ tup us , ⟨ e , rs i x x∈ ⟩ ⟩
  object-𝕄 inlₛ (a ∷ []) (oa ∷ []) nφ F G (left u) ⟨ u∈ , u≢ ⟩ with 𝕄-val (𝒪-𝕄 a oa nφ F G) u u∈ u≢
  ... | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ T.inl v , ⟨ bind≡ e , r ⟩ ⟩
  object-𝕄 inlₛ (a ∷ []) os nφ F G ω ω∈ = inj₁ ⟨ refl , args-errs (a ∷ []) [] (build inlₛ) os nφ F G (inj₁ ω∈) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inlₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inlₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inlₛ (a ∷ b ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inlₛ (a ∷ b ∷ as) (λ ()) ⟩
  object-𝕄 inrₛ (a ∷ []) (oa ∷ []) nφ F G (right u) ⟨ u∈ , u≢ ⟩ with 𝕄-val (𝒪-𝕄 a oa nφ F G) u u∈ u≢
  ... | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ T.inr v , ⟨ bind≡ e , r ⟩ ⟩
  object-𝕄 inrₛ (a ∷ []) os nφ F G ω ω∈ = inj₁ ⟨ refl , args-errs (a ∷ []) [] (build inrₛ) os nφ F G (inj₁ ω∈) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inrₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inrₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inrₛ (a ∷ b ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inrₛ (a ∷ b ∷ as) (λ ()) ⟩

  {- the related values of a set that holds some, and no ω -}
  𝕄→𝕍s : ∀ {D m} → 𝕄 D m → ∀ V → mem V ⊆ D → V ≢ [] → NoErr V → Σ[ v ∈ Val ] m ≡ just v × 𝕍s V v
  𝕄→𝕍s h [] V⊆ ne noe = ⊥-elim (ne refl)
  𝕄→𝕍s h (d₀ ∷ V) V⊆ ne noe with 𝕄-val h d₀ (V⊆ d₀ (here refl)) (noω noe (here refl))
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ = ⟨ v , ⟨ refl , all→𝕍s (d₀ ∷ V) (λ d d∈ → G d (𝕄-val h d (V⊆ d d∈) (noω noe d∈))) ⟩ ⟩
    where
    G : ∀ d → Σ[ v' ∈ Val ] just v ≡ just v' × 𝕍 d v' → 𝕍 d v
    G d ⟨ _ , ⟨ refl , r ⟩ ⟩ = r

  {- Calls ---------------------------------------------------------------------}

  {- an element of the result of a call: the callee returns a value related to it -}
  record Calls (φ : Frame) (ρm : MRegs) (a : Arg) (w : Value) : Set where
    constructor calls
    field
      k : ℕ
      e₁ e₂ : Val
      m : ℕ
      bbs : List Block
      bst : Block
      v : Val
      ea : arg φ ρm a ≡ just (code k)
      er₁ : ρm rdi ≡ just e₁
      er₂ : ρm rsi ≡ just e₂
      eg : global ds k ≡ just (body m bbs bst)
      ret : Ret (Callee m bbs bst e₁ e₂) v
      rel : 𝕍 w v

  {- a call that errs: at once, or in the callee -}
  CallErr : Frame → MRegs → Arg → Set
  CallErr φ ρm a = (∀ stk → callq? ds (arg φ ρm a) stk ρm ≡ stop o-error)
    ⊎ (Σ[ k ∈ ℕ ] Σ[ e₁ ∈ Val ] Σ[ e₂ ∈ Val ] Σ[ m ∈ ℕ ] Σ[ bbs ∈ List Block ] Σ[ bst ∈ Block ]
         arg φ ρm a ≡ just (code k) × ρm rdi ≡ just e₁ × ρm rsi ≡ just e₂ × global ds k ≡ just (body m bbs bst)
         × Err (Callee m bbs bst e₁ e₂))

  callq-next : ∀ {φ ρm a k e₁ e₂ m bbs bst} → arg φ ρm a ≡ just (code k) → ρm rdi ≡ just e₁ → ρm rsi ≡ just e₂
    → global ds k ≡ just (body m bbs bst) → ∀ stk → callq? ds (arg φ ρm a) stk ρm ≡ next (Callee m bbs bst e₁ e₂ stk)
  callq-next {ρm = ρm} ea er₁ er₂ eg stk rewrite ea | eg | er₁ | er₂ = refl

  callq-rdi : ∀ v {stk ρ} → ρ rdi ≡ nothing → callq? ds (just v) stk ρ ≡ stop o-error
  callq-rdi (code k) e rewrite e with global ds k
  ... | just (body _ _ _) = refl
  ... | nothing = refl
  callq-rdi (pair _ _) e = refl
  callq-rdi (const _ _) e = refl
  callq-rdi (tup _) e = refl
  callq-rdi (T.inl _) e = refl
  callq-rdi (T.inr _) e = refl

  callq-rsi : ∀ v {stk ρ} → ρ rsi ≡ nothing → callq? ds (just v) stk ρ ≡ stop o-error
  callq-rsi (code k) {ρ = ρ} e rewrite e with global ds k | ρ rdi
  ... | just (body _ _ _) | just _ = refl
  ... | just (body _ _ _) | nothing = refl
  ... | nothing | _ = refl
  callq-rsi (pair _ _) e = refl
  callq-rsi (const _ _) e = refl
  callq-rsi (tup _) e = refl
  callq-rsi (T.inl _) e = refl
  callq-rsi (T.inr _) e = refl

  callq-notcode : ∀ c v {stk ρ} → 𝕍 c v → ¬ IsFun c → callq? ds (just v) stk ρ ≡ stop o-error
  callq-notcode c (code k) r nf = ⊥-elim (nf (𝕍-code c k r))
  callq-notcode c (pair _ _) r nf = refl
  callq-notcode c (const _ _) r nf = refl
  callq-notcode c (tup _) r nf = refl
  callq-notcode c (T.inl _) r nf = refl
  callq-notcode c (T.inr _) r nf = refl

  call-𝕄 : ∀ {n σ ρs φ ρm} a → OK (_< K) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → ∀ w
    → w ∈ callᵉ ⟨ 𝒪 T n σ ρs a , ⟨ ρs rdi , ⟨ ρs rsi , ptt ⟩ ⟩ ⟩ → (w ≡ ω × CallErr φ ρm a) ⊎ Calls φ ρm a w
  call-𝕄 a oa nφ F G w (inj₁ ⟨ V , ⟨ U , ⟨ e∈ , ⟨ V⊆ , ⟨ U⊆ , ⟨ neV , ⟨ neU , ⟨ noeV , noeU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) _ e∈ (λ ()) | 𝕄→𝕍s (G rdi) V V⊆ neV noeV | 𝕄→𝕍s (G rsi) U U⊆ neU noeU
  ... | ⟨ code k , ⟨ ea , r ⟩ ⟩ | ⟨ e₁ , ⟨ er₁ , X𝕍 ⟩ ⟩ | ⟨ e₂ , ⟨ er₂ , Y𝕍 ⟩ ⟩ with r e₁ X𝕍 e₂ Y𝕍
  ... | ⟨ m , ⟨ bbs , ⟨ bst , ⟨ eg , inj₁ ⟨ refl , er ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₂ ⟨ k , ⟨ e₁ , ⟨ e₂ , ⟨ m , ⟨ bbs , ⟨ bst , ⟨ ea , ⟨ er₁ , ⟨ er₂ , ⟨ eg , er ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  ... | ⟨ m , ⟨ bbs , ⟨ bst , ⟨ eg , inj₂ ⟨ v , ⟨ ret , rv ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = inj₂ (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rv)
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩) =
    inj₁ ⟨ refl , inj₁ (λ stk → cong (λ m → callq? ds m stk ρm) (𝕄-ω (𝒪-𝕄 a oa nφ F G) ω∈)) ⟩
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ c , ⟨ c∈ , c≢ ⟩ ⟩ , inj₁ ω∈ ⟩) ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-rdi v (𝕄-ω (G rdi) ω∈))) ⟩
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ c , ⟨ c∈ , c≢ ⟩ ⟩ , inj₂ ⟨ _ , inj₁ ω∈ ⟩ ⟩) ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-rsi v (𝕄-ω (G rsi) ω∈))) ⟩
  call-𝕄 a oa nφ F G w (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , () ⟩ ⟩ ⟩) ⟩)
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ refl , inj₂ ⟨ ⟨ c , ⟨ c∈ , ⟨ c≢ , nf ⟩ ⟩ ⟩ , _ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , r ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-notcode c v r nf)) ⟩

  {- a call does not both err and return -}
  CallErr-Calls : ∀ {φ ρm a w} → CallErr φ ρm a → Calls φ ρm a w → ⊥
  CallErr-Calls {φ} {ρm} {a} (inj₁ st) (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel) with trans (sym (st halt)) (callq-next {φ} {ρm} {a} ea er₁ er₂ eg halt)
  ... | ()
  CallErr-Calls (inj₂ ⟨ k' , ⟨ e₁' , ⟨ e₂' , ⟨ m' , ⟨ bbs' , ⟨ bst' , ⟨ ea' , ⟨ er₁' , ⟨ er₂' , ⟨ eg' , er ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
                (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel)
      with trans (sym ea) ea' | trans (sym er₁) er₁' | trans (sym er₂) er₂'
  ... | refl | refl | refl with trans (sym eg) eg'
  ... | refl = Ret-Err ret er

  {- the same call returns the same value -}
  calls-det : ∀ {φ ρm a w w'} (c : Calls φ ρm a w) (c' : Calls φ ρm a w') → 𝕍 w' (Calls.v c)
  calls-det (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel) (calls k' e₁' e₂' m' bbs' bst' v' ea' er₁' er₂' eg' ret' rel')
      with trans (sym ea) ea' | trans (sym er₁) er₁' | trans (sym er₂) er₂'
  ... | refl | refl | refl with trans (sym eg) eg'
  ... | refl with Ret-det ret ret'
  ... | refl = rel'

  {- the caller: a call, a return of the callee, and the rest -}
  Res-↠ : ∀ {S S' w} → (∀ stk → S stk ↠ S' stk) → Res S' w → Res S w
  Res-↠ τ (inj₁ ⟨ refl , er ⟩) = inj₁ ⟨ refl , (λ stk → let ⟨ t , ⟨ τ' , e ⟩ ⟩ = er stk in ⟨ t , ⟨ τ stk ++↠ τ' , e ⟩ ⟩) ⟩
  Res-↠ τ (inj₂ ⟨ v , ⟨ r , rv ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ (λ stk → let ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ τ' , e ⟩ ⟩ ⟩ ⟩ ⟩ = r stk in ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ τ stk ++↠ τ' , e ⟩ ⟩ ⟩ ⟩ ⟩) , rv ⟩ ⟩

  via-call : ∀ {a is j bs f φ ρm w₀} (cl : Calls φ ρm a w₀) → ∀ stk
    → run (callq a ∷ is) j bs stk f φ ρm ↠ run is j bs stk nothing φ (regs (just (Calls.v cl)) nothing nothing)
  via-call {a} {is} {j} {bs} {f} {φ} {ρm} (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel) stk with ret (retK is j bs φ stk)
  ... | ⟨ bs₁ , ⟨ f₁ , ⟨ φ₁ , ⟨ ρ₁ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ =
    callq-next {φ} {ρm} {a} ea er₁ er₂ eg (retK is j bs φ stk) ∷↠ (τ ++↠ (cong (λ m → back m is j bs φ stk) e ∷↠ done))

  call-err : ∀ {a is j bs f φ ρm} → CallErr φ ρm a → Err (λ stk → run (callq a ∷ is) j bs stk f φ ρm)
  call-err {is = is} {j} {bs} {φ = φ} (inj₁ st) stk = ⟨ _ , ⟨ done , st (retK is j bs φ stk) ⟩ ⟩
  call-err {a} {is} {j} {bs} {φ = φ} {ρm} (inj₂ ⟨ k , ⟨ e₁ , ⟨ e₂ , ⟨ m , ⟨ bbs , ⟨ bst , ⟨ ea , ⟨ er₁ , ⟨ er₂ , ⟨ eg , er ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) stk
    with er (retK is j bs φ stk)
  ... | ⟨ t , ⟨ τ , e ⟩ ⟩ = ⟨ t , ⟨ callq-next {φ} {ρm} {a} ea er₁ er₂ eg (retK is j bs φ stk) ∷↠ τ , e ⟩ ⟩

  {- The fundamental lemma ----------------------------------------------------------}

  {- a jump to block l of bs: a missing block errs -}
  GoRes : List Block → ℕ → Maybe Bool → Frame → MRegs → Value → Set
  GoRes bs l f φ ρm w = (block-at bs l ≡ nothing × w ≡ ω)
    ⊎ (Σ[ b ∈ Block ] Σ[ bs' ∈ List Block ] block-at bs l ≡ just ⟨ b , bs' ⟩
        × Res (λ stk → run (Block.instrs b) (Block.jump b) bs' stk f φ ρm) w)

  go : ∀ {bs l f φ ρm w} {S : Fam} → (∀ stk → step ds (S stk) ≡ goto (block-at bs l) stk f φ ρm) → GoRes bs l f φ ρm w → Res S w
  go {f = f} {φ} {ρm} st (inj₁ ⟨ eb , refl ⟩) = Res-stop (λ stk → trans (st stk) (cong (λ mb → goto mb stk f φ ρm) eb))
  go {f = f} {φ} {ρm} st (inj₂ ⟨ b , ⟨ bs' , ⟨ eb , r ⟩ ⟩ ⟩) = Res-step (λ stk → trans (st stk) (cong (λ mb → goto mb stk f φ ρm) eb)) r

  {- the blocks bs are adequate -}
  AdeqB : ℕ → List Block → Set₁
  AdeqB n bs = ∀ l {σ ρs F φ ρm f w} → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f → w ∈ blocks T n bs l σ ρs F
    → GoRes bs l f φ ρm w

  adequate : ∀ {n} is j bs {σ ρs F φ ρm f w} → Code (_< K) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f
    → w ∈ ⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs)) σ ρs F → Res (λ stk → run is j bs stk f φ ρm) w

  {- a write to d, then the rest -}
  put-case : ∀ {n} d {D m} is j bs {σ ρs F φ ρm f w} {S : Fam}
    → (∀ stk → step ds (S stk) ≡ putM d m φ ρm (run is j bs stk f)) → 𝕄 D m
    → Code (_< K) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f
    → w ∈ putD n d D (⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs))) σ ρs F → Res S w
  put-case (var x) {D} {m} is j bs {σ} {ρs} {φ = φ} {ρm} {f} st h c AB refl F G Fl' w∈ with x <? length φ
  put-case (var x) {D} {m} is j bs {σ} {ρs} {φ = φ} {ρm} {f} st h c AB refl F G Fl' (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩) | yes x< =
    ⊥-elim (ne refl)
  put-case (var x) {D} {m} is j bs {σ} {ρs} {φ = φ} {ρm} {f} st h c AB refl F G Fl'
      (inj₁ ⟨ d₀ ∷ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , ⟨ _ , noe ⟩ ⟩ ⟩ ⟩) | yes x<
      with 𝕄-val h d₀ (V⊆ d₀ (here refl)) (noω noe (here refl))
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ with ≔-ok φ x v x<
  ... | ⟨ φ' , e ⟩ = Res-step (λ stk → trans (st stk) (cong (λ mφ → upd mφ ρm (run is j bs stk f)) e))
                       (adequate is j bs c AB (Assigned.len a) F' G Fl' w∈)
    where
    a = ≔-inv φ x e
    F' : 𝔽 (σ [ x ↦ₛ mem (d₀ ∷ V) ]) φ'
    F' y y< with y ≟ x
    ... | yes refl = λ d d∈ → inj₂ (G' d (𝕄-val h d (V⊆ d d∈) (noω noe d∈)))
      where
      G' : ∀ d → Σ[ v' ∈ Val ] just v ≡ just v' × 𝕍 d v' → Σ[ v' ∈ Val ] φ' ‼ x ≡ just v' × 𝕍 d v'
      G' d ⟨ _ , ⟨ refl , r ⟩ ⟩ = ⟨ v , ⟨ Assigned.here a , r ⟩ ⟩
    ... | no ne = subst (𝕄 (σ y)) (sym (Assigned.other a y ne)) (F y (subst (y <_) (Assigned.len a) y<))
  put-case (var x) is j bs st h c AB refl F G Fl' (inj₂ ⟨ refl , inj₁ () ⟩) | yes x<
  put-case (var x) is j bs st h c AB refl F G Fl' (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d' , ⟨ d'∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) | yes x< =
    ⊥-elim (nf (Λᵉ-fun d' d'∈))
  put-case (var x) {m = m} is j bs {φ = φ} {ρm} {f} st h c AB refl F G Fl' (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) | yes x< =
    Res-stop (λ stk → trans (st stk) (cong (λ m' → putM (var x) m' φ ρm (run is j bs stk f)) (𝕄-ω h ω∈)))
  put-case (var x) {m = m} is j bs {φ = φ} {ρm} {f} st h c AB refl F G Fl' ⟨ refl , ⟨ d₀ , d₀∈ ⟩ ⟩ | no ¬x< with h d₀ d₀∈
  ... | inj₁ ⟨ _ , e ⟩ = Res-stop (λ stk → trans (st stk) (cong (λ m' → putM (var x) m' φ ρm (run is j bs stk f)) e))
  ... | inj₂ ⟨ v , ⟨ e , _ ⟩ ⟩ =
    Res-stop (λ stk → trans (st stk) (trans (cong (λ m' → putM (var x) m' φ ρm (run is j bs stk f)) e)
                                            (cong (λ mφ → upd mφ ρm (run is j bs stk f)) (≔-out φ x v ¬x<))))
  put-case (reg g) is j bs {φ = φ} {ρm} {f} st h c AB nφ F G Fl' (inj₁ ⟨ refl , ω∈ ⟩) =
    Res-stop (λ stk → trans (st stk) (cong (λ m' → putM (reg g) m' φ ρm (run is j bs stk f)) (𝕄-ω h ω∈)))
  put-case (reg g) {D} is j bs {ρs = ρs} {φ = φ} {ρm} st h c AB nφ F G Fl' (inj₂ ⟨ ⟨ d₀ , ⟨ d₀∈ , d₀≢ ⟩ ⟩ , w∈ ⟩)
      with 𝕄-val h d₀ d₀∈ d₀≢
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ = Res-step st (adequate is j bs c AB nφ F G' Fl' w∈)
    where
    G' : ℝ (ρs [ g ≔ D ]) (ρm [ g ↦ₘ just v ])
    G' g' with g' ≟R g
    ... | yes refl rewrite ≔-here ρs g D | ↦ₘ-here ρm g (just v) = h
    ... | no ne rewrite ≔-other ρs g D g' ne | ↦ₘ-other ρm g (just v) g' ne = G g'

  {- a test that sets the flag, then the rest -}
  flag-case : ∀ {n} is j bs {σ ρs F₀ φ ρm mb w} {S : Fam}
    → (∀ stk → step ds (S stk) ≡ test mb (λ f' → run is j bs stk f' φ ρm)) → Fl F₀ mb
    → Code (_< K) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → w ∈ flagD F₀ (⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs))) σ ρs → Res S w
  flag-case is j bs {φ = φ} {ρm} st Fl₀ c AB nφ F G (inj₁ ⟨ refl , ω∈ ⟩) =
    Res-stop (λ stk → trans (st stk) (cong (λ mb → test mb (λ f' → run is j bs stk f' φ ρm)) (Fl-ω Fl₀ ω∈)))
  flag-case is j bs {F₀ = F₀} {φ} {ρm} st Fl₀ c AB nφ F G (inj₂ ⟨ ⟨ d₀ , ⟨ d₀∈ , d₀≢ ⟩ ⟩ , w∈ ⟩) with Fl₀ d₀ d₀∈
  ... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d₀≢ e)
  ... | inj₂ ⟨ b , ⟨ refl , _ ⟩ ⟩ = Res-step st (adequate is j bs c AB nφ F G Fl₀ w∈)

  bit-inj : ∀ d b → 𝕍 d (bit b) → IsInj d
  bit-inj d true r = 𝕍-inl d _ r
  bit-inj d false r = 𝕍-inr d _ r

  adequate (movq a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (𝒪-𝕄 a oa nφ F G) c AB nφ F G Fl' w∈
  adequate (subq a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (sub-𝕄 (𝒪-𝕄 (loc d) tt nφ F G) (𝒪-𝕄 a oa nφ F G)) c AB nφ F G Fl' w∈
  adequate (cmpq a₂ a₁ ∷ is) j bs ⟨ ⟨ o₂ , o₁ ⟩ , c ⟩ AB nφ F G Fl' w∈ =
    flag-case is j bs (λ _ → refl) (cmp-Fl (𝒪-𝕄 a₁ o₁ nφ F G) (𝒪-𝕄 a₂ o₂ nφ F G)) c AB nφ F G w∈
  adequate (sete d ∷ is) j bs {f = just b} ⟨ _ , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) h c AB nφ F G Fl' w∈
    where
    h : 𝕄 _ (just (bit b))
    h y y∈ with Fl' y y∈
    ... | inj₁ ⟨ _ , () ⟩
    ... | inj₂ ⟨ _ , ⟨ refl , r ⟩ ⟩ = inj₂ ⟨ bit b , ⟨ refl , r ⟩ ⟩
  adequate (sete d ∷ is) j bs {φ = φ} {ρm} {f = nothing} ⟨ _ , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs {φ = φ} {ρm = ρm} {f = nothing} {S = λ stk → run (sete d ∷ is) j bs stk nothing φ ρm} (λ stk → refl) h c AB nφ F G Fl' w∈
    where
    h : 𝕄 _ nothing
    h y y∈ with Fl' y y∈
    ... | inj₁ ⟨ e , _ ⟩ = inj₁ ⟨ e , refl ⟩
    ... | inj₂ ⟨ _ , ⟨ () , _ ⟩ ⟩
  adequate (testinl a ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    flag-case is j bs (λ _ → refl) (isinl-Fl (𝒪-𝕄 a oa nφ F G)) c AB nφ F G w∈
  adequate (alloc sh as d ∷ is) j bs ⟨ os , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (object-𝕄 sh as os nφ F G) c AB nφ F G Fl' w∈
  adequate (load fl a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (field-𝕄 fl (𝒪-𝕄 a oa nφ F G)) c AB nφ F G Fl' w∈
  adequate (callq a ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' (inj₁ ⟨ refl , ω∈ ⟩) with call-𝕄 a oa nφ F G ω ω∈
  ... | inj₁ ⟨ _ , ce ⟩ = inj₁ ⟨ refl , call-err ce ⟩
  ... | inj₂ cl = ⊥-elim (𝕍-ω {Calls.v cl} (Calls.rel cl))
  adequate (callq a ∷ is) j bs {σ} {ρs} {φ = φ} {ρm} {f} ⟨ oa , c ⟩ AB nφ F G Fl' (inj₂ ⟨ ⟨ w₀ , ⟨ w₀∈ , w₀≢ ⟩ ⟩ , w∈ ⟩)
      with call-𝕄 a oa nφ F G w₀ w₀∈
  ... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (w₀≢ e)
  ... | inj₂ cl = Res-↠ (via-call cl) (adequate is j bs c AB nφ F G' init-Fl w∈)
    where
    G' : ℝ (called _) (regs (just (Calls.v cl)) nothing nothing)
    G' rax w' w'∈ with call-𝕄 a oa nφ F G w' w'∈
    ... | inj₁ ⟨ _ , ce ⟩ = ⊥-elim (CallErr-Calls ce cl)
    ... | inj₂ cl' = inj₂ ⟨ Calls.v cl , ⟨ refl , calls-det cl cl' ⟩ ⟩
    G' rdi = init-𝕄
    G' rsi = init-𝕄
  adequate [] retq bs {φ = φ} {ρm} {f} _ AB nφ F G Fl' w∈ with G rax _ w∈
  ... | inj₁ ⟨ refl , e ⟩ = Res-stop st
    where
    st : ∀ stk → step ds (run [] retq bs stk f φ ρm) ≡ stop o-error
    st halt = cong halt? e
    st (retK is j bs' φ' stk) = cong (λ m → back m is j bs' φ' stk) e
  ... | inj₂ ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ stk → ⟨ bs , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ done , e ⟩ ⟩ ⟩ ⟩ ⟩) , r ⟩ ⟩
  adequate [] (jmp l) bs _ AB nφ F G Fl' w∈ = go {bs = bs} {l = l} (λ _ → refl) (AB l nφ F G Fl' w∈)
  adequate [] (je l₁ l₂) bs {f = f} _ AB nφ F G Fl' (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
      with Fl' (left u) (allL u (here refl))
  ... | inj₂ ⟨ true , ⟨ refl , _ ⟩ ⟩ = go {bs = bs} {l = l₁} (λ _ → refl) (AB l₁ nφ F G Fl' w∈)
  adequate [] (je l₁ l₂) bs {f = f} _ AB nφ F G Fl' (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩))
      with Fl' (right u) (allR u (here refl))
  ... | inj₂ ⟨ false , ⟨ refl , _ ⟩ ⟩ = go {bs = bs} {l = l₂} (λ _ → refl) (AB l₂ nφ F G Fl' w∈)
  adequate [] (je l₁ l₂) bs {φ = φ} {ρm} {f} _ AB nφ F G Fl' (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) with Fl-ω Fl' ω∈
  ... | refl = Res-stop (λ stk → refl)
  adequate [] (je l₁ l₂) bs _ AB nφ F G Fl' (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) with Fl' d d∈
  ... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d≢ e)
  ... | inj₂ ⟨ b , ⟨ _ , r ⟩ ⟩ = ⊥-elim (ni (bit-inj d b r))

  blocks-adeq : ∀ {n} bs → All (λ b → Code (_< K) (Block.instrs b)) bs → AdeqB n bs
  blocks-adeq [] _ l nφ F G Fl' w∈ = inj₁ ⟨ refl , w∈ ⟩
  blocks-adeq (b ∷ bs) (c ∷ cs) l nφ F G Fl' w∈ with l ≟ length bs
  ... | no _ = blocks-adeq bs cs l nφ F G Fl' w∈
  ... | yes _ = inj₂ ⟨ b , ⟨ bs , ⟨ refl , adequate (Block.instrs b) (Block.jump b) bs c (blocks-adeq bs cs) nφ F G Fl' w∈ ⟩ ⟩ ⟩

{- The table of the program -------------------------------------------------------}

{- a fresh frame of m slots -}
zeros-𝔽 : ∀ m → 𝔽 zerosD (zeros m)
zeros-𝔽 m x x< rewrite replicate-‼ m {const Int 0ℤ} x (subst (x <_) (length-replicate m) x<) = ℬ-𝕄 Int _

tab : ∀ Ns xs → ds ≡ xs ++ Ns → DefsWF Ns → 𝕋 (length Ns) (table Ns)
tab (b ∷ Ns) xs e ⟨ ok , wf ⟩ k k< d d∈ with k ≟ length Ns
... | no k≢ = tab Ns (xs ++ [ b ]) (trans e (sym (++-assoc xs [ b ] Ns))) wf k k<' d d∈
  where
  k<' : k < length Ns
  k<' with m≤n⇒m<n∨m≡n (≤-pred k<)
  ... | inj₁ lt = lt
  ... | inj₂ eq' = ⊥-elim (k≢ eq')
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) k< ν d∈ | yes refl = tt
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) k< (X ↦ ν) d∈ | yes refl = tt
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) k< (X ↦ (Y ↦ w)) ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ | yes refl = rel
  where
  𝕋' = tab Ns (xs ++ [ body m bbs bst ]) (trans e (sym (++-assoc xs [ body m bbs bst ] Ns))) wf
  rel : 𝕍code X (Y ↦ w) (length Ns)
  rel e₁ X𝕍 e₂ Y𝕍 =
    ⟨ m , ⟨ bbs , ⟨ bst , ⟨ trans (cong (λ L → global L (length Ns)) e) (reverse-‼-suffix xs _ Ns)
    , adequate 𝕋' (Block.instrs bst) (Block.jump bst) bbs c (blocks-adeq 𝕋' bbs cs) (frame-size m) (zeros-𝔽 (2 + (m ∸ 2))) G init-Fl w∈ ⟩ ⟩ ⟩ ⟩
    where
    G : ℝ (argsD (mem X) (mem Y)) (regs nothing (just e₁) (just e₂))
    G rax = init-𝕄
    G rdi d d∈ = inj₂ ⟨ e₁ , ⟨ refl , 𝕍s-∈ X X𝕍 d∈ ⟩ ⟩
    G rsi d d∈ = inj₂ ⟨ e₂ , ⟨ refl , 𝕍s-∈ Y Y𝕍 d∈ ⟩ ⟩

{- Adequacy -----------------------------------------------------------------------}

{- main: a run to a return of a related value, or, for ω, to an error -}
adequate-main : ∀ {n bs b w} → DefsWF ds → BodyOK (length ds) (body n bs b)
  → w ∈ ⟦ program ds (body n bs b) ⟧ₚ
  → Res (λ stk → run (Block.instrs b) (Block.jump b) bs stk nothing (zeros n) (regs (just (const Int 0ℤ)) nothing nothing)) w
adequate-main {n} {bs} {b} wf (c ∷ cs) w∈ =
  adequate (tab ds [] refl wf) (Block.instrs b) (Block.jump b) bs c (blocks-adeq (tab ds [] refl wf) bs cs) (length-replicate n) (zeros-𝔽 n) G init-Fl w∈
  where
  G : ℝ (called (zerosD 0)) (regs (just (const Int 0ℤ)) nothing nothing)
  G rax = ℬ-𝕄 Int _
  G rdi = init-𝕄
  G rsi = init-𝕄
