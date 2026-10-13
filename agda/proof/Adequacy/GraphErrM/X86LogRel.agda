{-

  Adequacy of the graph model with errors (Semantics/GraphErrM/X86.agda)
  for the X86 machine: every element of the denotation of a well-formed
  program is witnessed by a run of the machine of its global definitions
  ds, and ω by a run that stops with an error.

  As in Adequacy/X86LogRel.agda, a logical relation 𝕍 d v relates
  denotational values to machine values, and the code of a definition,
  Λ X. Λ Y. …, is related to code k when the machine runs definition k on
  values related to X and Y, on any stack, to a result related to the
  body's (Res). What is new is that a result w may be ω: Res S w says that
  S Errs on every stack when w = ω (Err), and otherwise returns a value
  related to w (Ret). A location is related to what the machine holds
  there (𝕄): ω to an unset location, any other element to a related value;
  so is the flag (Fl). The fundamental lemma (adequate) has a case for
  each check of the machine: e.g. a write Errs when its value is ω or its
  slot is beyond the frame, and a call Errs when its code, %rdi or %rsi is
  unset, its code is not code, or the callee Errs. A run cannot both
  return and err (Ret-Err), so a call whose result has a value holds no ω
  (calls-err).

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse; replicate)
open import Language.X86 using (Body)

module proof.Adequacy.GraphErrM.X86LogRel (ds : List Body) where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; δ; sub; eq; int; bool)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩) renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD)
open import proof.Framework.GraphModel.DOpSig using (■; Results)
open import proof.Framework.GraphModel.ErrorMonad
  hiding (K⟨_⟩; KOK; K-mono; K-≃; K-fin; K-ok; let-law; case-law) renaming (Val to Valᴰ)
open import Framework.GraphModel.Ops using (𝒯; car; cdr; payloadD) renaming (proj to projD; pair to pairD; inl to inlD; inr to inrD)
open import proof.Semantics.GraphErrM.Prim using (primᵐ; primD) renaming (out to dout)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
  hiding (Body)
open import Semantics.GraphErrM.X86
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
open import proof.Adequacy.Common using (ShapeOf; ShapeAt; has-length→length; length→has-length; δ?-inv)
open import proof.Adequacy.GraphErrM.LogRel using (δ?-nothing₁; δ?-nothing₂)
open import proof.Adequacy.GraphErrM.X86WF
open import proof.Adequacy.GraphErrM.X86Common ds
open import proof.Adequacy.GraphErrM.X86Soundness using ( _≟R_; ↦ₘ-here; ↦ₘ-other; ≔-here; ≔-other; args-inv; length-obs-list)

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (0ℤ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
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

vkind : Val → Kind
vkind (code k) = fun
vkind (pair v w) = prod
vkind (const B k) = base B
vkind (tup vs) = tup (length vs)
vkind (T.inl v) = inj
vkind (T.inr v) = inj

{- an element of the denotation of a value is of its kind -}
𝕍-kind : ∀ d v → 𝕍 d v → kind d ≡ vkind v
𝕍-kind (dconst k) (const B k) refl = refl
𝕍-kind ν (code k) r = refl
𝕍-kind (X ↦ w) (code k) r = refl
𝕍-kind ⦅ u₁ , u₂ ⦆ (pair v w) r = refl
𝕍-kind ⟨⟩ (tup []) refl = refl
𝕍-kind (tup[ i ] d) (tup vs) r = cong Kind.tup (sym (𝕍At-length i d vs r))
𝕍-kind (left d) (T.inl v) r = refl
𝕍-kind (right d) (T.inr v) r = refl

notint-obs : ∀ v → vkind v ≢ base Int → ∀ n → obs v ≢ o-const Int n
notint-obs (const .Int k) ni n refl = ni refl

{- the kind of a field -}
fkind : Field → Kind
fkind fstₛ = prod
fkind sndₛ = prod
fkind (getₛ {n} i) = tup n
fkind payload = inj

{- a field that the machine finds is of a value of its kind -}
field-kind : ∀ fl v {w} → get-field fl v ≡ just w → vkind v ≡ fkind fl
field-kind fstₛ (pair v w) refl = refl
field-kind sndₛ (pair v w) refl = refl
field-kind (getₛ i) (tup vs) e = cong Kind.tup (proj-just-length i vs e)
field-kind payload (T.inl v) refl = refl
field-kind payload (T.inr v) refl = refl

field-bad : ∀ fl v → vkind v ≢ fkind fl → get-field fl v ≡ nothing
field-bad fl v ne with get-field fl v in g
... | nothing = refl
... | just w = ⊥-elim (ne (field-kind fl v g))

{- Related locations ---------------------------------------------------------------}

{- a location holds a value related to every element of D other than ω,
   and is unset if D holds ω -}
Rel : Value → Maybe Val → Set
Rel d m = (d ≡ ω × m ≡ nothing) ⊎ (Σ[ v ∈ Val ] m ≡ just v × 𝕍 d v)

𝕄 : 𝒫 Value → Maybe Val → Set
𝕄 D m = ∀ d → d ∈ D → Rel d m

{- the flag, as the value that sete stores -}
Fl : 𝒫 Value → Maybe Bool → Set
Fl F f = 𝕄 F (mmap bit f)

𝕄-ω : ∀ {D m} → 𝕄 D m → ω ∈ D → m ≡ nothing
𝕄-ω h ω∈ with h ω ω∈
... | inj₁ ⟨ _ , e ⟩ = e
... | inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩ = ⊥-elim (𝕍-ω {v} r)

𝕄-val : ∀ {D m} → 𝕄 D m → ∀ d → d ∈ D → d ≢ ω → Σ[ v ∈ Val ] m ≡ just v × 𝕍 d v
𝕄-val h d d∈ d≢ with h d d∈
... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d≢ e)
... | inj₂ r = r

{- the values of D are related to the one value the location holds -}
𝕄-all : ∀ {D m v} → 𝕄 D m → m ≡ just v → ∀ d → d ∈ ⌊ D ⌋ → 𝕍 d v
𝕄-all h refl d d∈ with 𝕄-val h d (proj₁ d∈) (proj₂ d∈)
... | ⟨ _ , ⟨ refl , r ⟩ ⟩ = r

mmap-nothing : ∀ (f : Maybe Bool) → mmap bit f ≡ nothing → f ≡ nothing
mmap-nothing nothing _ = refl

mmap-just : ∀ (f : Maybe Bool) {x} → mmap bit f ≡ just x → Σ[ b ∈ Bool ] f ≡ just b × x ≡ bit b
mmap-just (just b) refl = ⟨ b , ⟨ refl , refl ⟩ ⟩

Fl-ω : ∀ {F f} → Fl F f → ω ∈ F → f ≡ nothing
Fl-ω {f = f} h ω∈ = mmap-nothing f (𝕄-ω h ω∈)

init-𝕄 : 𝕄 init nothing
init-𝕄 _ refl = inj₁ ⟨ refl , refl ⟩

init-Fl : Fl init nothing
init-Fl = init-𝕄

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

{- Operations ----------------------------------------------------------------------}

ℬ-𝕄 : ∀ B k → 𝕄 (ℬ B k ptt) (just (const B k))
ℬ-𝕄 B k (dconst k') ⟨ refl , refl ⟩ = inj₂ ⟨ const B k , ⟨ refl , refl ⟩ ⟩

𝕍all : 𝒫 Value → Val → Set
𝕍all X v = ∀ d → d ∈ X → 𝕍 d v

{- a bind: an error of its operand is the machine's error, and the values
   of the operand are related to the one the machine computes -}
𝕄-bind : ∀ {D m F} {k : Val → Maybe Val} → 𝕄 D m → (∀ {v} → 𝕍all ⌊ D ⌋ v → 𝕄 (F ⌊ D ⌋) (k v))
  → 𝕄 (D ≫= F) (m >>= k)
𝕄-bind h hF d (inj₁ ⟨ refl , ω∈ ⟩) = inj₁ ⟨ refl , bind-none (𝕄-ω h ω∈) ⟩
𝕄-bind h hF d (inj₂ ⟨ ⟨ d₀ , ⟨ d₀∈ , d₀≢ ⟩ ⟩ , d∈ ⟩) with 𝕄-val h d₀ d₀∈ d₀≢
... | ⟨ v , ⟨ refl , _ ⟩ ⟩ = hF (𝕄-all h refl) d d∈

{- a check: a value of the wrong kind is one the machine fails on -}
𝕄-check : ∀ {k X v A r} → 𝕍all X v → (vkind v ≢ k → r ≡ nothing) → 𝕄 A r → 𝕄 (checked k X A) r
𝕄-check {v = v} X𝕍 bad hA _ (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) =
  inj₁ ⟨ refl , bad (λ k≡ → ek (trans (𝕍-kind e v (X𝕍 e e∈)) k≡)) ⟩
𝕄-check X𝕍 bad hA d (inj₂ d∈) = hA d d∈

{- primitives, on two integers -}
int-out : ∀ p {n m u w} → u ≡ const Int n → w ≡ const Int m
  → (dout (δ p n m) ≡ ω × prim? p u w ≡ nothing) ⊎ (Σ[ v ∈ Val ] prim? p u w ≡ just v × 𝕍 (dout (δ p n m)) v)
int-out p {n} {m} refl refl = inj₂ ⟨ out (δ p n m) , ⟨ refl , 𝕍-out (δ p n m) ⟩ ⟩

prim-𝕄 : ∀ p {D E md me} → 𝕄 D md → 𝕄 E me
  → 𝕄 (primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩) (md >>= λ u → me >>= λ w → prim? p u w)
prim-𝕄 p {D} {E} hD hE = 𝕄-bind {F = λ X → E ≫= K X} hD λ {u} X𝕍 → 𝕄-bind {F = K ⌊ D ⌋} hE λ {w} Y𝕍 →
  𝕄-check X𝕍 (λ ni → cong (mmap out) (δ?-nothing₁ p (obs u) (obs w) (notint-obs u ni)))
    (𝕄-check Y𝕍 (λ ni → cong (mmap out) (δ?-nothing₂ p (obs u) (obs w) (notint-obs w ni)))
      λ { _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ → int-out p (X𝕍 _ n∈) (Y𝕍 _ m∈) })
  where
  K : 𝒫 Value → 𝒫 Value → 𝒫 Value
  K X Y = checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))

>>=-comm : ∀ {A B C : Set} (ma : Maybe A) (mb : Maybe B) (f : A → B → Maybe C)
  → (ma >>= λ a → mb >>= λ b → f a b) ≡ (mb >>= λ b → ma >>= λ a → f a b)
>>=-comm nothing nothing f = refl
>>=-comm nothing (just b) f = refl
>>=-comm (just a) nothing f = refl
>>=-comm (just a) (just b) f = refl

sub-𝕄 : ∀ {Dd Da md ma} → 𝕄 Dd md → 𝕄 Da ma
  → 𝕄 (primᵐ sub ⟨ Dd , ⟨ Da , ptt ⟩ ⟩) (ma >>= λ w → md >>= λ u → prim? sub u w)
sub-𝕄 {md = md} {ma} hd ha = subst (𝕄 _) (>>=-comm md ma (λ u w → prim? sub u w)) (prim-𝕄 sub hd ha)

{- a comparison sets the flag to the truth value that eq produces -}
cmp-bit : ∀ (m₁ m₂ : Maybe Val) → mmap bit (m₁ >>= λ v → m₂ >>= λ w → cmp v w) ≡ (m₁ >>= λ v → m₂ >>= λ w → prim? eq v w)
cmp-bit nothing m₂ = refl
cmp-bit (just v) nothing = refl
cmp-bit (just v) (just w) with δ? eq (obs v) (obs w) in d
... | nothing = refl
... | just r with δ?-inv eq (obs v) (obs w) d
...   | ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ = refl

cmp-Fl : ∀ {D₁ D₂ m₁ m₂} → 𝕄 D₁ m₁ → 𝕄 D₂ m₂
  → Fl (primᵐ eq ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩) (m₁ >>= λ v → m₂ >>= λ w → cmp v w)
cmp-Fl {m₁ = m₁} {m₂} h₁ h₂ = subst (𝕄 _) (sym (cmp-bit m₁ m₂)) (prim-𝕄 eq h₁ h₂)

{- the tag of an injection -}
inl-kind : ∀ v {b} → is-inl v ≡ just b → vkind v ≡ inj
inl-kind (T.inl v) refl = refl
inl-kind (T.inr v) refl = refl

isinl-Fl : ∀ {D m} → 𝕄 D m → Fl (isinlᵐ D) (m >>= is-inl)
isinl-Fl {m = m} h = subst (𝕄 _) (sym (mb m)) (𝕄-bind {F = λ X → checked inj X (isinlD X)} h λ {v} X𝕍 → 𝕄-check X𝕍 (bad v) (K X𝕍))
  where
  mb : ∀ m → mmap bit (m >>= is-inl) ≡ (m >>= λ v → mmap bit (is-inl v))
  mb nothing = refl
  mb (just v) = refl
  bad : ∀ v → vkind v ≢ inj → mmap bit (is-inl v) ≡ nothing
  bad v ne with is-inl v in e
  ... | nothing = refl
  ... | just b = ⊥-elim (ne (inl-kind v e))
  tl : ∀ v {u} → 𝕍 (left u) v → mmap bit (is-inl v) ≡ just (bit true)
  tl (T.inl v) r = refl
  tr : ∀ v {u} → 𝕍 (right u) v → mmap bit (is-inl v) ≡ just (bit false)
  tr (T.inr v) r = refl
  K : ∀ {X v} → 𝕍all X v → 𝕄 (isinlD X) (mmap bit (is-inl v))
  K {v = v} X𝕍 _ (inj₁ ⟨ u , ⟨ l , refl ⟩ ⟩) = inj₂ ⟨ _ , ⟨ tl v (X𝕍 _ l) , refl ⟩ ⟩
  K {v = v} X𝕍 _ (inj₂ ⟨ u , ⟨ r , refl ⟩ ⟩) = inj₂ ⟨ _ , ⟨ tr v (X𝕍 _ r) , refl ⟩ ⟩

{- the fields of a value -}
fkern : Field → 𝒫 Value → 𝒫 Value
fkern fstₛ X = car ⟨ X , ptt ⟩
fkern sndₛ X = cdr ⟨ X , ptt ⟩
fkern (getₛ i) X = projD i ⟨ X , ptt ⟩
fkern payload X = payloadD (X ⇂ ValPayload)

field-K : ∀ fl {X v} → 𝕍all X v → 𝕄 (fkern fl X) (get-field fl v)
field-K fstₛ {v = v} X𝕍 u ⟨ w , p∈ ⟩ = K v (X𝕍 _ p∈)
  where
  K : ∀ v → 𝕍 ⦅ u , w ⦆ v → Rel u (get-field fstₛ v)
  K (pair v₁ v₂) r = inj₂ ⟨ v₁ , ⟨ refl , proj₁ r ⟩ ⟩
field-K sndₛ {v = v} X𝕍 w ⟨ u , p∈ ⟩ = K v (X𝕍 _ p∈)
  where
  K : ∀ v → 𝕍 ⦅ u , w ⦆ v → Rel w (get-field sndₛ v)
  K (pair v₁ v₂) r = inj₂ ⟨ v₂ , ⟨ refl , proj₂ r ⟩ ⟩
field-K (getₛ i) {v = v} X𝕍 x t∈ = K v (X𝕍 _ t∈)
  where
  K : ∀ v → 𝕍 (tup[ i ] x) v → Rel x (get-field (getₛ i) v)
  K (tup vs) r = let ⟨ v' , ⟨ e , r' ⟩ ⟩ = 𝕍At-proj i x vs r in inj₂ ⟨ v' , ⟨ e , r' ⟩ ⟩
field-K payload {v = v} X𝕍 x (inj₁ l) = K v (X𝕍 _ (proj₁ l))
  where
  K : ∀ v → 𝕍 (left x) v → Rel x (get-field payload v)
  K (T.inl v₁) r = inj₂ ⟨ v₁ , ⟨ refl , r ⟩ ⟩
field-K payload {v = v} X𝕍 x (inj₂ rt) = K v (X𝕍 _ (proj₁ rt))
  where
  K : ∀ v → 𝕍 (right x) v → Rel x (get-field payload v)
  K (T.inr v₁) r = inj₂ ⟨ v₁ , ⟨ refl , r ⟩ ⟩

field-𝕄′ : ∀ fl {D m} → 𝕄 D m → 𝕄 (D ≫= λ X → checked (fkind fl) X (fkern fl X)) (m >>= get-field fl)
field-𝕄′ fl h = 𝕄-bind {F = λ X → checked (fkind fl) X (fkern fl X)} h λ {v} X𝕍 → 𝕄-check X𝕍 (field-bad fl v) (field-K fl X𝕍)

field-𝕄 : ∀ fl {D m} → 𝕄 D m → 𝕄 (field′ fl D) (m >>= get-field fl)
field-𝕄 fstₛ = field-𝕄′ fstₛ
field-𝕄 sndₛ = field-𝕄′ sndₛ
field-𝕄 (getₛ i) = field-𝕄′ (getₛ i)
field-𝕄 payload = field-𝕄′ payload

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

{- a tuple of related values -}
tup-𝕄 : ∀ n {Xs : Results (𝒫 Value) (replicate n ■)} {vs} → length vs ≡ n
  → (∀ j x → x ∈ nthD Xs j → 𝕍At j x vs) → 𝕄 (𝒯 n Xs) (just (tup vs))
tup-𝕄 zero {vs = []} _ _ ⟨⟩ tt = inj₂ ⟨ tup [] , ⟨ refl , refl ⟩ ⟩
tup-𝕄 (suc n) _ rs (tup[ i ] x) ⟨ refl , ⟨ x∈ , _ ⟩ ⟩ = inj₂ ⟨ _ , ⟨ refl , rs i x x∈ ⟩ ⟩

{- an injection of a related value -}
inl-𝕄 : ∀ {X v} → 𝕍all X v → 𝕄 (inlD ⟨ X , ptt ⟩) (just (T.inl v))
inl-𝕄 X𝕍 (left u) u∈ = inj₂ ⟨ _ , ⟨ refl , X𝕍 u u∈ ⟩ ⟩

inr-𝕄 : ∀ {X v} → 𝕍all X v → 𝕄 (inrD ⟨ X , ptt ⟩) (just (T.inr v))
inr-𝕄 X𝕍 (right u) u∈ = inj₂ ⟨ _ , ⟨ refl , X𝕍 u u∈ ⟩ ⟩

{- the flag of a jump to a left or right branch -}
bit-kind : ∀ b → vkind (bit b) ≡ inj
bit-kind true = refl
bit-kind false = refl

fl-left : ∀ f {u} → Rel (left u) (mmap bit f) → f ≡ just true
fl-left f (inj₁ ⟨ () , _ ⟩)
fl-left (just true) _ = refl
fl-left (just false) (inj₂ ⟨ _ , ⟨ refl , () ⟩ ⟩)
fl-left nothing (inj₂ ⟨ _ , ⟨ () , _ ⟩ ⟩)

fl-right : ∀ f {u} → Rel (right u) (mmap bit f) → f ≡ just false
fl-right f (inj₁ ⟨ () , _ ⟩)
fl-right (just false) _ = refl
fl-right (just true) (inj₂ ⟨ _ , ⟨ refl , () ⟩ ⟩)
fl-right nothing (inj₂ ⟨ _ , ⟨ () , _ ⟩ ⟩)

{- Related states ------------------------------------------------------------------}

module _ {K : ℕ} {T : Table} (𝕋T : 𝕋 K T) where

  𝒪-𝕄 : ∀ {n σ ρs φ ρm} a → OK (_< K) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → 𝕄 (𝒪 T n σ ρs a) (arg φ ρm a)
  𝒪-𝕄 {n} {φ = φ} (loc (var x)) _ refl F G with x <? length φ
  ... | yes x< = F x x<
  ... | no ¬x< = subst (𝕄 init) (sym (‼-out φ x ¬x<)) init-𝕄
  𝒪-𝕄 (loc (reg g)) _ _ F G = G g
  𝒪-𝕄 (imm B k) _ _ F G = ℬ-𝕄 B k
  𝒪-𝕄 (label k) k< _ F G d d∈ = inj₂ ⟨ code k , ⟨ refl , 𝕋T k k< d d∈ ⟩ ⟩


  {- the operands of alloc: an error of one is the machine's error, and
     their values are related to the ones the machine computes -}
  𝕄-args : ∀ {n σ ρs φ ρm} as acc {Kr : Results (𝒫 Value) (replicate (length as) ■) → 𝒫 Value} (k : List Val → Maybe Val)
    → All (OK (_< K)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → (∀ {vs} → length vs ≡ length as → (∀ j x → x ∈ nthD ⌊ 𝒪s T n σ ρs as ⌋s j → 𝕍At j x vs)
         → 𝕄 (Kr ⌊ 𝒪s T n σ ρs as ⌋s) (k (reverse acc ++ vs)))
    → 𝕄 (binds (length as) (𝒪s T n σ ρs as) Kr) (args φ ρm acc as k)
  𝕄-args [] acc k _ _ _ _ hK = subst (𝕄 _) (cong k (++-identityʳ (reverse acc))) (hK refl (λ ()))
  𝕄-args {n} {σ} {ρs} (a ∷ as) acc {Kr} k (o ∷ os) nφ F G hK =
    𝕄-bind {F = λ X → binds (length as) (𝒪s T n σ ρs as) (λ Xs → Kr ⟨ X , Xs ⟩)} (𝒪-𝕄 a o nφ F G) λ {v} X𝕍 →
    𝕄-args as (v ∷ acc) k os nφ F G λ {vs} len rs →
      subst (𝕄 _) (cong k (sym (trans (cong (_++ vs) (unfold-reverse v acc)) (++-assoc (reverse acc) [ v ] vs))))
        (hK (cong suc len) λ { zero x x∈ → ⟨ len , X𝕍 x x∈ ⟩ ; (suc j) x x∈ → rs j x x∈ })

  object-𝕄 : ∀ {n σ ρs φ ρm} sh as → All (OK (_< K)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → 𝕄 (object T n σ ρs sh as) (args φ ρm [] as (build sh))
  object-𝕄 {n} {σ} {ρs} pairₛ (a ∷ b ∷ []) os nφ F G = 𝕄-args (a ∷ b ∷ []) [] {pairD} (build pairₛ) os nφ F G P
    where
    P : ∀ {vs} → length vs ≡ 2 → (∀ j x → x ∈ nthD ⌊ 𝒪s T n σ ρs (a ∷ b ∷ []) ⌋s j → 𝕍At j x vs)
      → 𝕄 (pairD ⌊ 𝒪s T n σ ρs (a ∷ b ∷ []) ⌋s) (build pairₛ vs)
    P {v₁ ∷ v₂ ∷ []} _ rs ⦅ u , w ⦆ ⟨ u∈ , w∈ ⟩ = inj₂ ⟨ pair v₁ v₂ , ⟨ refl , ⟨ proj₂ (rs zero u u∈) , proj₂ (rs (suc zero) w w∈) ⟩ ⟩ ⟩
  object-𝕄 tupleₛ as os nφ F G = 𝕄-args as [] {𝒯 (length as)} (build tupleₛ) os nφ F G (tup-𝕄 (length as))
  object-𝕄 inlₛ (a ∷ []) (oa ∷ []) nφ F G = 𝕄-bind {F = λ X → inlD ⟨ X , ptt ⟩} (𝒪-𝕄 a oa nφ F G) inl-𝕄
  object-𝕄 inrₛ (a ∷ []) (oa ∷ []) nφ F G = 𝕄-bind {F = λ X → inrD ⟨ X , ptt ⟩} (𝒪-𝕄 a oa nφ F G) inr-𝕄
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ (a ∷ []) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ (a ∷ []) (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} pairₛ (a ∷ b ∷ c ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} pairₛ (a ∷ b ∷ c ∷ as) (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inlₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inlₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inlₛ (a ∷ b ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inlₛ (a ∷ b ∷ as) (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inrₛ [] os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inrₛ [] (λ ()) ⟩
  object-𝕄 {φ = φ} {ρm = ρm} inrₛ (a ∷ b ∷ as) os nφ F G _ refl = inj₁ ⟨ refl , arity-none {φ} {ρm} inrₛ (a ∷ b ∷ as) (λ ()) ⟩

  {- the related values of a set that holds some -}
  𝕄→𝕍s : ∀ {D m} → 𝕄 D m → ∀ V → mem V ⊆ ⌊ D ⌋ → V ≢ [] → Σ[ v ∈ Val ] m ≡ just v × 𝕍s V v
  𝕄→𝕍s h [] V⊆ ne = ⊥-elim (ne refl)
  𝕄→𝕍s h (d₀ ∷ V) V⊆ ne with 𝕄-val h d₀ (proj₁ (V⊆ d₀ (here refl))) (proj₂ (V⊆ d₀ (here refl)))
  ... | ⟨ v , ⟨ e , _ ⟩ ⟩ = ⟨ v , ⟨ e , all→𝕍s (d₀ ∷ V) (λ d d∈ → 𝕄-all h e d (V⊆ d d∈)) ⟩ ⟩

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

  {- a call that Errs: at once, or in the callee -}
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

  callq-notcode : ∀ v {stk ρ} → vkind v ≢ fun → callq? ds (just v) stk ρ ≡ stop o-error
  callq-notcode (code k) nf = ⊥-elim (nf refl)
  callq-notcode (pair _ _) nf = refl
  callq-notcode (const _ _) nf = refl
  callq-notcode (tup _) nf = refl
  callq-notcode (T.inl _) nf = refl
  callq-notcode (T.inr _) nf = refl

  call-𝕄 : ∀ {n σ ρs φ ρm} a → OK (_< K) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → ∀ w
    → w ∈ callᵐ ⟨ 𝒪 T n σ ρs a , ⟨ ρs rdi , ⟨ ρs rsi , ptt ⟩ ⟩ ⟩ → (w ≡ ω × CallErr φ ρm a) ⊎ Calls φ ρm a w
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₁ ⟨ refl , ω∈ ⟩) =
    inj₁ ⟨ refl , inj₁ (λ stk → cong (λ m → callq? ds m stk ρm) (𝕄-ω (𝒪-𝕄 a oa nφ F G) ω∈)) ⟩
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ ⟨ c , ⟨ c∈ , c≢ ⟩ ⟩ , inj₁ ⟨ refl , ω∈ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-rdi v (𝕄-ω (G rdi) ω∈))) ⟩
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ ⟨ c , ⟨ c∈ , c≢ ⟩ ⟩ , inj₂ ⟨ _ , inj₁ ⟨ refl , ω∈ ⟩ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-rsi v (𝕄-ω (G rsi) ω∈))) ⟩
  call-𝕄 {ρm = ρm} a oa nφ F G w (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ c , ⟨ ⟨ c∈ , c≢ ⟩ , ck ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) c c∈ c≢
  ... | ⟨ v , ⟨ ea , r ⟩ ⟩ =
    inj₁ ⟨ refl , inj₁ (λ stk → trans (cong (λ m → callq? ds m stk ρm) ea) (callq-notcode v λ e → ck (trans (𝕍-kind c v r) e))) ⟩
  call-𝕄 a oa nφ F G w (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , _ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
      with 𝕄-val (𝒪-𝕄 a oa nφ F G) _ e∈ (λ ()) | 𝕄→𝕍s (G rdi) V V⊆ neV | 𝕄→𝕍s (G rsi) U U⊆ neU
  ... | ⟨ code k , ⟨ ea , r ⟩ ⟩ | ⟨ e₁ , ⟨ er₁ , X𝕍 ⟩ ⟩ | ⟨ e₂ , ⟨ er₂ , Y𝕍 ⟩ ⟩ with r e₁ X𝕍 e₂ Y𝕍
  ... | ⟨ m , ⟨ bbs , ⟨ bst , ⟨ eg , inj₁ ⟨ refl , er ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ refl , inj₂ ⟨ k , ⟨ e₁ , ⟨ e₂ , ⟨ m , ⟨ bbs , ⟨ bst , ⟨ ea , ⟨ er₁ , ⟨ er₂ , ⟨ eg , er ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  ... | ⟨ m , ⟨ bbs , ⟨ bst , ⟨ eg , inj₂ ⟨ v , ⟨ ret , rv ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = inj₂ (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rv)

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

  {- a jump to block l of bs: a missing block Errs -}
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
  put-case (var x) {D} {m} is j bs {σ} {ρs} {Φ} {φ} {ρm} {f} {w} st h c AB refl F G Fl' w∈ with x <? length φ
  put-case (var x) {D} {m} is j bs {σ} {ρs} {Φ} {φ} {ρm} {f} {w} st h c AB refl F G Fl' w∈ | yes x<
      with proj₁ (letᵐ-unfold {D} {λ X → ⟦ is ⟧ˢ T (length φ) (⟦ j ⟧ʲ (blocks T (length φ) bs)) (σ [ x ↦ₛ X ]) ρs Φ}) w w∈
  ... | inj₁ ⟨ refl , ω∈ ⟩ = Res-stop (λ stk → trans (st stk) (cong (λ m' → putM (var x) m' φ ρm (run is j bs stk f)) (𝕄-ω h ω∈)))
  ... | inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈' , _ ⟩ , _ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ ⟩ with 𝕄→𝕍s h V V⊆ ne
  ...   | ⟨ v , ⟨ refl , Vs ⟩ ⟩ with ≔-ok φ x v x<
  ...     | ⟨ φ' , e ⟩ = Res-step (λ stk → trans (st stk) (cong (λ mφ → upd mφ ρm (run is j bs stk f)) e))
                           (adequate is j bs c AB (Assigned.len a) F' G Fl' w∈')
    where
    a = ≔-inv φ x e
    F' : 𝔽 (σ [ x ↦ₛ mem V ]) φ'
    F' y y< with y ≟ x
    ... | yes refl = λ d d∈ → inj₂ ⟨ v , ⟨ Assigned.here a , 𝕍s-∈ V Vs d∈ ⟩ ⟩
    ... | no ne' = subst (𝕄 (σ y)) (sym (Assigned.other a y ne')) (F y (subst (y <_) (Assigned.len a) y<))
  put-case (var x) is j bs {φ = φ} {ρm} {f} st h c AB refl F G Fl' (inj₁ ⟨ refl , ω∈ ⟩) | no ¬x< =
    Res-stop (λ stk → trans (st stk) (cong (λ m' → putM (var x) m' φ ρm (run is j bs stk f)) (𝕄-ω h ω∈)))
  put-case (var x) is j bs {φ = φ} {ρm} {f} st h c AB refl F G Fl' (inj₂ ⟨ ⟨ d₀ , ⟨ d₀∈ , d₀≢ ⟩ ⟩ , refl ⟩) | no ¬x<
      with 𝕄-val h d₀ d₀∈ d₀≢
  ... | ⟨ v , ⟨ e , _ ⟩ ⟩ =
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
  flag-case is j bs {mb = mb} st Fl₀ c AB nφ F G (inj₂ ⟨ ⟨ d₀ , ⟨ d₀∈ , d₀≢ ⟩ ⟩ , w∈ ⟩) with 𝕄-val Fl₀ d₀ d₀∈ d₀≢
  ... | ⟨ _ , ⟨ e , _ ⟩ ⟩ with mmap-just mb e
  ...   | ⟨ b , ⟨ refl , _ ⟩ ⟩ = Res-step st (adequate is j bs c AB nφ F G Fl₀ w∈)

  adequate (movq a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (𝒪-𝕄 a oa nφ F G) c AB nφ F G Fl' w∈
  adequate (subq a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (sub-𝕄 (𝒪-𝕄 (loc d) tt nφ F G) (𝒪-𝕄 a oa nφ F G)) c AB nφ F G Fl' w∈
  adequate (cmpq a₂ a₁ ∷ is) j bs ⟨ ⟨ o₂ , o₁ ⟩ , c ⟩ AB nφ F G Fl' w∈ =
    flag-case is j bs (λ _ → refl) (cmp-Fl (𝒪-𝕄 a₁ o₁ nφ F G) (𝒪-𝕄 a₂ o₂ nφ F G)) c AB nφ F G w∈
  adequate (sete d ∷ is) j bs {f = just b} ⟨ _ , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) Fl' c AB nφ F G Fl' w∈
  adequate (sete d ∷ is) j bs {φ = φ} {ρm} {f = nothing} ⟨ _ , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs {φ = φ} {ρm = ρm} {f = nothing} {S = λ stk → run (sete d ∷ is) j bs stk nothing φ ρm} (λ stk → refl) Fl' c AB nφ F G Fl' w∈
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
  adequate [] (je l₁ l₂) bs {φ = φ} {ρm} {f} _ AB nφ F G Fl' (inj₁ ⟨ refl , ω∈ ⟩) with Fl-ω {f = f} Fl' ω∈
  ... | refl = Res-stop (λ stk → refl)
  adequate [] (je l₁ l₂) bs {f = f} _ AB nφ F G Fl' (inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ d , ⟨ ⟨ d∈ , d≢ ⟩ , dk ⟩ ⟩ ⟩ ⟩)
      with 𝕄-val Fl' d d∈ d≢
  ... | ⟨ _ , ⟨ e , r ⟩ ⟩ with mmap-just f e
  ...   | ⟨ b , ⟨ _ , refl ⟩ ⟩ = ⊥-elim (dk (trans (𝕍-kind d (bit b) r) (bit-kind b)))
  adequate [] (je l₁ l₂) bs {f = f} _ AB nφ F G Fl' (inj₂ ⟨ _ , inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ all , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) ⟩)
      with fl-left f (Fl' (left u) (proj₁ (proj₁ (all u (here refl)))))
  ... | refl = go {bs = bs} {l = l₁} (λ _ → refl) (AB l₁ nφ F G Fl' w∈)
  adequate [] (je l₁ l₂) bs {f = f} _ AB nφ F G Fl' (inj₂ ⟨ _ , inj₂ (inj₂ ⟨ u , ⟨ U , ⟨ all , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) ⟩)
      with fl-right f (Fl' (right u) (proj₁ (proj₁ (all u (here refl)))))
  ... | refl = go {bs = bs} {l = l₂} (λ _ → refl) (AB l₂ nφ F G Fl' w∈)

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
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) k< (X ↦ (Y ↦ w)) ⟨ ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ , _ ⟩ | yes refl = rel
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
