{-

  Lemmas about reduction semantics (Framework/Reduction.agda), and forward
  simulations between them (proof/Framework/Simulation.agda):

  * runs of a reduction (Star*, Plus*), on terms or on the operands of a
    tuple, and a run of a subterm as a run in a context that reduces that
    subterm first (a frame: star-in, plus-in), and the frames of the
    operands of a context (LR);
  * how a target term answers the reduction of a source term (Ans): by a
    run to a related value, by a run to a stuck term, or by one or more
    steps to a term related to the reduct; congruence (ans-in), the
    operands of a tuple (ans-cons), and a missing result (ret?-ans);
  * the operands of a tuple, each with a property (Each), or related
    pointwise (Pw), and what a substitution may map a variable to: a
    variable or a value (VarOrValue);
  * the answers of a machine that ignore the index, with target steps
    first (pre, pre⋆);
  * the end theorem: if the reduction of every source term is answered
    by every related target term, and related values are observed alike,
    the two machines are equivalent (red-equivalent).

-}

module proof.Framework.Reduction (Obs : Set) (o-error : Obs) where

open import Framework.Smallstep Obs
open import proof.Framework.Smallstep Obs using (Plus; plus)
open import proof.Framework.Simulation Obs using (FSim; Answers≺; stops; steps; stutters; runs; equivalent)
open import Framework.Reduction Obs o-error public

open import Framework.abt.Sig using (Sig; ■)
open import Framework.abt.AbstractBindingTree using (ABT; Args; nil; cons; ast; `_)
open import Framework.ListUtil using (args→list; proj; has-length)
import Framework.Syntax.Scope as Sc
import proof.Framework.Syntax.Subst as Sb

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

toNext-to : ∀ {A o} {r : Red A} {M} → toNext o r ≡ next M → r ≡ to M
toNext-to {r = to _} refl = refl

{- a value in the context continues -}
val-in : ∀ {A B} {f : A → B} {r k} → r ≡ val → step-in f r k ≡ k
val-in refl = refl

{- Runs ------------------------------------------------------------------------}

module _ {T : Set} (red : T → Red T) where

  infixr 5 _◅_
  data Star* : T → T → Set where
    ε : ∀ {X} → Star* X X
    _◅_ : ∀ {X Y Z} → red X ≡ to Y → Star* Y Z → Star* X Z

  data Plus* : T → T → Set where
    plus : ∀ {X Y Z} → red X ≡ to Y → Star* Y Z → Plus* X Z

module _ {T : Set} {red : T → Red T} where

  infixr 5 _◅◅_
  _◅◅_ : ∀ {X Y Z} → Star* red X Y → Star* red Y Z → Star* red X Z
  ε ◅◅ τ = τ
  (s ◅ σ) ◅◅ τ = s ◅ (σ ◅◅ τ)

  star-plus : ∀ {X Y Z} → Star* red X Y → Plus* red Y Z → Plus* red X Z
  star-plus ε π = π
  star-plus (s ◅ σ) (plus s' τ) = plus s (σ ◅◅ (s' ◅ τ))

  plus-star : ∀ {X Y Z} → Plus* red X Y → Star* red Y Z → Plus* red X Z
  plus-star (plus s σ) τ = plus s (σ ◅◅ τ)

  {- one step -}
  one : ∀ {X Y} → red X ≡ to Y → Plus* red X Y
  one s = plus s ε

{- g is a frame: g X reduces X first, and then continues with κ X -}
record Frame {T U : Set} (redT : T → Red T) (redU : U → Red U) (g : T → U) : Set where
  constructor frame
  field
    κ : T → Red U
    eq : ∀ X → redU (g X) ≡ step-in g (redT X) (κ X)

module _ {T U : Set} {redT : T → Red T} {redU : U → Red U} {g : T → U}
         (F : Frame redT redU g) where
  open Frame F

  step-in-to : ∀ {X Y} → redT X ≡ to Y → redU (g X) ≡ to (g Y)
  step-in-to s = trans (eq _) (cong (λ r → step-in g r (κ _)) s)

  star-in : ∀ {X Y} → Star* redT X Y → Star* redU (g X) (g Y)
  star-in ε = ε
  star-in (s ◅ σ) = step-in-to s ◅ star-in σ

  plus-in : ∀ {X Y} → Plus* redT X Y → Plus* redU (g X) (g Y)
  plus-in (plus s σ) = plus (step-in-to s) (star-in σ)

  error-in : ∀ {X} → redT X ≡ error → redU (g X) ≡ error
  error-in e = trans (eq _) (cong (λ r → step-in g r (κ _)) e)

{- a frame in a frame -}
step-in-∘ : ∀ {A B C : Set} {f : B → C} {h : A → B} r {k k'}
  → step-in f (step-in h r k) k' ≡ step-in (λ x → f (h x)) r (step-in f k k')
step-in-∘ val = refl
step-in-∘ error = refl
step-in-∘ (to _) = refl

{- the empty context -}
frame-id : ∀ {T : Set} {red : T → Red T} → Frame red red (λ x → x)
frame-id {red = red} = frame (λ _ → val) (λ X → lemma (red X))
  where lemma : ∀ {T} (r : Red T) → r ≡ step-in (λ x → x) r val
        lemma val = refl
        lemma error = refl
        lemma (to _) = refl

frame-∘ : ∀ {T U V : Set} {redT : T → Red T} {redU : U → Red U} {redV : V → Red V}
  {h : T → U} {f : U → V} → Frame redT redU h → Frame redU redV f → Frame redT redV (λ x → f (h x))
frame-∘ {redT = redT} {h = h} {f = f} (frame κh eqh) (frame κf eqf) =
  frame _ (λ X → trans (eqf _) (trans (cong (λ r → step-in f r (κf (h X))) (eqh X)) (step-in-∘ {f = f} {h = h} (redT X))))

{- Answers ---------------------------------------------------------------------}

{- how a target term M' answers the reduction r of a source term M, for a
   relation R between source and target terms and a predicate Val on the
   target's values -}
data Ans {S T : Set} (red : T → Red T) (Val : T → Set) (R : S → T → Set) (M : S)
  : Red S → T → Set where
  val : ∀ {M' V'} → Star* red M' V' → Val V' → R M V' → Ans red Val R M val M'
  error : ∀ {M' W'} → Star* red M' W' → red W' ≡ error → Ans red Val R M error M'
  to : ∀ {M₁ M' M₁'} → Plus* red M' M₁' → R M₁ M₁' → Ans red Val R M (to M₁) M'

module _ {S T : Set} {red : T → Red T} {Val : T → Set} {R : S → T → Set} where

  ans-star : ∀ {M r X Y} → Star* red X Y → Ans red Val R M r Y → Ans red Val R M r X
  ans-star σ (val τ v m) = val (σ ◅◅ τ) v m
  ans-star σ (error τ w) = error (σ ◅◅ τ) w
  ans-star σ (to π m) = to (star-plus σ π) m

  ans-step : ∀ {M r X Y} → red X ≡ to Y → Ans red Val R M r Y → Ans red Val R M r X
  ans-step s = ans-star (s ◅ ε)

  {- a source subterm that is a value -}
  ans-skip : ∀ {A} {f : A → S} {r k M X} → r ≡ val → Ans red Val R M k X → Ans red Val R M (step-in f r k) X
  ans-skip refl a = a

{- congruence: the reduction of the subterm X of f X, in the frame g -}
ans-in : ∀ {S S' T U : Set} {redT : T → Red T} {redU : U → Red U} {ValT : T → Set} {ValU : U → Set}
  {R : S → T → Set} {R' : S' → U → Set} {f : S → S'} {g : T → U} {X X' r k}
  → Frame redT redU g → (∀ {Y Y'} → R Y Y' → R' (f Y) (g Y'))
  → Ans redT ValT R X r X'
  → (∀ {V'} → ValT V' → R X V' → Ans redU ValU R' (f X) k (g V'))
  → Ans redU ValU R' (f X) (step-in f r k) (g X')
ans-in G c (to π m) k = to (plus-in G π) (c m)
ans-in G c (error σ w) k = error (star-in G σ) (error-in G w)
ans-in G c (val σ v m) k = ans-star (star-in G σ) (k v m)

{- a result that may be missing, related pointwise -}
ret?-ans : ∀ {S T : Set} {red : T → Red T} {Val : T → Set} {R : S → T → Set} {M mv mw X}
  → M.Pointwise R mv mw → red X ≡ ret? mw → Ans red Val R M (ret? mv) X
ret?-ans (M.just r) e = to (one e) r
ret?-ans M.nothing e = error ε e

{- The operands of tuples ------------------------------------------------------}

{- the operands of two tuples, related pointwise -}
data Pw {Op₁ Op₂ : Set} {sig₁ : Op₁ → List Sig} {sig₂ : Op₂ → List Sig}
  (R : ABT Op₁ sig₁ → ABT Op₂ sig₂ → Set)
  : ∀ {n} → Args Op₁ sig₁ (replicate n ■) → Args Op₂ sig₂ (replicate n ■) → Set where
  [] : Pw R nil nil
  _∷_ : ∀ {n M M'} {as : Args Op₁ sig₁ (replicate n ■)} {as' : Args Op₂ sig₂ (replicate n ■)}
    → R M M' → Pw R as as' → Pw R (cons (ast M) as) (cons (ast M') as')

module _ {Op₁ Op₂ : Set} {sig₁ : Op₁ → List Sig} {sig₂ : Op₂ → List Sig}
         {R : ABT Op₁ sig₁ → ABT Op₂ sig₂ → Set} where

  pw-map : ∀ {S} → (∀ {M M'} → R M M' → S M M') → ∀ {n as as'} → Pw R {n} as as' → Pw S as as'
  pw-map f [] = []
  pw-map f (r ∷ rs) = f r ∷ pw-map f rs

  pw-list : ∀ {n as as'} → Pw R {n} as as' → Pointwise R (args→list as) (args→list as')
  pw-list [] = []
  pw-list (r ∷ rs) = r ∷ pw-list rs

  {- with the operands on the right, or on the left, well scoped -}
  zipʳ : ∀ {k n as as'} → Pw R {n} as as' → Sc.WS-args Op₂ sig₂ k as' → Pw (λ M M' → R M M' × Sc.WS Op₂ sig₂ k M') as as'
  zipʳ [] _ = []
  zipʳ (r ∷ rs) (w , ws) = (r , w) ∷ zipʳ rs ws

  unzipʳ : ∀ {k n as as'} → Pw (λ M M' → R M M' × Sc.WS Op₂ sig₂ k M') {n} as as' → Pw R as as' × Sc.WS-args Op₂ sig₂ k as'
  unzipʳ [] = [] , tt
  unzipʳ ((r , w) ∷ rs) = (r ∷ proj₁ (unzipʳ rs)) , w , proj₂ (unzipʳ rs)

  zipˡ : ∀ {k n as as'} → Pw R {n} as as' → Sc.WS-args Op₁ sig₁ k as → Pw (λ M M' → R M M' × Sc.WS Op₁ sig₁ k M) as as'
  zipˡ [] _ = []
  zipˡ (r ∷ rs) (w , ws) = (r , w) ∷ zipˡ rs ws

  unzipˡ : ∀ {k n as as'} → Pw (λ M M' → R M M' × Sc.WS Op₁ sig₁ k M) {n} as as' → Pw R as as' × Sc.WS-args Op₁ sig₁ k as
  unzipˡ [] = [] , tt
  unzipˡ ((r , w) ∷ rs) = (r ∷ proj₁ (unzipˡ rs)) , w , proj₂ (unzipˡ rs)

{- the operands of a tuple, each with the property P -}
infixr 5 _∷_
data Each {Op : Set} {sig : Op → List Sig} (P : ABT Op sig → Set) : ∀ {n} → Args Op sig (replicate n ■) → Set where
  [] : Each P nil
  _∷_ : ∀ {n M} {as : Args Op sig (replicate n ■)} → P M → Each P as → Each P (cons (ast M) as)

module _ {Op : Set} {sig : Op → List Sig} where

  {- a tuple has as many components as its operands -}
  has-length-args : ∀ {n} (as : Args Op sig (replicate n ■)) → has-length n (args→list as) ≡ true
  has-length-args {zero} nil = refl
  has-length-args {suc n} (cons (ast M) as) = has-length-args as

  {- a component of a tuple -}
  each-proj : ∀ {P : ABT Op sig → Set} {n m} (i : Fin n) {as : Args Op sig (replicate m ■)} {V}
    → Each P as → proj i (args→list as) ≡ just V → P V
  each-proj zero [] ()
  each-proj (suc i) [] ()
  each-proj {n = suc n} zero {cons (ast M) as} (p ∷ ps) e with has-length n (args→list as)
  each-proj zero (p ∷ ps) refl | true = p
  each-proj zero (p ∷ ps) () | false
  each-proj (suc i) (p ∷ ps) e = each-proj i ps e

{- the operands of tuples, the first and then the rest, when each language's
   red-args is red-cons (cons-eq: by refl) and the target's values reduce
   to val -}
module _ {Op₁ Op₂ : Set} {sig₁ : Op₁ → List Sig} {sig₂ : Op₂ → List Sig}
  {redT : ABT Op₂ sig₂ → Red (ABT Op₂ sig₂)} {Val : ABT Op₂ sig₂ → Set} {R : ABT Op₁ sig₁ → ABT Op₂ sig₂ → Set}
  (redT* : ∀ {n} → Args Op₂ sig₂ (replicate n ■) → Red (Args Op₂ sig₂ (replicate n ■)))
  (cons-eq : ∀ {n} X (as : Args Op₂ sig₂ (replicate n ■)) → redT* (cons (ast X) as) ≡ red-cons X as (redT X) (redT* as))
  (val-red : ∀ {V} → Val V → redT V ≡ val) where

  ans-cons : ∀ {n M M' r r'} {as : Args Op₁ sig₁ (replicate n ■)} {as'} → Pw R as as'
    → Ans redT Val R M r M' → Ans redT* (Each Val) (Pw R) as r' as'
    → Ans redT* (Each Val) (Pw R) (cons (ast M) as) (red-cons M as r r') (cons (ast M') as')
  ans-cons rs a as = ans-in (frame _ (λ X → cons-eq X _)) (_∷ rs) a
    λ v m → ans-in (frame {g = λ Xs → cons (ast _) Xs} _ (λ Xs → trans (cons-eq _ Xs) (val-in (val-red v)))) (m ∷_) as
      λ vs ms → val ε (v ∷ vs) (m ∷ ms)

{- the operands of a context h are reduced left to right: in a frame,
   once those before them are values -}
module _ {Op : Set} {sig : Op → List Sig} (red : ABT Op sig → Red (ABT Op sig)) (Val : ABT Op sig → Set) where

  LR : ∀ {n} → (Args Op sig (replicate n ■) → ABT Op sig) → Set
  LR {zero} h = ⊤
  LR {suc n} h = (∀ Ms → Frame red red (λ X → h (cons (ast X) Ms))) × (∀ {V} → Val V → LR (λ Ms → h (cons (ast V) Ms)))


{- a context of one operand -}
lr1 : ∀ {Op sig} {red : ABT Op sig → Red (ABT Op sig)} {Val} (h : Args Op sig (replicate 1 ■) → ABT Op sig) (κ : ABT Op sig → Red (ABT Op sig))
  → (∀ X → red (h (cons (ast X) nil)) ≡ step-in (λ Y → h (cons (ast Y) nil)) (red X) (κ X)) → LR red Val h
lr1 h κ e = (λ { nil → frame κ e }) , λ _ → tt

{- the context of all the operands -}
lr-args : ∀ {Op sig} {red : ABT Op sig → Red (ABT Op sig)} {Val}
  (red* : ∀ {n} → Args Op sig (replicate n ■) → Red (Args Op sig (replicate n ■)))
  → (∀ {n} X (as : Args Op sig (replicate n ■)) → red* (cons (ast X) as) ≡ red-cons X as (red X) (red* as))
  → (∀ {V} → Val V → red V ≡ val) → ∀ {n} {G : Args Op sig (replicate n ■) → ABT Op sig} → Frame red* red G → LR red Val G
lr-args red* ce vr {zero} F = tt
lr-args red* ce vr {suc n} F =
  (λ Ms → frame-∘ (frame _ (λ X → ce X Ms)) F) , λ v → lr-args red* ce vr (frame-∘ (frame _ (λ Xs → trans (ce _ Xs) (val-in (vr v)))) F)

{- what a substitution may map a variable to: a variable, or a value, for
   a property Value of terms that substitution keeps -}
module VarOrValue {Op : Set} {sig : Op → List Sig} (Value : ABT Op sig → Set)
  (value-sub : ∀ σ {V} → Value V → Value (Sb.sub Op sig σ V)) where
  open Sb Op sig using (sub; sub-args; exts; extend; ids; _•_; rename-sub)
  open Sc Op sig using (WS; WS-args)

  data VV : ABT Op sig → Set where
    vv-val : ∀ {V} → Value V → VV V
    vv-var : ∀ x → VV (` x)

  vv-sub : ∀ {σ F} → (∀ x → VV (σ x)) → VV F → VV (sub σ F)
  vv-sub h (vv-val v) = vv-val (value-sub _ v)
  vv-sub h (vv-var x) = h x

  vvs-sub : ∀ {σ n} {Fs : Args Op sig (replicate n ■)} → (∀ x → VV (σ x)) → Each VV Fs → Each VV (sub-args σ Fs)
  vvs-sub h [] = []
  vvs-sub h (v ∷ vs) = vv-sub h v ∷ vvs-sub h vs

  vv-exts : ∀ {σ} → (∀ x → VV (σ x)) → ∀ x → VV (exts σ x)
  vv-exts h zero = vv-var 0
  vv-exts {σ} h (suc x) = subst VV (sym (rename-sub suc (σ x))) (vv-sub (λ y → vv-var (suc y)) (h x))

  {- one value, for variable 0 -}
  vv-one : ∀ {V} → Value V → ∀ x → VV ((V • ids) x)
  vv-one v zero = vv-val v
  vv-one v (suc x) = vv-var x

  {- the substitution of a closure's body: values, and then ρ -}
  vv-extend : ∀ {n} {Fs : Args Op sig (replicate n ■)} {ρ} → Each Value Fs → (∀ x → VV (ρ x)) → ∀ x → VV (extend Fs ρ x)
  vv-extend [] h = h
  vv-extend (v ∷ vs) h = vv-extend vs λ { zero → vv-val v ; (suc x) → h x }

  {- closed, a value -}
  vv-value : ∀ {F} → VV F → WS 0 F → Value F
  vv-value (vv-val v) _ = v
  vv-value (vv-var x) ()

  vvs-values : ∀ {n} {Fs : Args Op sig (replicate n ■)} → Each VV Fs → WS-args 0 Fs → Each Value Fs
  vvs-values [] _ = []
  vvs-values (v ∷ vs) (w , ws) = vv-value v w ∷ vvs-values vs ws

{- Answers of a machine that ignore the index ------------------------------------}

module _ {S₁ : Set} {L : Machine} {R : S₁ → State L → Set} where

  {- target steps first -}
  pre : ∀ {a s s'} → Step L s s' → Answers≺ L (λ _ → R) 0 a s' → Answers≺ L (λ _ → R) 0 a s
  pre st (stops fin) = runs (plus st ε) fin
  pre st (steps (plus s σ) m) = steps {j = 0} (plus st (s ◅ σ)) m
  pre st (runs (plus s σ) fin) = runs (plus st (s ◅ σ)) fin
  pre st (stutters () m)

  pre⋆ : ∀ {a s t} → Star L s t → Answers≺ L (λ _ → R) 0 a t → Answers≺ L (λ _ → R) 0 a s
  pre⋆ ε a = a
  pre⋆ (st ◅ σ) a = pre st (pre⋆ σ a)

  any-i : ∀ {i a s} → Answers≺ L (λ _ → R) 0 a s → Answers≺ L (λ _ → R) i a s
  any-i (stops fin) = stops fin
  any-i (steps π m) = steps {j = 0} π m
  any-i (runs π fin) = runs π fin
  any-i (stutters () m)

{- The end theorem -------------------------------------------------------------}

module _ {A B : Set} {obs₁ : A → Obs} {red₁ : A → Red A} {obs₂ : B → Obs} {red₂ : B → Red B}
  {Val : B → Set} (val-red : ∀ {V} → Val V → red₂ V ≡ val)
  (R : A → B → Set) (sim : ∀ {M M'} → R M M' → Ans red₂ Val R M (red₁ M) M')
  (obs-R : ∀ {V V'} → R V V' → red₁ V ≡ val → Val V' → obs₁ V ≡ obs₂ V') where

  private
    module _ (P : B) where
      L₂ = reduction obs₂ red₂ P

      star : ∀ {X Y} → Star* red₂ X Y → Star L₂ X Y
      star ε = ε
      star (s ◅ σ) = cong (toNext (obs₂ _)) s ◅ star σ

      finish : ∀ {i X Y o} → Star* red₂ X Y → Final L₂ Y o → Answers≺ L₂ (λ _ → R) i (stop o) X
      finish ε fin = stops fin
      finish (s ◅ σ) fin = runs (plus (cong (toNext (obs₂ _)) s) (star σ)) fin

      answer : ∀ {i M M' r} → red₁ M ≡ r → Ans red₂ Val R M r M'
        → Answers≺ L₂ (λ _ → R) i (toNext (obs₁ M) r) M'
      answer e (val σ v m) rewrite obs-R m e v = finish σ (cong (toNext (obs₂ _)) (val-red v))
      answer e (error σ w) = finish σ (cong (toNext (obs₂ _)) w)
      answer e (to (plus s σ) m) = steps {j = 0} (plus (cong (toNext (obs₂ _)) s) (star σ)) m

  red-fsim : ∀ {M M'} → R M M' → FSim (reduction obs₁ red₁ M) (reduction obs₂ red₂ M')
  red-fsim {M' = P} m = record { match = λ _ → R ; init = 0 , m ; sim = λ m → answer P refl (sim m) }

  red-equivalent : ∀ {M M'} → R M M' → Equivalent (reduction obs₁ red₁ M) (reduction obs₂ red₂ M')
  red-equivalent m = equivalent (red-fsim m)
