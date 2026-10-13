{-

  Correctness of the remove-complex-operands pass (Clos5 → Clos5,
  Compiler/RCO.agda) by a forward simulation of the Clos5 machine by
  itself (see the design note in Semantics/CEK/Smallstep.agda).

  Values contain no code (a code pointer is a number), so the two
  machines compute the same values; the source runs with the table ds
  and the target with map rco ds, and global (map rco ds) k is rco of
  global ds k. Environments differ: the target's has the values of the
  lets in front, so a source term M in ρ₁ is related to the target term
  rename r (rco M) in ρ₂ when ρ₂ ‼ r x ≡ ρ₁ ‼ x for every x (Ren).

  A construct (app, pair, fst, ..., tuple, case, prim; its Kind) with
  operands M₁ … Mₙ becomes a chain of lets for the complex operands and
  then the construct on atoms. The source evaluates the operands in
  order, through its frames (Frame K vs Ms: the values vs so far, newest
  first, and the operands Ms still to come). The target's remaining code
  is described by Pend, one constructor per operand:

  * p-let: a complex operand; the target evaluates it under a letK frame
    in lock step with the source (the frame relation pend);
  * p-atom: an atom; the source evaluates it (two steps) while the target
    waits at the next let (wait-eval and wait-ret, with a decreasing
    index), since an atom is evaluated without effect;
  * p-done: no operands left; the target runs the construct on its atoms,
    which have the source's values, up to the same final frame (fin).

  When the last operand returns its value, the target runs ahead to that
  final frame (retT, as in DelaySim), so that both machines take the
  construct's own step (a call, a projection, ...) together and go wrong
  together.

  Precondition: the program is well scoped (Scoped: main is closed and each
  definition uses only its two parameters). An unbound atom goes wrong in
  the source before a later complex operand runs, but in the target only
  after it; e.g. app (x, M, 0) with x unbound goes wrong, while
  let y = M in app (x, y, 0) diverges when M does. The compiler produces
  well-scoped programs (compile-scoped, Compiler/PipelineScope.agda).

-}

module proof.Correctness.CEK.RCOSim where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos5
open import Language.Mon using (Atom; var; lit; ref; atom-rename)
open import Compiler.RCO
open import proof.Framework.Syntax.Rename Op sig
  using (ext; rename; rename-args; rename-fuse; rename-fuse-args; rename-id; rename-id-args)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Language.Prim using (Prim)
open import proof.Framework.ListUtil
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Next; next; stop; Step; Plus; plus; Star; ε; _◅_; plus-star; plus→star; step⁺; next?-same)
open import proof.Semantics.CEK.Simulation
  using (FSim; Answers≺; stops; steps; stutters; answers≺; answers-at; steps₁≺; Equivalent; equivalent; equiv-trans)
import Semantics.CEK.Clos5 as T
import Semantics.CEK.ISWIM as S
open import Compiler.Pipeline using (compile; compile-mon)
open import proof.Compiler.EncloseScope using (Closed)
open import proof.Correctness.CEK.CompilerSim using (compile-correct)
open import proof.Compiler.PipelineScope using (Scoped; compile-scoped)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; map; reverse; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any.Properties using (reverse⁻)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; +-suc; +-identityʳ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Environments and atoms -------------------------------------------------------}

{- the renaming r takes each variable of ρ₁ to one of ρ₂ with the same value -}
open import proof.Framework.Syntax.EnvRel Op sig using (Ren; ren-ext)

{- the atom A evaluates to a in ρ, in one step, with any table -}
record Ev (A : AST) (ρ : T.Env) (a : T.Val) : Set where
  constructor mk-ev
  field ev : ∀ ds κ → T.step ds (T.eval A ρ κ) ≡ next (T.ret a κ)
open Ev

{- an atom in scope has a value -}
ev-ws : ∀ {M ρ} → Atom M → WS (length ρ) M → Σ[ a ∈ T.Val ] Ev M ρ a
ev-ws {ρ = ρ} (var x) w =
  proj₁ (‼-< ρ x w) , mk-ev λ ds κ → cong (λ m → T.ret? m κ) (proj₂ (‼-< ρ x w))
ev-ws (lit B n) w = T.const B n , mk-ev λ ds κ → refl
ev-ws (ref n) w = T.code n , mk-ev λ ds κ → refl

{- an atom keeps its value under the lets that rco puts after it -}
ev-shift : ∀ {M ρ ρ' h k g a} → Atom M → (∀ x → ρ' ‼ h (k + g x) ≡ ρ ‼ x) → Ev M ρ a
  → Ev (rename h (rename (k +_) (rename g M))) ρ' a
ev-shift (var x) H e = mk-ev λ ds κ → trans (cong (λ m → T.ret? m κ) (H x)) (ev e ds κ)
ev-shift (lit B n) H (mk-ev e) = mk-ev e
ev-shift (ref n) H (mk-ev e) = mk-ev e

{- atoms As evaluated in order, after the values vs, give the values vs' -}
data AtomsEv (ρ : T.Env) : ∀ {m} → Args (replicate m ■) → List T.Val → List T.Val → Set where
  [] : ∀ {vs} → AtomsEv ρ Nil vs vs
  _∷_ : ∀ {m A a vs vs'} {As : Args (replicate m ■)} → Ev A ρ a → AtomsEv ρ As (a ∷ vs) vs'
    → AtomsEv ρ (A ,, As) vs vs'

{- The constructs, and the source frames for their operands ----------------------}

data Kind : ℕ → Set where
  kapp : Kind 3
  kpair : Kind 2
  kfst ksnd kinl kinr : Kind 1
  kget : ∀ {n} → Fin n → Kind 1
  ktup : ∀ n → Kind (suc n)
  kprim : Prim → Kind 2
  kcase : AST → AST → Kind 1   {- with its branches -}

build : ∀ {n} → Kind n → Args (replicate n ■) → AST
build kapp As = app ⦅ As ⦆
build kpair As = pair-op ⦅ As ⦆
build kfst As = fst-op ⦅ As ⦆
build ksnd As = snd-op ⦅ As ⦆
build kinl As = inl-op ⦅ As ⦆
build kinr As = inr-op ⦅ As ⦆
build (kget i) As = get i ⦅ As ⦆
build (ktup n) As = tuple (suc n) ⦅ As ⦆
build (kprim p) As = prim p ⦅ As ⦆
build (kcase M N) (L ,, Nil) = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆

{- what rco puts under k lets, on the atoms As -}
tb : ∀ {n} → Kind n → ℕ → Args (replicate n ■) → AST
tb (kcase M N) k As = case-on (rco M) (rco N) k As
tb K k As = build K As

Plain : ∀ {n} → Kind n → Set
Plain (kcase _ _) = ⊥
Plain _ = ⊤

{- κ' is the frame of K after the values vs, with the operands Ms to come -}
data Frame : ∀ {n} → Kind n → List T.Val → List AST → T.Env → T.Cont → T.Cont → Set where
  fAppF : ∀ {M N ρ κ} → Frame kapp [] (M ∷ N ∷ []) ρ κ (T.appF M N ρ κ)
  fAppE : ∀ {f N ρ κ} → Frame kapp (f ∷ []) (N ∷ []) ρ κ (T.appE f N ρ κ)
  fAppA : ∀ {e f ρ κ} → Frame kapp (e ∷ f ∷ []) [] ρ κ (T.appA f e κ)
  fPairL : ∀ {M ρ κ} → Frame kpair [] (M ∷ []) ρ κ (T.pairL M ρ κ)
  fPairR : ∀ {v ρ κ} → Frame kpair (v ∷ []) [] ρ κ (T.pairR v κ)
  fFst : ∀ {ρ κ} → Frame kfst [] [] ρ κ (T.fstK κ)
  fSnd : ∀ {ρ κ} → Frame ksnd [] [] ρ κ (T.sndK κ)
  fInl : ∀ {ρ κ} → Frame kinl [] [] ρ κ (T.inlK κ)
  fInr : ∀ {ρ κ} → Frame kinr [] [] ρ κ (T.inrK κ)
  fGet : ∀ {n} {i : Fin n} {ρ κ} → Frame (kget i) [] [] ρ κ (T.getK i κ)
  fTup : ∀ {n vs Ms ρ κ} → Frame (ktup n) vs Ms ρ κ (T.tupK vs Ms ρ κ)
  fPrimL : ∀ {p M ρ κ} → Frame (kprim p) [] (M ∷ []) ρ κ (T.primL p M ρ κ)
  fPrimR : ∀ {p v ρ κ} → Frame (kprim p) (v ∷ []) [] ρ κ (T.primR p v κ)
  fCase : ∀ {M N ρ κ} → Frame (kcase M N) [] [] ρ κ (T.caseK M N ρ κ)

start : ∀ {n} ds (K : Kind (suc n)) A (As : Args (replicate n ■)) ρ κ
  → Σ[ κ' ∈ T.Cont ] Frame K [] (args→list As) ρ κ κ'
      × T.step ds (T.eval (build K (A ,, As)) ρ κ) ≡ next (T.eval A ρ κ')
start ds kapp A (M ,, N ,, Nil) ρ κ = _ , fAppF , refl
start ds kpair A (M ,, Nil) ρ κ = _ , fPairL , refl
start ds kfst A Nil ρ κ = _ , fFst , refl
start ds ksnd A Nil ρ κ = _ , fSnd , refl
start ds kinl A Nil ρ κ = _ , fInl , refl
start ds kinr A Nil ρ κ = _ , fInr , refl
start ds (kget i) A Nil ρ κ = _ , fGet , refl
start ds (ktup n) A As ρ κ = _ , fTup , refl
start ds (kprim p) A (M ,, Nil) ρ κ = _ , fPrimL , refl
start ds (kcase M N) A Nil ρ κ = _ , fCase , refl

step-frame : ∀ ds {n} {K : Kind n} {vs M Ms ρ κ κ'} → Frame K vs (M ∷ Ms) ρ κ κ' → ∀ v
  → Σ[ κ'' ∈ T.Cont ] Frame K (v ∷ vs) Ms ρ κ κ'' × T.step ds (T.ret v κ') ≡ next (T.eval M ρ κ'')
step-frame ds fAppF v = _ , fAppE , refl
step-frame ds fAppE v = _ , fAppA , refl
step-frame ds fPairL v = _ , fPairR , refl
step-frame ds fTup v = _ , fTup , refl
step-frame ds fPrimL v = _ , fPrimR , refl

{- the target's final frame for K₂ relates to the source's for K₁: the
   same, or for case, branches compiled by rco under a renaming -}
data KRel : ∀ {n} → Kind n → Kind n → T.Env → T.Env → Set where
  plain : ∀ {n} {K : Kind n} {ρ₁ ρ₂} → Plain K → KRel K K ρ₁ ρ₂
  case : ∀ {M N M' N' h ρ₁ ρ₂} → M' ≡ rename h (rco M) → N' ≡ rename h (rco N)
    → (∀ v → Ren h (v ∷ ρ₁) (v ∷ ρ₂)) → WS (suc (length ρ₁)) M → WS (suc (length ρ₁)) N
    → KRel (kcase M N) (kcase M' N') ρ₁ ρ₂

{- The let chains of rco ---------------------------------------------------------}

lift-keep : ∀ {n} (f : ℕ → Args (replicate (suc n) ■) → AST) M Ms → Atom M
  → lift f (M ,, Ms) ≡ lift (λ k As → f k (rename (k +_) M ,, As)) Ms
lift-keep f M Ms a with atom? M
... | yes _ = refl
... | no na = ⊥-elim (na a)

lift-let : ∀ {n} (f : ℕ → Args (replicate (suc n) ■) → AST) M Ms → (Atom M → ⊥)
  → lift f (M ,, Ms)
    ≡ let-op ⦅ M ,, ⟩ lift (λ k As → f (suc k) (` k ,, As)) (rename-args suc Ms) ,, Nil ⦆
lift-let f M Ms na with atom? M
... | yes a = ⊥-elim (na a)
... | no _ = refl

rco-atom : ∀ {M} → Atom M → rco M ≡ M
rco-atom (var x) = refl
rco-atom (lit B n) = refl
rco-atom (ref n) = refl

lets-na : ∀ g bs N → (Atom (rename g N) → ⊥) → Atom (rename g (lets bs N)) → ⊥
lets-na g [] N na = na
lets-na g (M ∷ bs) N na ()

lift-na : ∀ {n} g (f : ℕ → Args (replicate n ■) → AST) Ms
  → (∀ k As → Atom (rename g (f k As)) → ⊥) → Atom (rename g (lift f Ms)) → ⊥
lift-na g f Ms na = lets-na g _ _ (na _ _)

{- rco makes an atom only of an atom -}
atom-rco : ∀ M g → Atom (rename g (rco M)) → Atom M
atom-rco (` x) g a = var x
atom-rco (fun-ref n ⦅ Nil ⦆) g a = ref n
atom-rco (lit B n ⦅ Nil ⦆) g a = lit B n
atom-rco (app ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → app ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (pair-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → pair-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (fst-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → fst-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (snd-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → snd-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (tuple n ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → tuple n ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (get i ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → get i ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (inl-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → inl-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (inr-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → inr-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) g a =
  ⊥-elim (lift-na g (case-on (rco M) (rco N)) (rco L ,, Nil) (λ { k (A ,, Nil) () }) a)
atom-rco (prim p ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → prim p ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) g ()

{- Indices: an upper bound on the source steps while the target waits -----------}

ix : AST → ℕ
ixs : ∀ {bs} → Args bs → ℕ
ix (` x) = 0
ix (op ⦅ args ⦆) = suc (ixs args)
ixs nil = 0
ixs (cons a args) = suc (suc (ixs args))

dl : List AST → ℕ
dl [] = 0
dl (_ ∷ Ms) = suc (suc (dl Ms))

dl-ixs : ∀ {n} (As : Args (replicate n ■)) → dl (args→list As) ≡ ixs As
dl-ixs {zero} Nil = refl
dl-ixs {suc n} (A ,, As) = cong (λ z → suc (suc z)) (dl-ixs As)

{- The table ----------------------------------------------------------------------}

global-map : ∀ ds k → global (map rco ds) k ≡ mmap rco (global ds k)
global-map ds = reverse-map-‼ rco ds

global-all : ∀ {P : AST → Set} {ds} → All P ds → ∀ k {N} → global ds k ≡ just N → P N
global-all {ds = ds} ps k eq = All.lookup ps (reverse⁻ (‼-any (reverse ds) k eq))

{- The simulation, for a program with table ds whose definitions are scoped -------}

module Sim (ds : List AST) (M₀ : AST) (wds : All (WS 2) ds) where

  L₂ = T.sem (rco-program (program ds M₀))

  infix 4 _≈k_

  mutual
    data _≈k_ : T.Cont → T.Cont → Set where
      halt : T.halt ≈k T.halt
      letK : ∀ {N h ρ₁ ρ₂ κ₁ κ₂} → (∀ v → Ren h (v ∷ ρ₁) (v ∷ ρ₂)) → WS (suc (length ρ₁)) N
        → κ₁ ≈k κ₂ → T.letK N ρ₁ κ₁ ≈k T.letK (rename h (rco N)) ρ₂ κ₂
      {- the source waits for an operand, the target for a let-bound one -}
      pend : ∀ {n} {K : Kind n} {vs Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂} → Frame K vs Ms ρ₁ κ₁ κ₁'
        → (∀ w → Pend K ρ₁ κ₁ κ₂ (w ∷ vs) Ms Q (w ∷ ρ₂)) → κ₁' ≈k T.letK Q ρ₂ κ₂
      {- both wait for the last operand of the construct -}
      fin : ∀ {n} {K₁ K₂ : Kind n} {vs ρ₁ ρ₂ κ₁ κ₂ κ₁' κ₂'} → Frame K₁ vs [] ρ₁ κ₁ κ₁'
        → Frame K₂ vs [] ρ₂ κ₂ κ₂' → KRel K₁ K₂ ρ₁ ρ₂ → κ₁ ≈k κ₂ → κ₁' ≈k κ₂'

    {- the target code Q in ρ₂ finishes the construct K of the source in ρ₁,
       after the values vs and with the operands Ms to come -}
    data Pend {n} (K : Kind n) (ρ₁ : T.Env) (κ₁ κ₂ : T.Cont)
      : List T.Val → List AST → AST → T.Env → Set where
      p-let : ∀ {vs M Ms Q Q' h ρ₂} → Q ≡ let-op ⦅ rename h (rco M) ,, ⟩ Q' ,, Nil ⦆
        → Ren h ρ₁ ρ₂ → WS (length ρ₁) M
        → (∀ w → Pend K ρ₁ κ₁ κ₂ (w ∷ vs) Ms Q' (w ∷ ρ₂)) → Pend K ρ₁ κ₁ κ₂ vs (M ∷ Ms) Q ρ₂
      p-atom : ∀ {vs A a Ms Q ρ₂} → Ev A ρ₁ a → Pend K ρ₁ κ₁ κ₂ (a ∷ vs) Ms Q ρ₂
        → Pend K ρ₁ κ₁ κ₂ vs (A ∷ Ms) Q ρ₂
      p-done : ∀ {K₂ : Kind n} {v vs Q ρ₂ ρ₂' κ₂'} → Plus L₂ (T.eval Q ρ₂ κ₂) (T.ret v κ₂')
        → Frame K₂ vs [] ρ₂' κ₂ κ₂' → KRel K K₂ ρ₁ ρ₂' → κ₁ ≈k κ₂
        → Pend K ρ₁ κ₁ κ₂ (v ∷ vs) [] Q ρ₂

  {- the target state related to returning v: past the last let, the target
     has run ahead to the final frame -}
  retP : ∀ {n} {K : Kind n} {ρ₁ κ₁ κ₂ vs Ms Q ρ₂} → T.State → Pend K ρ₁ κ₁ κ₂ vs Ms Q ρ₂ → T.State
  retP s (p-done {v = v} {κ₂' = κ₂'} _ _ _ _) = T.ret v κ₂'
  retP s _ = s

  retT : ∀ {κ₁ κ₂} → T.Val → κ₁ ≈k κ₂ → T.State
  retT v (pend {Q = Q} {ρ₂ = ρ₂} {κ₂ = κ₂} sf f) = retP (T.ret v (T.letK Q ρ₂ κ₂)) (f v)
  retT {κ₂ = κ₂} v _ = T.ret v κ₂

  data Match : ℕ → T.State → T.State → Set where
    eval~ : ∀ {M M' r ρ₁ ρ₂ κ₁ κ₂} → M' ≡ rename r (rco M) → Ren r ρ₁ ρ₂ → WS (length ρ₁) M
      → κ₁ ≈k κ₂ → Match (ix M) (T.eval M ρ₁ κ₁) (T.eval M' ρ₂ κ₂)
    ret~ : ∀ {v κ₁ κ₂} (k : κ₁ ≈k κ₂) → Match 0 (T.ret v κ₁) (retT v k)
    {- the source evaluates an atom operand while the target waits -}
    wait-eval : ∀ {n} {K : Kind n} {vs A a Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂} → Frame K vs Ms ρ₁ κ₁ κ₁'
      → Ev A ρ₁ a → Pend K ρ₁ κ₁ κ₂ (a ∷ vs) Ms Q ρ₂
      → Match (suc (suc (dl Ms))) (T.eval A ρ₁ κ₁') (T.eval Q ρ₂ κ₂)
    wait-ret : ∀ {n} {K : Kind n} {vs a M Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂} → Frame K vs (M ∷ Ms) ρ₁ κ₁ κ₁'
      → Pend K ρ₁ κ₁ κ₂ (a ∷ vs) (M ∷ Ms) Q ρ₂
      → Match (suc (dl (M ∷ Ms))) (T.ret a κ₁') (T.eval Q ρ₂ κ₂)

  reach-p : ∀ {n} {K : Kind n} {ρ₁ κ₁ κ₂ v vs Ms Q ρ₂} (p : Pend K ρ₁ κ₁ κ₂ (v ∷ vs) Ms Q (v ∷ ρ₂))
    → Star L₂ (T.ret v (T.letK Q ρ₂ κ₂)) (retP (T.ret v (T.letK Q ρ₂ κ₂)) p)
  reach-p (p-done π _ _ _) = refl ◅ plus→star π
  reach-p (p-let _ _ _ _) = ε
  reach-p (p-atom _ _) = ε

  ret-reach : ∀ {κ₁ κ₂} (k : κ₁ ≈k κ₂) v → Star L₂ (T.ret v κ₂) (retT v k)
  ret-reach (pend sf f) v = reach-p (f v)
  ret-reach halt v = ε
  ret-reach (letK _ _ _) v = ε
  ret-reach (fin _ _ _ _) v = ε

  ret?-ans : ∀ mv {i κ₁ κ₂ s₂} (k : κ₁ ≈k κ₂) → T.step (map rco ds) s₂ ≡ T.ret? mv κ₂
    → Answers≺ L₂ Match i (T.ret? mv κ₁) s₂
  ret?-ans mv k eq = answers≺ (next?-same (λ v → _ , ret-reach k v , ret~ k) eq)

  {- the source goes on to the operand M; the target is at Q, or has just
     stepped to Q (step-go) -}
  wait-go : ∀ {n} {K : Kind n} {vs M Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂ i} → Frame K vs Ms ρ₁ κ₁ κ₁'
    → Pend K ρ₁ κ₁ κ₂ vs (M ∷ Ms) Q ρ₂ → suc (suc (dl Ms)) < i
    → Answers≺ L₂ Match i (next (T.eval M ρ₁ κ₁')) (T.eval Q ρ₂ κ₂)
  wait-go sf (p-let refl rn w f) lt = steps₁≺ refl (eval~ refl rn w (pend sf f))
  wait-go sf (p-atom ev p) lt = stutters lt (wait-eval sf ev p)

  step-go : ∀ {n} {K : Kind n} {vs M Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂ i s₂} → Step L₂ s₂ (T.eval Q ρ₂ κ₂)
    → Frame K vs Ms ρ₁ κ₁ κ₁' → Pend K ρ₁ κ₁ κ₂ vs (M ∷ Ms) Q ρ₂
    → Answers≺ L₂ Match i (next (T.eval M ρ₁ κ₁')) s₂
  step-go st sf (p-let refl rn w f) = steps (plus st (refl ◅ ε)) (eval~ refl rn w (pend sf f))
  step-go st sf (p-atom ev p) = steps₁≺ st (wait-eval sf ev p)

  {- a call -}
  call-ans : ∀ m mN {w e κ₁ κ₂ i} → global ds m ≡ mN → κ₁ ≈k κ₂
    → Answers≺ L₂ Match i (T.call mN w e κ₁) (T.ret w (T.appA (T.code m) e κ₂))
  call-ans m (just N) {w} {e} {κ₂ = κ₂} eq k =
    steps₁≺ (cong (λ x → T.call x w e κ₂) (trans (global-map ds m) (cong (mmap rco) eq)))
          (eval~ (sym (rename-id (rco N))) (λ x → refl) (global-all wds m eq) k)
  call-ans m nothing {w} {e} {κ₂ = κ₂} eq k =
    stops (cong (λ x → T.call x w e κ₂) (trans (global-map ds m) (cong (mmap rco) eq)))

  {- the construct's own step, on the same values -}
  fin-sim : ∀ {n} {K₁ K₂ : Kind n} {vs ρ₁ ρ₂ κ₁ κ₂ κ₁' κ₂'} → KRel K₁ K₂ ρ₁ ρ₂
    → Frame K₁ vs [] ρ₁ κ₁ κ₁' → Frame K₂ vs [] ρ₂ κ₂ κ₂' → κ₁ ≈k κ₂
    → ∀ v {i} → Answers≺ L₂ Match i (T.step ds (T.ret v κ₁')) (T.ret v κ₂')
  fin-sim _ (fAppA {f = T.code m}) fAppA k w = call-ans m (global ds m) refl k
  fin-sim _ (fAppA {f = T.pair _ _}) fAppA k w = stops refl
  fin-sim _ (fAppA {f = T.const _ _}) fAppA k w = stops refl
  fin-sim _ (fAppA {f = T.tup _}) fAppA k w = stops refl
  fin-sim _ (fAppA {f = T.inl _}) fAppA k w = stops refl
  fin-sim _ (fAppA {f = T.inr _}) fAppA k w = stops refl
  fin-sim _ fPairR fPairR k w = ret?-ans (just _) k refl
  fin-sim _ fFst fFst k (T.pair a b) = ret?-ans (just a) k refl
  fin-sim _ fFst fFst k (T.code _) = stops refl
  fin-sim _ fFst fFst k (T.const _ _) = stops refl
  fin-sim _ fFst fFst k (T.tup _) = stops refl
  fin-sim _ fFst fFst k (T.inl _) = stops refl
  fin-sim _ fFst fFst k (T.inr _) = stops refl
  fin-sim _ fSnd fSnd k (T.pair a b) = ret?-ans (just b) k refl
  fin-sim _ fSnd fSnd k (T.code _) = stops refl
  fin-sim _ fSnd fSnd k (T.const _ _) = stops refl
  fin-sim _ fSnd fSnd k (T.tup _) = stops refl
  fin-sim _ fSnd fSnd k (T.inl _) = stops refl
  fin-sim _ fSnd fSnd k (T.inr _) = stops refl
  fin-sim _ fInl fInl k v = ret?-ans (just (T.inl v)) k refl
  fin-sim _ fInr fInr k v = ret?-ans (just (T.inr v)) k refl
  fin-sim (plain _) (fGet {i = i}) fGet k (T.tup vs) = ret?-ans (proj i vs) k refl
  fin-sim _ fGet fGet k (T.code _) = stops refl
  fin-sim _ fGet fGet k (T.pair _ _) = stops refl
  fin-sim _ fGet fGet k (T.const _ _) = stops refl
  fin-sim _ fGet fGet k (T.inl _) = stops refl
  fin-sim _ fGet fGet k (T.inr _) = stops refl
  fin-sim (plain _) fTup fTup k v = ret?-ans (just _) k refl
  fin-sim (plain _) (fPrimR {p} {u}) fPrimR k v = ret?-ans (T.prim? p u v) k refl
  fin-sim (plain p) fCase fCase k v = ⊥-elim p
  fin-sim (case eM eN hr wM wN) fCase fCase k (T.inl u) = steps₁≺ refl (eval~ eM (hr u) wM k)
  fin-sim (case eM eN hr wM wN) fCase fCase k (T.inr u) = steps₁≺ refl (eval~ eN (hr u) wN k)
  fin-sim (case _ _ _ _ _) fCase fCase k (T.code _) = stops refl
  fin-sim (case _ _ _ _ _) fCase fCase k (T.pair _ _) = stops refl
  fin-sim (case _ _ _ _ _) fCase fCase k (T.const _ _) = stops refl
  fin-sim (case _ _ _ _ _) fCase fCase k (T.tup _) = stops refl

  {- running the construct on its atoms, up to its final frame -}
  run-atoms : ∀ {n} {K : Kind n} {vs A a m ρ κ κ'} {As : Args (replicate m ■)} {vs'}
    → Frame K vs (args→list As) ρ κ κ' → Ev A ρ a → AtomsEv ρ As (a ∷ vs) vs'
    → Σ[ v ∈ T.Val ] Σ[ vs₀ ∈ List T.Val ] Σ[ κ'' ∈ T.Cont ]
        vs' ≡ v ∷ vs₀ × Frame K vs₀ [] ρ κ κ'' × Plus L₂ (T.eval A ρ κ') (T.ret v κ'')
  run-atoms {a = a} {κ' = κ'} sf e [] = a , _ , κ' , refl , sf , step⁺ (ev e _ κ')
  run-atoms {a = a} {κ' = κ'} sf e (evB ∷ at) with step-frame (map rco ds) sf a
  ... | _ , sf' , eq with run-atoms sf' evB at
  ...   | v , vs₀ , κ'' , e' , sf'' , π = v , vs₀ , κ'' , e' , sf'' , plus (ev e _ κ') (eq ◅ plus→star π)

  done-run : ∀ {n} {K : Kind (suc n)} {ρ₁ κ₁ κ₂} (K' : Kind (suc n)) (As : Args (replicate (suc n) ■))
    {ρ' vs'} → AtomsEv ρ' As [] vs' → KRel K K' ρ₁ ρ' → κ₁ ≈k κ₂
    → Pend K ρ₁ κ₁ κ₂ vs' [] (build K' As) ρ'
  done-run {κ₂ = κ₂} K' (A ,, As) {ρ'} (ev ∷ at) kr k with start (map rco ds) K' A As ρ' κ₂
  ... | _ , sf , eq with run-atoms sf ev at
  ...   | v , vs₀ , κ'' , refl , sf' , π = p-done (plus eq (plus→star π)) sf' kr k

  {- what rco puts under the lets, f k As, finishes the construct, for every
     k lets and atoms As with the values to come -}
  record Inv {n} (K : Kind (suc n)) (ρ₁ : T.Env) (κ₁ κ₂ : T.Cont) {m}
    (f : ℕ → Args (replicate m ■) → AST) (r : ℕ → ℕ) (ρ₂ : T.Env) (vs : List T.Val) : Set where
    constructor mk-inv
    field
      inv : ∀ k h ρ' As vs' → (∀ y → ρ' ‼ h (k + y) ≡ ρ₂ ‼ r y)
        → AtomsEv ρ' (rename-args h As) vs vs' → Pend K ρ₁ κ₁ κ₂ vs' [] (rename h (f k As)) ρ'
  open Inv

  inv-plain : ∀ {n} (K : Kind (suc n)) {ρ₁ κ₁ κ₂ r ρ₂} → Plain K → κ₁ ≈k κ₂
    → Inv K ρ₁ κ₁ κ₂ (tb K) r ρ₂ []
  inv-plain kapp p k = mk-inv λ _ h _ As _ _ at → done-run kapp (rename-args h As) at (plain p) k
  inv-plain kpair p k = mk-inv λ _ h _ As _ _ at → done-run kpair (rename-args h As) at (plain p) k
  inv-plain kfst p k = mk-inv λ _ h _ As _ _ at → done-run kfst (rename-args h As) at (plain p) k
  inv-plain ksnd p k = mk-inv λ _ h _ As _ _ at → done-run ksnd (rename-args h As) at (plain p) k
  inv-plain kinl p k = mk-inv λ _ h _ As _ _ at → done-run kinl (rename-args h As) at (plain p) k
  inv-plain kinr p k = mk-inv λ _ h _ As _ _ at → done-run kinr (rename-args h As) at (plain p) k
  inv-plain (kget i) p k = mk-inv λ _ h _ As _ _ at → done-run (kget i) (rename-args h As) at (plain p) k
  inv-plain (ktup n) p k = mk-inv λ _ h _ As _ _ at → done-run (ktup n) (rename-args h As) at (plain p) k
  inv-plain (kprim q) p k = mk-inv λ _ h _ As _ _ at → done-run (kprim q) (rename-args h As) at (plain p) k

  inv-case : ∀ {M N ρ₁ κ₁ κ₂ r ρ₂} → Ren r ρ₁ ρ₂ → WS (suc (length ρ₁)) M
    → WS (suc (length ρ₁)) N → κ₁ ≈k κ₂ → Inv (kcase M N) ρ₁ κ₁ κ₂ (tb (kcase M N)) r ρ₂ []
  inv-case {M} {N} {ρ₁} {r = r} {ρ₂} rn wM wN k = mk-inv λ { j h ρ' (L ,, Nil) vs' H at →
    done-run (kcase _ _) (rename h L ,, Nil) at
      (case (rename-fuse (ext h) (ext (j +_)) (rco M)) (rename-fuse (ext h) (ext (j +_)) (rco N))
            (hr j h ρ' H) wM wN) k }
    where
    hr : ∀ j h ρ' → (∀ y → ρ' ‼ h (j + y) ≡ ρ₂ ‼ r y)
      → ∀ v → Ren (λ x → ext h (ext (j +_) x)) (v ∷ ρ₁) (v ∷ ρ')
    hr j h ρ' H v zero = refl
    hr j h ρ' H v (suc y) = trans (H y) (rn y)

  keep-inv : ∀ {n} {K : Kind (suc n)} {ρ₁ κ₁ κ₂ m M a r g ρ₂ vs}
    {f : ℕ → Args (replicate (suc m) ■) → AST} → Atom M → Ev M ρ₁ a
    → (∀ x → ρ₂ ‼ r (g x) ≡ ρ₁ ‼ x) → Inv K ρ₁ κ₁ κ₂ f r ρ₂ vs
    → Inv K ρ₁ κ₁ κ₂ (λ k As → f k (rename (k +_) (rename g M) ,, As)) r ρ₂ (a ∷ vs)
  keep-inv {M = M} {g = g} am e rn i = mk-inv λ k h ρ' As vs' H at →
    inv i k h ρ' (rename (k +_) (rename g M) ,, As) vs' H
      (ev-shift am (λ x → trans (H (g x)) (rn x)) e ∷ at)

  let-inv : ∀ {n} {K : Kind (suc n)} {ρ₁ κ₁ κ₂ m r ρ₂ vs} {f : ℕ → Args (replicate (suc m) ■) → AST}
    → Inv K ρ₁ κ₁ κ₂ f r ρ₂ vs
    → ∀ w → Inv K ρ₁ κ₁ κ₂ (λ k As → f (suc k) (` k ,, As)) (ext r) (w ∷ ρ₂) (w ∷ vs)
  let-inv {r = r} {ρ₂} i w = mk-inv λ k h ρ' As vs' H at →
    inv i (suc k) h ρ' (` k ,, As) vs' (H₀ k h ρ' H) (ev₀ k h ρ' H ∷ at)
    where
    H₀ : ∀ k h ρ' → (∀ y → ρ' ‼ h (k + y) ≡ (w ∷ ρ₂) ‼ ext r y)
      → ∀ y → ρ' ‼ h (suc k + y) ≡ ρ₂ ‼ r y
    H₀ k h ρ' H y = trans (cong (λ z → ρ' ‼ h z) (sym (+-suc k y))) (H (suc y))
    ev₀ : ∀ k h ρ' → (∀ y → ρ' ‼ h (k + y) ≡ (w ∷ ρ₂) ‼ ext r y) → Ev (` h k) ρ' w
    ev₀ k h ρ' H = mk-ev λ ds κ →
      cong (λ m → T.ret? m κ) (trans (cong (λ z → ρ' ‼ h z) (sym (+-identityʳ k))) (H 0))

  {- the let chain of rco, for the operands Ms renamed by g, follows the
     source's evaluation of Ms -}
  lift-pend : ∀ {n} {K : Kind (suc n)} {ρ₁ κ₁ κ₂ m} (Ms : Args (replicate m ■))
    (f : ℕ → Args (replicate m ■) → AST) {r g ρ₂ vs}
    → (∀ x → ρ₂ ‼ r (g x) ≡ ρ₁ ‼ x) → WS-args (length ρ₁) Ms → Inv K ρ₁ κ₁ κ₂ f r ρ₂ vs
    → Pend K ρ₁ κ₁ κ₂ vs (args→list Ms) (rename r (lift f (rename-args g (rco-args Ms)))) ρ₂
  lift-pend {m = zero} Nil f {r} {ρ₂ = ρ₂} {vs} rn _ i = inv i 0 r ρ₂ Nil vs (λ y → refl) []
  lift-pend {K = K} {ρ₁} {κ₁} {κ₂} {suc m} (M ,, Ms) f {r} {g} {ρ₂} {vs} rn (wM , wMs) i
    with atom? M
  ... | yes am =
    subst (λ X → Pend K ρ₁ κ₁ κ₂ vs (M ∷ args→list Ms) (rename r X) ρ₂)
      (sym (trans (cong (λ Y → lift f (rename g Y ,, rename-args g (rco-args Ms))) (rco-atom am))
                  (lift-keep f (rename g M) _ (atom-rename g am))))
      (p-atom (proj₂ (ev-ws am wM))
        (lift-pend Ms f' rn wMs (keep-inv am (proj₂ (ev-ws am wM)) rn i)))
    where f' = λ k As → f k (rename (k +_) (rename g M) ,, As)
  ... | no na =
    subst (λ X → Pend K ρ₁ κ₁ κ₂ vs (M ∷ args→list Ms) (rename r X) ρ₂)
      (sym (lift-let f (rename g (rco M)) _ (λ a → na (atom-rco M g a))))
      (p-let (cong (λ X → let-op ⦅ X ,, ⟩ Q' ,, Nil ⦆) (rename-fuse r g (rco M))) rn wM
        (λ w → subst (λ X → Pend K ρ₁ κ₁ κ₂ (w ∷ vs) (args→list Ms) (rename (ext r) (lift f'' X)) (w ∷ ρ₂))
                     (sym (rename-fuse-args suc g (rco-args Ms)))
                     (lift-pend Ms f'' {ext r} {λ x → suc (g x)} rn wMs (let-inv i w))))
    where f'' = λ k As → f (suc k) (` k ,, As)
          Q' = rename (ext r) (lift f'' (rename-args suc (rename-args g (rco-args Ms))))

  {- evaluating a construct -}
  lifted~ : ∀ {n} (K : Kind (suc n)) A (As : Args (replicate n ■)) {r ρ₁ ρ₂ κ₁ κ₂ i}
    → Ren r ρ₁ ρ₂ → WS-args (length ρ₁) (A ,, As) → Inv K ρ₁ κ₁ κ₂ (tb K) r ρ₂ []
    → suc (suc (dl (args→list As))) < i
    → Answers≺ L₂ Match i (T.step ds (T.eval (build K (A ,, As)) ρ₁ κ₁))
        (T.eval (rename r (lift (tb K) (rco-args (A ,, As)))) ρ₂ κ₂)
  lifted~ K A As {r} {ρ₁} {ρ₂} {κ₁} {κ₂} rn ws i lt with start ds K A As ρ₁ κ₁
  ... | _ , sf , eq = answers-at eq (wait-go sf p₀ lt)
    where
    p₀ = subst (λ X → Pend K ρ₁ κ₁ κ₂ [] (A ∷ args→list As) (rename r (lift (tb K) X)) ρ₂)
               (rename-id-args {f = λ x → x} (λ _ → refl) (rco-args (A ,, As)))
               (lift-pend (A ,, As) (tb K) {r} {λ x → x} rn ws i)

  {- the source returns v to the frame of a construct, the target to a let -}
  pend-ans : ∀ {n} {K : Kind n} {vs v Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂} → Frame K vs Ms ρ₁ κ₁ κ₁'
    → (p : Pend K ρ₁ κ₁ κ₂ (v ∷ vs) Ms Q (v ∷ ρ₂))
    → Answers≺ L₂ Match 0 (T.step ds (T.ret v κ₁')) (retP (T.ret v (T.letK Q ρ₂ κ₂)) p)
  pend-ans {v = v} sf (p-done π sf₂ kr k) = fin-sim kr sf sf₂ k v
  pend-ans {v = v} {κ₁' = κ₁'} sf p@(p-let _ _ _ _) with step-frame ds sf v
  ... | _ , sf' , eq = answers-at eq (step-go refl sf' p)
  pend-ans {v = v} {κ₁' = κ₁'} sf p@(p-atom _ _) with step-frame ds sf v
  ... | _ , sf' , eq = answers-at eq (step-go refl sf' p)

  {- the source has evaluated an atom operand -}
  wait-ans : ∀ {n} {K : Kind n} {vs a Ms ρ₁ κ₁ κ₁' Q ρ₂ κ₂} → Frame K vs Ms ρ₁ κ₁ κ₁'
    → Pend K ρ₁ κ₁ κ₂ (a ∷ vs) Ms Q ρ₂
    → Answers≺ L₂ Match (suc (suc (dl Ms))) (next (T.ret a κ₁')) (T.eval Q ρ₂ κ₂)
  wait-ans sf (p-done π sf₂ kr k) = steps π (ret~ (fin sf sf₂ kr k))
  wait-ans sf p@(p-let _ _ _ _) = stutters (n<1+n _) (wait-ret sf p)
  wait-ans sf p@(p-atom _ _) = stutters (n<1+n _) (wait-ret sf p)

  sim : ∀ {i s₁ s₂} → Match i s₁ s₂ → Answers≺ L₂ Match i (T.step ds s₁) s₂
  sim (eval~ {M = ` x} {ρ₁ = ρ₁} {κ₂ = κ₂} refl rn w k) =
    ret?-ans (ρ₁ ‼ x) k (cong (λ m → T.ret? m κ₂) (rn x))
  sim (eval~ {M = fun-ref m ⦅ Nil ⦆} refl rn w k) = ret?-ans (just (T.code m)) k refl
  sim (eval~ {M = lit B n ⦅ Nil ⦆} refl rn w k) = ret?-ans (just (T.const B n)) k refl
  sim (eval~ {M = app ⦅ A ,, M ,, N ,, Nil ⦆} refl rn w k) =
    lifted~ kapp A (M ,, N ,, Nil) rn w (inv-plain kapp tt k) (n<1+n _)
  sim (eval~ {M = pair-op ⦅ A ,, M ,, Nil ⦆} refl rn w k) =
    lifted~ kpair A (M ,, Nil) rn w (inv-plain kpair tt k) (n<1+n _)
  sim (eval~ {M = fst-op ⦅ A ,, Nil ⦆} refl rn w k) = lifted~ kfst A Nil rn w (inv-plain kfst tt k) (n<1+n _)
  sim (eval~ {M = snd-op ⦅ A ,, Nil ⦆} refl rn w k) = lifted~ ksnd A Nil rn w (inv-plain ksnd tt k) (n<1+n _)
  sim (eval~ {M = inl-op ⦅ A ,, Nil ⦆} refl rn w k) = lifted~ kinl A Nil rn w (inv-plain kinl tt k) (n<1+n _)
  sim (eval~ {M = inr-op ⦅ A ,, Nil ⦆} refl rn w k) = lifted~ kinr A Nil rn w (inv-plain kinr tt k) (n<1+n _)
  sim (eval~ {M = get i ⦅ A ,, Nil ⦆} refl rn w k) =
    lifted~ (kget i) A Nil rn w (inv-plain (kget i) tt k) (n<1+n _)
  sim (eval~ {M = tuple zero ⦅ Nil ⦆} refl rn w k) = ret?-ans (just (T.tup [])) k refl
  sim (eval~ {M = tuple (suc n) ⦅ A ,, As ⦆} refl rn w k) =
    lifted~ (ktup n) A As rn w (inv-plain (ktup n) tt k)
      (subst (λ z → suc (suc z) < suc (suc (suc (ixs As)))) (sym (dl-ixs As)) (n<1+n _))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} refl rn (wL , wM , wN , _) k) =
    lifted~ (kcase M N) L Nil rn (wL , tt) (inv-case rn wM wN k) (s≤s (s≤s (s≤s z≤n)))
  sim (eval~ {M = prim p ⦅ A ,, M ,, Nil ⦆} refl rn w k) =
    lifted~ (kprim p) A (M ,, Nil) rn w (inv-plain (kprim p) tt k) (n<1+n _)
  sim (eval~ {M = let-op ⦅ M ,, ⟩ N ,, Nil ⦆} refl rn (wM , wN , _) k) =
    steps₁≺ refl (eval~ refl rn wM (letK (λ v → ren-ext v rn) wN k))
  sim (ret~ halt) = stops refl
  sim (ret~ (letK hr w k)) = steps₁≺ refl (eval~ refl (hr _) w k)
  sim (ret~ {v = v} (pend sf f)) = pend-ans sf (f v)
  sim (ret~ {v = v} (fin sf₁ sf₂ kr k)) = fin-sim kr sf₁ sf₂ k v
  sim (wait-eval {A = A} {ρ₁ = ρ₁} {κ₁' = κ₁'} sf e p) = answers-at (ev e ds κ₁') (wait-ans sf p)
  sim (wait-ret {a = a} {κ₁' = κ₁'} sf p) with step-frame ds sf a
  ... | _ , sf' , eq = answers-at eq (wait-go sf' p (n<1+n _))

{- The end theorem -----------------------------------------------------------------}

rco-fsim : ∀ P → Scoped P → FSim (T.sem P) (T.sem (rco-program P))
rco-fsim (program ds M) (wds , wM) = record
  { match = Match
  ; init = _ , eval~ (sym (rename-id (rco M))) (λ x → refl) wM halt
  ; sim = sim }
  where open Sim ds M wds

rco-correct : ∀ P → Scoped P → Equivalent (T.sem P) (T.sem (rco-program P))
rco-correct P s = equivalent (rco-fsim P s)

{- The whole compiler, into monadic normal form --------------------------------}

compile-mon-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile-mon M))
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct (compile M) (compile-scoped M c))
