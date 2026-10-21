{-

  Correctness of the lift-locals pass (monadic Clos5 → Imp,
  Compiler/LiftLocals.agda) by a forward simulation of the Clos5
  reduction semantics by the Imp machine (see the design note in
  Semantics/Reduction/Smallstep.agda).

  The source substitutes values for variables; the target keeps them
  in the slots of its frame. A source term is C (sub σ M) for a monadic
  term M of the program and a substitution σ of values, in an evaluation
  context C, a stack of lets; the target runs lift M in a frame φ that
  holds the values of σ (Ag), with a continuation that does what C
  does (Kont): the let frames assign their slot and run their body, and
  the target also returns from calls (callK), which the source does not
  see. The values are related as data (_≈v_): Clos5's value terms and
  the machine's values.

  The source takes no step to evaluate an atom (a substituted variable is
  already a value) while the target takes two, and the target enters a
  let in a step of its own; these are matched with the next source step.
  As in the CEK proof, the frame φ is ρ reversed and then the free slots
  (Fr n ρ φ), and a variable out of scope is a variable in the source and
  a slot beyond the frame in the target, which error alike.

  There is no precondition.

-}

module Untyped.proof.Correctness.Reduction.LiftLocalsRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Untyped.Language.Clos5 using (AST; Args; ■; program; `_; _⦅_⦆; fun-ref; app; lit; pair-op; fst-op; snd-op;
  tuple; get; inl-op; inr-op; case-op; prim; let-op; cons; nil; ast; bind)
import Untyped.Language.Clos5 as L5
import Untyped.Language.Imp as Imp
open Imp using (simple; atm)
open import Untyped.Language.Mon
open import Untyped.Compiler.LiftLocals
open import Untyped.Compiler.Pipeline using (compile; compile-mon; compile-imp)
open import Untyped.Compiler.RCO using (rco-program-mon)
open import Untyped.proof.Compiler.EncloseScope using (Closed)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error using (Red; val; error; to; step-in; toNext; Frame; frame; frame-id; frame-∘; val-in; ret?; pre; pre⋆; any-i)
open import Framework.Smallstep Obs using (Machine; Next; next; stop; Star; ε; _◅_; Step)
open import proof.Framework.Smallstep Obs using (Plus; plus)
open import proof.Framework.Simulation Obs using (FSim; Answers≺; stops; steps; runs; stutters; equivalent; equiv-trans)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Untyped.proof.Semantics.Reduction.Clos5 as S
import Semantics.Reduction.ISWIM as ISWIMᵣ
import Untyped.Semantics.CEK.Imp as I
import Semantics.CEK.Values as Vl
open import Untyped.proof.Correctness.Reduction.RCORed using (compile-mon-correct)
open import proof.Framework.Syntax.Subst L5.Op L5.sig using (Subst; sub; sub-args; exts; ids; _•_; _[_]; sub-id; exts-[])
open import proof.Framework.ListUtil using (_‼_; ‼-≥; ‼-++; args→list; proj; proj-pw; ‼-pw)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; reverse; replicate; _++_; _ʳ++_)
open import Data.List.Properties using (ʳ++-defn; length-ʳ++; length-reverse; length-replicate; ++-identityʳ; unfold-reverse; ++-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _⊔_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-monoʳ-≤; +-suc; +-identityʳ; m≤m⊔n; m≤n⊔m; m≤m+n; ≮⇒≥; <⇒≱)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- Values ------------------------------------------------------------------------}

{- a Clos5 value term and a machine value -}
infix 4 _≈v_ _≈vs_
data _≈v_ : AST → I.Val → Set
data _≈vs_ : ∀ {n} → Args (replicate n ■) → List I.Val → Set
data _≈v_ where
  fun : ∀ {k} → fun-ref k ⦅ Nil ⦆ ≈v I.code k
  pair : ∀ {V W v w} → V ≈v v → W ≈v w → pair-op ⦅ V ,, W ,, Nil ⦆ ≈v I.pair v w
  lit : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈v I.const B k
  tuple : ∀ {n} {Vs : Args (replicate n ■)} {vs} → Vs ≈vs vs → tuple n ⦅ Vs ⦆ ≈v I.tup vs
  inl : ∀ {V v} → V ≈v v → inl-op ⦅ V ,, Nil ⦆ ≈v I.inl v
  inr : ∀ {V v} → V ≈v v → inr-op ⦅ V ,, Nil ⦆ ≈v I.inr v
data _≈vs_ where
  [] : Nil ≈vs []
  _∷_ : ∀ {n V v} {Vs : Args (replicate n ■)} {vs} → V ≈v v → Vs ≈vs vs → (V ,, Vs) ≈vs (v ∷ vs)

≈v-value : ∀ {V v} → V ≈v v → S.Value V
≈vs-values : ∀ {n} {Vs : Args (replicate n ■)} {vs} → Vs ≈vs vs → S.Values Vs
≈v-value fun = S.fun
≈v-value (pair r s) = S.pair (≈v-value r) (≈v-value s)
≈v-value lit = S.lit
≈v-value (tuple rs) = S.tuple (≈vs-values rs)
≈v-value (inl r) = S.inl (≈v-value r)
≈v-value (inr r) = S.inr (≈v-value r)
≈vs-values [] = S.[]
≈vs-values (r ∷ rs) = ≈v-value r S.∷ ≈vs-values rs

obs≈v : ∀ {V v} → V ≈v v → S.obs V ≡ I.obs v
obs≈vs : ∀ {n} {Vs : Args (replicate n ■)} {vs} → Vs ≈vs vs → S.obs-args Vs ≡ Vl.obs-list vs
obs≈v fun = refl
obs≈v (pair r s) = refl
obs≈v lit = refl
obs≈v (tuple rs) = cong o-tuple (obs≈vs rs)
obs≈v (inl r) = cong o-inl (obs≈v r)
obs≈v (inr r) = cong o-inr (obs≈v r)
obs≈vs [] = refl
obs≈vs (r ∷ rs) = cong₂′ (obs≈v r) (obs≈vs rs)
  where cong₂′ : ∀ {a b : Obs} {as bs} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
        cong₂′ refl refl = refl

out≈ : ∀ o → S.out o ≈v Vl.out o
out≈ (int n) = lit
out≈ (bool true) = inl (tuple [])
out≈ (bool false) = inr (tuple [])

≈vs-list : ∀ {n} {Vs : Args (replicate n ■)} {vs} → Vs ≈vs vs → Pointwise _≈v_ (args→list Vs) vs
≈vs-list [] = []
≈vs-list (r ∷ rs) = r ∷ ≈vs-list rs

{- an operand: a value, or a variable out of scope -}
data Lk (X : AST) (mv : Maybe I.Val) : Set where
  ok : ∀ {v} → X ≈v v → mv ≡ just v → Lk X mv
  unb : ∀ {y} → X ≡ ` y → mv ≡ nothing → Lk X mv

{- σ gives the values of ρ, and variables beyond it -}
Ag : Subst → List I.Val → Set
Ag σ ρ = ∀ x → Lk (σ x) (ρ ‼ x)

ag-ext : ∀ {σ ρ V v} → V ≈v v → Ag σ ρ → Ag (V • σ) (v ∷ ρ)
ag-ext r ag zero = ok r refl
ag-ext r ag (suc x) = ag x

{- Frames (as in the CEK proof) ---------------------------------------------------}

data Fr (n : ℕ) (ρ : List I.Val) : I.Frame → Set where
  frame : ∀ σ → length (ρ ʳ++ σ) ≡ n → Fr n ρ (ρ ʳ++ σ)

‼-ʳ++ : ∀ (ρ : List I.Val) {σ} x → x < length ρ → (ρ ʳ++ σ) ‼ (length ρ ∸ suc x) ≡ ρ ‼ x
‼-ʳ++ (v ∷ ρ) zero _ =
  subst₂ (λ φ k → φ ‼ k ≡ just v) (sym (ʳ++-defn ρ)) (length-reverse ρ) (‼-++ (reverse ρ))
‼-ʳ++ (v ∷ ρ) (suc x) (s≤s lt) = ‼-ʳ++ ρ x lt

look : ∀ {n ρ φ} → Fr n ρ φ → ∀ x → φ ‼ slot n (length ρ) x ≡ ρ ‼ x
look {n} {ρ} (frame σ len) x with x <? length ρ
... | yes lt = ‼-ʳ++ ρ x lt
... | no ¬lt = trans (‼-≥ (ρ ʳ++ σ) n (≤-reflexive len)) (sym (‼-≥ ρ x (≮⇒≥ ¬lt)))

upd-++ : ∀ (π : I.Frame) {t σ v} → (π ++ t ∷ σ) I.[ length π ]≔ v ≡ just (π ++ v ∷ σ)
upd-++ [] = refl
upd-++ (u ∷ π) = cong (mmap (u ∷_)) (upd-++ π)

assign : ∀ {n ρ φ} v → Fr n ρ φ → length ρ < n
  → Σ[ φ' ∈ I.Frame ] φ I.[ length ρ ]≔ v ≡ just φ' × Fr n (v ∷ ρ) φ'
assign {ρ = ρ} v (frame [] len) lt =
  ⊥-elim (<⇒≱ lt (≤-reflexive (trans (sym len) (trans (length-ʳ++ ρ) (+-identityʳ _)))))
assign {ρ = ρ} v (frame (t ∷ σ) len) lt =
  ρ ʳ++ v ∷ σ , eq , frame σ (trans (length-ʳ++ ρ) (trans (sym (length-ʳ++ ρ)) len))
  where
  eq : (ρ ʳ++ t ∷ σ) I.[ length ρ ]≔ v ≡ just (ρ ʳ++ v ∷ σ)
  eq rewrite ʳ++-defn ρ {t ∷ σ} | ʳ++-defn ρ {v ∷ σ} | sym (length-reverse ρ) = upd-++ (reverse ρ)

{- the frame sizes of nested terms -}
bnd : ∀ d {h h' n} → h ≤ h' → d + h' ≤ n → d + h ≤ n
bnd d le b = ≤-trans (+-monoʳ-≤ d le) b

sbnd : ∀ d h {n} → d + suc h ≤ n → suc d + h ≤ n
sbnd d h {n} = subst (_≤ n) (+-suc d h)

room : ∀ d h {n} → suc d + h ≤ n → d < n
room d h b = ≤-trans (s≤s (m≤m+n d h)) b

{- an atom, in the source and in the target -}
atm-lk : ∀ {σ n ρ φ A} → Ag σ ρ → Fr n ρ φ → (a : Atom A) → Lk (sub σ A) (I.atom φ (lift-atom n (length ρ) a))
atm-lk ag fr (var x) with ag x
... | ok r e = ok r (trans (look fr x) e)
... | unb e e' = unb e (trans (look fr x) e')
atm-lk ag fr (lit B k) = ok lit refl
atm-lk ag fr (ref k) = ok fun refl

{- The table ---------------------------------------------------------------------}

Lifted : AST → Imp.Body → Set
Lifted N b = Σ[ m ∈ Mon N ] b ≡ lift-body 2 m

glob : ∀ {ds} (ms : All Mon ds) k → M.Pointwise Lifted (L5.global ds k) (Imp.global (lift-defs ms) k)
glob ms k = ‼-pw (reverse⁺ (lifted ms)) k
  where
  lifted : ∀ {ds} (ms : All Mon ds) → Pointwise Lifted ds (lift-defs ms)
  lifted [] = []
  lifted (m ∷ ms) = (m , refl) ∷ lifted ms

{- The simulation, for a program with table ds and main body n₀, e₀ ----------------}

module Sim {ds : List AST} (ms : All Mon ds) (n₀ : ℕ) (e₀ : Imp.Exp) where

  ds₂ = lift-defs ms
  L₂ = I.sem (Imp.program ds₂ (Imp.body n₀ e₀))
  red = S.red ds

  {- the target continuation κ does what the source context C does, given
     a frame of n slots that starts with ρ -}
  data Kont : ℕ → List I.Val → (AST → AST) → I.Cont → Set where
    halt : ∀ {n ρ} → Kont n ρ (λ X → X) I.halt
    letK : ∀ {n ρ σ B C κ} (m : Mon B) → suc (length ρ) + height m ≤ n → Ag σ ρ → Kont n ρ C κ
      → Kont n ρ (λ X → C (let-op ⦅ X ,, ⟩ sub (exts σ) B ,, Nil ⦆))
                 (I.assignK (length ρ) (lift n (suc (length ρ)) m) κ)
    weak : ∀ {n ρ v C κ} → Kont n ρ C κ → Kont n (v ∷ ρ) C κ
    call : ∀ {n n' ρ ρ' φ C κ} → Kont n' ρ' C κ → Fr n' ρ' φ → Kont n ρ C (I.callK φ κ)

  {- C is a context of the source reduction -}
  kframe : ∀ {n ρ C κ} → Kont n ρ C κ → Frame red red C
  kframe halt = frame-id
  kframe (letK m b ag k) = frame-∘ (frame _ (λ _ → refl)) (kframe k)
  kframe (weak k) = kframe k
  kframe (call k fr) = kframe k

  infix 4 _~_
  data _~_ : AST → I.State → Set where
    eval~ : ∀ {M n ρ φ σ C κ} (m : Mon M) → length ρ + height m ≤ n → Fr n ρ φ → Ag σ ρ → Kont n ρ C κ
      → C (sub σ M) ~ I.eval (lift n (length ρ) m) φ κ
    ret~ : ∀ {V v n ρ φ C κ} → V ≈v v → Fr n ρ φ → Kont n ρ C κ → C V ~ I.ret v φ κ

  Ans : Next AST → I.State → Set
  Ans = Answers≺ L₂ (λ _ → _~_) 0

  {- the source's step of C X, given the reduction of X -}
  in-ctx : ∀ {n ρ C κ X r s} (k : Kont n ρ C κ) → red X ≡ r
    → Ans (toNext (S.obs (C X)) (step-in C r (Frame.κ (kframe k) X))) s → Ans (toNext (S.obs (C X)) (red (C X))) s
  in-ctx {X = X} k refl a = subst (λ z → Ans (toNext _ z) _) (sym (Frame.eq (kframe k) X)) a

  {- an operand of the source, in a context f with continuation k -}
  lk-step : ∀ {B : Set} {X mv} → Lk X mv → Red B → Red B
  lk-step (ok _ _) k = k
  lk-step (unb _ _) k = error

  opd : ∀ {B : Set} {f : AST → B} {k X mv} (l : Lk X mv) → step-in f (red X) k ≡ lk-step l k
  opd (ok r _) = val-in (S.value-red (≈v-value r))
  opd (unb refl _) = refl

  {- the target evaluates an operand -}
  tgt : ∀ {mv φ κ v} → mv ≡ just v → I.ret? mv φ κ ≡ next (I.ret v φ κ)
  tgt refl = refl

  tgt-error : ∀ {mv φ κ} → mv ≡ nothing → I.ret? mv φ κ ≡ stop o-error
  tgt-error refl = refl

  {- the target returns a value to κ, as the source's context C does -}
  ret-ans : ∀ {n ρ φ C κ V v} → V ≈v v → Fr n ρ φ → (k : Kont n ρ C κ)
    → Ans (toNext (S.obs (C V)) (Frame.κ (kframe k) V)) (I.ret v φ κ)
  ret-ans r fr halt = stops (cong stop (sym (obs≈v r)))
  ret-ans {ρ = ρ} {v = v} r fr (letK {σ = σ} {B} {C} m b ag k) with assign v fr (room (length ρ) (height m) b)
  ... | _ , eq , fr' =
    steps {j = 0} (plus (cong (λ x → I.goto x _ _) eq) ε)
          (subst (λ X → C X ~ _) (sym (exts-[] _ σ B)) (eval~ m b fr' (ag-ext r ag) (weak k)))
  ret-ans r (frame σ len) (weak {v = u} k) = ret-ans r (frame (u ∷ σ) len) k
  ret-ans r fr (call k fr') = pre refl (ret-ans r fr' k)

  lk-red : ∀ {X mv} (l : Lk X mv) → red X ≡ lk-step l val
  lk-red (ok r _) = S.value-red (≈v-value r)
  lk-red (unb refl _) = refl

  {- the operands of a tuple, in the source and the target -}
  data Ops (φ : I.Frame) : ∀ {m} → Args (replicate m ■) → List Imp.Atm → Set where
    [] : Ops φ Nil []
    _∷_ : ∀ {m X a} {Xs : Args (replicate m ■)} {as} → Lk X (I.atom φ a) → Ops φ Xs as → Ops φ (X ,, Xs) (a ∷ as)

  ops : ∀ {σ n ρ φ m} {As : Args (replicate m ■)} → Ag σ ρ → Fr n ρ φ → (as : Atoms As)
    → Ops φ (sub-args σ As) (lift-atoms n (length ρ) as)
  ops ag fr [] = []
  ops ag fr (a ∷ as) = atm-lk ag fr a ∷ ops ag fr as

  rev-∷ : ∀ (v : I.Val) acc vs → reverse (v ∷ acc) ++ vs ≡ reverse acc ++ v ∷ vs
  rev-∷ v acc vs = trans (cong (_++ vs) (unfold-reverse v acc)) (++-assoc (reverse acc) (v ∷ []) vs)

  {- either all are values, which the target collects after acc, or one is
     unbound, and both error -}
  tup-run : ∀ {φ κ m} {Xs : Args (replicate m ■)} {as} → Ops φ Xs as → ∀ acc {s}
    → I.step ds₂ s ≡ I.res ds₂ (I.tuple-next acc as) φ κ
    → (Σ[ vs ∈ List I.Val ] Xs ≈vs vs × S.red-args ds Xs ≡ val × Plus L₂ s (I.ret (I.tup (reverse acc ++ vs)) φ κ))
      ⊎ (S.red-args ds Xs ≡ error × Σ[ t ∈ I.State ] Star L₂ s t × I.step ds₂ t ≡ stop o-error)
  tup-run [] acc st =
    inj₁ ([] , [] , refl , plus (trans st (cong (λ vs → next (I.ret (I.tup vs) _ _)) (sym (++-identityʳ _)))) ε)
  tup-run {φ} {κ} (_∷_ {as = as} l@(ok {v} r e) os) acc st
    with tup-run os (v ∷ acc) {I.ret v φ (I.frm (I.tupK acc as) κ)} refl
  ... | inj₁ (vs , rs , ev , plus s σ) =
    inj₁ (_ , r ∷ rs , trans (opd l) (cong (λ x → step-in _ x val) ev)
         , plus st (tgt e ◅ subst (λ z → Star L₂ _ (I.ret (I.tup z) φ κ)) (rev-∷ v acc vs) (s ◅ σ)))
  ... | inj₂ (ev , t , σ , fin) = inj₂ (trans (opd l) (cong (λ x → step-in _ x val) ev) , t , st ◅ tgt e ◅ σ , fin)
  tup-run (l@(unb _ e) ∷ os) acc st = inj₂ (opd l , _ , st ◅ ε , tgt-error e)

  {- a projection or a primitive, once its operands are values -}
  ret?-ans : ∀ {n ρ φ C κ T mv mw s} {κT : Red AST} → M.Pointwise _≈v_ mv mw → Fr n ρ φ → Kont n ρ C κ
    → I.step ds₂ s ≡ I.ret? mw φ κ → Ans (toNext (S.obs (C T)) (step-in C (ret? mv) κT)) s
  ret?-ans (M.just r) fr k st = steps {j = 0} (plus st ε) (ret~ r fr k)
  ret?-ans M.nothing fr k st = stops st

  {- what a call does, once its operands are values -}
  call-ans : ∀ {n ρ φ C κ T X₁ X₂ X₃ v₁ v₂ v₃} {κT : Red AST} → X₁ ≈v v₁ → X₂ ≈v v₂ → X₃ ≈v v₃
    → Fr n ρ φ → Kont n ρ C κ
    → Ans (toNext (S.obs (C T)) (step-in C (S.call ds X₁ X₂ X₃) κT)) (I.ret v₃ φ (I.frm (I.appA v₁ v₂) κ))
  call-ans {φ = φ} {C} {κ} {T} {X₂ = X₂} {X₃} {v₂ = v₂} {v₃} {κT} (fun {k'}) r₂ r₃ fr k = call-pw (glob ms k') refl
    where
    call-pw : ∀ {mN mb s} → M.Pointwise Lifted mN mb → I.step ds₂ s ≡ I.call mb v₂ v₃ φ κ
      → Ans (toNext (S.obs (C T)) (step-in C (S.call? mN X₂ X₃) κT)) s
    call-pw (M.just (m , refl)) st =
      steps {j = 0} (plus st ε)
            (eval~ {ρ = _ ∷ _ ∷ []} m ≤-refl (frame (I.zeros (height m)) (cong (2 +_) (length-replicate (height m))))
                   (λ { zero → ok r₃ refl ; (suc zero) → ok r₂ refl ; (suc (suc x)) → unb refl refl }) (call k fr))
    call-pw M.nothing st = stops st
  call-ans (pair _ _) r₂ r₃ fr k = stops refl
  call-ans lit r₂ r₃ fr k = stops refl
  call-ans (tuple _) r₂ r₃ fr k = stops refl
  call-ans (inl _) r₂ r₃ fr k = stops refl
  call-ans (inr _) r₂ r₃ fr k = stops refl

  fst-ans : ∀ {n ρ φ C κ T X v} {κT : Red AST} → X ≈v v → Fr n ρ φ → Kont n ρ C κ
    → Ans (toNext (S.obs (C T)) (step-in C (S.fst? X) κT)) (I.ret v φ (I.frm I.fstK κ))
  fst-ans (pair r₁ r₂) fr k = steps {j = 0} (plus refl ε) (ret~ r₁ fr k)
  fst-ans fun fr k = stops refl
  fst-ans lit fr k = stops refl
  fst-ans (tuple _) fr k = stops refl
  fst-ans (inl _) fr k = stops refl
  fst-ans (inr _) fr k = stops refl

  snd-ans : ∀ {n ρ φ C κ T X v} {κT : Red AST} → X ≈v v → Fr n ρ φ → Kont n ρ C κ
    → Ans (toNext (S.obs (C T)) (step-in C (S.snd? X) κT)) (I.ret v φ (I.frm I.sndK κ))
  snd-ans (pair r₁ r₂) fr k = steps {j = 0} (plus refl ε) (ret~ r₂ fr k)
  snd-ans fun fr k = stops refl
  snd-ans lit fr k = stops refl
  snd-ans (tuple _) fr k = stops refl
  snd-ans (inl _) fr k = stops refl
  snd-ans (inr _) fr k = stops refl

  get-ans : ∀ {n ρ φ C κ T X v m} {i : Fin m} {κT : Red AST} → X ≈v v → Fr n ρ φ → Kont n ρ C κ
    → Ans (toNext (S.obs (C T)) (step-in C (S.get? i X) κT)) (I.ret v φ (I.frm (I.getK i) κ))
  get-ans {i = i} (tuple rs) fr k = ret?-ans (proj-pw {R = _≈v_} i (≈vs-list rs)) fr k refl
  get-ans fun fr k = stops refl
  get-ans (pair _ _) fr k = stops refl
  get-ans lit fr k = stops refl
  get-ans (inl _) fr k = stops refl
  get-ans (inr _) fr k = stops refl

  prim-ans : ∀ {n ρ φ C κ T X₁ X₂ v₁ v₂ p} {κT : Red AST} → X₁ ≈v v₁ → X₂ ≈v v₂ → Fr n ρ φ → Kont n ρ C κ
    → Ans (toNext (S.obs (C T)) (step-in C (S.prim? p X₁ X₂) κT)) (I.ret v₂ φ (I.frm (I.primR p v₁) κ))
  prim-ans {X₁ = X₁} {X₂} {p = p} r₁ r₂ fr k =
    ret?-ans (subst₂ (λ o₁ o₂ → M.Pointwise _≈v_ (mmap S.out (δ? p (S.obs X₁) (S.obs X₂))) (mmap Vl.out (δ? p o₁ o₂)))
                     (obs≈v r₁) (obs≈v r₂) (out-pw (δ? p (S.obs X₁) (S.obs X₂)))) fr k refl
    where out-pw : ∀ mo → M.Pointwise _≈v_ (mmap S.out mo) (mmap Vl.out mo)
          out-pw (just o) = M.just (out≈ o)
          out-pw nothing = M.nothing

  sim-eval : ∀ {M n ρ φ σ C κ} (m : Mon M) → length ρ + height m ≤ n → Fr n ρ φ → Ag σ ρ → (k : Kont n ρ C κ)
    → Ans (toNext (S.obs (C (sub σ M))) (red (C (sub σ M)))) (I.eval (lift n (length ρ) m) φ κ)
  sim-eval (atom a) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (lk-red l) (pre (tgt e) (ret-ans r fr k))
  ... | l@(unb _ e) = in-ctx k (lk-red l) (stops (tgt-error e))
  sim-eval (app (a ∷ c ∷ d ∷ [])) b fr ag k with atm-lk ag fr a | atm-lk ag fr c | atm-lk ag fr d
  ... | l₁@(ok r₁ e₁) | l₂@(ok r₂ e₂) | l₃@(ok r₃ e₃) =
    in-ctx k (trans (opd l₁) (trans (opd l₂) (opd l₃)))
      (pre refl (pre (tgt e₁) (pre refl (pre (tgt e₂) (pre refl (pre (tgt e₃) (call-ans r₁ r₂ r₃ fr k)))))))
  ... | l₁@(ok r₁ e₁) | l₂@(ok r₂ e₂) | l₃@(unb _ e₃) =
    in-ctx k (trans (opd l₁) (trans (opd l₂) (opd l₃)))
      (pre refl (pre (tgt e₁) (pre refl (pre (tgt e₂) (pre refl (stops (tgt-error e₃)))))))
  ... | l₁@(ok r₁ e₁) | l₂@(unb _ e₂) | _ =
    in-ctx k (trans (opd l₁) (opd l₂)) (pre refl (pre (tgt e₁) (pre refl (stops (tgt-error e₂)))))
  ... | l₁@(unb _ e₁) | _ | _ = in-ctx k (opd l₁) (pre refl (stops (tgt-error e₁)))
  sim-eval (pair (a ∷ c ∷ [])) b fr ag k with atm-lk ag fr a | atm-lk ag fr c
  ... | l₁@(ok r₁ e₁) | l₂@(ok r₂ e₂) =
    in-ctx k (trans (opd l₁) (opd l₂))
      (pre refl (pre (tgt e₁) (pre refl (pre (tgt e₂) (pre refl (ret-ans (pair r₁ r₂) fr k))))))
  ... | l₁@(ok r₁ e₁) | l₂@(unb _ e₂) =
    in-ctx k (trans (opd l₁) (opd l₂)) (pre refl (pre (tgt e₁) (pre refl (stops (tgt-error e₂)))))
  ... | l₁@(unb _ e₁) | _ = in-ctx k (opd l₁) (pre refl (stops (tgt-error e₁)))
  sim-eval (fst (a ∷ [])) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (fst-ans r fr k)))
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval (snd (a ∷ [])) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (snd-ans r fr k)))
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval (tuple as) b fr ag k with tup-run (ops ag fr as) [] refl
  ... | inj₁ (vs , rs , ev , plus s σ) =
    in-ctx k (cong (λ x → step-in _ x val) ev) (pre s (pre⋆ σ (ret-ans (tuple rs) fr k)))
  ... | inj₂ (ev , t , σ , fin) = in-ctx k (cong (λ x → step-in _ x val) ev) (pre⋆ σ (stops fin))
  sim-eval (get (a ∷ [])) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (get-ans r fr k)))
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval (inl (a ∷ [])) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (pre refl (ret-ans (inl r) fr k))))
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval (inr (a ∷ [])) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (pre refl (ret-ans (inr r) fr k))))
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval {n = n} {ρ} {φ} {σ} {C} {κ} (case {M = M₁} {N = M₂} a m₁ m₂) b fr ag k with atm-lk ag fr a
  ... | l@(ok r e) = in-ctx k (opd l) (pre refl (pre (tgt e) (case-ans r)))
    where
    b' = sbnd (length ρ) _ b
    case-ans : ∀ {X v} → X ≈v v
      → Ans (toNext (S.obs (C (case-op ⦅ X ,, ⟩ sub (exts σ) M₁ ,, ⟩ sub (exts σ) M₂ ,, Nil ⦆)))
                    (step-in C (S.case? X (sub (exts σ) M₁) (sub (exts σ) M₂))
                             (Frame.κ (kframe k) (case-op ⦅ X ,, ⟩ sub (exts σ) M₁ ,, ⟩ sub (exts σ) M₂ ,, Nil ⦆))))
            (I.ret v φ (I.caseK (length ρ) (lift n (suc (length ρ)) m₁) (lift n (suc (length ρ)) m₂) κ))
    case-ans {v = I.inl v₀} (inl r₀) with assign v₀ fr (room (length ρ) _ b')
    ... | _ , eq , fr' = steps {j = 0} (plus (cong (λ x → I.goto x _ _) eq) ε)
      (subst (λ Z → C Z ~ _) (sym (exts-[] _ σ M₁))
             (eval~ m₁ (bnd (suc (length ρ)) (m≤m⊔n (height m₁) (height m₂)) b') fr' (ag-ext r₀ ag) (weak k)))
    case-ans {v = I.inr v₀} (inr r₀) with assign v₀ fr (room (length ρ) _ b')
    ... | _ , eq , fr' = steps {j = 0} (plus (cong (λ x → I.goto x _ _) eq) ε)
      (subst (λ Z → C Z ~ _) (sym (exts-[] _ σ M₂))
             (eval~ m₂ (bnd (suc (length ρ)) (m≤n⊔m (height m₁) (height m₂)) b') fr' (ag-ext r₀ ag) (weak k)))
    case-ans fun = stops refl
    case-ans (pair _ _) = stops refl
    case-ans lit = stops refl
    case-ans (tuple _) = stops refl
  ... | l@(unb _ e) = in-ctx k (opd l) (pre refl (stops (tgt-error e)))
  sim-eval (prim {p} (a ∷ c ∷ [])) b fr ag k with atm-lk ag fr a | atm-lk ag fr c
  ... | l₁@(ok {v₁} r₁ e₁) | l₂@(ok {v₂} r₂ e₂) =
    in-ctx k (trans (opd l₁) (opd l₂))
      (pre refl (pre (tgt e₁) (pre refl (pre (tgt e₂) (prim-ans r₁ r₂ fr k)))))
  ... | l₁@(ok r₁ e₁) | l₂@(unb _ e₂) =
    in-ctx k (trans (opd l₁) (opd l₂)) (pre refl (pre (tgt e₁) (pre refl (stops (tgt-error e₂)))))
  ... | l₁@(unb _ e₁) | _ = in-ctx k (opd l₁) (pre refl (stops (tgt-error e₁)))
  sim-eval {ρ = ρ} (let′ m₁ m₂) b fr ag k =
    pre refl (sim-eval m₁ (bnd (length ρ) (m≤m⊔n (height m₁) (suc (height m₂))) b) fr ag
                (letK m₂ (sbnd (length ρ) (height m₂) (bnd (length ρ) (m≤n⊔m (height m₁) _) b)) ag k))

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Ans (toNext (S.obs s₁) (red s₁)) s₂
  sim (eval~ m b fr ag k) = sim-eval m b fr ag k
  sim (ret~ {V} r fr k) = in-ctx k (S.value-red (≈v-value r)) (ret-ans r fr k)

{- The end theorem ---------------------------------------------------------------}

lift-correct : ∀ P (mp : MonProgram P) → Equivalent (S.sem P) (I.sem (lift-program P mp))
lift-correct (program ds M) (ms , m) = equivalent fsim
  where
  open Sim ms (height m) (lift (height m) 0 m)
  fsim : FSim (S.sem (program ds M)) L₂
  fsim = record { match = λ _ → _~_
                ; init = 0 , subst (λ X → X ~ I.eval (lift (height m) 0 m) (I.zeros (height m)) I.halt) (sub-id M)
                           (eval~ {ρ = []} m ≤-refl (frame (I.zeros (height m)) (length-replicate (height m)))
                                  (λ x → unb refl refl) halt)
                ; sim = λ m → any-i (sim m) }

{- The whole compiler, into Imp --------------------------------------------------}

compile-imp-correct : ∀ M → Closed M → Equivalent (ISWIMᵣ.sem M) (I.sem (compile-imp M))
compile-imp-correct M c =
  equiv-trans (compile-mon-correct M c) (lift-correct (compile-mon M) (rco-program-mon (compile M)))
