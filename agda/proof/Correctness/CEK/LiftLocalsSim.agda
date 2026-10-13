{-

  Correctness of the lift-locals pass (monadic Clos5 → Imp,
  Compiler/LiftLocals.agda) by a forward simulation of the Clos5 machine
  by the Imp machine (see the design note in Semantics/CEK/Smallstep.agda).

  The machines run in lock step, both evaluating the operands of a
  construct through continuation frames, and compute the same values
  (the Imp machine's are Clos5's); the only extra target steps are the
  returns from calls (callK), which the target takes as soon as the
  source returns a value (pop).

  The environment ρ of the source is laid out in the frame φ of the
  target, at depth d = length ρ: variable x is in slot d - 1 - x, so
  φ = ρ ʳ++ σ (ρ reversed, then the slots σ above it), and φ has the n
  slots of its body (Fr n ρ φ). So a variable in scope reads its value,
  and one out of scope reads slot n, beyond the frame, and goes wrong as
  in the source. A term at depth d with h nested binders has d + h ≤ n,
  so the let or case at depth d finds slot d in σ and assigns it, which
  gives the frame (v ∷ ρ) ʳ++ σ' of the depth d + 1.

  A continuation of the target needs only a frame that starts with the
  environment its frames were made in: Kont n ρ κ₁ κ₂ when κ₂ continues as
  κ₁ given any frame Fr n ρ φ. As the code at depth d writes only slots
  d and above, a continuation for ρ is one for v ∷ ρ (weak). A call
  continues in a fresh frame, under callK with the caller's frame (call).

  There is no precondition.

-}

module proof.Correctness.CEK.LiftLocalsSim where

open import Language.Clos5 using (AST; program; Args; ■)
import Language.Clos5 as L5
import Language.Imp as Imp
open import Language.Mon
open import Compiler.LiftLocals
open import proof.Framework.ListUtil using (_‼_; ‼-≥; ‼-++; args→list; proj)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Machine; next; plus; Star; ε; _◅_; Answers; stops; steps)
open import proof.Semantics.CEK.Simulation
  using (Equivalent; equivalent; plus-simulation; equiv-trans)
import Semantics.CEK.Clos5 as C
import Semantics.CEK.Imp as I
import Semantics.CEK.ISWIM as S
open import Compiler.Pipeline using (compile; compile-mon; compile-imp)
open import Compiler.RCO using (rco-program-mon)
open import proof.Compiler.EncloseScope using (Closed)
open import proof.Correctness.CEK.RCOSim using (compile-mon-correct)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; reverse; replicate; _++_; _ʳ++_)
open import Data.List.Properties using (ʳ++-defn; length-ʳ++; length-reverse; length-replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing) renaming (map to mmap)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _⊔_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-monoʳ-≤; +-suc; +-identityʳ; m≤m⊔n; m≤n⊔m; m≤m+n; ≮⇒≥; <⇒≱)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- Frames ------------------------------------------------------------------------}

{- φ has n slots and starts with ρ, reversed -}
data Fr (n : ℕ) (ρ : C.Env) : I.Frame → Set where
  frame : ∀ σ → length (ρ ʳ++ σ) ≡ n → Fr n ρ (ρ ʳ++ σ)

‼-ʳ++ : ∀ (ρ : C.Env) {σ} x → x < length ρ → (ρ ʳ++ σ) ‼ (length ρ ∸ suc x) ≡ ρ ‼ x
‼-ʳ++ (v ∷ ρ) zero _ =
  subst₂ (λ φ k → φ ‼ k ≡ just v) (sym (ʳ++-defn ρ)) (length-reverse ρ) (‼-++ (reverse ρ))
‼-ʳ++ (v ∷ ρ) (suc x) (s≤s lt) = ‼-ʳ++ ρ x lt

{- a variable reads its value from its slot -}
look : ∀ {n ρ φ} → Fr n ρ φ → ∀ x → φ ‼ slot n (length ρ) x ≡ ρ ‼ x
look {n} {ρ} (frame σ len) x with x <? length ρ
... | yes lt = ‼-ʳ++ ρ x lt
... | no ¬lt = trans (‼-≥ (ρ ʳ++ σ) n (≤-reflexive len)) (sym (‼-≥ ρ x (≮⇒≥ ¬lt)))

upd-++ : ∀ (π : I.Frame) {t σ v} → (π ++ t ∷ σ) I.[ length π ]≔ v ≡ just (π ++ v ∷ σ)
upd-++ [] = refl
upd-++ (u ∷ π) = cong (mmap (u ∷_)) (upd-++ π)

{- assigning slot length ρ, below n, pushes the value on ρ -}
assign : ∀ {n ρ φ} v → Fr n ρ φ → length ρ < n
  → Σ[ φ' ∈ I.Frame ] φ I.[ length ρ ]≔ v ≡ just φ' × Fr n (v ∷ ρ) φ'
assign {ρ = ρ} v (frame [] len) lt =
  ⊥-elim (<⇒≱ lt (≤-reflexive (trans (sym len) (trans (length-ʳ++ ρ) (+-identityʳ _)))))
assign {ρ = ρ} v (frame (t ∷ σ) len) lt =
  ρ ʳ++ v ∷ σ , eq , frame σ (trans (length-ʳ++ ρ) (trans (sym (length-ʳ++ ρ)) len))
  where
  eq : (ρ ʳ++ t ∷ σ) I.[ length ρ ]≔ v ≡ just (ρ ʳ++ v ∷ σ)
  eq rewrite ʳ++-defn ρ {t ∷ σ} | ʳ++-defn ρ {v ∷ σ} | sym (length-reverse ρ) = upd-++ (reverse ρ)

fr-≤ : ∀ {n ρ φ} → Fr n ρ φ → length ρ + 0 ≤ n
fr-≤ {ρ = ρ} (frame σ len) =
  ≤-trans (+-monoʳ-≤ (length ρ) z≤n) (≤-reflexive (trans (sym (length-ʳ++ ρ)) len))

{- the frame sizes of nested terms -}
bnd : ∀ d {h h' n} → h ≤ h' → d + h' ≤ n → d + h ≤ n
bnd d le b = ≤-trans (+-monoʳ-≤ d le) b

sbnd : ∀ d h {n} → d + suc h ≤ n → suc d + h ≤ n
sbnd d h {n} = subst (_≤ n) (+-suc d h)

room : ∀ d h {n} → suc d + h ≤ n → d < n
room d h b = ≤-trans (s≤s (m≤m+n d h)) b

{- The table ---------------------------------------------------------------------}

Lifted : AST → Imp.Body → Set
Lifted N b = Σ[ m ∈ Mon N ] b ≡ lift-body 2 m

lifted : ∀ {ds} (ms : All Mon ds) → Pointwise Lifted ds (lift-defs ms)
lifted [] = []
lifted (m ∷ ms) = (m , refl) ∷ lifted ms

‼-pw : ∀ {xs ys} → Pointwise Lifted xs ys → ∀ k → M.Pointwise Lifted (xs ‼ k) (ys ‼ k)
‼-pw [] k = M.nothing
‼-pw (r ∷ rs) zero = M.just r
‼-pw (r ∷ rs) (suc k) = ‼-pw rs k

glob : ∀ {ds} (ms : All Mon ds) k → M.Pointwise Lifted (L5.global ds k) (Imp.global (lift-defs ms) k)
glob ms k = ‼-pw (reverse⁺ (lifted ms)) k

{- The simulation, for a program with table ds and main body n₀, e₀ ----------------}

module Sim {ds : List AST} (ms : All Mon ds) (n₀ : ℕ) (e₀ : Imp.Exp) where

  ds₂ = lift-defs ms
  L₂ = I.sem (Imp.program ds₂ (Imp.body n₀ e₀))

  private variable
    n n' : ℕ
    ρ ρ' : C.Env
    φ : I.Frame
    v w : C.Val
    B D N : AST
    κ₁ : C.Cont
    κ₂ : I.Cont

  mutual
    {- κ₂ continues as κ₁ given a frame of n slots that starts with ρ -}
    data Kont : ℕ → C.Env → C.Cont → I.Cont → Set where
      head : KontH n ρ κ₁ κ₂ → Kont n ρ κ₁ κ₂
      weak : Kont n ρ κ₁ κ₂ → Kont n (v ∷ ρ) κ₁ κ₂
      call : Kont n' ρ' κ₁ κ₂ → Fr n' ρ' φ → Kont n ρ κ₁ (I.callK φ κ₂)

    data KontH : ℕ → C.Env → C.Cont → I.Cont → Set where
      halt : KontH n ρ C.halt I.halt
      letK : (m : Mon N) → suc (length ρ) + height m ≤ n → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.letK N ρ κ₁) (I.assignK (length ρ) (lift n (suc (length ρ)) m) κ₂)
      caseK : (m₁ : Mon B) (m₂ : Mon D) → suc (length ρ) + (height m₁ ⊔ height m₂) ≤ n
        → Kont n ρ κ₁ κ₂ → KontH n ρ (C.caseK B D ρ κ₁)
            (I.caseK (length ρ) (lift n (suc (length ρ)) m₁) (lift n (suc (length ρ)) m₂) κ₂)
      appF : (b : Atom B) (c : Atom D) → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.appF B D ρ κ₁) (I.frm (I.appF (lift-atom n (length ρ) b) (lift-atom n (length ρ) c)) κ₂)
      appE : (c : Atom D) → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.appE v D ρ κ₁) (I.frm (I.appE v (lift-atom n (length ρ) c)) κ₂)
      appA : Kont n ρ κ₁ κ₂ → KontH n ρ (C.appA v w κ₁) (I.frm (I.appA v w) κ₂)
      pairL : (b : Atom B) → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.pairL B ρ κ₁) (I.frm (I.pairL (lift-atom n (length ρ) b)) κ₂)
      pairR : Kont n ρ κ₁ κ₂ → KontH n ρ (C.pairR v κ₁) (I.frm (I.pairR v) κ₂)
      fstK : Kont n ρ κ₁ κ₂ → KontH n ρ (C.fstK κ₁) (I.frm I.fstK κ₂)
      sndK : Kont n ρ κ₁ κ₂ → KontH n ρ (C.sndK κ₁) (I.frm I.sndK κ₂)
      tupK : ∀ {k vs} {As : Args (replicate k ■)} (as : Atoms As) → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.tupK vs (args→list As) ρ κ₁) (I.frm (I.tupK vs (lift-atoms n (length ρ) as)) κ₂)
      getK : ∀ {k} {i : Fin k} → Kont n ρ κ₁ κ₂ → KontH n ρ (C.getK i κ₁) (I.frm (I.getK i) κ₂)
      inlK : Kont n ρ κ₁ κ₂ → KontH n ρ (C.inlK κ₁) (I.frm I.inlK κ₂)
      inrK : Kont n ρ κ₁ κ₂ → KontH n ρ (C.inrK κ₁) (I.frm I.inrK κ₂)
      primL : ∀ {p} (b : Atom B) → Kont n ρ κ₁ κ₂
        → KontH n ρ (C.primL p B ρ κ₁) (I.frm (I.primL p (lift-atom n (length ρ) b)) κ₂)
      primR : ∀ {p} → Kont n ρ κ₁ κ₂ → KontH n ρ (C.primR p v κ₁) (I.frm (I.primR p v) κ₂)

  infix 4 _~_
  data _~_ : C.State → I.State → Set where
    eval~ : (m : Mon N) → length ρ + height m ≤ n → Fr n ρ φ → Kont n ρ κ₁ κ₂
      → C.eval N ρ κ₁ ~ I.eval (lift n (length ρ) m) φ κ₂
    ret~ : KontH n ρ κ₁ κ₂ → Fr n ρ φ → C.ret v κ₁ ~ I.ret v φ κ₂

  {- the target returns from calls -}
  pop : Kont n ρ κ₁ κ₂ → Fr n ρ φ → Σ[ s₂ ∈ I.State ] Star L₂ (I.ret v φ κ₂) s₂ × C.ret v κ₁ ~ s₂
  pop (head h) fr = _ , ε , ret~ h fr
  pop (weak {v = u} k) (frame σ len) = pop k (frame (u ∷ σ) len)
  pop (call k fr') fr with pop k fr'
  ... | s , σ , m = s , refl ◅ σ , m

  go : ∀ {s₁ s₂ s₂'} → I.step ds₂ s₂ ≡ next s₂' → s₁ ~ s₂' → Answers L₂ _~_ (next s₁) s₂
  go st m = steps (plus st ε) m

  ret-ans : ∀ {s₂} → I.step ds₂ s₂ ≡ next (I.ret v φ κ₂) → Kont n ρ κ₁ κ₂ → Fr n ρ φ
    → Answers L₂ _~_ (next (C.ret v κ₁)) s₂
  ret-ans st k fr with pop k fr
  ... | _ , σ , m = steps (plus st σ) m

  ret?-ans : ∀ {s₂} mv → I.step ds₂ s₂ ≡ I.ret? mv φ κ₂ → Kont n ρ κ₁ κ₂ → Fr n ρ φ
    → Answers L₂ _~_ (C.ret? mv κ₁) s₂
  ret?-ans (just v) st k fr = ret-ans st k fr
  ret?-ans nothing st k fr = stops st

  call-ans : ∀ {s₂ mN mb} → M.Pointwise Lifted mN mb → I.step ds₂ s₂ ≡ I.call mb v w φ κ₂
    → Kont n ρ κ₁ κ₂ → Fr n ρ φ → Answers L₂ _~_ (C.call mN w v κ₁) s₂
  call-ans (M.just (m , refl)) st k fr = go st
    (eval~ m ≤-refl (frame (I.zeros (height m)) (cong (2 +_) (length-replicate (height m)))) (call k fr))
  call-ans M.nothing st k fr = stops st

  tup-ans : ∀ {s₂ k vs} {As : Args (replicate k ■)} (as : Atoms As)
    → I.step ds₂ s₂ ≡ I.res ds₂ (I.tuple-next vs (lift-atoms n (length ρ) as)) φ κ₂
    → Kont n ρ κ₁ κ₂ → Fr n ρ φ → Answers L₂ _~_ (next (C.tuple-next vs (args→list As) ρ κ₁)) s₂
  tup-ans [] st k fr = ret-ans st k fr
  tup-ans (a ∷ as) st k fr = go st (eval~ (atom a) (fr-≤ fr) fr (head (tupK as k)))

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (C.step ds s₁) s₂
  sim (eval~ {ρ = ρ} {φ = φ} {κ₂ = κ₂} (atom (var x)) b fr k) =
    ret?-ans (ρ ‼ x) (cong (λ mv → I.ret? mv φ κ₂) (look fr x)) k fr
  sim (eval~ (atom (lit B j)) b fr k) = ret-ans refl k fr
  sim (eval~ (atom (ref j)) b fr k) = ret-ans refl k fr
  sim (eval~ (app (a ∷ c ∷ e ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (appF c e k)))
  sim (eval~ (pair (a ∷ c ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (pairL c k)))
  sim (eval~ (fst (a ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (fstK k)))
  sim (eval~ (snd (a ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (sndK k)))
  sim (eval~ (tuple as) b fr k) = tup-ans as refl k fr
  sim (eval~ (get (a ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (getK k)))
  sim (eval~ (inl (a ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (inlK k)))
  sim (eval~ (inr (a ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (inrK k)))
  sim (eval~ (prim (a ∷ c ∷ [])) b fr k) = go refl (eval~ (atom a) b fr (head (primL c k)))
  sim (eval~ {ρ = ρ} (case a m₁ m₂) b fr k) =
    go refl (eval~ (atom a) (bnd (length ρ) z≤n b) fr (head (caseK m₁ m₂ (sbnd (length ρ) _ b) k)))
  sim (eval~ {ρ = ρ} (let′ m₁ m₂) b fr k) =
    go refl (eval~ m₁ (bnd (length ρ) (m≤m⊔n (height m₁) (suc (height m₂))) b) fr
      (head (letK m₂ (sbnd (length ρ) (height m₂) (bnd (length ρ) (m≤n⊔m (height m₁) _) b)) k)))
  sim (ret~ halt fr) = stops refl
  sim (ret~ {ρ = ρ} {v = v} (letK m b k) fr) with assign v fr (room (length ρ) (height m) b)
  ... | _ , eq , fr' = go (cong (λ x → I.goto x _ _) eq) (eval~ m b fr' (weak k))
  sim (ret~ {ρ = ρ} {v = C.inl v} (caseK m₁ m₂ b k) fr) with assign v fr (room (length ρ) _ b)
  ... | _ , eq , fr' = go (cong (λ x → I.goto x _ _) eq)
    (eval~ m₁ (bnd (suc (length ρ)) (m≤m⊔n (height m₁) (height m₂)) b) fr' (weak k))
  sim (ret~ {ρ = ρ} {v = C.inr v} (caseK m₁ m₂ b k) fr) with assign v fr (room (length ρ) _ b)
  ... | _ , eq , fr' = go (cong (λ x → I.goto x _ _) eq)
    (eval~ m₂ (bnd (suc (length ρ)) (m≤n⊔m (height m₁) (height m₂)) b) fr' (weak k))
  sim (ret~ {v = C.code _} (caseK _ _ _ _) _) = stops refl
  sim (ret~ {v = C.pair _ _} (caseK _ _ _ _) _) = stops refl
  sim (ret~ {v = C.const _ _} (caseK _ _ _ _) _) = stops refl
  sim (ret~ {v = C.tup _} (caseK _ _ _ _) _) = stops refl
  sim (ret~ (appF c e k) fr) = go refl (eval~ (atom c) (fr-≤ fr) fr (head (appE e k)))
  sim (ret~ (appE e k) fr) = go refl (eval~ (atom e) (fr-≤ fr) fr (head (appA k)))
  sim (ret~ (appA {v = C.code j} k) fr) = call-ans (glob ms j) refl k fr
  sim (ret~ (appA {v = C.pair _ _} k) fr) = stops refl
  sim (ret~ (appA {v = C.const _ _} k) fr) = stops refl
  sim (ret~ (appA {v = C.tup _} k) fr) = stops refl
  sim (ret~ (appA {v = C.inl _} k) fr) = stops refl
  sim (ret~ (appA {v = C.inr _} k) fr) = stops refl
  sim (ret~ (pairL c k) fr) = go refl (eval~ (atom c) (fr-≤ fr) fr (head (pairR k)))
  sim (ret~ (pairR k) fr) = ret-ans refl k fr
  sim (ret~ {v = C.pair _ _} (fstK k) fr) = ret-ans refl k fr
  sim (ret~ {v = C.code _} (fstK k) fr) = stops refl
  sim (ret~ {v = C.const _ _} (fstK k) fr) = stops refl
  sim (ret~ {v = C.tup _} (fstK k) fr) = stops refl
  sim (ret~ {v = C.inl _} (fstK k) fr) = stops refl
  sim (ret~ {v = C.inr _} (fstK k) fr) = stops refl
  sim (ret~ {v = C.pair _ _} (sndK k) fr) = ret-ans refl k fr
  sim (ret~ {v = C.code _} (sndK k) fr) = stops refl
  sim (ret~ {v = C.const _ _} (sndK k) fr) = stops refl
  sim (ret~ {v = C.tup _} (sndK k) fr) = stops refl
  sim (ret~ {v = C.inl _} (sndK k) fr) = stops refl
  sim (ret~ {v = C.inr _} (sndK k) fr) = stops refl
  sim (ret~ (tupK as k) fr) = tup-ans as refl k fr
  sim (ret~ {v = C.tup vs} (getK {i = i} k) fr) = ret?-ans (proj i vs) refl k fr
  sim (ret~ {v = C.code _} (getK k) fr) = stops refl
  sim (ret~ {v = C.pair _ _} (getK k) fr) = stops refl
  sim (ret~ {v = C.const _ _} (getK k) fr) = stops refl
  sim (ret~ {v = C.inl _} (getK k) fr) = stops refl
  sim (ret~ {v = C.inr _} (getK k) fr) = stops refl
  sim (ret~ (inlK k) fr) = ret-ans refl k fr
  sim (ret~ (inrK k) fr) = ret-ans refl k fr
  sim (ret~ (primL c k) fr) = go refl (eval~ (atom c) (fr-≤ fr) fr (head (primR k)))
  sim (ret~ {v = w} (primR {v = u} {p = p} k) fr) = ret?-ans (C.prim? p u w) refl k fr

{- The end theorem ---------------------------------------------------------------}

lift-correct : ∀ P (mp : MonProgram P) → Equivalent (C.sem P) (I.sem (lift-program P mp))
lift-correct (program ds M) (ms , m) = equivalent (plus-simulation _~_
  (eval~ m ≤-refl (frame (I.zeros (height m)) (length-replicate (height m))) (head halt)) sim)
  where open Sim ms (height m) (lift (height m) 0 m)

{- The whole compiler, into Imp --------------------------------------------------}

compile-imp-correct : ∀ M → Closed M → Equivalent (S.sem M) (I.sem (compile-imp M))
compile-imp-correct M c =
  equiv-trans (compile-mon-correct M c) (lift-correct (compile-mon M) (rco-program-mon (compile M)))
