{-

  Correctness of select instructions (CFG → X86, Compiler/Select.agda),
  clock for clock (see the design note in Clock.agda): the pass keeps
  every call, and in both interpreters only calls tick, so for every
  clock the two programs give the same result. There is no
  precondition.

  The relation is the identity on frames: the X86 frame is the CFG
  frame, and the registers are arbitrary. A block of X86 runs its
  instructions in continuation-passing style, so the instructions that
  select-simple r d puts in front of the rest of a block nest around it,
  and simple-ok says that they compute the value of r and store it in d,
  with any registers after (k v is what the rest computes from there).
  The atoms of r are read as in CFG (atm-ok, atoms-ok), except that a
  call reads its operator after its operands, which matters only when
  reading the operator goes wrong (wrong-ok). A block keeps its label,
  so the jumps agree (jump-ok), and a call runs the prologue and then
  the selected start of the callee in the frame CFG uses (call-pw).

-}

module proof.Correctness.Interp.SelectFuel where

open import Framework.Primitives using (Int)
open import Language.Imp as Imp using (var; lit; fun-ref)
open import Language.Prim using (sub; eq; int; bool)
open import Language.CFG as CFG using (return; seq; goto; case)
open import Language.X86 using (Block; Body; var; reg; rax; retq)
open import Compiler.Select
open import Compiler.Pipeline using (compile-cfg; compile-x86)
open import proof.Compiler.EncloseScope using (Closed)
open import Semantics.Observation using (o-const; δ?)
open import proof.Framework.ListUtil using (_‼_; ‼-pw)
open import proof.Semantics.Interp.Clock
open import Semantics.Interp.Clos5 using (Val; code; pair; const; tup; inl; inr; obs; out; first; second; project; prim?)
open import Semantics.Interp.Imp using (_[_]≔_; atom; atoms; eval-simple)
import Semantics.Interp.CFG as G
import Semantics.Interp.X86 as X
open X using (regs; arg; args; write; bool?)
import Semantics.Interp.ISWIM as ISWIM
open import proof.Correctness.Interp.ExplicateFuel using (compile-cfg-correct)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; map; reverse)
open import Data.List.Properties using (++-identityʳ; length-map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

private variable A : Set

{- equality gives a truth value -}
eq-bool : ∀ o₁ o₂ {n} → δ? eq o₁ o₂ ≢ just (int n)
eq-bool (o-const Int n) (o-const Int m) ()

{- prim? eq, then k; cmpq, then g -}
cmp-ok : ∀ v w {k : Val → Result A} {g} → (∀ b → k (out (bool b)) ≡ g b)
  → (from-maybe (prim? eq v w) >>= k) ≡ (from-maybe (δ? eq (obs v) (obs w)) >>= λ o → bool? o >>= g)
cmp-ok v w h with δ? eq (obs v) (obs w) in e
... | nothing = refl
... | just (bool b) = h b
... | just (int n) = ⊥-elim (eq-bool _ _ e)

{- atom a, then f and k in CFG, and g in X86 -}
atm-ok : ∀ a φ ρ {f : Val → Result Val} {k : Val → Result A} {g} → (∀ v → (f v >>= k) ≡ g v)
  → ((atom φ a >>= f) >>= k) ≡ (arg (φ , ρ) (select-atm a) >>= g)
atm-ok (var x) φ ρ h with φ ‼ x
... | just v = h v
... | nothing = refl
atm-ok (lit B k) φ ρ h = h _
atm-ok (fun-ref k) φ ρ h = h _

wrong-ok : ∀ a φ ρ {g : Val → Result A} → (∀ v → g v ≡ wrong) → (arg (φ , ρ) (select-atm a) >>= g) ≡ wrong
wrong-ok (var x) φ ρ h with φ ‼ x
... | just v = h v
... | nothing = refl
wrong-ok (lit B k) φ ρ h = h _
wrong-ok (fun-ref k) φ ρ h = h _

{- the atoms as, onto us -}
atoms-ok : ∀ as φ ρ us {k : Val → Result A} {g} → (∀ vs → k (tup (reverse vs)) ≡ g vs)
  → ((atoms φ us as >>= λ vs → ret (tup (reverse vs))) >>= k) ≡ args (φ , ρ) us (map select-atm as) g
atoms-ok [] φ ρ us h = h us
atoms-ok (var x ∷ as) φ ρ us h with φ ‼ x
... | just v = atoms-ok as φ ρ (v ∷ us) h
... | nothing = refl
atoms-ok (lit B k ∷ as) φ ρ us h = atoms-ok as φ ρ _ h
atoms-ok (fun-ref k ∷ as) φ ρ us h = atoms-ok as φ ρ _ h

{- Clock for clock ------------------------------------------------------------------}

module _ (ds : List CFG.Body) where
  private ds' = map (select-body prologue) ds

  {- at clock ck, where calls agree -}
  module _ (ck : ℕ) (calls : ∀ f e w → G.call ds ck (G.code? ds f) e w ≡ X.call ds' ck (X.code? ds' f) e w) where

    {- r, computed into d, then the rest of a block -}
    simple-ok : ∀ r d φ ρ {bs is j} {k : Val → Result Val}
      → (∀ v ρ' → k v ≡ write (φ , ρ') d v λ s → X.run ds' ck bs s is j)
      → (eval-simple (λ f → G.call ds ck (G.code? ds f)) φ r >>= k) ≡ X.run ds' ck bs (φ , ρ) (select-simple r d ++ is) j
    simple-ok (Imp.atm (var x)) d φ ρ h with φ ‼ x
    ... | just v = h v ρ
    ... | nothing = refl
    simple-ok (Imp.atm (lit B k)) d φ ρ h = h _ ρ
    simple-ok (Imp.atm (fun-ref k)) d φ ρ h = h _ ρ
    simple-ok (Imp.app (var y) e a) d φ ρ h with φ ‼ y
    ... | just f = atm-ok e φ ρ λ e → atm-ok a φ _ λ w → bind≡ (calls f e w) λ v → h v (regs (just v) nothing nothing nothing)
    ... | nothing = sym (wrong-ok e φ ρ λ _ → wrong-ok a φ _ λ _ → refl)
    simple-ok (Imp.app (lit B k) e a) d φ ρ h =
      atm-ok e φ ρ λ e → atm-ok a φ _ λ w → bind≡ (calls (const B k) e w) λ v → h v (regs (just v) nothing nothing nothing)
    simple-ok (Imp.app (fun-ref k) e a) d φ ρ h =
      atm-ok e φ ρ λ e → atm-ok a φ _ λ w → bind≡ (calls (code k) e w) λ v → h v (regs (just v) nothing nothing nothing)
    simple-ok (Imp.pair a b) d φ ρ h = atm-ok a φ ρ λ v → atm-ok b φ ρ λ w → h (pair v w) ρ
    simple-ok (Imp.fst a) d φ ρ h = atm-ok a φ ρ λ v → bind-cong (first v) λ w → h w ρ
    simple-ok (Imp.snd a) d φ ρ h = atm-ok a φ ρ λ v → bind-cong (second v) λ w → h w ρ
    simple-ok (Imp.tuple as) d φ ρ h = atoms-ok as φ ρ [] λ vs → h _ ρ
    simple-ok (Imp.get i a) d φ ρ h = atm-ok a φ ρ λ v → bind-cong (project i v) λ w → h w ρ
    simple-ok (Imp.inl a) d φ ρ h = atm-ok a φ ρ λ v → h (inl v) ρ
    simple-ok (Imp.inr a) d φ ρ h = atm-ok a φ ρ λ v → h (inr v) ρ
    simple-ok (Imp.prim sub a b) d φ ρ h =
      atm-ok a φ ρ λ v → atm-ok b φ _ λ w → bind-cong (from-maybe (prim? sub v w)) λ u → h u _
    simple-ok (Imp.prim eq a b) d φ ρ h = atm-ok a φ ρ λ v → atm-ok b φ ρ λ w → cmp-ok v w λ b → h _ _

    {- t, and block l, with the blocks bs -}
    tail-ok : ∀ t bs φ ρ
      → G.tail ds ck bs φ t ≡ X.run ds' ck (map select-tail bs) (φ , ρ) (Block.instrs (select-tail t)) (Block.jump (select-tail t))
    jump-ok : ∀ bs l φ ρ → G.jump ds ck bs φ l ≡ X.jump ds' ck (map select-tail bs) (φ , ρ) l

    tail-ok (return r) bs φ ρ =
      trans (sym (bind-ret _)) (trans (simple-ok r (reg rax) φ ρ {map select-tail bs} {[]} {retq} λ v ρ' → refl)
                                      (cong (λ is → X.run ds' ck (map select-tail bs) (φ , ρ) is retq) (++-identityʳ (select-simple r (reg rax)))))
    tail-ok (seq x r t) bs φ ρ = simple-ok r (var x) φ ρ λ v ρ' → bind-cong (from-maybe (φ [ x ]≔ v)) λ φ' → tail-ok t bs φ' ρ'
    tail-ok (goto l) bs φ ρ = jump-ok bs l φ ρ
    tail-ok (case (var y) x l₁ l₂) bs φ ρ with φ ‼ y
    ... | nothing = refl
    ... | just (inl w) = bind-cong (from-maybe (φ [ x ]≔ w)) λ φ' → jump-ok bs l₁ φ' (record ρ { flag = just true })
    ... | just (inr w) = bind-cong (from-maybe (φ [ x ]≔ w)) λ φ' → jump-ok bs l₂ φ' (record ρ { flag = just false })
    ... | just (code _) = refl
    ... | just (pair _ _) = refl
    ... | just (const _ _) = refl
    ... | just (tup _) = refl
    tail-ok (case (lit B k) x l₁ l₂) bs φ ρ = refl
    tail-ok (case (fun-ref k) x l₁ l₂) bs φ ρ = refl

    jump-ok [] l φ ρ = refl
    jump-ok (t ∷ bs) l φ ρ with l ≟ length bs | l ≟ length (map select-tail bs)
    ... | yes _ | yes _ = tail-ok t bs φ ρ
    ... | no _ | no _ = jump-ok bs l φ ρ
    ... | yes p | no q = ⊥-elim (q (trans p (sym (length-map select-tail bs))))
    ... | no p | yes q = ⊥-elim (p (trans q (length-map select-tail bs)))

  {- definition k of the X86 program is definition k of the CFG program, selected -}
  Def : CFG.Body → Body → Set
  Def b b' = b' ≡ select-body prologue b

  code-pw : ∀ f → M.Pointwise Def (G.code? ds f) (X.code? ds' f)
  code-pw (code k) = ‼-pw (reverse⁺ (pw ds)) k
    where pw : ∀ ds → Pointwise Def ds (map (select-body prologue) ds)
          pw [] = []
          pw (d ∷ ds) = refl ∷ pw ds
  code-pw (pair _ _) = M.nothing
  code-pw (const B k) = M.nothing
  code-pw (tup _) = M.nothing
  code-pw (inl _) = M.nothing
  code-pw (inr _) = M.nothing

  calls≡ : ∀ ck f e w → G.call ds ck (G.code? ds f) e w ≡ X.call ds' ck (X.code? ds' f) e w
  call-pw : ∀ ck {mb mb'} → M.Pointwise Def mb mb' → ∀ e w → G.call ds ck mb e w ≡ X.call ds' ck mb' e w

  calls≡ ck f = call-pw ck (code-pw f)

  call-pw ck M.nothing e w = refl
  call-pw zero (M.just _) e w = refl
  call-pw (suc ck) (M.just {CFG.body n bs t} refl) e w = tail-ok ck (calls≡ ck) t bs _ _

{- The end theorem -----------------------------------------------------------------}

select-correct : ∀ P → Equivalent (G.sem P) (X.sem (select P))
select-correct (CFG.program ds (CFG.body n bs t)) = clocked-≡ λ ck →
  tail-ok ds ck (calls≡ ds ck) t bs _ _

{- The whole compiler, into X86 ---------------------------------------------------}

compile-x86-correct : ∀ M → Closed M → Equivalent (ISWIM.sem M) (X.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct (compile-cfg M))
