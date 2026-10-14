{-

  The X86 programs of the compiler (Compiler/Pipeline.agda) are well
  formed for the graph model with errors (WF, GraphErr/X86WF.agda), and
  x86-error-iff, x86-const-iff, x86-converges-iff and x86-diverges-iff,
  the characterizations of GraphErr/X86.agda for the programs
  compile-x86 M of closed ISWIM programs M.

-}

module proof.Adequacy.GraphErr.X86CompileWF where


open import Language.X86
import Language.Clos4 as C4
import Language.Clos5 as C5
import Language.Mon as Mo
import Language.Imp as I
import Language.CFG as G
import Language.Prim as P
open import Compiler.Globalize using (Defs; glob; glob-arg; glob-args)
open import Compiler.RCO using (lets; binds; atoms; atomize; atom?; lift; case-on; rco; rco-args; rco-program; rco-program-mon)
open import Compiler.LiftLocals using (lift-atom; lift-atoms; lift-body; lift-defs; lift-program) renaming (lift to liftL)
open import Compiler.Explicate using (explicate-assign; explicate-tail; explicate-body; explicate)
open import Compiler.Select using (select-atm; select-simple; select-tail; prologue; select-body; select)
open import Compiler.Pipeline using (compile; compile₄; compile-x86)
open import Compiler.EncloseScope using (Closed)
open import proof.Framework.Syntax.Rename C5.Op C5.sig using (rename; rename-arg; rename-args; ext)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.abt.Sig using (■)

open import Data.List using (List; []; _∷_; _++_; length; map; replicate)
open import Data.List.Properties using (length-map; length-++; ++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; m≤n+m; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)
open import proof.Adequacy.GraphErr.X86WF
open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω) renaming (const to dconst)
open import Semantics.GraphErr.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.X86 as X86ₘ
open import proof.Adequacy.GraphErr.X86 using (error-iff; const-iff; converges-iff; diverges-iff)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

{- The compiler produces well-formed programs -------------------------------------

  Globalize adds the code of a function as a definition after those made
  from the functions nested in it, and the code refers only to those
  (glob-shape, as in Correctness/Graph/GlobalizeCorrect.agda); so each
  definition refers only to older ones, and main to existing ones (RB).
  Remove complex operands renames no reference (rb-rco); lift locals,
  explicate control and select instructions keep the atoms, so the labels
  of the program are its references (ex-tail, lift-ok). -}

RB : ℕ → C5.AST → Set
RB-arg : ∀ {b} → ℕ → C5.Arg b → Set
RB-args : ∀ {bs} → ℕ → C5.Args bs → Set

RB n (C5.` x) = ⊤
RB n (C5.fun-ref k C5.⦅ args ⦆) = k < n
RB n (op C5.⦅ args ⦆) = RB-args n args

RB-arg n (C5.ast M) = RB n M
RB-arg n (C5.bind a) = RB-arg n a
RB-arg n (C5.clear a) = RB-arg n a

RB-args n C5.nil = ⊤
RB-args n (C5.cons a args) = RB-arg n a × RB-args n args

RB-mono : ∀ {n m} (M : C5.AST) → n ≤ m → RB n M → RB m M
RB-arg-mono : ∀ {n m b} (a : C5.Arg b) → n ≤ m → RB-arg n a → RB-arg m a
RB-args-mono : ∀ {n m bs} (args : C5.Args bs) → n ≤ m → RB-args n args → RB-args m args

RB-mono (C5.` x) n≤m tt = tt
RB-mono (C5.fun-ref k C5.⦅ args ⦆) n≤m k<n = <-≤-trans k<n n≤m
RB-mono (C5.app C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.lit B k C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.pair-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.fst-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.snd-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.tuple x C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.get x C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.inl-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.inr-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.case-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.let-op C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (C5.prim p C5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r

RB-arg-mono (C5.ast M) n≤m r = RB-mono M n≤m r
RB-arg-mono (C5.bind a) n≤m r = RB-arg-mono a n≤m r
RB-arg-mono (C5.clear a) n≤m r = RB-arg-mono a n≤m r

RB-args-mono C5.nil n≤m tt = tt
RB-args-mono (C5.cons a args) n≤m (ra , rs) = RB-arg-mono a n≤m ra , RB-args-mono args n≤m rs

{- Globalize ---------------------------------------------------------------------}

Extends : Defs → Defs → Set
Extends ds ds' = Σ[ more ∈ Defs ] ds' ≡ more ++ ds

ext-trans : ∀ {ds₁ ds₂ ds₃} → Extends ds₁ ds₂ → Extends ds₂ ds₃ → Extends ds₁ ds₃
ext-trans {ds₁} (m₁ , refl) (m₂ , refl) = m₂ ++ m₁ , sym (++-assoc m₂ m₁ ds₁)

ext-length : ∀ {ds ds'} → Extends ds ds' → length ds ≤ length ds'
ext-length {ds} (more , refl) = subst (length ds ≤_) (sym (length-++ more)) (m≤n+m (length ds) (length more))

Shape′ : Defs → C5.AST × Defs → Set
Shape′ ds r = Extends ds (proj₂ r) × RB (length (proj₂ r)) (proj₁ r)

glob-shape : ∀ (M : C4.AST) ds → Shape′ ds (glob M ds)
glob-shape-arg : ∀ {b} (a : C4.Arg b) ds
  → Extends ds (proj₂ (glob-arg a ds)) × RB-arg (length (proj₂ (glob-arg a ds))) (proj₁ (glob-arg a ds))
glob-shape-args : ∀ {bs} (args : C4.Args bs) ds
  → Extends ds (proj₂ (glob-args args ds))
    × RB-args (length (proj₂ (glob-args args ds))) (proj₁ (glob-args args ds))

glob-shape (C4.` x) ds = ([] , refl) , tt
glob-shape (C4.fun-op C4.⦅ C4.cons (C4.clear (C4.bind (C4.bind (C4.ast N)))) C4.nil ⦆) ds =
  ext-trans (proj₁ (glob-shape N ds)) (proj₁ (glob N ds) ∷ [] , refl) , n<1+n (length (proj₂ (glob N ds)))
glob-shape (C4.app C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.lit B k C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.pair-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.fst-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.snd-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.tuple n C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.get i C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.inl-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.inr-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.case-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.let-op C4.⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (C4.prim p C4.⦅ args ⦆) ds = glob-shape-args args ds

glob-shape-arg (C4.ast M) ds = glob-shape M ds
glob-shape-arg (C4.bind a) ds = glob-shape-arg a ds
glob-shape-arg (C4.clear a) ds = glob-shape-arg a ds

glob-shape-args C4.nil ds = ([] , refl) , tt
glob-shape-args (C4.cons a args) ds =
  ext-trans (proj₁ sa) (proj₁ ss)
  , RB-arg-mono (proj₁ (glob-arg a ds)) (ext-length (proj₁ ss)) (proj₂ sa) , proj₂ ss
  where
  sa = glob-shape-arg a ds
  ss = glob-shape-args args (proj₂ (glob-arg a ds))

{- the definitions, newest first, refer only to older ones -}
DefsRB : List C5.AST → Set
DefsRB [] = ⊤
DefsRB (N ∷ Ns) = RB (length Ns) N × DefsRB Ns

glob-rb : ∀ M ds → DefsRB ds → DefsRB (proj₂ (glob M ds))
glob-rb-arg : ∀ {b} (a : C4.Arg b) ds → DefsRB ds → DefsRB (proj₂ (glob-arg a ds))
glob-rb-args : ∀ {bs} (args : C4.Args bs) ds → DefsRB ds → DefsRB (proj₂ (glob-args args ds))

glob-rb (C4.` x) ds d = d
glob-rb (C4.fun-op C4.⦅ C4.cons (C4.clear (C4.bind (C4.bind (C4.ast N)))) C4.nil ⦆) ds d =
  proj₂ (glob-shape N ds) , glob-rb N ds d
glob-rb (C4.app C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.lit B k C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.pair-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.fst-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.snd-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.tuple n C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.get i C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.inl-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.inr-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.case-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.let-op C4.⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (C4.prim p C4.⦅ args ⦆) ds d = glob-rb-args args ds d

glob-rb-arg (C4.ast M) ds d = glob-rb M ds d
glob-rb-arg (C4.bind a) ds d = glob-rb-arg a ds d
glob-rb-arg (C4.clear a) ds d = glob-rb-arg a ds d

glob-rb-args C4.nil ds d = d
glob-rb-args (C4.cons a args) ds d = glob-rb-args args (proj₂ (glob-arg a ds)) (glob-rb-arg a ds d)

{- Remove complex operands keeps the references --------------------------------}

module _ {K : ℕ} where

  rb-rename : ∀ r M → RB K M → RB K (rename r M)
  rb-rename-arg : ∀ {b} r (a : C5.Arg b) → RB-arg K a → RB-arg K (rename-arg r a)
  rb-rename-args : ∀ {bs} r (as : C5.Args bs) → RB-args K as → RB-args K (rename-args r as)
  rb-rename r (C5.` x) _ = tt
  rb-rename r (C5.fun-ref k C5.⦅ as ⦆) k< = k<
  rb-rename r (C5.app C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.lit B k C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.pair-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.fst-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.snd-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.tuple n C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.get i C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.inl-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.inr-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.case-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.prim p C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (C5.let-op C5.⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename-arg r (C5.ast M) rb = rb-rename r M rb
  rb-rename-arg r (C5.bind a) rb = rb-rename-arg (ext r) a rb
  rb-rename-arg r (C5.clear a) rb = rb
  rb-rename-args r C5.nil _ = tt
  rb-rename-args r (C5.cons a as) (ra , rs) = rb-rename-arg r a ra , rb-rename-args r as rs

  rb-lets : ∀ bs N → All (RB K) bs → RB K N → RB K (lets bs N)
  rb-lets [] N _ r = r
  rb-lets (M ∷ Ms) N (rM ∷ rs) r = rM , rb-lets Ms N rs r , tt

  rb-atomize : ∀ {n} (Ms : C5.Args (replicate n ■)) → RB-args K Ms
    → All (RB K) (binds (atomize Ms)) × RB-args K (atoms (atomize Ms))
  rb-atomize {zero} Nil _ = [] , tt
  rb-atomize {suc n} (M ,, Ms) (r , rs) with atom? M
  ... | yes _ = let (rl , ra) = rb-atomize Ms rs in rl , rb-rename _ M r , ra
  ... | no _ = let (rl , ra) = rb-atomize (rename-args suc Ms) (rb-rename-args suc Ms rs) in (r ∷ rl) , tt , ra

  rb-lift : ∀ {n} (f : ℕ → C5.Args (replicate n ■) → C5.AST) Ms → RB-args K Ms
    → (∀ j As → RB-args K As → RB K (f j As)) → RB K (lift f Ms)
  rb-lift f Ms r hf = let (rl , ra) = rb-atomize Ms r in rb-lets (binds (atomize Ms)) _ rl (hf _ _ ra)

  rb-rco : ∀ M → RB K M → RB K (rco M)
  rb-rco-args : ∀ {n} (Ms : C5.Args (replicate n ■)) → RB-args K Ms → RB-args K (rco-args Ms)
  rb-rco (C5.` x) r = r
  rb-rco (C5.fun-ref k C5.⦅ Nil ⦆) r = r
  rb-rco (C5.app C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.app C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.lit B k C5.⦅ Nil ⦆) r = r
  rb-rco (C5.pair-op C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.pair-op C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.fst-op C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.fst-op C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.snd-op C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.snd-op C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.tuple n C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.tuple n C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.get i C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.get i C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.inl-op C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.inl-op C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.inr-op C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.inr-op C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.prim p C5.⦅ Ms ⦆) r = rb-lift (λ _ → C5.prim p C5.⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (C5.case-op C5.⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (rL , rM , rN , _) =
    rb-lift (case-on (rco M) (rco N)) (rco L ,, Nil) (rb-rco L rL , tt) λ { j (A ,, Nil) (rA , _) →
      rA , rb-rename _ (rco M) (rb-rco M rM) , rb-rename _ (rco N) (rb-rco N rN) , tt }
  rb-rco (C5.let-op C5.⦅ M ,, ⟩ N ,, Nil ⦆) (rM , rN , _) = rb-rco M rM , rb-rco N rN , tt
  rb-rco-args {zero} Nil _ = tt
  rb-rco-args {suc n} (M ,, Ms) (r , rs) = rb-rco M r , rb-rco-args Ms rs

{- Lift locals, explicate control and select instructions keep the atoms ---------------}

Code-++ : ∀ {L} xs {ys} → Code L xs → Code L ys → Code L (xs ++ ys)
Code-++ [] _ c = c
Code-++ (i ∷ xs) (r , cs) c = r , Code-++ xs cs c

module _ (K : ℕ) where

  {- what select instructions makes of a simple expression, an Imp
     expression and a tail reads only labels below K -}
  Sim : I.Simple → Set
  Sim s = ∀ d → Code (_< K) (select-simple s d)

  ExpOK : I.Exp → Set
  ExpOK (I.simple s) = Sim s
  ExpOK (I.case a x e₁ e₂) = OK (_< K) (select-atm a) × ExpOK e₁ × ExpOK e₂
  ExpOK (I.assign x e₁ e₂) = ExpOK e₁ × ExpOK e₂

  TailOK : G.Tail → Set
  TailOK t = Code (_< K) (Block.instrs (select-tail t))

  ex-assign : ∀ e x k bs → ExpOK e → TailOK k → All TailOK bs
    → TailOK (proj₁ (explicate-assign e x k bs)) × All TailOK (proj₂ (explicate-assign e x k bs))
  ex-assign (I.simple s) x k bs ok tk ab = Code-++ (select-simple s (var x)) (ok (var x)) tk , ab
  ex-assign (I.assign y e₁ e₂) x k bs (o₁ , o₂) tk ab =
    let (t , ab₁) = ex-assign e₂ x k bs o₂ tk ab in ex-assign e₁ y _ _ o₁ t ab₁
  ex-assign (I.case a y e₁ e₂) x k bs (oa , o₁ , o₂) tk ab =
    let (t₁ , ab₂) = ex-assign e₁ x (G.goto _) (k ∷ bs) o₁ tt (tk ∷ ab)
        (t₂ , ab₄) = ex-assign e₂ x (G.goto _) (_ ∷ _) o₂ tt (t₁ ∷ ab₂) in
    (oa , oa , tt) , t₂ ∷ ab₄

  ex-tail : ∀ e bs → ExpOK e → All TailOK bs → TailOK (proj₁ (explicate-tail e bs)) × All TailOK (proj₂ (explicate-tail e bs))
  ex-tail (I.simple s) bs ok ab = ok (reg rax) , ab
  ex-tail (I.assign x e₁ e₂) bs (o₁ , o₂) ab = let (t , ab₁) = ex-tail e₂ bs o₂ ab in ex-assign e₁ x _ _ o₁ t ab₁
  ex-tail (I.case a x e₁ e₂) bs (oa , o₁ , o₂) ab =
    let (t₁ , ab₁) = ex-tail e₁ bs o₁ ab
        (t₂ , ab₃) = ex-tail e₂ (_ ∷ _) o₂ (t₁ ∷ ab₁) in
    (oa , oa , tt) , t₂ ∷ ab₃

  atom-ok : ∀ {n d M} (a : Mo.Atom M) → RB K M → OK (_< K) (select-atm (lift-atom n d a))
  atom-ok (Mo.var x) _ = tt
  atom-ok (Mo.lit B k) _ = tt
  atom-ok (Mo.ref k) k< = k<

  atoms-ok : ∀ {n d m Ms} (as : Mo.Atoms {m} Ms) → RB-args K Ms → All (OK (_< K)) (map select-atm (lift-atoms n d as))
  atoms-ok Mo.[] _ = []
  atoms-ok (a Mo.∷ as) (r , rs) = atom-ok a r ∷ atoms-ok as rs

  lift-ok : ∀ {n d M} (m : Mo.Mon M) → RB K M → ExpOK (liftL n d m)
  lift-ok (Mo.atom a) r _ = atom-ok a r , tt
  lift-ok (Mo.app (a Mo.∷ (b Mo.∷ (c Mo.∷ Mo.[])))) (ra , rb , rc , _) _ = atom-ok b rb , atom-ok c rc , atom-ok a ra , tt , tt
  lift-ok (Mo.pair (a Mo.∷ (b Mo.∷ Mo.[]))) (ra , rb , _) _ = (atom-ok a ra ∷ atom-ok b rb ∷ []) , tt
  lift-ok (Mo.fst (a Mo.∷ Mo.[])) (ra , _) _ = atom-ok a ra , tt
  lift-ok (Mo.snd (a Mo.∷ Mo.[])) (ra , _) _ = atom-ok a ra , tt
  lift-ok (Mo.tuple as) rs _ = atoms-ok as rs , tt
  lift-ok (Mo.get (a Mo.∷ Mo.[])) (ra , _) _ = atom-ok a ra , tt
  lift-ok (Mo.inl (a Mo.∷ Mo.[])) (ra , _) _ = (atom-ok a ra ∷ []) , tt
  lift-ok (Mo.inr (a Mo.∷ Mo.[])) (ra , _) _ = (atom-ok a ra ∷ []) , tt
  lift-ok (Mo.prim {P.sub} (a Mo.∷ (b Mo.∷ Mo.[]))) (ra , rb , _) _ = atom-ok a ra , atom-ok b rb , tt , tt
  lift-ok (Mo.prim {P.eq} (a Mo.∷ (b Mo.∷ Mo.[]))) (ra , rb , _) _ = (atom-ok b rb , atom-ok a ra) , tt , tt
  lift-ok (Mo.case a m₁ m₂) (ra , r₁ , r₂ , _) = atom-ok a ra , lift-ok m₁ r₁ , lift-ok m₂ r₂
  lift-ok (Mo.let′ m₁ m₂) (r₁ , r₂ , _) = lift-ok m₁ r₁ , lift-ok m₂ r₂

{- a body compiled at depth d₀, with the instructions pre first -}
body-ok : ∀ {K} pre d₀ {M} (m : Mo.Mon M) → RB K M → (∀ {is} → Code (_< K) is → Code (_< K) (pre ++ is))
  → BodyOK K (select-body pre (explicate-body (lift-body d₀ m)))
body-ok {K} pre d₀ m r hp =
  let (t , ab) = ex-tail K _ _ (lift-ok K m r) [] in hp t ∷ map⁺ ab
  where open import Data.List.Relation.Unary.All.Properties using (map⁺)

length-lift : ∀ {ds} (ms : All Mo.Mon ds) → length (lift-defs ms) ≡ length ds
length-lift [] = refl
length-lift (m ∷ ms) = cong suc (length-lift ms)

{- the definitions, newest first -}
defs-ok : ∀ ds (ms : All Mo.Mon (map rco ds)) → DefsRB ds
  → DefsWF (map (select-body prologue) (map explicate-body (lift-defs ms)))
defs-ok [] [] _ = tt
defs-ok (N ∷ Ns) (m ∷ ms) (rb , wf) =
  subst (λ K → BodyOK K (select-body prologue (explicate-body (lift-body 2 m)))) (sym len)
    (body-ok {length Ns} prologue 2 m (rb-rco N rb) λ c → tt , tt , c)
  , defs-ok Ns ms wf
  where
  len = trans (length-map _ (map explicate-body (lift-defs ms)))
          (trans (length-map _ (lift-defs ms)) (trans (length-lift ms) (length-map rco Ns)))

{- the compiler produces well-formed programs -}
compile-x86-wf : ∀ M → Closed M → WF (compile-x86 M)
compile-x86-wf M _ = wf (proj₂ (glob M₄ [])) (proj₁ (glob M₄ [])) (glob-rb M₄ [] tt) (proj₂ (glob-shape M₄ []))
  where
  M₄ = compile₄ M
  wf : ∀ ds M → DefsRB ds → RB (length ds) M
    → WF (select (explicate (lift-program (rco-program (C5.program ds M)) (rco-program-mon (C5.program ds M)))))
  wf ds M wfd rb =
    defs-ok ds ms wfd
    , subst (λ K → BodyOK K (select-body [] (explicate-body (lift-body 0 m)))) (sym len) (body-ok {length ds} [] 0 m (rb-rco M rb) λ c → c)
    where
    ms = proj₁ (rco-program-mon (C5.program ds M))
    m = proj₂ (rco-program-mon (C5.program ds M))
    len = trans (length-map _ (map explicate-body (lift-defs ms)))
            (trans (length-map _ (lift-defs ms)) (trans (length-lift ms) (length-map rco ds)))

{- The programs of the compiler ---------------------------------------------------}

x86-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
x86-error-iff M c = error-iff (compile-x86 M) (compile-x86-wf M c)

x86-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff M c = const-iff (compile-x86 M) (compile-x86-wf M c)

x86-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₓ × d ≢ ω) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
x86-converges-iff M c = converges-iff (compile-x86 M) (compile-x86-wf M c)

x86-diverges-iff : ∀ M → Closed M
  → Diverges (X86ₘ.sem (compile-x86 M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile-x86 M ⟧ₓ))
x86-diverges-iff M c = diverges-iff (compile-x86 M) (compile-x86-wf M c)
