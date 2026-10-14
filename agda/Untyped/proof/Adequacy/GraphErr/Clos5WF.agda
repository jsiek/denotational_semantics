{-

  Well-formed Clos5 programs for the graph model with errors, the
  precondition of soundness and adequacy for the Clos5 machine
  (Adequacy/GraphErr/Clos5.agda), and the proof that globalize produces
  them from every Clos4 term (compile-wf).

  Each reference refers to an existing definition, and the code of a
  definition only to older ones (RB): the semantics interprets each
  definition with the table of the older ones only, while the machine
  looks references up in the whole table.

  Unlike proof/Adequacy/Clos5WF.agda, scoping is not needed: an unbound
  variable denotes init = {ω} and errs in the machine, so the logical
  relation relates them. (RB and the shape of globalize are as in
  proof/Correctness/Graph/GlobalizeCorrect.agda, which is outside the
  graph model with errors.)

-}

module Untyped.proof.Adequacy.GraphErr.Clos5WF where

open import Untyped.Language.Clos4
import Untyped.Language.Clos5 as L5
open import Untyped.Compiler.Globalize
open import Untyped.Compiler.Pipeline using (compile; compile₄)

open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; m≤n+m; n<1+n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

{- References to older definitions ----------------------------------------------}

RB : ℕ → L5.AST → Set
RB-arg : ∀ {b} → ℕ → L5.Arg b → Set
RB-args : ∀ {bs} → ℕ → L5.Args bs → Set

RB n (L5.` x) = ⊤
RB n (L5.fun-ref k L5.⦅ args ⦆) = k < n
RB n (op L5.⦅ args ⦆) = RB-args n args

RB-arg n (L5.ast M) = RB n M
RB-arg n (L5.bind a) = RB-arg n a
RB-arg n (L5.clear a) = RB-arg n a

RB-args n L5.nil = ⊤
RB-args n (L5.cons a args) = RB-arg n a × RB-args n args

RB-mono : ∀ {n m} (M : L5.AST) → n ≤ m → RB n M → RB m M
RB-arg-mono : ∀ {n m b} (a : L5.Arg b) → n ≤ m → RB-arg n a → RB-arg m a
RB-args-mono : ∀ {n m bs} (args : L5.Args bs) → n ≤ m → RB-args n args → RB-args m args

RB-mono (L5.` x) n≤m tt = tt
RB-mono (L5.fun-ref k L5.⦅ args ⦆) n≤m k<n = <-≤-trans k<n n≤m
RB-mono (L5.app L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.lit B k L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.pair-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.fst-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.snd-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.tuple x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.get x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inl-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inr-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.case-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.let-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.prim p L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r

RB-arg-mono (L5.ast M) n≤m r = RB-mono M n≤m r
RB-arg-mono (L5.bind a) n≤m r = RB-arg-mono a n≤m r
RB-arg-mono (L5.clear a) n≤m r = RB-arg-mono a n≤m r

RB-args-mono L5.nil n≤m tt = tt
RB-args-mono (L5.cons a args) n≤m ⟨ ra , rs ⟩ = ⟨ RB-arg-mono a n≤m ra , RB-args-mono args n≤m rs ⟩

{- the definitions, newest first, refer only to older ones -}
DefsWF : List L5.AST → Set
DefsWF [] = ⊤
DefsWF (N ∷ Ns) = RB (length Ns) N × DefsWF Ns

WF : L5.Program → Set
WF (L5.program ds M) = DefsWF ds × RB (length ds) M

{- The shape of globalize -------------------------------------------------------}

Extends : Defs → Defs → Set
Extends ds ds' = Σ[ more ∈ Defs ] ds' ≡ more ++ ds

ext-trans : ∀ {ds₁ ds₂ ds₃} → Extends ds₁ ds₂ → Extends ds₂ ds₃ → Extends ds₁ ds₃
ext-trans {ds₁} ⟨ m₁ , refl ⟩ ⟨ m₂ , refl ⟩ = ⟨ m₂ ++ m₁ , sym (++-assoc m₂ m₁ ds₁) ⟩

ext-length : ∀ {ds ds'} → Extends ds ds' → length ds ≤ length ds'
ext-length {ds} ⟨ more , refl ⟩ = subst (length ds ≤_) (sym (length-++ more)) (m≤n+m (length ds) (length more))

Shape : Defs → L5.AST × Defs → Set
Shape ds r = Extends ds (proj₂ r) × RB (length (proj₂ r)) (proj₁ r)

glob-shape : ∀ (M : AST) ds → Shape ds (glob M ds)
glob-shape-arg : ∀ {b} (a : Arg b) ds
  → Extends ds (proj₂ (glob-arg a ds)) × RB-arg (length (proj₂ (glob-arg a ds))) (proj₁ (glob-arg a ds))
glob-shape-args : ∀ {bs} (args : Args bs) ds
  → Extends ds (proj₂ (glob-args args ds))
    × RB-args (length (proj₂ (glob-args args ds))) (proj₁ (glob-args args ds))

glob-shape (` x) ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds =
  ⟨ ext-trans (proj₁ (glob-shape N ds)) ⟨ proj₁ (glob N ds) ∷ [] , refl ⟩
  , n<1+n (length (proj₂ (glob N ds))) ⟩
glob-shape (app ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (lit B k ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (pair-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (fst-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (snd-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (tuple n ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (get i ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inl-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inr-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (case-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (let-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (prim p ⦅ args ⦆) ds = glob-shape-args args ds

glob-shape-arg (ast M) ds = glob-shape M ds
glob-shape-arg (bind a) ds = glob-shape-arg a ds
glob-shape-arg (clear a) ds = glob-shape-arg a ds

glob-shape-args nil ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape-args (cons a args) ds =
  ⟨ ext-trans (proj₁ sa) (proj₁ ss)
  , ⟨ RB-arg-mono (proj₁ (glob-arg a ds)) (ext-length (proj₁ ss)) (proj₂ sa) , proj₂ ss ⟩ ⟩
  where
  sa = glob-shape-arg a ds
  ss = glob-shape-args args (proj₂ (glob-arg a ds))

{- globalize adds definitions that refer only to older ones -}
glob-wf : ∀ M ds → DefsWF ds → DefsWF (proj₂ (glob M ds))
glob-wf-arg : ∀ {b} (a : Arg b) ds → DefsWF ds → DefsWF (proj₂ (glob-arg a ds))
glob-wf-args : ∀ {bs} (args : Args bs) ds → DefsWF ds → DefsWF (proj₂ (glob-args args ds))

glob-wf (` x) ds d = d
glob-wf (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds d =
  ⟨ proj₂ (glob-shape N ds) , glob-wf N ds d ⟩
glob-wf (app ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (lit B k ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (pair-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (fst-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (snd-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (tuple n ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (get i ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (inl-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (inr-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (case-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (let-op ⦅ args ⦆) ds d = glob-wf-args args ds d
glob-wf (prim p ⦅ args ⦆) ds d = glob-wf-args args ds d

glob-wf-arg (ast M) ds d = glob-wf M ds d
glob-wf-arg (bind a) ds d = glob-wf-arg a ds d
glob-wf-arg (clear a) ds d = glob-wf-arg a ds d

glob-wf-args nil ds d = d
glob-wf-args (cons a args) ds d = glob-wf-args args (proj₂ (glob-arg a ds)) (glob-wf-arg a ds d)

{- The compiler ------------------------------------------------------------------}

globalize-wf : ∀ M → WF (globalize M)
globalize-wf M = ⟨ glob-wf M [] tt , proj₂ (glob-shape M []) ⟩

compile-wf : ∀ M → WF (compile M)
compile-wf M = globalize-wf (compile₄ M)
