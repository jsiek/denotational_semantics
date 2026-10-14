{-

  Facts about the code typed select instructions produces
  (Compiler/Typed/Select.agda), for every CFGᵀ program: they hold by the
  typing, so select needs no well-formedness precondition.

  * Definitions exist: the code pointer of definition f, its level,
    finds the selected body of f among the X86 definitions (global-sel).
  * Labels exist: label l, its level, finds the selected block l, with
    the selected blocks older than it (block-sel).
  * Frames are large enough: a tail at frame context Δ has depth at
    least the length of Δ (depth-≥), and block l of bs, and the blocks
    older than it, have depths at most that of bs (block-depth). A body's
    frame has as many slots as the depths of its start and blocks.

-}

module proof.Compiler.Typed.SelectFacts where

open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.CFG as CFG using (Tail; return; seq; goto; case; Blocks; _▷_; Body; Blk; blk; block)
open import Compiler.Typed.Select
open import Framework.Lookup using (_!_)
open import proof.Framework.Membership using (lvl-<)
open import proof.Framework.ListUtil using (‼-snoc-<; ‼-snoc-length)
open import Framework.ListUtil using (_‼_)
import Language.X86 as L
open import Semantics.CEK.X86 using (block-at)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; reverse)
open import Data.List.Properties using (unfold-reverse; length-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; _<_; _⊔_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; <-irrefl; <⇒≢)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Definitions exist -------------------------------------------------------------}

len-defs : ∀ {Σ ns} (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) → length (select-defs ds) ≡ length ns
len-defs [] = refl
len-defs (d ∷ ds) = cong ℕ.suc (len-defs ds)

global-sel : ∀ {Σ ns n} (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) (f : ns ∋ n)
  → reverse (select-defs ds) ‼ lvl f ≡ just (select-body prologue (ds ! f))
global-sel {ns = n ∷ ns} (d ∷ ds) f rewrite unfold-reverse (select-body prologue d) (select-defs ds) = go f
  where
  xs = reverse (select-defs ds)
  len : length xs ≡ length ns
  len = trans (length-reverse (select-defs ds)) (len-defs ds)
  go : ∀ {m} (f : (n ∷ ns) ∋ m) → (xs ∷ʳ select-body prologue d) ‼ lvl f ≡ just (select-body prologue ((d ∷ ds) ! f))
  go Z = subst (λ k → (xs ∷ʳ select-body prologue d) ‼ k ≡ just (select-body prologue d)) len
           (‼-snoc-length xs (select-body prologue d))
  go (S f) = trans (‼-snoc-< xs (select-body prologue d) (lvl f) (subst (lvl f <_) (sym len) (lvl-< f)))
                   (global-sel ds f)

{- Labels exist ------------------------------------------------------------------}

len-blocks : ∀ {Σ Bs} (bs : Blocks Σ Bs) → length (select-blocks bs) ≡ length Bs
len-blocks CFG.[] = refl
len-blocks (bs ▷ t) = cong ℕ.suc (len-blocks bs)

block-sel : ∀ {Σ Bs Δ} (bs : Blocks Σ Bs) (l : Bs ∋ Δ)
  → block-at (select-blocks bs) (lvl l) ≡ just (select-tail (Blk.tail (block bs l)) , select-blocks (Blk.blocks (block bs l)))
block-sel {Bs = _ ∷ Bs} (bs ▷ t) Z with length Bs ≟ length (select-blocks bs)
... | yes _ = refl
... | no ne = ⊥-elim (ne (sym (len-blocks bs)))
block-sel (bs ▷ t) (S l) with lvl l ≟ length (select-blocks bs)
... | yes e = ⊥-elim (<⇒≢ (lvl-< l) (trans e (len-blocks bs)))
... | no _ = block-sel bs l

{- Frames are large enough -------------------------------------------------------}

depth-≥ : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) → length Δ ≤ depth t
depth-≥ (return s) = ≤-refl
depth-≥ (seq p s t) = m≤m⊔n _ _
depth-≥ (goto l) = ≤-refl
depth-≥ (case a p l₁ l₂) = m≤m⊔n _ _

block-depth : ∀ {Σ Bs Δ} (bs : Blocks Σ Bs) (l : Bs ∋ Δ)
  → depth (Blk.tail (block bs l)) ≤ blocks-depth bs × blocks-depth (Blk.blocks (block bs l)) ≤ blocks-depth bs
block-depth (bs ▷ t) Z = m≤m⊔n _ _ , m≤n⊔m _ _
block-depth (bs ▷ t) (S l) with block-depth bs l
... | p , q = ≤-trans p (m≤n⊔m _ _) , ≤-trans q (m≤n⊔m _ _)
