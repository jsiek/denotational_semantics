{-

  Definitions shared by the soundness and adequacy proofs for X86 in the
  graph model with errors (see GraphErr/X86.agda for the overview): runs
  of the X86 machine of the definitions ds, frames, the blocks a jump
  finds (or does not), and where a definition found by the machine
  (global ds k) sits in the table.

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Language.X86 using (Body)

module proof.Adequacy.GraphErrM.X86Common (ds : List Body) where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (ν)
open import Language.X86 hiding (Body)
open import Semantics.GraphErrM.X86 using (table; blocks; ⟦_⟧ᵇ; init) renaming (code to codeD)
open import Semantics.CEK.X86
open import proof.Framework.Runs using (module Runs)
open import proof.Adequacy.GraphErrM.X86WF using (DefsWF)
open import proof.Framework.ListUtil using (_‼_)
open import proof.Framework.ListUtil using (‼-just; replicate-‼; reverse-‼-split; reverse-‼-suffix) public

open import Data.List.Properties using (length-replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; _∸_; _⊔_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; <⇒≢; <-≤-trans; ≤-trans; n≤1+n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)
open import Relation.Nullary using (yes; no)

open Runs (step ds) public

{- Frames ---------------------------------------------------------------------------}

{- what an assignment to slot x does -}
record Assigned (φ : Frame) (x : ℕ) (v : Val) (φ' : Frame) : Set where
  field
    len : length φ' ≡ length φ
    here : φ' ‼ x ≡ just v
    other : ∀ y → y ≢ x → φ' ‼ y ≡ φ ‼ y
    inside : x < length φ

≔-inv : ∀ φ x {v φ'} → φ [ x ]≔ v ≡ just φ' → Assigned φ x v φ'
≔-inv (u ∷ φ) zero refl = record { len = refl ; here = refl ; other = oth ; inside = s≤s z≤n }
  where
  oth : ∀ y → y ≢ zero → _
  oth zero ne = ⊥-elim (ne refl)
  oth (suc y) ne = refl
≔-inv (u ∷ φ) (suc x) {v} e with φ [ x ]≔ v in e'
≔-inv (u ∷ φ) (suc x) refl | just φ'' = record
  { len = cong suc (Assigned.len a) ; here = Assigned.here a ; other = oth ; inside = s≤s (Assigned.inside a) }
  where
  a = ≔-inv φ x e'
  oth : ∀ y → y ≢ suc x → _
  oth zero ne = refl
  oth (suc y) ne = Assigned.other a y (λ eq → ne (cong suc eq))

≔-ok : ∀ φ x v → x < length φ → Σ[ φ' ∈ Frame ] φ [ x ]≔ v ≡ just φ'
≔-ok (u ∷ φ) zero v _ = v ∷ φ , refl
≔-ok (u ∷ φ) (suc x) v (s≤s x<) with ≔-ok φ x v x<
... | φ' , e rewrite e = u ∷ φ' , refl

{- an assignment to a slot beyond the frame fails -}
≔-out : ∀ φ x v → (x < length φ → Data.Empty.⊥) → φ [ x ]≔ v ≡ nothing
≔-out [] x v _ = refl
≔-out (u ∷ φ) zero v ¬x< = ⊥-elim (¬x< (s≤s z≤n))
≔-out (u ∷ φ) (suc x) v ¬x< rewrite ≔-out φ x v (λ x< → ¬x< (s≤s x<)) = refl

{- a slot beyond the frame is not there -}
‼-out : ∀ (φ : Frame) x → (x < length φ → Data.Empty.⊥) → φ ‼ x ≡ nothing
‼-out [] x _ = refl
‼-out (u ∷ φ) zero ¬x< = ⊥-elim (¬x< (s≤s z≤n))
‼-out (u ∷ φ) (suc x) ¬x< = ‼-out φ x (λ x< → ¬x< (s≤s x<))

{- the frame of a definition -}
frame-size : ∀ n → length (zeros (2 + (n ∸ 2))) ≡ 2 ⊔ n
frame-size zero = refl
frame-size (suc zero) = refl
frame-size (suc (suc n)) = cong (λ m → suc (suc m)) (length-replicate n)

{- Blocks --------------------------------------------------------------------------}

blocks-at : ∀ {T n} bs l {b bs'} → block-at bs l ≡ just (b , bs') → blocks T n bs l ≡ ⟦ b ⟧ᵇ T n (blocks T n bs')
blocks-at (c ∷ bs) l e with l ≟ length bs
blocks-at (c ∷ bs) l refl | yes _ = refl
... | no _ = blocks-at bs l e

{- a missing block Errs -}
blocks-none : ∀ {T n} bs l → block-at bs l ≡ nothing → ∀ σ ρ φ → blocks T n bs l σ ρ φ ≡ init
blocks-none [] l e σ ρ φ = refl
blocks-none (c ∷ bs) l e with l ≟ length bs
blocks-none (c ∷ bs) l () | yes _
... | no _ = blocks-none bs l e

{- The table of global definitions --------------------------------------------------}

{- the definition that the machine finds at k sits on top of the k
   definitions older than it -}
global-split : ∀ k {b} → global ds k ≡ just b → Σ[ xs ∈ List Body ] Σ[ Ns ∈ List Body ] ds ≡ xs ++ b ∷ Ns × length Ns ≡ k
global-split = reverse-‼-split ds

table-agree : ∀ xs Ns j → j < length Ns → table (xs ++ Ns) j ≡ table Ns j
table-agree [] Ns j j< = refl
table-agree (x ∷ xs) Ns j j< with j ≟ length (xs ++ Ns)
... | no _ = table-agree xs Ns j j<
... | yes refl = ⊥-elim (<⇒≢ (<-≤-trans j< (len≤ xs)) refl)
  where
  len≤ : ∀ xs → length Ns ≤ length (xs ++ Ns)
  len≤ [] = Data.Nat.Properties.≤-refl
  len≤ (_ ∷ xs) = ≤-trans (len≤ xs) (n≤1+n _)

table-at : ∀ xs b Ns → table (xs ++ b ∷ Ns) (length Ns) ≡ codeD (table Ns) b
table-at xs b Ns = trans (table-agree xs (b ∷ Ns) (length Ns) (n<1+n _)) top
  where
  top : table (b ∷ Ns) (length Ns) ≡ codeD (table Ns) b
  top with length Ns ≟ length Ns
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

{- every entry of a table is a function -}
ν-table : ∀ (Ns : List Body) k → ν ∈ table Ns k
ν-table [] k = tt , tt
ν-table (N ∷ Ns) k with k ≟ length Ns
... | yes _ = tt , tt
... | no _ = ν-table Ns k

DefsWF-suffix : ∀ xs {Ns} → DefsWF (xs ++ Ns) → DefsWF Ns
DefsWF-suffix [] w = w
DefsWF-suffix (x ∷ xs) w = DefsWF-suffix xs (proj₂ w)
