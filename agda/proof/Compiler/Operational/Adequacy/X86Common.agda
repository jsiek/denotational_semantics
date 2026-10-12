{-

  Definitions shared by the soundness and adequacy proofs for X86
  (see Adequacy/X86.agda for the overview): runs of the X86 machine of
  the definitions ds, frames, the blocks a jump finds, and where a
  definition found by the machine (global ds k) sits in the table.

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Compiler.Lang.X86 using (Body)

module proof.Compiler.Operational.Adequacy.X86Common (ds : List Body) where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain using (ν)
open import Compiler.Lang.X86 hiding (Body)
open import Compiler.Model.Graph.Sem.X86 using (table; blocks; ⟦_⟧ᵇ)
  renaming (Regs to SRegs; code to codeD)
open import Compiler.Operational.Machine.X86
open import proof.Compiler.Operational.Adequacy.Common using (module Runs)
open import proof.Compiler.Operational.Adequacy.X86WF using (DefsWF)
open import Framework.ListUtil using (_‼_)
open import Framework.ListUtil using (‼-just; replicate-‼; reverse-‼-split; reverse-‼-suffix) public

open import Data.Integer using ()
open import Data.List.Properties using (length-replicate)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; _∸_; _⊔_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; ≤-pred; m≤n⇒m<n∨m≡n; <⇒≢; <-≤-trans; ≤-trans; n≤1+n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
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

blocks-inv : ∀ {T n} bs l {σ ρ φ d} → d ∈ blocks T n bs l σ ρ φ
  → Σ[ b ∈ Block ] Σ[ bs' ∈ List Block ] block-at bs l ≡ just (b , bs') × d ∈ ⟦ b ⟧ᵇ T n (blocks T n bs') σ ρ φ
blocks-inv (c ∷ bs) l d∈ with l ≟ length bs
... | yes _ = c , bs , refl , d∈
... | no _ = blocks-inv bs l d∈

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

{- every existing definition is a function -}
ν-table : ∀ (Ns : List Body) k → k < length Ns → ν ∈ table Ns k
ν-table (N ∷ Ns) k k< with k ≟ length Ns
... | yes _ = tt
... | no k≢ with m≤n⇒m<n∨m≡n (≤-pred k<)
...   | inj₁ lt = ν-table Ns k lt
...   | inj₂ eq = ⊥-elim (k≢ eq)

DefsWF-suffix : ∀ xs {Ns} → DefsWF (xs ++ Ns) → DefsWF Ns
DefsWF-suffix [] w = w
DefsWF-suffix (x ∷ xs) w = DefsWF-suffix xs (proj₂ w)
