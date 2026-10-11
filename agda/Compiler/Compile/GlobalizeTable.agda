{-

  The table of global definitions that the globalize pass threads through
  the term only grows (_⊑_: ds' extends ds with newer definitions), and a
  definition stays where it is as the table grows (global-⊑). Shared by
  the CompCert-style and CakeML-style proofs of globalize and by the
  adequacy proof for Clos5.

-}

module Compiler.Compile.GlobalizeTable where

open import Compiler.Lang.Clos4
open import Compiler.Lang.Clos5 using (global)
open import Compiler.Compile.Globalize
open import Compiler.Lang.ListUtil using (_‼_; ‼-++)

open import Data.List using ([]; _∷_; _++_; [_]; length; reverse)
open import Data.List.Properties using (++-assoc; reverse-++; unfold-reverse; length-reverse)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

infix 4 _⊑_

{- ds ⊑ ds': ds' extends ds with newer definitions -}
_⊑_ : Defs → Defs → Set
ds ⊑ ds' = Σ[ xs ∈ Defs ] ds' ≡ xs ++ ds

⊑-refl : ∀ {ds} → ds ⊑ ds
⊑-refl = [] , refl

⊑-trans : ∀ {ds₁ ds₂ ds₃} → ds₁ ⊑ ds₂ → ds₂ ⊑ ds₃ → ds₁ ⊑ ds₃
⊑-trans {ds₁} (xs , refl) (ys , refl) = ys ++ xs , sym (++-assoc ys xs ds₁)

⊑-∷ : ∀ {d ds ds'} → ds ⊑ ds' → ds ⊑ d ∷ ds'
⊑-∷ {d} (xs , refl) = d ∷ xs , refl

∷-⊑ : ∀ {d ds ds'} → d ∷ ds ⊑ ds' → ds ⊑ ds'
∷-⊑ {d} {ds} (xs , refl) = xs ++ [ d ] , sym (++-assoc xs [ d ] ds)

{- the pass only adds definitions -}
glob-grows : ∀ M ds → ds ⊑ proj₂ (glob M ds)
glob-grows-arg : ∀ {b} (a : Arg b) ds → ds ⊑ proj₂ (glob-arg a ds)
glob-grows-args : ∀ {bs} (args : Args bs) ds → ds ⊑ proj₂ (glob-args args ds)

glob-grows (` x) ds = ⊑-refl
glob-grows (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds = ⊑-∷ (glob-grows N ds)
glob-grows (app ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (lit B k ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (pair-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (fst-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (snd-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (tuple n ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (get i ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (inl-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (inr-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (case-op ⦅ args ⦆) ds = glob-grows-args args ds
glob-grows (let-op ⦅ args ⦆) ds = glob-grows-args args ds

glob-grows-arg (ast M) ds = glob-grows M ds
glob-grows-arg (bind a) ds = glob-grows-arg a ds
glob-grows-arg (clear a) ds = glob-grows-arg a ds

glob-grows-args nil ds = ⊑-refl
glob-grows-args (cons a args) ds =
  ⊑-trans (glob-grows-arg a ds) (glob-grows-args args (proj₂ (glob-arg a ds)))

{- a definition stays where it is as the table grows -}
global-⊑ : ∀ {d ds ds'} → d ∷ ds ⊑ ds' → global ds' (length ds) ≡ just d
global-⊑ {d} {ds} (xs , refl) =
  trans (cong (_‼ length ds)
          (trans (reverse-++ xs (d ∷ ds))
            (trans (cong (_++ reverse xs) (unfold-reverse d ds))
                   (++-assoc (reverse ds) [ d ] (reverse xs)))))
        (subst (λ n → (reverse ds ++ d ∷ reverse xs) ‼ n ≡ just d)
               (length-reverse ds) (‼-++ (reverse ds)))
