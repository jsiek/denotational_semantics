{-# OPTIONS --allow-unsolved-metas #-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Filter.Domain.ISWIM.Domain as Domain
open import Compiler.Model.Filter.Domain.ISWIM.Ops as Ops
open import Compiler.Lang.Clos3 as Clos3
open import Compiler.Lang.Clos4 as Clos4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Compiler.Model.Filter.Sem.Clos3Iswim as Source
open import Compiler.Model.Filter.Sem.Clos4Iswim as Target
open import Compiler.Model.Filter.Sem.Clos4Good as Good
open import NewSemantics Clos4.Op Clos4.sig as Clos4Sem
open Clos4Sem.Semantics Clos4Iswim-Semantics renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open Clos4Sem.Semantics Clos4Good-Semantics renaming (⟦_⟧ to ⟦_⟧G; ⟦_⟧ₐ to ⟦_⟧ₐG; ⟦_⟧₊ to ⟦_⟧₊G)
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
  renaming (_≟_ to _n≟_)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; reduce)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; map⁻)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; suc; zero) renaming (_≟_ to _f≟_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary.Core using (Rel)
open import Data.Bool using (Bool; true; false)

module Compiler.Correctness.Delay.Goodness where

  un-left : Value → Value
  un-left (left d) = d
  un-left (u ⊔ v) = un-left u ⊔ un-left v
  un-left d = ω

  un-left-⊑ : ∀ {u v} → left u ⊑ v → u ⊑ un-left v
  un-left-⊑ (⊑-⊔-R1-å åu Lu⊑v) = ⊑-⊔-R1-å åu (un-left-⊑ Lu⊑v)
  un-left-⊑ (⊑-⊔-R2-å åu Lu⊑v) = ⊑-⊔-R2-å åu (un-left-⊑ Lu⊑v)
  un-left-⊑ (⊑-left-å åu Lu⊑v) = Lu⊑v
  un-left-⊑ (⊑-split (split-left split) Lu⊑v Lu⊑v₁) = ⊑-split split (un-left-⊑ Lu⊑v) (un-left-⊑ Lu⊑v₁)

  un-left-mono : ∀ {u v} → u ⊑ v → un-left u ⊑ un-left v
  un-left-mono ⊑-ω = ⊑-ω
  un-left-mono ⊑-ν-ν = ⊑-ω
  un-left-mono ⊑-ν-↦ = ⊑-ω
  un-left-mono ⊑-const = ⊑-ω
  un-left-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (un-left-mono u⊑v)
  un-left-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (un-left-mono u⊑v)
  un-left-mono (⊑-fst-å åu u⊑v) = ⊑-ω
  un-left-mono (⊑-snd-å åu u⊑v) = ⊑-ω
  un-left-mono (⊑-tup-å åu u⊑v) = ⊑-ω
  un-left-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
  un-left-mono (⊑-left-å åu u⊑v) = u⊑v
  un-left-mono (⊑-right-å åu u⊑v) = ⊑-ω
  un-left-mono (⊑-split split-⊔ u⊑v u⊑v₁) = ⊑-split split-⊔ (un-left-mono u⊑v) (un-left-mono u⊑v₁)
  un-left-mono (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-ω
  un-left-mono (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-ω
  un-left-mono (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-ω
  un-left-mono (⊑-split (split-tup split) u⊑v u⊑v₁) = ⊑-ω
  un-left-mono (⊑-split (split-left split) u⊑v u⊑v₁) = ⊑-split split (un-left-mono u⊑v) (un-left-mono u⊑v₁)
  un-left-mono (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-ω

  un-cdr : Value → Value
  un-cdr ∣ d ⦆ = d
  un-cdr (u ⊔ v) = un-cdr u ⊔ un-cdr v
  un-cdr d = ω

  un-cdr-⊑ : ∀ {u v} → ∣ u ⦆ ⊑ v → u ⊑ un-cdr v
  un-cdr-⊑ (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1-å åu (un-cdr-⊑ u⊑v)
  un-cdr-⊑ (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2-å åu (un-cdr-⊑ u⊑v)
  un-cdr-⊑ (⊑-snd-å åu u⊑v) = u⊑v
  un-cdr-⊑ (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-split split (un-cdr-⊑ u⊑v) (un-cdr-⊑ u⊑v₁)

  un-cdr-mono : ∀ {u v} → u ⊑ v → un-cdr u ⊑ un-cdr v
  un-cdr-mono ⊑-ω = ⊑-ω
  un-cdr-mono ⊑-ν-ν = ⊑-ω
  un-cdr-mono ⊑-ν-↦ = ⊑-ω
  un-cdr-mono ⊑-const = ⊑-ω
  un-cdr-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (un-cdr-mono u⊑v)
  un-cdr-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (un-cdr-mono u⊑v)
  un-cdr-mono (⊑-fst-å åu u⊑v) = ⊑-ω
  un-cdr-mono (⊑-snd-å åu u⊑v) = u⊑v
  un-cdr-mono (⊑-tup-å åu u⊑v) = ⊑-ω
  un-cdr-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
  un-cdr-mono (⊑-left-å åu u⊑v) = ⊑-ω
  un-cdr-mono (⊑-right-å åu u⊑v) = ⊑-ω
  un-cdr-mono (⊑-split split-⊔ u⊑v u⊑v₁) = ⊑-split split-⊔ (un-cdr-mono u⊑v) (un-cdr-mono u⊑v₁)
  un-cdr-mono (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-ω
  un-cdr-mono (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-ω
  un-cdr-mono (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-split split (un-cdr-mono u⊑v) (un-cdr-mono u⊑v₁)
  un-cdr-mono (⊑-split (split-tup split) u⊑v u⊑v₁) = ⊑-ω
  un-cdr-mono (⊑-split (split-left split) u⊑v u⊑v₁) = ⊑-ω
  un-cdr-mono (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-ω

{- V ↦ u -} {- un-↦ V ctxt -}
  un-↦ : Value → Value → Value
  un-↦ V (V' ↦ w) with V' ⊑? V
  ... | yes V'⊑V = w
  ... | no neq = ω
  un-↦ V (u ⊔ v) = un-↦ V u ⊔ un-↦ V v
  un-↦ V d = ω

  un-↦-⊑ : ∀ {V u v} → V ↦ u ⊑ v → u ⊑ un-↦ V v
  un-↦-⊑ (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1-å åu (un-↦-⊑ u⊑v)
  un-↦-⊑ (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2-å åu (un-↦-⊑ u⊑v)
  un-↦-⊑ {V} (⊑-↦-å {V} {u} {V'} åu₂ u⊑v u⊑v₁) with V' ⊑? V
  ... | no V'⋢V = ⊥-elim (V'⋢V u⊑v₁)
  ... | yes V'⊑V = u⊑v
  un-↦-⊑ (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-split split (un-↦-⊑ u⊑v) (un-↦-⊑ u⊑v₁)

{-
U ↦ u ⊑ V ↦ v

{- so u ⊑ v and V ⊑ U -}

w2 ⊑ w1

consider 

un-↦ w1 (U ↦ u)   and   un-↦ w2 (V ↦ v)


we check
  U ⊑? w1          and    V ⊑? w2

  no | _  then ⊑-ω
  yes | no then   u ⊑? ω
       ... need a contradiction
       -------------------------
     u ⊑ v , V ⊑ U , U ⊑ w1 , w2 ⊑ w1 , ¬ V ⊑ w2 , 
       --------------------------
-}


  un-↦-mono : ∀ {u v V V'} → u ⊑ v → V ⊑ V' → un-↦ V u ⊑ un-↦ V' v
  un-↦-mono ⊑-ω V'⊑V = ⊑-ω
  un-↦-mono ⊑-ν-ν V'⊑V = ⊑-ω
  un-↦-mono ⊑-ν-↦ V'⊑V = ⊑-ω
  un-↦-mono ⊑-const V'⊑V = ⊑-ω
  un-↦-mono (⊑-⊔-R1-å åu u⊑v) V'⊑V = ⊑-⊔-R1 (un-↦-mono u⊑v V'⊑V)
  un-↦-mono (⊑-⊔-R2-å åu u⊑v) V'⊑V = ⊑-⊔-R2 (un-↦-mono u⊑v V'⊑V)
  un-↦-mono (⊑-fst-å åu u⊑v) V'⊑V = ⊑-ω
  un-↦-mono (⊑-snd-å åu u⊑v) V'⊑V = ⊑-ω
  un-↦-mono (⊑-tup-å åu u⊑v) V'⊑V = ⊑-ω
  un-↦-mono {u₁ ↦ u₂}{v₁ ↦ v₂}{V}{V'} (⊑-↦-å åu₂ u⊑v u⊑v₁) V'⊑V 
    with u₁ ⊑? V | v₁ ⊑? V'
  ... | no u₁⋢ | _ = ⊑-ω
  ... | yes u₁⊑ | no v₁⋢ = ⊥-elim (v₁⋢ (⊑-trans (⊑-trans u⊑v₁ u₁⊑) V'⊑V))
  ... | yes u₁⊑ | yes v₁⊑ = u⊑v
  un-↦-mono (⊑-left-å åu u⊑v) V'⊑V = ⊑-ω
  un-↦-mono (⊑-right-å åu u⊑v) V'⊑V = ⊑-ω
  un-↦-mono (⊑-split split-⊔ u⊑v u⊑v₁) V'⊑V = 
    ⊑-split split-⊔ (un-↦-mono u⊑v V'⊑V) (un-↦-mono u⊑v₁ V'⊑V)
  un-↦-mono {u₁ ↦ u₂}{v}{V}{V'}(⊑-split (split-↦ split) u⊑v u⊑v₁) V'⊑V
    with u₁ ⊑? V
  ... | no u₁⋢ = ⊑-ω
  ... | yes u₁⊑ with un-↦-mono u⊑v V'⊑V | un-↦-mono u⊑v₁ V'⊑V 
  ... | u⊑v' | u⊑v₁' with u₁ ⊑? V
  ... | no u₁⋢ = ⊥-elim (u₁⋢ u₁⊑)
  ... | yes u₁⊑' = ⊑-split split u⊑v' u⊑v₁'
  un-↦-mono (⊑-split (split-fst split) u⊑v u⊑v₁) V'⊑V = ⊑-ω
  un-↦-mono (⊑-split (split-snd split) u⊑v u⊑v₁) V'⊑V = ⊑-ω
  un-↦-mono (⊑-split (split-tup split) u⊑v u⊑v₁) V'⊑V = ⊑-ω
  un-↦-mono (⊑-split (split-left split) u⊑v u⊑v₁) V'⊑V = ⊑-ω
  un-↦-mono (⊑-split (split-right split) u⊑v u⊑v₁) V'⊑V = ⊑-ω
  

  un-right : Value → Value
  un-right (right d) = d
  un-right (u ⊔ v) = un-right u ⊔ un-right v
  un-right d = ω

  un-right-⊑ : ∀ {u v} → right u ⊑ v → u ⊑ un-right v
  un-right-⊑ (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1-å åu (un-right-⊑ u⊑v)
  un-right-⊑ (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2-å åu (un-right-⊑ u⊑v)
  un-right-⊑ (⊑-right-å åu u⊑v) = u⊑v
  un-right-⊑ (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-split split (un-right-⊑ u⊑v) (un-right-⊑ u⊑v₁)

  un-right-mono : ∀ {u v} → u ⊑ v → un-right u ⊑ un-right v
  un-right-mono ⊑-ω = ⊑-ω
  un-right-mono ⊑-ν-ν = ⊑-ω
  un-right-mono ⊑-ν-↦ = ⊑-ω
  un-right-mono ⊑-const = ⊑-ω
  un-right-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (un-right-mono u⊑v)
  un-right-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (un-right-mono u⊑v)
  un-right-mono (⊑-fst-å åu u⊑v) = ⊑-ω
  un-right-mono (⊑-snd-å åu u⊑v) = ⊑-ω
  un-right-mono (⊑-tup-å åu u⊑v) = ⊑-ω
  un-right-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-left-å åu u⊑v) = ⊑-ω
  un-right-mono (⊑-right-å åu u⊑v) = u⊑v
  un-right-mono (⊑-split split-⊔ u⊑v u⊑v₁) = ⊑-split split-⊔ (un-right-mono u⊑v) (un-right-mono u⊑v₁)
  un-right-mono (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-split (split-tup split) u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-split (split-left split) u⊑v u⊑v₁) = ⊑-ω
  un-right-mono (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-split split (un-right-mono u⊑v) (un-right-mono u⊑v₁)

  un-tup : ∀ {n} → (i : Fin n) → Value → Value
  un-tup {n} i (tup[_]_ {n'} i' d) with n n≟ n'
  ... | no neq = ω
  ... | yes refl with i f≟ i'
  ... | yes refl = d
  ... | no neq = ω
  un-tup i (u ⊔ v) = un-tup i u ⊔ un-tup i v
  un-tup i d = ω

  un-tup-⊑ : ∀ {n} {i : Fin n} {u v} → tup[ i ] u ⊑ v → u ⊑ un-tup i v
  un-tup-⊑ (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1-å åu (un-tup-⊑ u⊑v)
  un-tup-⊑ (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2-å åu (un-tup-⊑ u⊑v)
  un-tup-⊑ {n}{i} (⊑-tup-å åu u⊑v) with n n≟ n 
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl with i f≟ i 
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl = u⊑v
  un-tup-⊑ (⊑-split (split-tup split) u⊑v u⊑v₁) = ⊑-split split (un-tup-⊑ u⊑v) (un-tup-⊑ u⊑v₁)

  un-tup-mono : ∀ {n}{i : Fin n}{u v} → u ⊑ v → un-tup i u ⊑ un-tup i v
  un-tup-mono ⊑-ω = ⊑-ω
  un-tup-mono ⊑-ν-ν = ⊑-ω
  un-tup-mono ⊑-ν-↦ = ⊑-ω
  un-tup-mono ⊑-const = ⊑-ω
  un-tup-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (un-tup-mono u⊑v)
  un-tup-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (un-tup-mono u⊑v)
  un-tup-mono (⊑-fst-å åu u⊑v) = ⊑-ω
  un-tup-mono (⊑-snd-å åu u⊑v) = ⊑-ω
  un-tup-mono {n}{i} (⊑-tup-å {n'}{i'} åu u⊑v) with n n≟ n'
  ... | no neq = ⊑-ω
  ... | yes refl with i f≟ i'
  ... | no neq = ⊑-ω
  ... | yes refl = u⊑v
  un-tup-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
  un-tup-mono (⊑-left-å åu u⊑v) = ⊑-ω
  un-tup-mono (⊑-right-å åu u⊑v) = ⊑-ω
  un-tup-mono (⊑-split split-⊔ u⊑v u⊑v₁) = ⊑-split split-⊔ (un-tup-mono u⊑v) (un-tup-mono u⊑v₁)
  un-tup-mono (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-ω
  un-tup-mono (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-ω
  un-tup-mono (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-ω
  un-tup-mono {n}{i} (⊑-split (split-tup {n'}{i'} split) u⊑v u⊑v₁)
     with n n≟ n'
  ... | no neq = ⊑-ω
  ... | yes refl with i f≟ i'   
  ... | no neq = ⊑-ω
  ... | yes refl with un-tup-mono {n}{i} u⊑v | un-tup-mono {n}{i} u⊑v₁
  ... | u⊑v' | u⊑v₁' with n n≟ n
  ... | no neq = ⊥-elim (neq refl)
  ... | yes refl with i f≟ i
  ... | no neqi = ⊥-elim (neqi refl)
  ... | yes refl = ⊑-split split u⊑v' u⊑v₁'
  un-tup-mono (⊑-split (split-left split) u⊑v u⊑v₁) = ⊑-ω
  un-tup-mono (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-ω

  un-car : Value → Value
  un-car ⦅ d ∣ = d
  un-car (u ⊔ v) = un-car u ⊔ un-car v
  un-car d = ω

  un-car-⊑ : ∀ {u v} → ⦅ u ∣ ⊑ v → u ⊑ un-car v
  un-car-⊑ (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1-å åu (un-car-⊑ u⊑v)
  un-car-⊑ (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2-å åu (un-car-⊑ u⊑v)
  un-car-⊑ (⊑-fst-å åu u⊑v) = u⊑v
  un-car-⊑ (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-split split (un-car-⊑ u⊑v) (un-car-⊑ u⊑v₁)

  un-car-mono : ∀ {u v} → u ⊑ v → un-car u ⊑ un-car v
  un-car-mono ⊑-ω = ⊑-ω
  un-car-mono ⊑-ν-ν = ⊑-ω
  un-car-mono ⊑-ν-↦ = ⊑-ω
  un-car-mono ⊑-const = ⊑-ω
  un-car-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (un-car-mono u⊑v)
  un-car-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (un-car-mono u⊑v)
  un-car-mono (⊑-fst-å åu u⊑v) = u⊑v
  un-car-mono (⊑-snd-å åu u⊑v) = ⊑-ω
  un-car-mono (⊑-tup-å åu u⊑v) = ⊑-ω
  un-car-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
  un-car-mono (⊑-left-å åu u⊑v) = ⊑-ω
  un-car-mono (⊑-right-å åu u⊑v) = ⊑-ω
  un-car-mono (⊑-split split-⊔ u⊑v u⊑v₁) = ⊑-split split-⊔ (un-car-mono u⊑v) (un-car-mono u⊑v₁)
  un-car-mono (⊑-split (split-↦ split) u⊑v u⊑v₁) = ⊑-ω
  un-car-mono (⊑-split (split-fst split) u⊑v u⊑v₁) = ⊑-split split (un-car-mono u⊑v) (un-car-mono u⊑v₁)
  un-car-mono (⊑-split (split-snd split) u⊑v u⊑v₁) = ⊑-ω
  un-car-mono (⊑-split (split-tup split) u⊑v u⊑v₁) = ⊑-ω
  un-car-mono (⊑-split (split-left split) u⊑v u⊑v₁) = ⊑-ω
  un-car-mono (⊑-split (split-right split) u⊑v u⊑v₁) = ⊑-ω

  {- Big idea: 
    ⦅ FV ↦ w ∣ ⊔ ∣ FV ⦆
        yes ( ∣ FV ⦆ ⊑ ctxt )
         -> ⦅ FV' ↦ w' ∣ ⊔ ∣ FV' ⦆
   
    left (u ⊔ v)  ->>  u    ( u ⊔ v )
    left u ⊔ left v  ->> u   ( u ⊔ v )
    

   fro (u ⊔ v) = fro u ⊔ fro v
   ⦅ (⦅ FV ↦ u ∣ ⊔ ∣ FV ⦆) ↦ w ∣ 

   ∣ ∣ FV ⦆ ⦆ 
    

  ((λ f (λ x (f x)))  id) 42



  -}

  mkGood : (ctxt : Value) → Value → Value
  mkGood ctxt ⦅ FV ↦ w ∣ with ∣ FV ⦆ ⊑? ctxt
  ... | yes FV⊑ctxt = ⦅ mkGood FV FV      {- ctxt =? (FV ⊔ un-cdr ctxt)-}
                        ↦ mkGood (un-↦ FV ctxt) w ∣   {- same ctxt here? -}
  ... | no FV⋢ctxt = ⦅ ν ∣
  mkGood ctxt (u ⊔ v) = mkGood ctxt u ⊔ mkGood ctxt v
  mkGood ctxt (V ↦ w) = mkGood V V ↦ mkGood (un-↦ V ctxt) w
  mkGood ctxt ω = ω
  mkGood ctxt ν = ν
  mkGood ctxt (const k) = const k
  mkGood ctxt ⦅ u ⊔ v ∣ = mkGood ctxt ⦅ u ∣ ⊔ mkGood ctxt ⦅ v ∣
  mkGood ctxt ⦅ v ∣ = ⦅ mkGood (un-cdr ctxt) v ∣
  mkGood ctxt ∣ v ⦆ = ∣ mkGood (un-cdr ctxt) v ⦆
  mkGood ctxt (tup[ i ] v) = tup[ i ] (mkGood (un-tup i ctxt) v)
  mkGood ctxt (left v) = left (mkGood (un-left ctxt) v)
  mkGood ctxt (right v) = right (mkGood (un-right ctxt) v)

  
  {-
  "un-↦ V v applies v to V"
  that is, it takes the codomains of all arrows in v that have a domain smaller than V
  -}

  counterexample :  ∀ {U u V v} → U ↦ u ⊑ V ↦ v →
        {- ==   "u ⊑ v × V ⊑ U" -}
     un-↦ U (U ↦ u ⊔ V ↦ v) ⊑ (un-↦ V (V ↦ v ⊔ U ↦ u))
    {- by V ⊑ U ==  "u ⊔ v ⊑ v"  -} 
  counterexample (⊑-↦-å åu₂ u⊑v V⊑U) = {!   !}
  counterexample (⊑-split split U↦u⊑V↦V U↦u⊑V↦V₁) = {!   !}

{- so we have u and v where u ⊑ v, ctxt-u ⊑ ctxt-v, but 
   the context of the codomain of u ⋢ the context of the codomain of v -}
{- in fact, we have guaranteed that 
  the ctxt of the codomain of v ⊑ the ctxt of the codomain of u -}

{- the problem is that if I am a smaller codomain,
   then I am evaluated in a larger context.

   --> U ↦ u ⊑ V ↦ v
   --> U ↦ u ⊔ V ↦ v ⊑ "--" (by refl)
   ctxt = ctxt' = U ↦ u ⊔ V ↦ v
   V ⊑ U

   u ⊑ v
   ctxt-u = un-↦ U ctxt = u ⊔ v
   ctxt-v = un-↦ V ctxt = v

   mkGood ctxt (U ↦ u) ⊑ mkGood ctxt' (V ↦ v)

     mkGood U U ↦ mkGood (un-↦ U ctxt) u 
   ⊑ mkGood V V ↦ mkGood (un-↦ V ctxt') v
  
     mkGood U U ↦ mkGood (u ⊔ v) u 
   ⊑ mkGood V V ↦ mkGood v v

  V ⊑ U
  mkGood V V ⊑ mkGood U U

   requirement:
   mkGood (u ⊔ v) u ⊑ 
   mkGood v v






   In the extreme, because we can inflate domains to be arbitrarily large,
   for the smaller value, the codomain can be guaranteed to be evaluated in the context of the entire
   codomain of its context. 
   Meanwhile, it is hard to state that the domain of an arrow being large enough
   to produce its codomain is enough to guarantee that it is large enough to produce
   the values needed to show that it's codomain is good.
   -}

  {- 
  but if we mkGood a codomain with ctxt itself, is this enough? 
  I'm going to try this in GoodnessNew.agda
   + For introduction cases, we're okay as long as mkGood works, even if it
     removes a lot of information from a lot of values.
   + For the purposes of elimination cases, we are producing a witness,
     and we can bring to bear the existence of values in a down-closed ⊔-closed denotation.
   + in this case, what this means is that if the context of the codomain of an arrow should be
    "un-↦ (dom arrow) context"
    then we're fine to set the context of the codomain as the codomain itself as long
    as we're guaranteed that given an arrow V ↦ w in context ctxt,
    then some arrow exists in the denotation equal to
    V ↦ (un-↦ V ctxt)
    
  -}


  mkGood-split-⊑ : ∀ ctxt {u uL uR} → uL ◃ u ▹ uR → mkGood ctxt u ⊑ mkGood ctxt uL ⊔ mkGood ctxt uR
  mkGood-split-⊑ ctxt split-⊔ = ⊑-refl
  mkGood-split-⊑ ctxt {V ↦ u} (split-↦ split) = ⊑-trans (⊑-↦ ⊑-refl (mkGood-split-⊑ (un-↦ V ctxt) split)) ⊑-dist-fun
  mkGood-split-⊑ ctxt (split-fst split) = mkGood-split-⊑-fst ctxt split (λ ctxt' → mkGood-split-⊑ ctxt' split)
    where 
    mkGood-split-⊑-fst : ∀ ctxt {u uL uR} → uL ◃ u ▹ uR → (IH : ∀ ctxt → mkGood ctxt u ⊑ mkGood ctxt uL ⊔ mkGood ctxt uR) 
       → mkGood ctxt ⦅ u ∣ ⊑ mkGood ctxt ⦅ uL ∣ ⊔ mkGood ctxt ⦅ uR ∣
    mkGood-split-⊑-fst ctxt split-⊔ IH = ⊑-refl
    mkGood-split-⊑-fst ctxt {V ↦ u} (split-↦ split) IH with ∣ V ⦆ ⊑? ctxt
    ... | yes V⊑ctxt = ⊑-trans (⊑-fst (IH ctxt)) ⊑-dist-fst
    ... | no V⋢ctxt = ⊑-⊔-R1 ⊑-refl
    mkGood-split-⊑-fst ctxt (split-fst split) IH = ⊑-trans (⊑-fst (IH (un-cdr ctxt))) ⊑-dist-fst
    mkGood-split-⊑-fst ctxt (split-snd split) IH = ⊑-trans (⊑-fst (IH (un-cdr ctxt))) ⊑-dist-fst
    mkGood-split-⊑-fst ctxt (split-tup split) IH = ⊑-trans (⊑-fst (IH (un-cdr ctxt))) ⊑-dist-fst
    mkGood-split-⊑-fst ctxt (split-left split) IH = ⊑-trans (⊑-fst (IH (un-cdr ctxt))) ⊑-dist-fst
    mkGood-split-⊑-fst ctxt (split-right split) IH = ⊑-trans (⊑-fst (IH (un-cdr ctxt))) ⊑-dist-fst
  mkGood-split-⊑ ctxt (split-snd split) = ⊑-trans (⊑-snd (mkGood-split-⊑ (un-cdr ctxt) split)) ⊑-dist-snd
  mkGood-split-⊑ ctxt (split-tup {n}{i} split) = ⊑-trans (⊑-tup (mkGood-split-⊑ (un-tup i ctxt) split)) ⊑-dist-tup
  mkGood-split-⊑ ctxt (split-left split) = ⊑-trans (⊑-left (mkGood-split-⊑ (un-left ctxt) split)) ⊑-dist-left
  mkGood-split-⊑ ctxt (split-right split) = ⊑-trans (⊑-right (mkGood-split-⊑ (un-right ctxt) split)) ⊑-dist-right
  
  ω⊑mkGoodcar : ∀ {ctxt d} → ⦅ ω ∣ ⊑ mkGood ctxt ⦅ d ∣
  ω⊑mkGoodcar {ctxt} {ω} = ⊑-refl
  ω⊑mkGoodcar {ctxt} {ν} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {const k} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {d ⊔ d₁} = ⊑-⊔-R1 (ω⊑mkGoodcar {ctxt} {d})
  ω⊑mkGoodcar {ctxt} {d ↦ d₁} with ∣ d ⦆ ⊑? ctxt
  ... | yes good-↦ = ⊑-fst ⊑-ω
  ... | no bad-↦ = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {⦅ d ∣} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {∣ d ⦆} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {tup[ i ] d} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {left d} = ⊑-fst ⊑-ω
  ω⊑mkGoodcar {ctxt} {right d} = ⊑-fst ⊑-ω

  ν⊑mkGoodcar : ∀ {ctxt d} → ν ⊑ d → ⦅ ν ∣ ⊑ mkGood ctxt ⦅ d ∣
  ν⊑mkGoodcar {ctxt} {.ν} ⊑-ν-ν = ⊑-refl
  ν⊑mkGoodcar {ctxt} {V ↦ d} ⊑-ν-↦ with ∣ V ⦆ ⊑? ctxt
  ... | no V⋢ctxt = ⊑-refl
  ... | yes V⊑ctxt = ⊑-fst ⊑-ν-↦
  ν⊑mkGoodcar {ctxt} {v ⊔ w} (⊑-⊔-R1-å åu ν⊑v) = ⊑-⊔-R1 (ν⊑mkGoodcar ν⊑v)
  ν⊑mkGoodcar {ctxt} {v ⊔ w} (⊑-⊔-R2-å åu ν⊑w) = ⊑-⊔-R2 (ν⊑mkGoodcar ν⊑w)

  mkGood-ctxt : ∀ ctxt ctxt' d → ctxt ⊑ ctxt' → mkGood ctxt d ⊑ mkGood ctxt' d
  mkGood-ctxt ctxt ctxt' ω ctxt⊑ = ⊑-ω
  mkGood-ctxt ctxt ctxt' ν ctxt⊑ = ⊑-ν-ν
  mkGood-ctxt ctxt ctxt' (const k) ctxt⊑ = ⊑-const
  mkGood-ctxt ctxt ctxt' (d ⊔ d₁) ctxt⊑ = 
    ⊔⊑⊔ (mkGood-ctxt ctxt ctxt' d ctxt⊑) (mkGood-ctxt ctxt ctxt' d₁ ctxt⊑)
  mkGood-ctxt ctxt ctxt' (d ↦ d₁) ctxt⊑ = 
    ⊑-↦ ⊑-refl (mkGood-ctxt (un-↦ d ctxt) (un-↦ d ctxt') d₁ (un-↦-mono ctxt⊑ ⊑-refl))
  mkGood-ctxt ctxt ctxt' ⦅ d ∣ ctxt⊑ = mkGood-ctxt-car ctxt ctxt' d ctxt⊑
    where
    mkGood-ctxt-car : ∀ ctxt ctxt' d → ctxt ⊑ ctxt' → mkGood ctxt ⦅ d ∣ ⊑ mkGood ctxt' ⦅ d ∣
    mkGood-ctxt-car ctxt ctxt' ω ctxt⊑ = ⊑-refl
    mkGood-ctxt-car ctxt ctxt' ν ctxt⊑ = ⊑-refl
    mkGood-ctxt-car ctxt ctxt' (const k) ctxt⊑ = ⊑-refl
    mkGood-ctxt-car ctxt ctxt' (d ⊔ d₁) ctxt⊑ = 
      ⊔⊑⊔ (mkGood-ctxt-car ctxt ctxt' d ctxt⊑) (mkGood-ctxt-car ctxt ctxt' d₁ ctxt⊑)
    mkGood-ctxt-car ctxt ctxt' (FV ↦ w) ctxt⊑ with ∣ FV ⦆ ⊑? ctxt
    ... | no FV⋢ctxt = ν⊑mkGoodcar ⊑-ν-↦
    ... | yes FV⊑ctxt with ∣ FV ⦆ ⊑? ctxt'
    ... | no FV⋢ctxt' = ⊥-elim (FV⋢ctxt' (⊑-trans FV⊑ctxt ctxt⊑))
    ... | yes FV⊑ctxt'
      = ⊑-fst (⊑-↦ ⊑-refl (mkGood-ctxt (un-↦ FV ctxt) (un-↦ FV ctxt') w (un-↦-mono ctxt⊑ ⊑-refl)))
    mkGood-ctxt-car ctxt ctxt' ⦅ d ∣ ctxt⊑ = 
      ⊑-fst (mkGood-ctxt-car (un-cdr ctxt) (un-cdr ctxt') d 
                                  (un-cdr-mono ctxt⊑))
    mkGood-ctxt-car ctxt ctxt' ∣ d ⦆ ctxt⊑ = 
      ⊑-fst (⊑-snd (mkGood-ctxt (un-cdr (un-cdr ctxt)) (un-cdr (un-cdr ctxt')) 
                                 d (un-cdr-mono (un-cdr-mono ctxt⊑))))
    mkGood-ctxt-car ctxt ctxt' (tup[ i ] d) ctxt⊑ = 
      ⊑-fst (⊑-tup (mkGood-ctxt (un-tup i (un-cdr ctxt)) (un-tup i (un-cdr ctxt')) d 
                                     (un-tup-mono (un-cdr-mono ctxt⊑))))
    mkGood-ctxt-car ctxt ctxt' (left d) ctxt⊑ = 
      ⊑-fst (⊑-left (mkGood-ctxt (un-left (un-cdr ctxt)) (un-left (un-cdr ctxt')) d 
                                      (un-left-mono (un-cdr-mono ctxt⊑))))
    mkGood-ctxt-car ctxt ctxt' (right d) ctxt⊑ = 
      ⊑-fst (⊑-right (mkGood-ctxt (un-right (un-cdr ctxt)) (un-right (un-cdr ctxt')) d 
                                       (un-right-mono (un-cdr-mono ctxt⊑))))
  mkGood-ctxt ctxt ctxt' ∣ d ⦆ ctxt⊑ = 
    ⊑-snd (mkGood-ctxt (un-cdr ctxt) (un-cdr ctxt') d (un-cdr-mono ctxt⊑))
  mkGood-ctxt ctxt ctxt' (tup[ i ] d) ctxt⊑ = 
    ⊑-tup (mkGood-ctxt (un-tup i ctxt) (un-tup i ctxt') d (un-tup-mono ctxt⊑))
  mkGood-ctxt ctxt ctxt' (left d) ctxt⊑ = 
    ⊑-left (mkGood-ctxt (un-left ctxt) (un-left ctxt') d (un-left-mono ctxt⊑))
  mkGood-ctxt ctxt ctxt' (right d) ctxt⊑ = 
    ⊑-right (mkGood-ctxt (un-right ctxt) (un-right ctxt') d (un-right-mono ctxt⊑))
  
  mkGood-mono-ctxt : ∀ ctxt ctxt' d d' → ctxt ⊑ ctxt' → d ⊑ d' → mkGood ctxt d ⊑ mkGood ctxt' d'
  mkGood-mono-ctxt ctxt ctxt' .ω d' ctxt⊑ ⊑-ω = ⊑-ω
  mkGood-mono-ctxt ctxt ctxt' .ν .ν ctxt⊑ ⊑-ν-ν = ⊑-ν-ν
  mkGood-mono-ctxt ctxt ctxt' .ν .(_ ↦ _) ctxt⊑ ⊑-ν-↦ = ⊑-ν-↦
  mkGood-mono-ctxt ctxt ctxt' .(const _) .(const _) ctxt⊑ ⊑-const = ⊑-const
  mkGood-mono-ctxt ctxt ctxt' d (u ⊔ v) ctxt⊑ (⊑-⊔-R1-å åu d⊑u) = ⊑-⊔-R1 (mkGood-mono-ctxt ctxt ctxt' d u ctxt⊑ d⊑u)
  mkGood-mono-ctxt ctxt ctxt' d (u ⊔ v) ctxt⊑ (⊑-⊔-R2-å åu d⊑v) = ⊑-⊔-R2 (mkGood-mono-ctxt ctxt ctxt' d v ctxt⊑ d⊑v)
  mkGood-mono-ctxt ctxt ctxt' (⦅ d ∣) (⦅ d' ∣) ctxt⊑ (⊑-fst-å åu d⊑) = 
    mkGood-mono-ctxt-fst ctxt ctxt' d d' ctxt⊑ d⊑
    where
    mkGood-mono-ctxt-fst : ∀ ctxt ctxt' d d' → ctxt ⊑ ctxt' → d ⊑ d' 
       → mkGood ctxt ⦅ d ∣ ⊑ mkGood ctxt' ⦅ d' ∣
    mkGood-mono-ctxt-fst ctxt ctxt' .ω d' ctxt⊑ ⊑-ω = ω⊑mkGoodcar {ctxt'}{d'}
    mkGood-mono-ctxt-fst ctxt ctxt' .ν .ν ctxt⊑ ⊑-ν-ν = ⊑-refl
    mkGood-mono-ctxt-fst ctxt ctxt' .ν .(_ ↦ _) ctxt⊑ ⊑-ν-↦ = ν⊑mkGoodcar ⊑-ν-↦
    mkGood-mono-ctxt-fst ctxt ctxt' .(const _) .(const _) ctxt⊑ ⊑-const = ⊑-refl
    mkGood-mono-ctxt-fst ctxt ctxt' d (v ⊔ w) ctxt⊑ (⊑-⊔-R1-å åu d⊑) = 
      ⊑-⊔-R1 (mkGood-mono-ctxt-fst ctxt ctxt' d v ctxt⊑ d⊑)
    mkGood-mono-ctxt-fst ctxt ctxt' d (v ⊔ w) ctxt⊑ (⊑-⊔-R2-å åu d⊑) = 
      ⊑-⊔-R2 (mkGood-mono-ctxt-fst ctxt ctxt' d w ctxt⊑ d⊑)
    mkGood-mono-ctxt-fst ctxt ctxt' (⦅ u ∣) (⦅ v ∣) ctxt⊑ (⊑-fst-å åu d⊑) = 
      ⊑-fst (mkGood-mono-ctxt-fst (un-cdr ctxt) (un-cdr ctxt') u v 
                                  (un-cdr-mono ctxt⊑) d⊑)
    mkGood-mono-ctxt-fst ctxt ctxt' (∣ u ⦆) (∣ v ⦆) ctxt⊑ (⊑-snd-å åu d⊑) = 
      ⊑-fst (⊑-snd (mkGood-mono-ctxt (un-cdr (un-cdr ctxt)) (un-cdr (un-cdr ctxt')) u v 
                                     (un-cdr-mono (un-cdr-mono ctxt⊑)) d⊑))
    mkGood-mono-ctxt-fst ctxt ctxt' (tup[ i ] u) (tup[ i ] v) ctxt⊑ (⊑-tup-å åu d⊑) = 
      ⊑-fst (⊑-tup (mkGood-mono-ctxt (un-tup i (un-cdr ctxt)) (un-tup i (un-cdr ctxt')) u v 
                                     (un-tup-mono (un-cdr-mono ctxt⊑)) d⊑))
    mkGood-mono-ctxt-fst ctxt ctxt' (U ↦ u) (V ↦ v) ctxt⊑ (⊑-↦-å åu₂ d⊑ d⊑₁) with
      ∣ U ⦆ ⊑? ctxt
    ... | no U⋢ctxt = ν⊑mkGoodcar ⊑-ν-↦
    ... | yes U⊑ctxt with ∣ V ⦆ ⊑? ctxt'
    ... | no V⋢ctxt' = ⊥-elim (V⋢ctxt' (⊑-trans (⊑-snd d⊑₁) (⊑-trans U⊑ctxt ctxt⊑)))
    ... | yes V⊑ctxt' = ⊑-fst (⊑-↦ (mkGood-mono-ctxt V U V U d⊑₁ d⊑₁) 
                                    (mkGood-mono-ctxt (un-↦ U ctxt) (un-↦ V ctxt') u v (un-↦-mono ctxt⊑ {! d⊑₁  !}) d⊑))
    mkGood-mono-ctxt-fst ctxt ctxt' (left u) (left v) ctxt⊑ (⊑-left-å åu d⊑) = 
      ⊑-fst (⊑-left (mkGood-mono-ctxt (un-left (un-cdr ctxt)) (un-left (un-cdr ctxt')) u v 
                                      (un-left-mono (un-cdr-mono ctxt⊑)) d⊑))
    mkGood-mono-ctxt-fst ctxt ctxt' (right u) (right v) ctxt⊑ (⊑-right-å åu d⊑) = 
      ⊑-fst (⊑-right (mkGood-mono-ctxt (un-right (un-cdr ctxt)) (un-right (un-cdr ctxt')) u v 
                                       (un-right-mono (un-cdr-mono ctxt⊑)) d⊑))
    mkGood-mono-ctxt-fst ctxt ctxt' d d' ctxt⊑ (⊑-split {d}{dL}{dR} split d⊑ d⊑₁) = 
      ⊑-trans (mkGood-split-⊑ ctxt (split-fst split)) 
              (⊑-⊔-L (mkGood-mono-ctxt-fst ctxt ctxt' dL d' ctxt⊑ d⊑) 
                     (mkGood-mono-ctxt-fst ctxt ctxt' dR d' ctxt⊑ d⊑₁))
  mkGood-mono-ctxt ctxt ctxt' (∣ d ⦆) (∣ d' ⦆) ctxt⊑ (⊑-snd-å åu d⊑) = 
    ⊑-snd (mkGood-mono-ctxt (un-cdr ctxt) (un-cdr ctxt') d d' (un-cdr-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' (tup[ i ] d) (tup[ i ] d') ctxt⊑ (⊑-tup-å åu d⊑) = 
    ⊑-tup (mkGood-mono-ctxt (un-tup i ctxt) (un-tup i ctxt') d d' (un-tup-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' (V ↦ w) (V' ↦ w') ctxt⊑ (⊑-↦-å åu₂ w⊑w' V'⊑V) = 
    ⊑-↦ (mkGood-mono-ctxt V' V V' V V'⊑V V'⊑V) 
         (mkGood-mono-ctxt (un-↦ V ctxt) (un-↦ V' ctxt') w w' 
                           {!   !}
                           w⊑w')
  mkGood-mono-ctxt ctxt ctxt' (left d) (left d') ctxt⊑ (⊑-left-å åu d⊑) = 
    ⊑-left (mkGood-mono-ctxt (un-left ctxt) (un-left ctxt') d d' (un-left-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' (right d) (right d') ctxt⊑ (⊑-right-å åu d⊑) = 
    ⊑-right (mkGood-mono-ctxt (un-right ctxt) (un-right ctxt') d d' (un-right-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' d d' ctxt⊑ (⊑-split {u}{uL}{uR} split d⊑ d⊑₁) = 
    ⊑-trans (mkGood-split-⊑ ctxt split) (⊑-⊔-L (mkGood-mono-ctxt ctxt ctxt' uL d' ctxt⊑ d⊑) 
                                                (mkGood-mono-ctxt ctxt ctxt' uR d' ctxt⊑ d⊑₁))

  mkGood-mono : ∀ ctxt ctxt' d d' → d ⊑ d' → ctxt ⊑ ctxt' × ctxt' ⊑ ctxt → mkGood ctxt d ⊑ mkGood ctxt' d'
  mkGood-mono ctxt ctxt' .ω d' ⊑-ω ctxt≃ = ⊑-ω
  mkGood-mono ctxt ctxt' .ν .ν ⊑-ν-ν ctxt≃ = ⊑-ν-ν
  mkGood-mono ctxt ctxt' .ν .(_ ↦ _) ⊑-ν-↦ ctxt≃ = ⊑-ν-↦
  mkGood-mono ctxt ctxt' .(const _) .(const _) ⊑-const ctxt≃ = ⊑-const
  mkGood-mono ctxt ctxt' d (v ⊔ w) (⊑-⊔-R1-å åu d⊑) ctxt≃ = 
    ⊑-⊔-R1 (mkGood-mono ctxt ctxt' d v d⊑ ctxt≃)
  mkGood-mono ctxt ctxt' d (v ⊔ w) (⊑-⊔-R2-å åu d⊑) ctxt≃ = 
    ⊑-⊔-R2 (mkGood-mono ctxt ctxt' d w d⊑ ctxt≃)
  mkGood-mono ctxt ctxt' ⦅ u ∣ ⦅ v ∣ (⊑-fst-å åu d⊑) ctxt≃ = {!  !}
  mkGood-mono ctxt ctxt' ∣ u ⦆ ∣ v ⦆ (⊑-snd-å åu d⊑) ctxt≃ = 
    ⊑-snd (mkGood-mono (un-cdr ctxt) (un-cdr ctxt') u v d⊑ ⟨ un-cdr-mono (proj₁ ctxt≃) , un-cdr-mono (proj₂ ctxt≃) ⟩)
  mkGood-mono ctxt ctxt' (tup[ i ] u) (tup[ i ] v) (⊑-tup-å åu d⊑) ctxt≃ = 
    ⊑-tup (mkGood-mono (un-tup i ctxt) (un-tup i ctxt') u v d⊑ ⟨ un-tup-mono (proj₁ ctxt≃) , un-tup-mono (proj₂ ctxt≃) ⟩)
  mkGood-mono ctxt ctxt' (U ↦ u) (V ↦ v) (⊑-↦-å åu₂ d⊑ d⊑₁) ctxt≃ = 
    ⊑-↦ {! mkGood-mono V U V U d⊑₁   !} {!   !}

  {- 
    ⊑-↦ (mkGood-mono V U V U d⊑₁ {!   !}) (mkGood-mono (un-↦ U ctxt) (un-↦ V ctxt') u v d⊑ 
         ⟨ un-↦-mono (proj₁ ctxt≃) {!   !} , un-↦-mono (proj₂ ctxt≃) d⊑₁ ⟩)
         -}
  mkGood-mono ctxt ctxt' (left u) (left v) (⊑-left-å åu d⊑) ctxt≃ = 
    ⊑-left (mkGood-mono (un-left ctxt) (un-left ctxt') u v d⊑ ⟨ un-left-mono (proj₁ ctxt≃) , un-left-mono (proj₂ ctxt≃) ⟩)
  mkGood-mono ctxt ctxt' (right u) (right v) (⊑-right-å åu d⊑) ctxt≃ =
    ⊑-right (mkGood-mono (un-right ctxt) (un-right ctxt') u v d⊑ ⟨ un-right-mono (proj₁ ctxt≃) , un-right-mono (proj₂ ctxt≃) ⟩)
  mkGood-mono ctxt ctxt' d d' (⊑-split {d}{dL}{dR} split d⊑ d⊑₁) ctxt≃ = 
    ⊑-trans (mkGood-split-⊑ ctxt split) (⊑-⊔-L (mkGood-mono ctxt ctxt' dL d' d⊑ ctxt≃) 
                                                (mkGood-mono ctxt ctxt' dR d' d⊑₁ ctxt≃))

  {-
  mkGood-mono : ∀ ctxt ctxt' d d' → d ⊑ d' → ctxt ⊑ ctxt' → mkGood ctxt d ⊑ mkGood ctxt' d'

  doesn't work: (env-map (λ d → mkGood d d) ρ)
  -}

  {-
  ⦅ V ↦ w ∣    ⦅ V ↦ w ∣
  
  -}

  Target-to-Good : ∀ M ρ d ctxt 
        → d ∈ ⟦ delay M ⟧' ρ → ctxt ∈ ⟦ delay M ⟧' ρ
        → d ⊑ ctxt
        → ∀ ρ'
          → (ρ~ : ∀ i d ctxt → d ∈ ρ i 
                             → ctxt ∈ ρ i 
                             → d ⊑ ctxt  {- this condition might not be necessary -}
                             → mkGood ctxt d ∈ ρ' i)
          → mkGood ctxt d ∈ ⟦ delay M ⟧G ρ'
  Target-to-Good (` x) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = ρ~ x d ctxt d∈ ctxt∈ d⊑ctxt
  Target-to-Good (clos-op x₁ ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (app ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (lit B k ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (tuple x₁ ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (get i ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ ω ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = 
    Target-to-Good M ρ ω ω d∈ d∈ ⊑-ω ρ' ρ~
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ (left d) ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = 
    Target-to-Good M ρ d (un-left ctxt) d∈ {!   !} (un-left-⊑ d⊑ctxt) ρ' ρ~  {- will need join-closed-ness -}
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ v) ctxt ⟨ u∈ , v∈ ⟩ ctxt∈ d⊑ctxt ρ' ρ~ = 
    ⟨ Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ u ctxt u∈ ctxt∈ (proj₁ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ 
    , Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ v ctxt v∈ ctxt∈ (proj₂ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ ⟩
  Target-to-Good (inr-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (case-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  
  {- Let's try to make this a function
  data mkGood : (ctxt : Value) → (input : Value) → (output : Value) → Set where
    mkGood-base-keep : ∀ {ctxt FV FV' w w'}
                    → (cond : ∣ FV ⦆ ⊑ ctxt)
                    → mkGood (FV ⊔ (un-cdr ctxt)) FV FV'
                    → mkGood (un-↦ (FV ⊔ (un-cdr ctxt)) ctxt) w w'
                    → mkGood ctxt ⦅ FV ↦ w ∣ ⦅ FV' ↦ w' ∣
    mkGood-base-toss : ∀ {ctxt FV w}
                   → (¬cond : ¬ (∣ FV ⦆ ⊑ ctxt))
                   → mkGood ctxt ⦅ FV ↦ w ∣ ⦅ ν ∣
    mkGood-↦ : ∀ {ctxt V V' w w'}
              → mkGood V V V'
              → mkGood (un-↦ V ctxt) w w'
              → mkGood ctxt (V ↦ w) (V' ↦ w')
    mkGood-⊔ : ∀ {ctxt u v u' v'}
             → mkGood ctxt u u'
             → mkGood ctxt v v'
             → mkGood ctxt (u ⊔ v) (u' ⊔ v')
    mkGood-left : ∀ {ctxt d d'}
                → mkGood (un-left ctxt) d d'
                → mkGood ctxt (left d) (left d')
 

  {- what does a theorem statement look like? -}
  Target-to-Good : ∀ M ρ d ctxt 
        → d ∈ ⟦ delay M ⟧' ρ → ctxt ∈ ⟦ delay M ⟧' ρ
        → d ⊑ ctxt
        → ∀ d' ρ'
          → (d~ : mkGood ctxt d d')
          → (ρ~ : ∀ i d ctxt d' → d ∈ ρ i 
                                → ctxt ∈ ρ i 
                                → d ⊑ ctxt 
                                → mkGood ctxt d d'
                                → d' ∈ ρ' i)
          → d' ∈ ⟦ delay M ⟧G ρ'
  Target-to-Good (` x) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = ρ~ x d ctxt d' d∈ ctxt∈ d⊑ctxt d~
  Target-to-Good (clos-op x₁ ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (app ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (lit B k ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (tuple x₁ ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (get i ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (inl-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (inr-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (case-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  -}


  {- what does a monotonicity condition look like? -}


{- EXTRA attempts

   data _good-with_ : Value → Value → Set where
    good-base : ∀ {FV u v} 
             → ∣ FV ⦆ ⊑ v
             → ⦅ FV ↦ u ∣ good-with v
    good-⊔-R1 : ∀ {u v₁ v₂}   {- could try to define this using atomicity and splitting            -}
             → u good-with v₁
             → u good-with (v₁ ⊔ v₂)
    good-⊔-R2 : ∀ {u v₁ v₂}
             → u good-with v₂
             → u good-with (v₁ ⊔ v₂)
    good-⊔-L : ∀ {u₁ u₂ v}
             → (u₁ ⊔ u₂) good-with v
    good-↦ : ∀ {V w v}
            → w good-with v
            → (V ↦ w) good-with (V ↦ v)   {- could do V V' V⊑V' (V' ↦ v) -}
    good-car : ∀ {u v} → u good-with v
            → ⦅ u ∣ good-with ⦅ v ∣
    good-cdr : ∀ {u v} → u good-with v
            → ∣ u ⦆ good-with ∣ v ⦆
    good-tup : ∀ {n}{i : Fin n}{u v} → u good-with v 
            → (tup[ i ] u) good-with (tup[ i ] v)
    good-left : ∀ {u v} → u good-with v 
             → (left u) good-with (left v)
    good-right : ∀ {u v} → u good-with v 
              → (right u) good-with (right v) 



  data hasF : Value → Set where
    hasF-base : ∀ {FV u} → hasF ⦅ FV ↦ u ∣
    hasF-⊔-L : ∀ {u v} → hasF u → hasF (u ⊔ v)
    hasF-⊔-R : ∀ {u v} → hasF v → hasF (u ⊔ v)
    hasF-left : ∀ {v} → hasF v → hasF (left v)
  
  hasF? : ∀ (v : Value) → Dec (hasF v)
  hasF? v = {!   !}

  _applies-to_ : ∀ {u} → (𝕗u : hasF u) → Value → Set
  (hasF-base {FV}{u}) applies-to v = ∣ FV ⦆ ⊑ v
  (hasF-⊔-L 𝕗u) applies-to v = 𝕗u applies-to v
  (hasF-⊔-R 𝕗u) applies-to v = 𝕗u applies-to v
  (hasF-left 𝕗u) applies-to v = 𝕗u applies-to (un-left v)


  _applies-to?_ : ∀ {u}(𝕗u : hasF u) (v : Value) → Dec (𝕗u applies-to v)
  hasF-base {FV} applies-to? v = ∣ FV ⦆ ⊑? v
  hasF-⊔-L 𝕗u applies-to? v = 𝕗u applies-to? v
  hasF-⊔-R 𝕗u applies-to? v = 𝕗u applies-to? v
  hasF-left 𝕗u applies-to? v = 𝕗u applies-to? (un-left v)







  -}   