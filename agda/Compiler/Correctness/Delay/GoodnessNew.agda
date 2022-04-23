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

module Compiler.Correctness.Delay.GoodnessNew where

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

  un-left-ℒ : ∀ {D} → (⊔-closed D) → ∀ d → d ∈ ℒ ⟨ D , ptt ⟩ → un-left d ∈ D
  un-left-ℒ ⊔D ω d∈ = d∈
  un-left-ℒ ⊔D (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⊔D (un-left u) (un-left v) (un-left-ℒ ⊔D u u∈) (un-left-ℒ ⊔D v v∈)
  un-left-ℒ ⊔D (left d) d∈ = d∈

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
                        ↦ mkGood w w ∣   {- same ctxt here? -}
  ... | no FV⋢ctxt = ⦅ ν ∣
  mkGood ctxt (u ⊔ v) = mkGood ctxt u ⊔ mkGood ctxt v
  mkGood ctxt (V ↦ w) = mkGood V V ↦ mkGood w w {- context for w: un-↦ V ctxt ?? -}
  mkGood ctxt ω = ω
  mkGood ctxt ν = ν
  mkGood ctxt (const k) = const k
  mkGood ctxt ⦅ u ⊔ v ∣ = mkGood ctxt ⦅ u ∣ ⊔ mkGood ctxt ⦅ v ∣
  mkGood ctxt ⦅ v ∣ = ⦅ mkGood (un-cdr ctxt) v ∣
  mkGood ctxt ∣ v ⦆ = ∣ mkGood (un-cdr ctxt) v ⦆
  mkGood ctxt (tup[ i ] v) = tup[ i ] (mkGood (un-tup i ctxt) v)
  mkGood ctxt (left v) = left (mkGood (un-left ctxt) v)
  mkGood ctxt (right v) = right (mkGood (un-right ctxt) v)


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
    ⊑-↦ ⊑-refl (mkGood-ctxt d₁ d₁ d₁ ⊑-refl)
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
      = ⊑-fst (⊑-↦ ⊑-refl (mkGood-ctxt w w w ⊑-refl))
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


 
  {- ⊑-trans (⊑-↦ ⊑-refl (mkGood-split-⊑ (un-↦ V ctxt) split)) ⊑-dist-fun -}

  mkGood-split-⊑ : ∀ ctxt {u uL uR} → uL ◃ u ▹ uR → mkGood ctxt u ⊑ mkGood ctxt uL ⊔ mkGood ctxt uR
  mkGood-split-⊑ ctxt split-⊔ = ⊑-refl
  mkGood-split-⊑ ctxt {V ↦ u} (split-↦ {V}{u}{uL}{uR} split) = 
    ⊑-trans (⊑-↦ ⊑-refl {!   !}) ⊑-dist-fun
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
                                    (mkGood-mono-ctxt u v u v d⊑ d⊑))
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
         (mkGood-mono-ctxt w w' w w' 
                           w⊑w' 
                           w⊑w')
  mkGood-mono-ctxt ctxt ctxt' (left d) (left d') ctxt⊑ (⊑-left-å åu d⊑) = 
    ⊑-left (mkGood-mono-ctxt (un-left ctxt) (un-left ctxt') d d' (un-left-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' (right d) (right d') ctxt⊑ (⊑-right-å åu d⊑) = 
    ⊑-right (mkGood-mono-ctxt (un-right ctxt) (un-right ctxt') d d' (un-right-mono ctxt⊑) d⊑)
  mkGood-mono-ctxt ctxt ctxt' d d' ctxt⊑ (⊑-split {u}{uL}{uR} split d⊑ d⊑₁) = 
    ⊑-trans (mkGood-split-⊑ ctxt split) (⊑-⊔-L (mkGood-mono-ctxt ctxt ctxt' uL d' ctxt⊑ d⊑) 
                                                (mkGood-mono-ctxt ctxt ctxt' uR d' ctxt⊑ d⊑₁))

  postulate
    ⊔-closed-Target : ∀ M ρ → ⊔-closed (⟦ M ⟧' ρ)

  ρ-ext : Env Value → Value → Env Value
  ρ-ext ρ a = (⊑-closure a) • ρ



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
  Target-to-Good (app ⦅ M ,, N ,, Nil ⦆) ρ d ctxt 
    ⟨ V , ⟨ ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ , V∈ ⟩ ⟩  ctxt∈ d⊑ctxt ρ' ρ~ = 
     ⟨ mkGood V V , ⟨ ⟨ mkGood FV FV , ⟨ G1 , IHM2 ⟩ ⟩ , IHN ⟩ ⟩
     where
     IHM1 : ⦅ mkGood FV FV ↦ mkGood V V ↦ mkGood d d ∣ ∈ ⟦ delay M ⟧G ρ'
     IHM1 with Target-to-Good M ρ ⦅ FV ↦ V ↦ d ∣ (⦅ FV ↦ V ↦ d ∣ ⊔ ∣ FV ⦆) d∈ {!   !} {!   !} ρ' ρ~  
     ... | IH with ∣ FV ⦆ ⊑? (⦅ FV ↦ V ↦ d ∣ ⊔ ∣ FV ⦆)
     ... | no FV⋢ = ⊥-elim (FV⋢ (⊑-⊔-R2 ⊑-refl)) 
     ... | yes FV⊑ = IH
     G1 : ⦅ mkGood FV FV ↦ mkGood V V ↦ mkGood ctxt d ∣ ∈ ⟦ delay M ⟧G ρ'
     G1 = {!    !}
     helper : ∀ {A B ctxt d ctxt'} → ctxt' ⊑ ctxt
                → ⦅ A ↦ B ↦ mkGood ctxt d ∣ ⊑ ⦅ A ↦ B ↦ mkGood ctxt' d ∣
     helper ctxt⊑ = ⊑-fst (⊑-↦ ⊑-refl (⊑-↦ ⊑-refl {! mkGood-ctxt   !}))
     IHM2 : ∣ mkGood FV FV ⦆ ∈ ⟦ delay M ⟧G ρ'
     IHM2 = Target-to-Good M ρ ∣ FV ⦆ ∣ FV ⦆ FV∈ FV∈ ⊑-refl ρ' ρ~
     IHN : mkGood V V ∈ ⟦ delay N ⟧G ρ'
     IHN = Target-to-Good N ρ V V V∈ V∈ ⊑-refl ρ' ρ~
  Target-to-Good (lit B k ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (tuple x₁ ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (get i ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ ω ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = 
    Target-to-Good M ρ ω ω d∈ d∈ ⊑-ω ρ' ρ~
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ (left d) ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = 
    Target-to-Good M ρ d (un-left ctxt) d∈ (un-left-ℒ (⊔-closed-Target (delay M) ρ) ctxt ctxt∈) (un-left-⊑ d⊑ctxt) ρ' ρ~  {- will need join-closed-ness -}
  Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ v) ctxt ⟨ u∈ , v∈ ⟩ ctxt∈ d⊑ctxt ρ' ρ~ = 
    ⟨ Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ u ctxt u∈ ctxt∈ (proj₁ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ 
    , Target-to-Good (inl-op ⦅ M ,, Nil ⦆) ρ v ctxt v∈ ctxt∈ (proj₂ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ ⟩
  Target-to-Good (inr-op ⦅ x ⦆) ρ d ctxt d∈ ctxt∈ d⊑ctxt ρ' ρ~ = {!   !}
  Target-to-Good (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d ctxt 
    (inj₁ ⟨ V , ⟨ LV∈L , d∈M ⟩ ⟩) ctxt∈ d⊑ctxt ρ' ρ~ = 
    inj₁ ⟨ mkGood V V , ⟨ Target-to-Good L ρ (left V) (left V) LV∈L LV∈L ⊑-refl ρ' ρ~ 
                      , {!  !} ⟩ ⟩
    where
    V•ρ'~ : ∀ i d ctxt → d ∈ (ρ-ext ρ V) i → ctxt ∈ (ρ-ext ρ V) i
          → d ⊑ ctxt → (mkGood ctxt d) ∈ (ρ-ext ρ' (mkGood V V)) i
    V•ρ'~ zero d ctxt d∈ ctxt∈ d⊑ctxt = mkGood-mono-ctxt ctxt V d V ctxt∈ (⊑-trans d⊑ctxt ctxt∈)
    V•ρ'~ (suc i) d ctxt d∈ ctxt∈ d⊑ctxt = ρ~ i d ctxt d∈ ctxt∈ d⊑ctxt
    IHM : mkGood d d ∈ ⟦ delay M ⟧G (ρ-ext ρ' (mkGood V V))
    IHM = Target-to-Good M (ρ-ext ρ V) d d d∈M d∈M ⊑-refl (ρ-ext ρ' (mkGood V V)) V•ρ'~
    G1 : mkGood ctxt d ∈ ⟦ delay M ⟧G (ρ-ext ρ' (mkGood V V))
    G1 = {!    !}
  Target-to-Good (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d ctxt 
    (inj₂ ⟨ V , ⟨ RV∈L , d∈N ⟩ ⟩) ctxt∈ d⊑ctxt ρ' ρ~ = 
    inj₂ ⟨ mkGood V V , ⟨ {!   !} , {!   !} ⟩ ⟩
  

  Target-to-Good' : ∀ M ρ d 
        → ∀ ρ'
        → (ρ~ : ∀ i d → d ∈ ρ i 
                      → Σ[ ctxt ∈ Value ] ctxt ∈ ρ i 
                          × d ⊑ ctxt  {- this condition might not be necessary -}
                          × mkGood ctxt d ∈ ρ' i)
        → d ∈ ⟦ delay M ⟧' ρ 
        → Σ[ ctxt ∈ Value ] ctxt ∈ ⟦ delay M ⟧' ρ × d ⊑ ctxt
            × mkGood ctxt d ∈ ⟦ delay M ⟧G ρ'
  Target-to-Good' (` x) ρ d ρ' ρ~ = ρ~ x d
  Target-to-Good' (clos-op x₁ ⦅ x ⦆) ρ d ρ' ρ~ d∈ = {!   !}
  Target-to-Good' (app ⦅ M ,, N ,, Nil ⦆) ρ d ρ' ρ~ 
    ⟨ V , ⟨ ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ , V∈ ⟩ ⟩ = 
    ⟨ d , ⟨ ⟨ V , ⟨ ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ , V∈ ⟩ ⟩ , ⟨ ⊑-refl 
    , ⟨ mkGood (proj₁ IHN) V , ⟨ ⟨ mkGood (un-cdr (proj₁ IHM2)) FV , ⟨ {!   !} , proj₂ (proj₂ (proj₂ IHM2)) ⟩ ⟩ , proj₂ (proj₂ (proj₂ IHN)) ⟩ ⟩ ⟩ ⟩ ⟩
    where
    IHM1 : Σ[ fctxt ∈ Value ] fctxt ∈ ⟦ delay M ⟧' ρ × ⦅ FV ↦ V ↦ d ∣ ⊑ fctxt 
              × mkGood fctxt ⦅ FV ↦ V ↦ d ∣ ∈ ⟦ delay M ⟧G ρ'
    IHM1 = Target-to-Good' M ρ ⦅ FV ↦ V ↦ d ∣ ρ' ρ~ d∈
    IHM2 : Σ[ FVctxt ∈ Value ] FVctxt ∈ ⟦ delay M ⟧' ρ × ∣ FV ⦆ ⊑ FVctxt
              × mkGood FVctxt ∣ FV ⦆ ∈ ⟦ delay M ⟧G ρ'
    IHM2 = Target-to-Good' M ρ ∣ FV ⦆ ρ' ρ~ FV∈
    IHN : Σ[ Vctxt ∈ Value ] Vctxt ∈ ⟦ delay N ⟧' ρ × V ⊑ Vctxt × mkGood Vctxt V ∈ ⟦ delay N ⟧G ρ'
    IHN = Target-to-Good' N ρ V ρ' ρ~ V∈
    {- ⟨ mkGood V V , ⟨ ⟨ mkGood FV FV , ⟨ G1 , IHM2 ⟩ ⟩ , IHN ⟩ ⟩
     where
     IHM1 : ⦅ mkGood FV FV ↦ mkGood V V ↦ mkGood d d ∣ ∈ ⟦ delay M ⟧G ρ'
     IHM1 with Target-to-Good M ρ ⦅ FV ↦ V ↦ d ∣ (⦅ FV ↦ V ↦ d ∣ ⊔ ∣ FV ⦆) d∈ {!   !} {!   !} ρ' ρ~  
     ... | IH with ∣ FV ⦆ ⊑? (⦅ FV ↦ V ↦ d ∣ ⊔ ∣ FV ⦆)
     ... | no FV⋢ = ⊥-elim (FV⋢ (⊑-⊔-R2 ⊑-refl)) 
     ... | yes FV⊑ = IH
     G1 : ⦅ mkGood FV FV ↦ mkGood V V ↦ mkGood ctxt d ∣ ∈ ⟦ delay M ⟧G ρ'
     G1 = {!    !}
     helper : ∀ {A B ctxt d ctxt'} → ctxt' ⊑ ctxt
                → ⦅ A ↦ B ↦ mkGood ctxt d ∣ ⊑ ⦅ A ↦ B ↦ mkGood ctxt' d ∣
     helper ctxt⊑ = ⊑-fst (⊑-↦ ⊑-refl (⊑-↦ ⊑-refl {! mkGood-ctxt   !}))
     IHM2 : ∣ mkGood FV FV ⦆ ∈ ⟦ delay M ⟧G ρ'
     IHM2 = Target-to-Good M ρ ∣ FV ⦆ ∣ FV ⦆ FV∈ FV∈ ⊑-refl ρ' ρ~
     IHN : mkGood V V ∈ ⟦ delay N ⟧G ρ'
     IHN = Target-to-Good N ρ V V V∈ V∈ ⊑-refl ρ' ρ~
  -}
  Target-to-Good' (lit B k ⦅ x ⦆) ρ d ρ' ρ~ d∈ = {!   !}
  Target-to-Good' (tuple x₁ ⦅ x ⦆) ρ d ρ' ρ~ d∈ = {!   !}
  Target-to-Good' (get i ⦅ x ⦆) ρ d ρ' ρ~ d∈ = {!   !}
  Target-to-Good' (inl-op ⦅ M ,, Nil ⦆) ρ ω ρ' ρ~ d∈ = {!   !}
    {- Target-to-Good' M ρ ω ω d∈ d∈ ⊑-ω ρ' ρ~ -}
  Target-to-Good' (inl-op ⦅ M ,, Nil ⦆) ρ (left d) ρ' ρ~ d∈ = {!   !}
    {- Target-to-Good' M ρ d (un-left ctxt) d∈ (un-left-ℒ (⊔-closed-Target (delay M) ρ) ctxt ctxt∈) (un-left-⊑ d⊑ctxt) ρ' ρ~ -} {- will need join-closed-ness -}
  Target-to-Good' (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ v) ρ' ρ~ ⟨ u∈ , v∈ ⟩ = {!   !}
   {-
    ⟨ Target-to-Good' (inl-op ⦅ M ,, Nil ⦆) ρ u ctxt u∈ ctxt∈ (proj₁ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ 
    , Target-to-Good' (inl-op ⦅ M ,, Nil ⦆) ρ v ctxt v∈ ctxt∈ (proj₂ (⊑-split-inv-R d⊑ctxt split-⊔)) ρ' ρ~ ⟩
    -}
  Target-to-Good' (inr-op ⦅ x ⦆) ρ d ρ' ρ~ d∈ = {!   !}
  Target-to-Good' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d ρ' ρ~
    (inj₁ ⟨ V , ⟨ LV∈L , d∈M ⟩ ⟩) = {!   !}
  {-
    inj₁ ⟨ mkGood V V , ⟨ Target-to-Good L ρ (left V) (left V) LV∈L LV∈L ⊑-refl ρ' ρ~ 
                      , {!  !} ⟩ ⟩
    where
    V•ρ'~ : ∀ i d ctxt → d ∈ (ρ-ext ρ V) i → ctxt ∈ (ρ-ext ρ V) i
          → d ⊑ ctxt → (mkGood ctxt d) ∈ (ρ-ext ρ' (mkGood V V)) i
    V•ρ'~ zero d ctxt d∈ ctxt∈ d⊑ctxt = mkGood-mono-ctxt ctxt V d V ctxt∈ (⊑-trans d⊑ctxt ctxt∈)
    V•ρ'~ (suc i) d ctxt d∈ ctxt∈ d⊑ctxt = ρ~ i d ctxt d∈ ctxt∈ d⊑ctxt
    IHM : mkGood d d ∈ ⟦ delay M ⟧G (ρ-ext ρ' (mkGood V V))
    IHM = Target-to-Good M (ρ-ext ρ V) d d d∈M d∈M ⊑-refl (ρ-ext ρ' (mkGood V V)) V•ρ'~
    G1 : mkGood ctxt d ∈ ⟦ delay M ⟧G (ρ-ext ρ' (mkGood V V))
    G1 = {!    !}
    -}
  Target-to-Good' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d ρ' ρ~
    (inj₂ ⟨ V , ⟨ RV∈L , d∈N ⟩ ⟩) = {!   !}
    {- inj₂ ⟨ mkGood V V , ⟨ {!   !} , {!   !} ⟩ ⟩ -}



