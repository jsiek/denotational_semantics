{-# OPTIONS --allow-unsolved-metas #-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Filter.Domain.ISWIM.Domain as Domain
open import Compiler.Model.Filter.Domain.ISWIM.Ops as Ops
open import Compiler.Model.Filter.Sem.Clos3Iswim as Source
open import Compiler.Model.Filter.Sem.Clos4Iswim as Target
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; reduce)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; map⁻)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)
open import Data.Bool using (Bool; true; false)

module Compiler.Correctness.Delay.ReflectIswimIswim where

{- Record of working times on "easy" version of the reverse proof -}
{- 3:22 - _


-}


fro : Value → Value
fro ω = ω
fro ν = ν  {- for mapping over closure functions -}
fro (const k) = const k
fro (V ↦ w) = fro V ↦ fro w {- for mapping over closure functions -}
fro ⦅ u ∣ = ω
{-
fro ⦅ ν ∣ = ω
fro ⦅ FV ↦ u ∣ = ω {- I might want this to be ν,
    but then we'll need additional info from the language -}
fro ⦅ u ⊔ v ∣ = fro ⦅ u ∣ ⊔ fro ⦅ v ∣ {- nice and uniform -}
fro ⦅ x ∣ = ω  {- catch-all case -} -}
fro (⦅ FV ↦ u ∣ ⊔ ∣ FV' ⦆) with FV ⊑? FV'
... | yes FV⊑ = fro u {- trying to handle this case uniformly -}
... | no FV⋢ = ν
fro (u ⊔ v) = fro u ⊔ fro v  {- catch-all case, nice and uniform -}
fro ∣ v ⦆ = ω {- always in closure denotation -}
fro (tup[ i ] v) = tup[ i ] (fro v)
fro (left v) = left (fro v)
fro (right v) = right (fro v)

fro left (u ⊔ v) = left (fro u ⊔ v)  = cases
fro left (u ⊔ v) = left (fro u ⊔ v) = 
fro left u ⊔ left v = left (fro u) ⊔ left (fro v)
    but what if?
    fro left u  ⊔ left v = left fro (u ⊔ v)


{-
bad example?

with FV ⊑ FV'
fro (left (⦅ FV ↦ u ∣ ⊔ ∣ FV' ⦆))
= left (fro (a ⊔ b))
= left (fro u)

now we split

fro (left a) ◃ fro (left (a ⊔ b)) ▹ fro (left b)
  = ω                                  = ω

so fro (uL ⊔ uR) = ω ⊔ ω  ⊑ left (Fro u) = fro u

-}


fro-dist : ∀ u v → (fro u ⊔ fro v) ⊑ fro (u ⊔ v)
fro-dist ⦅ FV ↦ u ∣ ∣ FV' ⦆ with FV ⊑? FV'
... | yes FV⊑ = ⊑-⊔-L ⊑-ω ⊑-ω
... | no FV⋢ = ⊑-⊔-L ⊑-ω ⊑-ω
fro-dist ω v = ⊑-refl
fro-dist ν v = ⊑-refl
fro-dist (const k) v = ⊑-refl
fro-dist (u ⊔ u₁) v = ⊑-refl
fro-dist (u ↦ u₁) v = ⊑-refl
fro-dist ⦅ ω ∣ v = ⊑-refl
fro-dist ⦅ ν ∣ v = ⊑-refl
fro-dist ⦅ const k ∣ v = ⊑-refl
fro-dist ⦅ u ⊔ u₁ ∣ v = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ ω = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ ν = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (const k) = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (v ⊔ v₁) = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (v ↦ v₁) = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ ⦅ v ∣ = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (tup[ i ] v) = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (left v) = ⊑-refl
fro-dist ⦅ u ↦ u₁ ∣ (right v) = ⊑-refl
fro-dist ⦅ ⦅ u ∣ ∣ v = ⊑-refl
fro-dist ⦅ ∣ u ⦆ ∣ v = ⊑-refl
fro-dist ⦅ tup[ i ] u ∣ v = ⊑-refl
fro-dist ⦅ left u ∣ v = ⊑-refl
fro-dist ⦅ right u ∣ v = ⊑-refl
fro-dist ∣ u ⦆ v = ⊑-refl
fro-dist (tup[ i ] u) v = ⊑-refl
fro-dist (left u) v = ⊑-refl
fro-dist (right u) v = ⊑-refl



{- fro-dist-inv : ∀ u v → (fro (u ⊔ v) ⊑ fro u ⊔ fro v)
             ⊎ (Σ[ FV ∈ Value ] Σ[ u' ∈ Value ] Σ[ FV' ∈ Value ]
                 u ≡ ⦅ FV ↦ u' ∣ × v ≡ ∣ FV' ⦆ × FV ⊑ FV'
-}

fro-Atomic : ∀ v → Atomic v → Atomic (fro v)
fro-Atomic ω åv = tt
fro-Atomic ν åv = tt
fro-Atomic (const k) åv = tt
fro-Atomic (v ↦ v₁) åv = fro-Atomic v₁ åv
fro-Atomic ⦅ v ↦ (v₁ ↦ v₂) ∣ åv = tt
fro-Atomic ⦅ v ↦ ω ∣ åv = tt
fro-Atomic ⦅ v ↦ ν ∣ åv = tt
fro-Atomic ⦅ v ↦ const k ∣ åv = tt
fro-Atomic ⦅ v ↦ ⦅ v₁ ∣ ∣ åv = tt
fro-Atomic ⦅ v ↦ ∣ v₁ ⦆ ∣ åv = tt
fro-Atomic ⦅ v ↦ tup[ i ] v₁ ∣ åv = tt
fro-Atomic ⦅ v ↦ left v₁ ∣ åv = tt
fro-Atomic ⦅ v ↦ right v₁ ∣ åv = tt
fro-Atomic ⦅ ω ∣ åv = tt
fro-Atomic ⦅ ν ∣ åv = tt
fro-Atomic ⦅ const k ∣ åv = tt
fro-Atomic ⦅ ⦅ v ∣ ∣ åv = tt
fro-Atomic ⦅ ∣ v ⦆ ∣ åv = tt
fro-Atomic ⦅ tup[ i ] v ∣ åv = tt
fro-Atomic ⦅ left v ∣ åv = tt
fro-Atomic ⦅ right v ∣ åv = tt
fro-Atomic ∣ v ⦆ åv = tt
fro-Atomic (tup[ i ] v) åv = fro-Atomic v åv
fro-Atomic (left v) åv = fro-Atomic v åv
fro-Atomic (right v) åv = fro-Atomic v åv

fro-mono : ∀ {u v} → u ⊑ v → fro u ⊑ fro v
fro-split-⊑ : ∀ {u uL uR} → uL ◃ u ▹ uR → fro u ⊑ fro (uL ⊔ uR)
fro-upper-bound : ∀ {uL uR v} → uL ⊑ v → uR ⊑ v → fro (uL ⊔ uR) ⊑ fro v

fro-mono ⊑-ω = ⊑-ω
fro-mono ⊑-ν-ν = ⊑-ν-ν
fro-mono ⊑-ν-↦ = ⊑-ν-↦
fro-mono ⊑-const = ⊑-const
fro-mono {u} {v ⊔ w} (⊑-⊔-R1-å åu u⊑v) = 
  ⊑-trans (⊑-⊔-R1 (fro-mono u⊑v)) (fro-dist v w)
fro-mono {u} {v ⊔ w} (⊑-⊔-R2-å åu u⊑v) = 
  ⊑-trans (⊑-⊔-R2 (fro-mono u⊑v)) (fro-dist v w)
fro-mono (⊑-fst-å åu u⊑v) = ⊑-ω
fro-mono (⊑-snd-å åu u⊑v) = ⊑-ω
fro-mono (⊑-tup-å åu u⊑v) = ⊑-tup (fro-mono u⊑v)
fro-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-↦ (fro-mono u⊑v₁) (fro-mono u⊑v)
fro-mono (⊑-left-å åu u⊑v) = ⊑-left (fro-mono u⊑v)
fro-mono (⊑-right-å åu u⊑v) = ⊑-right (fro-mono u⊑v)
fro-mono (⊑-split {u} split u⊑v u⊑v₁) = ⊑-trans (fro-split-⊑ split) (fro-upper-bound u⊑v u⊑v₁)

fro-split-⊑ {.(uL ⊔ uR)} {uL} {uR} split-⊔ = ⊑-refl
fro-split-⊑ {.(_ ↦ _)} {.(_ ↦ _)} {.(_ ↦ _)} (split-↦ split) = 
  {! fro-mono    !}
fro-split-⊑ {.(⦅ _ ∣)} {.(⦅ _ ∣)} {.(⦅ _ ∣)} (split-fst split) = {!   !}
fro-split-⊑ {.(∣ _ ⦆)} {.(∣ _ ⦆)} {.(∣ _ ⦆)} (split-snd split) = {!   !}
fro-split-⊑ {.(tup[ _ ] _)} {.(tup[ _ ] _)} {.(tup[ _ ] _)} (split-tup split) = {!   !}
fro-split-⊑ {.(left _)} {.(left _)} {.(left _)} (split-left split) = {!   !}
fro-split-⊑ {.(right _)} {.(right _)} {.(right _)} (split-right split) = {!   !}

fro-upper-bound {uL} {uR} {v} L⊑ R⊑ = {! !}



{-
ν-⊑-fro-fst : ∀ {u w} → ν ⊑ fro ⦅ u ↦ w ∣
ν-⊑-fro-fst {u} {ω} = ⊑-ν-ν
ν-⊑-fro-fst {u} {ν} = ⊑-ν-ν
ν-⊑-fro-fst {u} {const k} = ⊑-ν-ν
ν-⊑-fro-fst {u} {w ⊔ w₁} = ⊑-⊔-R1-å tt ν-⊑-fro-fst
ν-⊑-fro-fst {u} {w ↦ w₁} = ⊑-ν-↦
ν-⊑-fro-fst {u} {⦅ w ∣} = ⊑-ν-ν
ν-⊑-fro-fst {u} {∣ w ⦆} = ⊑-ν-ν
ν-⊑-fro-fst {u} {tup[ i ] w} = ⊑-ν-ν
ν-⊑-fro-fst {u} {left w} = ⊑-ν-ν
ν-⊑-fro-fst {u} {right w} = ⊑-ν-ν

fro-split-⊑ : ∀ {u uL uR} → uL ◃ u ▹ uR → fro u ⊑ fro uL ⊔ fro uR
fro-split-⊑ split-⊔ = ⊔⊑⊔ ⊑-refl ⊑-refl
fro-split-⊑ (split-↦ split) = ⊑-trans (⊑-↦ ⊑-refl (fro-split-⊑ split)) ⊑-dist-fun
fro-split-⊑ {⦅ .(uL ⊔ uR) ∣} {⦅ uL ∣} {⦅ uR ∣} (split-fst split-⊔) = ⊔⊑⊔ ⊑-refl ⊑-refl
fro-split-⊑ (split-fst (split-↦ split-⊔)) = fro-split-⊑ split-⊔
fro-split-⊑ (split-fst (split-↦ (split-↦ split))) = fro-split-⊑ (split-↦ split)
fro-split-⊑ (split-fst (split-↦ (split-fst split))) = ⊑-⊔-R1-å tt ⊑-ν-ν
fro-split-⊑ (split-fst (split-↦ (split-snd split))) = ⊑-⊔-R1-å tt ⊑-ν-ν
fro-split-⊑ (split-fst (split-↦ (split-tup split))) = ⊑-⊔-R1-å tt ⊑-ν-ν
fro-split-⊑ (split-fst (split-↦ (split-left split))) = ⊑-⊔-R1-å tt ⊑-ν-ν
fro-split-⊑ (split-fst (split-↦ (split-right split))) = ⊑-⊔-R1-å tt ⊑-ν-ν
fro-split-⊑ (split-fst (split-fst split)) = ⊑-ω
fro-split-⊑ (split-fst (split-snd split)) = ⊑-ω
fro-split-⊑ (split-fst (split-tup split)) = ⊑-ω
fro-split-⊑ (split-fst (split-left split)) = ⊑-ω
fro-split-⊑ (split-fst (split-right split)) = ⊑-ω
fro-split-⊑ (split-snd split) = ⊑-ω
fro-split-⊑ (split-tup split) = ⊑-trans (⊑-tup (fro-split-⊑ split)) ⊑-dist-tup
fro-split-⊑ (split-left split) = ⊑-trans (⊑-left (fro-split-⊑ split)) ⊑-dist-left
fro-split-⊑ (split-right split) = ⊑-trans (⊑-right (fro-split-⊑ split)) ⊑-dist-right


fro-mono : ∀ {u v} → u ⊑ v → fro u ⊑ fro v
fro-mono ⊑-ω = ⊑-ω
fro-mono ⊑-ν-ν = ⊑-ν-ν
fro-mono ⊑-ν-↦ = ⊑-ν-↦
fro-mono ⊑-const = ⊑-const
fro-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (fro-mono u⊑v)
fro-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (fro-mono u⊑v)
fro-mono {⦅ u ∣}{⦅ v ∣} (⊑-fst-å åu u⊑v) = G u v åu u⊑v
  where
  G : ∀ u v → Atomic u → u ⊑ v → fro ⦅ u ∣ ⊑ fro ⦅ v ∣
  G .ω v åu ⊑-ω = ⊑-ω
  G .ν .ν åu ⊑-ν-ν = ⊑-ν-ν
  G .ν .(_ ↦ _) åu ⊑-ν-↦ = ν-⊑-fro-fst
  G .(const _) .(const _) åu ⊑-const = ⊑-ω
  G u (v ⊔ w) åu (⊑-⊔-R1-å åu₁ u⊑v) = ⊑-⊔-R1 (G u v åu u⊑v)
  G u (v ⊔ w) åu (⊑-⊔-R2-å åu₁ u⊑v) = ⊑-⊔-R2 (G u w åu u⊑v)
  G .(⦅ _ ∣) .(⦅ _ ∣) åu (⊑-fst-å åu₁ u⊑v) = ⊑-ω
  G .(∣ _ ⦆) .(∣ _ ⦆) åu (⊑-snd-å åu₁ u⊑v) = ⊑-ω
  G .(tup[ _ ] _) .(tup[ _ ] _) åu (⊑-tup-å åu₁ u⊑v) = ⊑-ω
  G (uV ↦ u) (vV ↦ v) åu (⊑-↦-å åu₂ u⊑v u⊑v₁) = G' uV u vV v åu u⊑v u⊑v₁
     where
     G' : ∀ uV u vV v → Atomic u → u ⊑ v → vV ⊑ uV
        → fro ⦅ uV ↦ u ∣ ⊑ fro ⦅ vV ↦ v ∣
     G' uV .ω vV v åu ⊑-ω vV⊑uV = ν-⊑-fro-fst
     G' uV .ν vV .ν åu ⊑-ν-ν vV⊑uV = ⊑-ν-ν
     G' uV .ν vV .(_ ↦ _) åu ⊑-ν-↦ vV⊑uV = ⊑-ν-↦
     G' uV .(const _) vV .(const _) åu ⊑-const vV⊑uV = ⊑-ν-ν
     G' uV u vV (v ⊔ w) åu (⊑-⊔-R1-å åu₁ u⊑v) vV⊑uV = 
       ⊑-⊔-R1 (G' uV u vV v åu₁ u⊑v vV⊑uV)
     G' uV u vV (v ⊔ w) åu (⊑-⊔-R2-å åu₁ u⊑v) vV⊑uV = 
       ⊑-⊔-R2 (G' uV u vV w åu₁ u⊑v vV⊑uV)
     G' uV .(⦅ _ ∣) vV .(⦅ _ ∣) åu (⊑-fst-å åu₁ u⊑v) vV⊑uV = ⊑-ν-ν
     G' uV .(∣ _ ⦆) vV .(∣ _ ⦆) åu (⊑-snd-å åu₁ u⊑v) vV⊑uV = ⊑-ν-ν
     G' uV .(tup[ _ ] _) vV .(tup[ _ ] _) åu (⊑-tup-å åu₁ u⊑v) vV⊑uV = ⊑-ν-ν
     G' uV (uV' ↦ u) vV (vV' ↦ v) åu (⊑-↦-å åu₂ u⊑v u⊑v₁) vV⊑uV = 
        ⊑-↦ (fro-mono u⊑v₁) (fro-mono u⊑v)
     G' uV .(left _) vV .(left _) åu (⊑-left-å åu₁ u⊑v) vV⊑uV = ⊑-ν-ν
     G' uV .(right _) vV .(right _) åu (⊑-right-å åu₁ u⊑v) vV⊑uV = ⊑-ν-ν
     G' uV u vV v åu (⊑-split split u⊑v u⊑v₁) vV⊑uV = ⊥-elim (unsplittable u åu split)
  G .(left _) .(left _) åu (⊑-left-å åu₁ u⊑v) = ⊑-ω
  G .(right _) .(right _) åu (⊑-right-å åu₁ u⊑v) = ⊑-ω
  G u v åu (⊑-split split u⊑v u⊑v₁) = ⊥-elim (unsplittable u åu split)
fro-mono (⊑-snd-å åu u⊑v) = ⊑-ω
fro-mono (⊑-tup-å åu u⊑v) = ⊑-tup (fro-mono u⊑v)
fro-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-↦ (fro-mono u⊑v₁) (fro-mono u⊑v)
fro-mono (⊑-left-å åu u⊑v) = ⊑-left (fro-mono u⊑v)
fro-mono (⊑-right-å åu u⊑v) = ⊑-right (fro-mono u⊑v)
fro-mono (⊑-split {u}{uL}{uR} split uL⊑v uR⊑v) = 
  ⊑-trans (fro-split-⊑ split) (⊑-split split-⊔ (fro-mono uL⊑v) (fro-mono uR⊑v))


env-map : ∀ {A B : Set} → (A → B) → (ℕ → 𝒫 A) → (ℕ → 𝒫 B)
env-map {A} {B} f ρ x b = Σ[ a ∈ A ] a ∈ (ρ x) × b ≡ f a

postulate
  ⟦⟧'-⊑-closed : ∀ (M : AST') ρ (u v : Value) → v ∈ ⟦ M ⟧' ρ → u ⊑ v → u ∈ ⟦ M ⟧' ρ
  ⟦⟧'-⊔-closed : ∀ (M : AST') ρ (u v : Value) → u ∈ ⟦ M ⟧' ρ → v ∈ ⟦ M ⟧' ρ
                → (u ⊔ v) ∈ ⟦ M ⟧' ρ
  ⟦⟧-⊔-closed : ∀ (M : AST) ρ (u v : Value) → u ∈ ⟦ M ⟧ ρ → v ∈ ⟦ M ⟧ ρ
                → (u ⊔ v) ∈ ⟦ M ⟧ ρ
  ⟦⟧-⊑-closed : ∀ (M : AST) ρ (u v : Value) → v ∈ ⟦ M ⟧ ρ → u ⊑ v → u ∈ ⟦ M ⟧ ρ 

⊆ₑ-refl : ∀ {A : Set} {ρ : Env A} → ρ ⊆ₑ ρ
⊆ₑ-refl i d d∈ = d∈

env-ext-⊆ : ∀ {A}{ρ ρ' : Env A}{D D'} → ρ ⊆ₑ ρ' → D ⊆ D' → (D • ρ) ⊆ₑ (D' • ρ')
env-ext-⊆ ρ⊆ D⊆ zero d d∈ = D⊆ d d∈
env-ext-⊆ ρ⊆ D⊆ (suc i) d d∈ = ρ⊆ i d d∈

env-ext-⊑-⊆ : ∀ {ρ ρ' V V'} → ρ ⊆ₑ ρ' → V ⊑ V' → (⊑-closure V • ρ) ⊆ₑ (⊑-closure V' • ρ')
env-ext-⊑-⊆ ρ⊆ V⊑ = env-ext-⊆ ρ⊆ λ d d⊑ → ⊑-trans d⊑ V⊑

helpful-lemma : ∀ M ρ u v → (u ⊔ v) ∈ ⟦ M ⟧' ρ → u ∈ ⟦ M ⟧' ρ × v ∈ ⟦ M ⟧' ρ
helpful-lemma M ρ u v u⊔v∈M = 
  ⟨ ⟦⟧'-⊑-closed M ρ u (u ⊔ v) u⊔v∈M (⊑-⊔-R1 ⊑-refl) 
  , ⟦⟧'-⊑-closed M ρ v (u ⊔ v) u⊔v∈M (⊑-⊔-R2 ⊑-refl) ⟩


delay-reflect : ∀ M ρ
  {- → (ρ~ : ∀ₑ ⊔-closed' ρ) -}
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
delay-args-reflect-nth : ∀ {n} args (i : Fin n) ρ d 
   → d ∈ nthD (⟦ del-map-args args ⟧₊' ρ) i
   → fro d ∈ nthD (⟦ args ⟧₊ (env-map fro ρ)) i

delay-reflect (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ω d∈ = 
  ⟨ ω , ⟨ tt , tt ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ 
  with delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d d∈
   | delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d₁ d₁∈ 
... | ⟨ V , ⟨ IHd , V∈ ⟩ ⟩ | ⟨ V₁ , ⟨ IHd₁ , V₁∈ ⟩ ⟩ = 
   ⟨ V ⊔ V₁ , ⟨ ⟨ Gd , Gd₁ ⟩ , ⟨ V∈ , V₁∈ ⟩ ⟩ ⟩
  where
  Gd : (fro d) ∈ Λ ⟨ (λ x → ⟦ N ⟧ (x • ⊑-closure (V ⊔ V₁) • (λ _ x₁ → x₁ ≡ ω))) , ptt ⟩
  Gd = lower (Λ-mono ⟨ (λ x → ⟦ N ⟧ (x • ⊑-closure V • (λ _ x₁ → x₁ ≡ ω))) , ptt ⟩ 
                     ⟨ (λ z → ⟦ N ⟧ (z • ⊑-closure (V ⊔ V₁) • (λ _ x → x ≡ ω))) , ptt ⟩ 
                     ⟨ (λ D D' D⊆ → lift λ d' d'∈ → 
                       Source.⟦⟧-monotone N 
                                          (env-ext-⊆ (env-ext-⊑-⊆ ⊆ₑ-refl 
                                                     (⊑-⊔-R1 ⊑-refl)) D⊆) 
                                          d' d'∈) , ptt ⟩) 
                     (fro d) IHd
  Gd₁ : (fro d₁) ∈ Λ ⟨ (λ x → ⟦ N ⟧ (x • ⊑-closure (V ⊔ V₁) • (λ _ x₁ → x₁ ≡ ω))) , ptt ⟩
  Gd₁ = lower (Λ-mono ⟨ (λ x → ⟦ N ⟧ (x • ⊑-closure V₁ • (λ _ x₁ → x₁ ≡ ω))) , ptt ⟩ 
                     ⟨ (λ z → ⟦ N ⟧ (z • ⊑-closure (V ⊔ V₁) • (λ _ x → x ≡ ω))) , ptt ⟩ 
                     ⟨ (λ D D' D⊆ → lift λ d' d'∈ → 
                       Source.⟦⟧-monotone N 
                                          (env-ext-⊆ (env-ext-⊑-⊆ ⊆ₑ-refl 
                                                     (⊑-⊔-R2 ⊑-refl)) D⊆) 
                                          d' d'∈) , ptt ⟩) 
                     (fro d₁) IHd₁
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ d ∣ d∈ = {! d  !}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ∣ d ⦆ d∈ = 
  ⟨ ω , ⟨ tt , tt ⟩ ⟩
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d 
  ⟨ V , ⟨ ⟨ FV , ⟨ FV↦V↦d∈carM' , FV∈cdrM' ⟩ ⟩ , V∈N ⟩ ⟩ 
  = ⟨ fro V , ⟨ delay-reflect M ρ ⦅ FV ↦ V ↦ d ∣ FV↦V↦d∈carM' 
            ,  delay-reflect N ρ V V∈N ⟩ ⟩
delay-reflect (lit B k ⦅ Nil ⦆) ρ ω d∈ = tt
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const k₁) d∈ = d∈
delay-reflect (lit B k ⦅ Nil ⦆) ρ (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ = 
  ⟨ delay-reflect (lit B k ⦅ Nil ⦆) ρ d d∈ 
  , delay-reflect (lit B k ⦅ Nil ⦆) ρ d₁ d₁∈ ⟩
delay-reflect (tuple n ⦅ args ⦆) ρ ω d∈ = tt
delay-reflect (tuple n ⦅ args ⦆) ρ (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ =
  ⟨ delay-reflect (tuple n ⦅ args ⦆) ρ d d∈ 
  , delay-reflect (tuple n ⦅ args ⦆) ρ d₁ d₁∈ ⟩
delay-reflect (tuple (suc n) ⦅ args ⦆) ρ (tup[ i ] d) ⟨ refl , d∈ ⟩ = 
  ⟨ refl , delay-args-reflect-nth args i ρ d d∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d d∈ = delay-reflect M ρ (tup[ i ] d) d∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ω d∈ = tt
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ = 
  ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ d d∈ 
  , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ d₁ d₁∈ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left d) d∈ = delay-reflect M ρ d d∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ω d∈ = tt
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (d ⊔ d₁) ⟨ d∈ , d₁∈ ⟩ =
  ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ d d∈ 
  , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ d₁ d₁∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right d) d∈ = delay-reflect M ρ d d∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ fro V , ⟨ G 
        , Source.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M ((⊑-closure V) • ρ) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : left (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ (left V) LV∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) =
   inj₂ ⟨ fro V , ⟨ G 
        , Source.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N ((⊑-closure V) • ρ) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : right (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ (right V) RV∈

delay-args-reflect-nth {suc n} (arg ,, args) zero ρ d d∈ = 
  delay-reflect arg ρ d d∈
delay-args-reflect-nth {suc n} (arg ,, args) (suc i) ρ d d∈ = 
  delay-args-reflect-nth args i ρ d d∈



{- CLOS 
⦅ FV ↦ V ↦ w , d₁ ⦆' ⟨ ⟨ FV' , ⟨ w∈ , FV'∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ 
  with FV d≟ d₁
... | yes refl = ⟨ ω , ⟨ fro FV , ⟨ ω ⊢ fro V ↦ fro w 
                 , ⟨ G1 , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IH : fro w ∈ ⟦ N ⟧ (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)))
  IH = delay-reflect N ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)) w w∈
  H : (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω))) ⊆ₑ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono !}
  H (suc zero) d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono !}
  H (suc (suc i)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) IH
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) (u ⊔ u₁) u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G2 (suc n) (fv ,, fvs) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) ∥ ds ∥ u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro d₁ ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs d₁ d₁∈
... | no neq = ⟨ ω , ⟨ fro d₁ , ⟨ ν 
                , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) (u ⊔ u₁) u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G2 (suc n) (fv ,, fvs) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) ∥ ds ∥ u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro d₁ ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs d₁ d₁∈

{-
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV ↦ ν , d₁ ⦆' 
   ⟨ ⟨ FV' , ⟨ ν∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ = 
   ⟨ ω , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV ↦ (w ⊔ w₁) , d₁ ⦆' 
   ⟨ ⟨ FV' , ⟨ w∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
   ⟨ ω , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ ν , d₁ ⦆' 
  ⟨ ⟨ FV , ⟨ ν∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
  ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ u ⊔ v , d₁ ⦆' 
  ⟨ ⟨ FV , ⟨ ⟨ u∈ , v∈ ⟩ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
  ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ 
  with delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ u u∈
     | delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ v v∈
... | IHu | IHv = ⟦⟧-⊔-closed (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) (env-map fro ρ) (fro u) (fro v) IHu IHv
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ d ∣  
  ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ = {!   !}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ∣ d ⦆ 
  ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ = {!   !}
-}
-}


{- APP ⟨ fro FV , ⟨ fro V , ⟨ IHM , IHN ⟩ ⟩ ⟩
  where
  IHN : fro V ∈ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect N ρ V V∈N
  ⦅FV↦V↦d,FV⦆∈M' : ⦅ FV ↦ (V ↦ d) , FV ⦆' ∈ ⟦ delay M ⟧' ρ
  ⦅FV↦V↦d,FV⦆∈M' = 
      ⟦⟧'-⊔-closed (delay M) ρ ⦅ FV ↦ V ↦ d ∣ ∣ FV ⦆ FV↦V↦d∈carM' FV∈cdrM'
  IHM : (fro V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV d≟ FV 
        | delay-reflect M ρ ⦅ FV ↦ (V ↦ d) , FV ⦆' ⦅FV↦V↦d,FV⦆∈M' 
  ... | yes refl | IHM' = IHM'
  ... | no neq | IHM' = ⊥-elim (neq refl) -}


 {- TUPLE  G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d d∈ , ds'∈ ⟩
  G (suc n) (arg ,, args) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) (u ⊔ u₁) u∈ , G (suc n) (arg ,, args) v v∈ ⟩
  G (suc n) (arg ,, args) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) ∥ ds ∥ u∈ , G (suc n) (arg ,, args) v v∈ ⟩ -}

 {-  ⟨ n , ⟨ fros ds , ⟨ delay-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩ -}

{- LEFT and RIGHT
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ((u ⊔ u₁) ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁) u∈ 
    , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ((left u) ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left u) u∈ 
    , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩ 
  = ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁) u∈ 
    , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right u ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right u) u∈ 
    , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
-}



















{-
data applies : Value → Value → Set where
  app-base : ∀ {V w a} → V ⊑ a → applies ⦅ V ↦ w ∣ ∣ a ⦆
  app-fun-å : ∀ {Vf f Va a} → Atomic f → Atomic a
            → applies f a
            → applies (Vf ↦ f) (Va ↦ a)
  app-tup-å : ∀ {n}{i : Fin n}{f a} → Atomic f → Atomic a
            → applies f a
            → applies (tup[ i ] f) (tup[ i ] a)
  app-fst-å : ∀ {f a} → Atomic f → Atomic a
            → applies f a
            → applies ⦅ f ∣ ⦅ a ∣
  app-snd-å : ∀ {f a} → Atomic f → Atomic a
            → applies f a
            → applies ∣ f ⦆ ∣ a ⦆
  app-left-å : ∀ {f a} → Atomic f → Atomic a
            → applies f a
            → applies (left f) (left a)
  app-right-å : ∀ {f a} → Atomic f → Atomic a
            → applies f a
            → applies (right f) (right a)
  app-split-rator : ∀ {f fL fR a} → fL ◃ f ▹ fR 
                  → applies fL a → applies fR a → applies f a
  app-split-rand : ∀ {f a aL aR} → aL ◃ a ▹ aR → Atomic f
                  → applies f aL → applies f aR → applies f a

data fro : Value → Value → Set where
  fro-const : ∀ {B k} → fro (const {B} k) (const k)
  fro-
-}


{-
fro : Value → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ⦅ f ∣ = ν
fro ∣ FV ⦆ = ν
fro (tup[ i ] d) = tup[ i ] (fro d)
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fro (⦅ FV ↦ (V ↦ w) ∣ ⊔ ∣ FV' ⦆) with  FV ⊑? FV'
... | yes FV⊑ = fro V ↦ fro w
... | no FV⋢ = ν
fro (u ⊔ v) = fro u ⊔ fro v

fro-⊔-⊑ : ∀ u v → fro u ⊔ (fro v) ⊑ fro (u ⊔ v)
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ ∣ v ⦆ with u ⊑? v
... | yes u⊑v = ⊑-⊔-L ⊑-ν-↦ ⊑-ν-↦
... | no u⋢v = ⊑-⊔-L ⊑-ν-ν ⊑-ν-ν
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ ω = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ ν = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (const k) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (v ⊔ v₁) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (v ↦ v₁) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ ⦅ v ∣ = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (tup[ i ] v) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (left v) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ u₁ ↦ u₂ ∣ (right v) = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ ω ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ ν ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ const k ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ (u₁ ⊔ u₂) ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ ⦅ u₁ ∣ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ ∣ u₁ ⦆ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ tup[ i ] u₁ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ left u₁ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ↦ right u₁ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ ω ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ ν ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ const k ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ u ⊔ u₁ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ ⦅ u ∣ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ ∣ u ⦆ ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ tup[ i ] u ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ left u ∣ v = ⊑-refl
fro-⊔-⊑ ⦅ right u ∣ v = ⊑-refl
fro-⊔-⊑ ω v = ⊑-refl
fro-⊔-⊑ ν v = ⊑-refl
fro-⊔-⊑ (const k) v = ⊑-refl
fro-⊔-⊑ (u ⊔ u₁) v = ⊑-refl
fro-⊔-⊑ (u ↦ u₁) v = ⊑-refl
fro-⊔-⊑ ∣ u ⦆ v = ⊑-refl
fro-⊔-⊑ (tup[ i ] u) v = ⊑-refl
fro-⊔-⊑ (left u) v = ⊑-refl
fro-⊔-⊑ (right u) v = ⊑-refl

fro-split-⊑ : ∀ {u uL uR} → uL ◃ u ▹ uR
            → fro u ⊑ fro (uL ⊔ uR)
fro-split-⊑ {.(uL ⊔ uR)} {uL} {uR} split-⊔ = ⊑-refl
fro-split-⊑ {.(_ ↦ _)} {.(_ ↦ _)} {.(_ ↦ _)} (split-↦ split) = ⊑-ω
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ V ↦ uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ ω ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ ν ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ const k ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ uL ⊔ uL₁ ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ ⦅ uL ∣ ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ ∣ uL ⦆ ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ tup[ i ] uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ left uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ right uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ ω ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ ν ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ const k ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ (uL ⊔ uL₁) ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ ⦅ uL ∣ ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ ∣ uL ⦆ ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ tup[ i ] uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ left uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {⦅ u ∣} {⦅ FV ↦ right uL ∣} {⦅ uR ∣} (split-fst split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {.(∣ _ ⦆)} {.(∣ _ ⦆)} {.(∣ _ ⦆)} (split-snd split) = ⊑-⊔-R1 ⊑-ν-ν
fro-split-⊑ {.(tup[ _ ] _)} {.(tup[ _ ] _)} {.(tup[ _ ] _)} (split-tup split) = 
       {!   !}
fro-split-⊑ {.(left _)} {.(left _)} {.(left _)} (split-left split) = {!   !}
fro-split-⊑ {.(right _)} {.(right _)} {.(right _)} (split-right split) = {!   !}   

-}

{- 
fro-split-⊑ : ∀ {u uL uR v} → uL ◃ u ▹ uR 
              → uL ⊑ v → uR ⊑ v
              → (∀ w → uL ⊑ w → fro uL ⊑ fro w) 
              → (∀ w → uR ⊑ w → fro uR ⊑ fro w)
            ------------------------------------- 
              → fro u ⊑ fro v
fro-split-⊑ {u}{uL}{uR}{v} split L⊑ R⊑ IHL IHR = ⊑-trans H3 H2
   where
   H1 : u ⊑ uL ⊔ uR
   H1 = ⊑-dist-⊔ split
   IHL' : fro uL ⊑ fro v
   IHL' = IHL v L⊑
   IHR' : fro uR ⊑ fro v
   IHR' = IHR v R⊑
   H2 : fro (uL ⊔ uR) ⊑ fro v
   H2 = {!   !}
   H3 : fro u ⊑ fro (uL ⊔ uR)
   H3 = fro-split-⊑ split (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl) IHL IHR
-}

      {-
fro-split-⊑ {.(uL ⊔ uR)} {uL} {uR} {v} split-⊔ L⊑ R⊑ IHL IHR = 
  {!   !}
fro-split-⊑ {.(_ ↦ _)} {.(_ ↦ _)} {.(_ ↦ _)} {v} (split-↦ split) L⊑ R⊑ IHL IHR = 
  ⊑-ω
fro-split-⊑ {u} {uL} {uR} {v ⊔ w} split (⊑-⊔-R1-å åu L⊑) R⊑ IHL IHR = 
  ⊑-trans (⊑-⊔-R1  (fro-split-⊑ split L⊑ {!   !} IHL IHR)) (fro-⊔-⊑ v w)
fro-split-⊑ {u} {uL} {uR} {v ⊔ w} split (⊑-⊔-R2-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(⦅ _ ∣)} {.(⦅ _ ∣)} {.(⦅ _ ∣)} {.(⦅ _ ∣)} (split-fst split) (⊑-fst-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(⦅ _ ∣)} {.(⦅ _ ∣)} {.(⦅ _ ∣)} {v} (split-fst split) (⊑-split split₁ L⊑ L⊑₁) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(∣ _ ⦆)} {.(∣ _ ⦆)} {.(∣ _ ⦆)} {.(∣ _ ⦆)} (split-snd split) (⊑-snd-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(∣ _ ⦆)} {.(∣ _ ⦆)} {.(∣ _ ⦆)} {v} (split-snd split) (⊑-split split₁ L⊑ L⊑₁) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(tup[ _ ] _)} {.(tup[ _ ] _)} {.(tup[ _ ] _)} {.(tup[ _ ] _)} (split-tup split) (⊑-tup-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(tup[ _ ] _)} {.(tup[ _ ] _)} {.(tup[ _ ] _)} {v} (split-tup split) (⊑-split split₁ L⊑ L⊑₁) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(left _)} {.(left _)} {.(left _)} {.(left _)} (split-left split) (⊑-left-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(left _)} {.(left _)} {.(left _)} {v} (split-left split) (⊑-split split₁ L⊑ L⊑₁) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(right _)} {.(right _)} {.(right _)} {.(right _)} (split-right split) (⊑-right-å åu L⊑) R⊑ IHL IHR = {!   !}
fro-split-⊑ {.(right _)} {.(right _)} {.(right _)} {v} (split-right split) (⊑-split split₁ L⊑ L⊑₁) R⊑ IHL IHR = {!   !}
-}
{-

          uL ⊑ v   uL ◃ u ▹ uR   uR ⊑ v
⊑-split  ----------------------------------
                      u ⊑ v

⊑-split         uL ---------
                  \          \
                    u - - - - v
                  /          /
                 uR ---------

                fro uL ---------
                                \
                   fro u - - - - fro v
                                /
                fro uR ---------


to-split-⊑ : ∀ {u uL uR} → uL ◃ u ▹ uR → to u ⊑ (to uL ⊔ to uR)
to-split-⊑ split-⊔ = ⊔⊑⊔ ⊑-refl ⊑-refl
to-split-⊑ { u ↦ v}{ u ↦ vL}{ u ↦ vR} (split-↦ split) = 
  ⊑-⊔-L (⊑-trans {⦅ to FV ↦ to u ↦ to v ∣}
    {⦅ to FV ↦ to u ↦ to vL ∣ ⊔ ⦅ to FV ↦ to u ↦ to vR ∣}
    {⦅ to FV ↦ to u ↦ to vL , to FV ⦆' ⊔  ⦅ to FV ↦ to u ↦ to vR , to FV ⦆'}
     (⊑-trans {⦅ to FV ↦ to u ↦ to v ∣}{⦅ to FV ↦ to u ↦ (to vL ⊔ to vR) ∣}
                       {⦅ to FV ↦ to u ↦ to vL ∣ ⊔ ⦅ to FV ↦ to u ↦ to vR ∣} 
                       (⊑-fst (⊑-↦ ⊑-refl (⊑-↦ ⊑-refl (to-split-⊑ split)))) 
                       (⊑-dist-⊔ (split-fst (split-↦ (split-↦ split-⊔))))) 
                       (⊔⊑⊔ (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R1 ⊑-refl))) 
                       (⊑-⊔-R1 (⊑-⊔-R2 ⊑-refl))
to-split-⊑ (split-fst split) = ⊑-trans (⊑-fst (to-split-⊑ split)) 
                                           (⊑-dist-⊔ (split-fst split-⊔))
to-split-⊑ (split-snd split) = ⊑-trans (⊑-snd (to-split-⊑ split)) 
                                           (⊑-dist-⊔ (split-snd split-⊔))
to-split-⊑ (split-tup split) = ⊑-trans (⊑-tup (to-split-⊑ split)) 
                                           (⊑-dist-⊔ (split-tup split-⊔))
to-split-⊑ (split-left split) = ⊑-trans (⊑-left (to-split-⊑ split)) 
                                           (⊑-dist-⊔ (split-left split-⊔))
to-split-⊑ (split-right split) = ⊑-trans (⊑-right (to-split-⊑ split)) 
                                           (⊑-dist-⊔ (split-right split-⊔))

-}

{- I need to deal with splitting in a somewhat similar fashion to to-mono 
... I also want lemmas for "u ⊑ vL ⊔ vR" to handle the diversity of cases
... probably should get splitting going first.  

-}


{-  with FV d≟ FV'
... | yes refl = (fro FV) ⊢ fro V ↦ fro w
... | no neq = ν
fro (u ⊔ v) = fro u ⊔ fro v
-}
{-
fro-mono : ∀ {u v} → u ⊑ v → fro u ⊑ fro v
fro-mono {.ω} ⊑-ω = ⊑-ω
fro-mono {.ν} ⊑-ν-ν = ⊑-ω
fro-mono {.ν} ⊑-ν-↦ = ⊑-ω
fro-mono {.(const _)} ⊑-const = ⊑-const
fro-mono {u} {vL ⊔ vR} (⊑-⊔-R1-å åu u⊑v) with vL | vR
... | ω | v' = {!   !}
... | ν | v' = {!   !}
... | const k | v' = {!   !}
... | u' ⊔ u'' | v' = {!   !}
... | u' ↦ u'' | v' = {!   !}
... | ∣ u' ⦆ | v' = {!   !}
... | tup[ i ] u' | v' = {!   !}
... | left u' | v' = {!   !}
... | right u' | v' = {!   !}
... | ⦅ FV ↦ (V ↦ w) ∣ | ∣ FV' ⦆ with  FV d≟ FV'
... | yes refl = {!   !}
... | no neq = {!   !}
fro-mono {u} {vL ⊔ vR} (⊑-⊔-R1-å åu u⊑v) | ⦅ u' ∣ | v' = {!   !}
fro-mono {u} {vL ⊔ vR} (⊑-⊔-R2-å åu u⊑v) = {!   !}
fro-mono {.(⦅ _ ∣)} (⊑-fst-å åu u⊑v) = {!   !}
fro-mono {.(∣ _ ⦆)} (⊑-snd-å åu u⊑v) = {!   !}
fro-mono {.(tup[ _ ] _)} (⊑-tup-å åu u⊑v) = ⊑-tup (fro-mono u⊑v)
fro-mono {.(_ ↦ _)} (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
fro-mono {.(left _)} (⊑-left-å åu u⊑v) = ⊑-left (fro-mono u⊑v)
fro-mono {.(right _)} (⊑-right-å åu u⊑v) = ⊑-right (fro-mono u⊑v)
fro-mono {u} (⊑-split split u⊑v u⊑v₁) = {!   !}
-}
{-


fros-nth : ∀ {n} V i → fro (OpTarget.nth {n} V i) ≡ OpSource.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i


delay-reflect : ∀ M ρ
  {- → (ρ~ : ∀ₑ ⊔-closed' ρ) -}
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
delay-reflect (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
  ⦅ FV ↦ V ↦ w , d₁ ⦆' ⟨ ⟨ FV' , ⟨ w∈ , FV'∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ 
  with FV d≟ d₁
... | yes refl = ⟨ ω , ⟨ fro FV , ⟨ ω ⊢ fro V ↦ fro w 
                 , ⟨ G1 , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IH : fro w ∈ ⟦ N ⟧ (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)))
  IH = delay-reflect N ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)) w w∈
  H : (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω))) ⊆ₑ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono !}
  H (suc zero) d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono !}
  H (suc (suc i)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) IH
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) (u ⊔ u₁) u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G2 (suc n) (fv ,, fvs) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) ∥ ds ∥ u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro d₁ ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs d₁ d₁∈
... | no neq = ⟨ ω , ⟨ fro d₁ , ⟨ ν 
                , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) (u ⊔ u₁) u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G2 (suc n) (fv ,, fvs) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩
    = ⟨ G2 (suc n) (fv ,, fvs) ∥ ds ∥ u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro d₁ ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs d₁ d₁∈

{-
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV ↦ ν , d₁ ⦆' 
   ⟨ ⟨ FV' , ⟨ ν∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ = 
   ⟨ ω , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV ↦ (w ⊔ w₁) , d₁ ⦆' 
   ⟨ ⟨ FV' , ⟨ w∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
   ⟨ ω , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ ν , d₁ ⦆' 
  ⟨ ⟨ FV , ⟨ ν∈ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
  ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ u ⊔ v , d₁ ⦆' 
  ⟨ ⟨ FV , ⟨ ⟨ u∈ , v∈ ⟩ , FV∈ ⟩ ⟩ , ⟨ f , ⟨ f∈ , d₁∈ ⟩ ⟩ ⟩ =
  ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} 
   , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (u ⊔ v) ⟨ u∈ , v∈ ⟩ 
  with delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ u u∈
     | delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ v v∈
... | IHu | IHv = ⟦⟧-⊔-closed (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) (env-map fro ρ) (fro u) (fro v) IHu IHv
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ d ∣  
  ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ = {!   !}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ∣ d ⦆ 
  ⟨ FV , ⟨ d∈ , FV∈ ⟩ ⟩ = {!   !}
-}


delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d 
  ⟨ V , ⟨ ⟨ FV , ⟨ FV↦V↦d∈carM' , FV∈cdrM' ⟩ ⟩ , V∈N ⟩ ⟩ 
  = ⟨ fro FV , ⟨ fro V , ⟨ IHM , IHN ⟩ ⟩ ⟩
  where
  IHN : fro V ∈ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect N ρ V V∈N
  ⦅FV↦V↦d,FV⦆∈M' : ⦅ FV ↦ (V ↦ d) , FV ⦆' ∈ ⟦ delay M ⟧' ρ
  ⦅FV↦V↦d,FV⦆∈M' = 
      ⟦⟧'-⊔-closed (delay M) ρ ⦅ FV ↦ V ↦ d ∣ ∣ FV ⦆ FV↦V↦d∈carM' FV∈cdrM'
  IHM : (fro  fro V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV d≟ FV 
        | delay-reflect M ρ ⦅ FV ↦ (V ↦ d) , FV ⦆' ⦅FV↦V↦d,FV⦆∈M' 
  ... | yes refl | IHM' = IHM'
  ... | no neq | IHM' = ⊥-elim (neq refl)
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const k₁ ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (lit B k ⦅ Nil ⦆) ρ (const k₁) u∈ 
     , delay-reflect (lit B k ⦅ Nil ⦆) ρ v v∈ ⟩
delay-reflect (lit B k ⦅ Nil ⦆) ρ (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (lit B k ⦅ Nil ⦆) ρ (u ⊔ u₁) u∈ 
     , delay-reflect (lit B k ⦅ Nil ⦆) ρ v v∈ ⟩
delay-reflect (tuple n ⦅ args ⦆) ρ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d d∈ , ds'∈ ⟩
  G (suc n) (arg ,, args) (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) (u ⊔ u₁) u∈ , G (suc n) (arg ,, args) v v∈ ⟩
  G (suc n) (arg ,, args) (∥ ds ∥ ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) ∥ ds ∥ u∈ , G (suc n) (arg ,, args) v v∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d 
  ⟨ n , ⟨ ds , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ n , ⟨ fros ds , ⟨ delay-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ((u ⊔ u₁) ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁) u∈ 
    , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ((left u) ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left u) u∈ 
    , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁ ⊔ v) ⟨ u∈ , v∈ ⟩ 
  = ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (u ⊔ u₁) u∈ 
    , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right u ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right u) u∈ 
    , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ v v∈ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M ((⊑-closure' V) • ρ) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono  !}
    H (suc i) d d∈ = d∈
    G : left (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ (left V) LV∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) =
   inj₂ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N ((⊑-closure' V) • ρ) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = {! fro-mono  !}
    H (suc i) d d∈ = d∈
    G : right (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ (right V) RV∈


{-

⦅ ν , FV ⦆ 
  ⟨ tt , FV∈ ⟩ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ tt , FV∈ ⟩ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ w∈N , FV∈ ⟩ 
  with FV' d≟' FV
... | no FV'≠ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ w∈N , FV∈ ⟩ | yes refl = ⟨ ω , ⟨ fro FV , ⟨ ω ⊢ fro V ↦ fro w , ⟨ G1 , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  init-closed : ∀ₑ ⊔-closed' (λ i v → v ≡ ω)
  init-closed i = singleton-⊔-closed' ω
  IH : fro w ∈ ⟦ N ⟧ (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)))
  IH = delay-reflect N ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)) 
                     (∀ₑ-ext ⊔-closed' (∀ₑ-ext ⊔-closed' init-closed 
                                       (⊑-closure'-⊔-closed FV')) 
                                       (⊑-closure'-⊔-closed V)) w w∈N
  H : (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω))) ⊆ₑ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
  H (suc zero) d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
  H (suc (suc i)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) IH
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (u ⊔ v) , FV ⦆ 
  d∈
  = {!   !}
  {- TODO: I just need to try these cases out; not sure yet what to expect. -}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ u ⊔ v , FV ⦆ 
  d∈
  = {!   !}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ (u ⊔ v) 
  ⟨ u∈ , v∈ ⟩ 
  with delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ u u∈ 
    | delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ v v∈ 
... | IHu | IHv with ⊔-closed-⟦⟧ (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
                                  (env-map fro ρ) {!   !} (fro u) (fro v) IHu IHv
... | ⟨ u⊔v , ⟨ u⊔v∈ , u⊔v⊑ ⟩ ⟩ = 
  ⊑-closed-⟦⟧ (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) (env-map fro ρ)
     {!   !} {!   !} {!   !} u⊔v∈ u⊔v⊑
{-
... | ⟨ FVu , ⟨ Vu , ⟨ wu , ⟨ arru∈ΛΛN , ⟨ Vu∈𝒯fvs , u'≡Vwu ⟩ ⟩ ⟩ ⟩ ⟩ 
    | ⟨ FVv , ⟨ Vv , ⟨ wv , ⟨ arrv∈ΛΛN , ⟨ Vv∈𝒯fvs , v'≡Vwv ⟩ ⟩ ⟩ ⟩ ⟩
  = ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
  -}
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , V∈N' ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ ⟨ FV' , ⦅FV↦[V↦d],FV'⦆∈M' ⟩ , ⟨ f , ⦅f,FV⦆∈M' ⟩ ⟩ ⟩
   = ⟨ fro FV , ⟨ fro V , ⟨ IH , delay-reflect N ρ ρ~ V V∈N' ⟩ ⟩ ⟩
  where
  pre-witness : ⦅ (FV ↦ (V ↦ d)) ⊔ f , FV' ⊔ FV ⦆ ∈ ⟦ delay M ⟧' ρ
  pre-witness = {!   !}
  witness : ⦅ FV ↦ (V ↦ d) , FV ⦆ ∈ ⟦ delay M ⟧' ρ
  witness = ⊑-closed-⟦⟧' (delay M) ρ {!   !} 
            ⦅ FV ↦ V ↦ d , FV ⦆ ⦅ FV ↦ V ↦ d ⊔ f , FV' ⊔ FV ⦆ pre-witness
            (⊑-pair (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl))
  IH : (fro  fro V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IH with FV d≟' FV | delay-reflect M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ⦆ witness
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | yes refl | IH' = IH'
delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ u u∈ 
     , delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ ρ~ d d∈ , ds'∈ ⟩
  G (suc n) (arg ,, args) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) u u∈ , G (suc n) (arg ,, args) v v∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ ρ~ d 
  ⟨ n , ⟨ ds , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ n , ⟨ fros ds , ⟨ delay-reflect M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect M ρ ρ~ v v∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ u u∈ 
  , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect M ρ ρ~ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ u u∈ 
  , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M ((⊑-closure' V) • ρ) (∀ₑ-ext ⊔-closed' ρ~ (⊑-closure'-⊔-closed V)) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : left (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ ρ~ (left V) LV∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) =
   inj₂ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N ((⊑-closure' V) • ρ) (∀ₑ-ext ⊔-closed' ρ~ (⊑-closure'-⊔-closed V)) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : right (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ ρ~ (right V) RV∈



{-




fro-set : 𝒫 Value → 𝒫 Value
fro-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fros-nth : ∀ {n} V i → fro (OpTarget.nth {n} V i) ≡ OpSource.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i


fro-mono : ∀ {u v} → u ⊑ v → fro u ⊑ fro v
fro-mono ⊑-ω = ⊑-ω
fro-mono ⊑-ν-ν = ⊑-ω
fro-mono ⊑-ν-↦ = ⊑-ω
fro-mono ⊑-const = ⊑-const
fro-mono (⊑-⊔-R1-å åu u⊑v) = ⊑-⊔-R1 (fro-mono u⊑v)
fro-mono (⊑-⊔-R2-å åu u⊑v) = ⊑-⊔-R2 (fro-mono u⊑v)
fro-mono (⊑-pair-å {u} {u'} {v} {v'} åfst åsnd u⊑v u⊑v₁) = {!  !}
fro-mono ⊑-nil = ⊑-nil
fro-mono (⊑-tup-å åus u⊑v u⊑v₁) = ⊑-tup (fro-mono u⊑v) (fro-mono u⊑v₁)
fro-mono (⊑-↦-å åu₂ u⊑v u⊑v₁) = ⊑-ω
fro-mono (⊑-left-å åu u⊑v) = ⊑-left (fro-mono u⊑v)
fro-mono (⊑-right-å åu u⊑v) = ⊑-right (fro-mono u⊑v)
fro-mono (⊑-split split u⊑v u⊑v₁) = 
  ⊑-split {!   !} (fro-mono u⊑v) (fro-mono u⊑v₁)

{-
fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)
-}

reg-⊔-closed' : (𝒫 Value) → Set
reg-⊔-closed' D = ∀ u v → u ∈ D → v ∈ D → (u ⊔ v) ∈ D

postulate 
  ⊔-closed-⟦⟧ : ∀ M ρ
    → (ρ~ : ∀ₑ ⊔-closed ρ)
    → ⊔-closed (⟦ M ⟧ ρ)
  ⊔-closed-⟦⟧' : ∀ M ρ 
    → (ρ~ : ∀ₑ ⊔-closed' ρ)
    → ⊔-closed' (⟦ M ⟧' ρ)
  ⊑-closed-⟦⟧ : ∀ M ρ
    → (ρ~ : ∀ₑ ⊑-closed ρ)
    → ⊑-closed (⟦ M ⟧ ρ)
  ⊑-closed-⟦⟧' : ∀ M ρ
    → (ρ~ : ∀ₑ ⊑-closed' ρ)
    → ⊑-closed' (⟦ M ⟧' ρ)
  reg-⊔-closed-⟦⟧' : ∀ M ρ
    → (ρ~ : ∀ₑ reg-⊔-closed' ρ)
    → reg-⊔-closed' (⟦ M ⟧' ρ) 

keylemma : ∀ M ρ {u1 u2 v1 v2} → ⦅ u1 , u2 ⦆ ∈ ⟦ M ⟧' ρ → ⦅ v1 , v2 ⦆ ∈ ⟦ M ⟧' ρ
         → ⦅ u1 , v2 ⦆ ∈ ⟦ M ⟧' ρ
keylemma M ρ u∈ v∈ = {!   !}   
 {-
   where
   uv1∈car : u1 ⊔ v1 ∈ ⟦ car ⦅ M ,, Nil ⦆' ⟧' ρ
   uv1∈car = ? {- by ⊔-closed of car M -}



       then ⦅ u1 ⊔ v1 , FV ⦆ ∈ M 
       


       ⦅ u1 ⊔ v1 ⊔ stuff1 , u2 ⊔ v2 ⊔ stuff2 ⦆ ∈ M {!   !}

    
    easy: ⦅ u1 , u2 ⦆ ⊔ ⦅ v1 , v2 ⦆  ∈ M
    
      ⦅ u1 ⊔ v1 , u2 ⊔ v2 ⦆ < ⦅ u1 , u2 ⦆ ⊔ ⦅ v1 , v2 ⦆  ???


      ⦅ u1 ⊔ v1 , w ⦆ < ⦅ u1 , w ⦆ ⊔ ⦅ v1 , w ⦆


⦅ u1 ⊔ v1 , u2 ⊔ v2 ⦆ < (⦅ u1 , v2 ⦆ ⊔ ⦅ u2 , v2 ⦆) ⊔ (⦅ u1 , u2 ⦆ ⊔ ⦅ v1 , u2 ⦆) 


⦅ u1 ⊔ u2 , v ⦆ ==> ⦅ u1 , v ⦆ ⦅ u2 , v ⦆


  
 →           u₁ ◃ u ▹ u₂
 →           v₁ ◃ v ▹ v₂
     → ⦅ u₁ , v₁ ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u₂ , v₂ ⦆

 →           u₁ ◃ u ▹ u₂
 →           v₁ ◃ v ▹ v₂
     → ⦅ u₁ , v₂ ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u₂ , v₁ ⦆

Atomic v
→ v ◃ v ▹ v


  split-pair-fst : ∀ {u u₁ u₂ v}
        →           u₁ ◃ u ▹ u₂ 
      -------------------------------------
        → ⦅ u₁ , v ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u₂ , v ⦆

  split-pair-snd : ∀ {u v v₁ v₂}
        → Atomic u
        →           v₁ ◃ v ▹ v₂
      --------------------------------------
        → ⦅ u , v₁ ⦆ ◃ ⦅ u , v ⦆ ▹ ⦅ u , v₂ ⦆


    ⊑-split : ∀ {u u₁ u₂ v}
       → (split : u₁ ◃ u ▹ u₂)
       → (⊑L : u₁ ⊑ v)
       → (⊑R : u₂ ⊑ v)
      -------------
       → u ⊑ v

      ⦅ u1 , v2 ⦆  <  ⦅ u1 , u2 ⦆ ⊔ ⦅ v1 , v2 ⦆  ????      

      (f,f) < (f,g) ⊔ (g,f)
                 in pair D1 D2
                 in app D1 D2

      (a,d) < (a,b) ⊔ (c,d)
      

      these being equal then that's sort of like a determinism property


      DEFINITELY TRUE: ⦅ u1 , u2 ⦆ ⊔ ⦅ v1 , v2 ⦆ < ⦅ u1 ⊔ v1 , u2 ⊔ v2 ⦆ 
             split
             <-pair
             <-pair



       -}
   


delay-reflect : ∀ M ρ
  → (ρ~ : ∀ₑ ⊔-closed' ρ)
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
delay-reflect (` x) ρ ρ~ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ ν , FV ⦆ 
  ⟨ tt , FV∈ ⟩ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ tt , FV∈ ⟩ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ w∈N , FV∈ ⟩ 
  with FV' d≟' FV
... | no FV'≠ = ⟨ ω , ⟨ fro FV , ⟨ ν , ⟨ tt , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where 
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ w∈N , FV∈ ⟩ | yes refl = ⟨ ω , ⟨ fro FV , ⟨ ω ⊢ fro V ↦ fro w , ⟨ G1 , ⟨ G3 , refl ⟩ ⟩ ⟩ ⟩ ⟩
  where
  init-closed : ∀ₑ ⊔-closed' (λ i v → v ≡ ω)
  init-closed i = singleton-⊔-closed' ω
  IH : fro w ∈ ⟦ N ⟧ (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)))
  IH = delay-reflect N ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω)) 
                     (∀ₑ-ext ⊔-closed' (∀ₑ-ext ⊔-closed' init-closed 
                                       (⊑-closure'-⊔-closed FV')) 
                                       (⊑-closure'-⊔-closed V)) w w∈N
  H : (env-map fro ((⊑-closure' V) • (⊑-closure' FV) • (λ i d → d ≡ ω))) ⊆ₑ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
  H (suc zero) d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
  H (suc (suc i)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ ((⊑-closure (fro V)) • (⊑-closure (fro FV)) • (λ i d → d ≡ ω))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) IH
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G2 (suc n) (fv ,, fvs) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G2 (suc n) (fv ,, fvs) u u∈ , G2 (suc n) (fv ,, fvs) v v∈ ⟩
  G3 : fro FV ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 = G2 n fvs FV FV∈
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (u ⊔ v) , FV ⦆ 
  d∈
  = {!   !}
  {- TODO: I just need to try these cases out; not sure yet what to expect. -}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ u ⊔ v , FV ⦆ 
  d∈
  = {!   !}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ (u ⊔ v) 
  ⟨ u∈ , v∈ ⟩ 
  with delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ u u∈ 
    | delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ v v∈ 
... | IHu | IHv with ⊔-closed-⟦⟧ (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
                                  (env-map fro ρ) {!   !} (fro u) (fro v) IHu IHv
... | ⟨ u⊔v , ⟨ u⊔v∈ , u⊔v⊑ ⟩ ⟩ = 
  ⊑-closed-⟦⟧ (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) (env-map fro ρ)
     {!   !} {!   !} {!   !} u⊔v∈ u⊔v⊑
{-
... | ⟨ FVu , ⟨ Vu , ⟨ wu , ⟨ arru∈ΛΛN , ⟨ Vu∈𝒯fvs , u'≡Vwu ⟩ ⟩ ⟩ ⟩ ⟩ 
    | ⟨ FVv , ⟨ Vv , ⟨ wv , ⟨ arrv∈ΛΛN , ⟨ Vv∈𝒯fvs , v'≡Vwv ⟩ ⟩ ⟩ ⟩ ⟩
  = ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
  -}
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , V∈N' ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ ⟨ FV' , ⦅FV↦[V↦d],FV'⦆∈M' ⟩ , ⟨ f , ⦅f,FV⦆∈M' ⟩ ⟩ ⟩
   = ⟨ fro FV , ⟨ fro V , ⟨ IH , delay-reflect N ρ ρ~ V V∈N' ⟩ ⟩ ⟩
  where
  pre-witness : ⦅ (FV ↦ (V ↦ d)) ⊔ f , FV' ⊔ FV ⦆ ∈ ⟦ delay M ⟧' ρ
  pre-witness = {!   !}
  witness : ⦅ FV ↦ (V ↦ d) , FV ⦆ ∈ ⟦ delay M ⟧' ρ
  witness = ⊑-closed-⟦⟧' (delay M) ρ {!   !} 
            ⦅ FV ↦ V ↦ d , FV ⦆ ⦅ FV ↦ V ↦ d ⊔ f , FV' ⊔ FV ⦆ pre-witness
            (⊑-pair (⊑-⊔-R1 ⊑-refl) (⊑-⊔-R2 ⊑-refl))
  IH : (fro  fro V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IH with FV d≟' FV | delay-reflect M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ⦆ witness
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | yes refl | IH' = IH'
delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩
  = ⟨ delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ u u∈ 
     , delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ ρ~ d d∈ , ds'∈ ⟩
  G (suc n) (arg ,, args) (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
    ⟨ G (suc n) (arg ,, args) u u∈ , G (suc n) (arg ,, args) v v∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ ρ~ d 
  ⟨ n , ⟨ ds , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ n , ⟨ fros ds , ⟨ delay-reflect M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect M ρ ρ~ v v∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ u u∈ 
  , delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect M ρ ρ~ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = 
  ⟨ delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ u u∈ 
  , delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ v v∈ ⟩
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩) = 
   inj₁ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M ((⊑-closure' V) • ρ) (∀ₑ-ext ⊔-closed' ρ~ (⊑-closure'-⊔-closed V)) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : left (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ ρ~ (left V) LV∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩) =
   inj₂ ⟨ fro V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N ((⊑-closure' V) • ρ) (∀ₑ-ext ⊔-closed' ρ~ (⊑-closure'-⊔-closed V)) d d∈) ⟩ ⟩
    where
    H : env-map fro ((⊑-closure' V) • ρ) ⊆ₑ (⊑-closure (fro V)) • env-map fro ρ
    H zero d ⟨ a , ⟨ a⊑ , refl ⟩ ⟩ = fro-mono a⊑
    H (suc i) d d∈ = d∈
    G : right (fro V) ∈ ⟦ L ⟧ (env-map fro ρ)
    G = delay-reflect L ρ ρ~ (right V) RV∈



{-

delay-reflect' : ∀ M ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ 
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ ρ~ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ ν , FV ⦆ 
  ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  = ?
{-

  with FV' mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → LangTarget.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → LangSource.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → LangSource.init))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
-}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ with FV↦[V↦d]∈carM'
... | ⟨ FV' , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ = 
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect'-⊆ N ρ ρ~ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ ρ~) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros  fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM = ?
{- with FV mem⊆? (FV ++ FV') | delay-reflect' M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV)) -}
delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect' (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ ρ~ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ~ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect' M (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (left b) (LV∈ b b∈)
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect' N (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (right b) (RV∈ b b∈)
delay-reflect'-⊆ M ρ ρ~ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ ρ~ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ ρ~ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ ρ~ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ ρ~ = 
  ⟨ lift (delay-reflect' M ρ ρ~) , del-map-args-reflect' args ρ ρ~ ⟩


-}




{-


{-
reverse direction explanation and design decisions:

Our values for this direction include annotated pairs.
All pairs represent closures, and they contain a single value followed 
  by a list of values.
⦅ u , V ⦆

The interesting case is when the first part contains a (2-ary) function 
  and the second part contains a rep of the captured local environment.
⦅ FV' ↦ (V ↦ w) , FV ⦆
  When such closures are applied, we apply the first projection 
  to the second projection and then to the argument.
  Given such a value, we can determine that the
  application succeeds if FV' ⊆ FV. However, if FV' ⊈ FV,
  we cannot conclude that the application fails. This is because we take
  first and second projections of the denotation: a set of such pairs.
  What we really need to track is whether,
Given a pair ⦅ FV' ↦ (V ↦ w) , FV ⦆ in a denotation D,
  is FV' ⊆ cdr D or not?
This is something that we can determine when we create the pairs and carry as an annotation.
  ⦅ FV' ↦ (V ↦ w) , FV ⦆ ∈ D
  where 
  b = true when FV' ⊆ cdr D, and
  b = false otherwise (but everything else about the denotation of pair holds)
Intuitively, this means that when a lambda generates a pair that represents
  self-application (of the function in the closure to its captured environment)
  we mark that pair with true. And when it generates a pair based on taking
  some garbage as input (a pair outside of the calling convention), then
  we mark that pair as false.


For the closure case, these annotations are sufficient for us to have a theorem
  written with a function fro : Value → Value such that we get the theorem 
delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ).
  The function is simply based on whether self-application would succeed or fail
  on the value; if it would fail, we map it to the empty function which is
  always in a function declaration.

fro ⦅ ν , FV ⦆) = fros ν
fro ⦅ FV' ↦ ν , FV ⦆) = fros ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros FV' ⊢ fros V ↦ fro w
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros ν {- NOT for app; this a default value for closure case -}
fro ⦅ u , v ⦆) = ω

app M N ->  ((car M')  (cdr M')) N'
d' ∈ target ==> d ∈ source  (where d' ~ d)

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ u , V ⦆) = u ∈ D₁ × mem V ⊆ D₂ × V ≢ []
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ U ↦ w , V ⦆) = 
   (mem U ⊆ D₂ × U ≢ []) × (U ↦ w ∈ D₁) × mem V ⊆ D₂ × V ≢ []
{- could do U ⊆ V also, would get neU for free -}
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False


let y = 5; let g = λ x. y x; (g 2)
              ν               ν · 2
let y = 5; < λ f. λ x. f[0] x , [ y ] > ; ((g[0] g[1]) 2)
           ⦅ ([ 2 ↦ 3 ]) ↦ (2 ↦ 3) , [ 5 ] ⦆    (([ 2 ↦ 3 ]) ↦ (2 ↦ 3)) · [ 5 ] · 2
           ⦅ ([ 5 ]) ↦ XX , [ 5 ] ⦆                 can we prove ν ∈ g[0] g[1] XX
let d' ∈ delay (application)
  ...  case (looks bad)  -> contradiction
      => bad[0] bad[1] = {ν} ... contradicts that the app succeeds.
  ...  case (looks good) -> straightforward proof

let d' ∈ delay (application)
  - things we know
  -> construct a nice enough pair of values
    FV ↦ V ↦ d ∈ g[0] and FV' ⊆ g[1]
    ⦅ FV ↦ V ↦ d , XX ⦆ ∈ g
     and we know FV ⊆ cdr g
    ∀ fv ∈ FV' → ∃ ?,V → ⦅ XX , V ⦆ ∈ g × fv ∈ V

    then, there must be a single pair that is "good"
    ⦅ FV ↦ V ↦ d , FV' ⦆ ∈ g   -> application succeeds, we get result.
    then fro (construction) ∈ the application
      because 



However, such a function will not be enough for an application case.
While a "false" tag indicates that an application of the arrow should fail,
this information is available at the closure introduction site, but 
this information isn't available at the application site... so we define
a logical relation to carry that information.

...
a potential problem or complication: a "false" tag as currently defined
doesn't actually indicate that the application will fail, but 
is just not a guarantee of success. If we wanted "false" to indicate
the negation of FV' ⊆ FV... then our pair operator may no longer be monotonic.

...
another approach that we can use to tackle this (while using a function)
is to prove that given our compatible first and second projections, there
exists a pair which contains both of those projections in the denotation.
This is a pain, because it essentially requires proving down-closed-ness on
an ordering and union-closed-ness on denotations in our language.
I'll want to do this proof on paper befrore I attempt it, because
I'm not certain at this moment that the approach guarantees success.

...
Another approach might be to prove that
any time a pair is in a denotation and self-application succeeds, then
there exists a true-tagged version of that pair in the denotation as well.
-}

{-
Current attempt:
I'm fairly committed to avoiding ordering and joining, so let's first try
the relational approach, but while sidestepping the monotonicity problem...

The idea is to push all of the info in the annotation into the relation,
and "remove the annotation to permit monotonicity".

...or in our case, we simply ignore the existing annotation, which already
permits monotonicity.

f ∈ car g 
FV ⊆ cdr g
----------------
⦅ f , FV ⦆ ∈ g


g1 ⊔ g2 ⊑ g 



application union-closed

(a ↦ b) union (c ↦ d)  

x , x' ∈ app A B
x union x' ∈ app A B

(a ↦ x) , (a' ↦ x') ∈ A
a , a' ∈ B
a union a' ∈ B
(a union a' ↦ x union x′) ∈ A

we know a ↦ x union a' ↦ x' ∈ A (by IH of union-closed)
a union a' ↦ x union x'  ⊑ a ↦ x union a' ↦ x' is true
... use ⊑-closed to finish the proof.

a ↦ x
a' ↦ x'
a intersection a' ↦ x union x'

a ⊔ b ∈ D =  a ∈ D ∧ b ∈ D

A ↦ (x,Y) ⊔ A ↦ (x',Y')
(or A and A', but A ~ A' guaranteed)
A ↦ (x ⊔ x' , Y ++ Y') 


-}

{-

{-
data add2cdr : Value → Value → Value → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆

get-cdr : ∀ (D : 𝒫 Value) u {v u+v} → add2cdr u v u+v
        → 𝒫 Value
get-cdr D u +cdr-pair = cdr ⟨ D , ptt ⟩
get-cdr D (V ↦ w) (+cdr-↦ +cdr) = 
  get-cdr (OpTarget.⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩) w +cdr
get-cdr D (left u) (+cdr-left +cdr) = 
  get-cdr (OpTarget.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D (right u) (+cdr-right +cdr) =
  get-cdr (OpTarget.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-head +cdr) = 
  get-cdr (OpTarget.proj 0 ⟨ D , ptt ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-tail +cdr) = 
  get-cdr (rest ⟨ D , ptt ⟩) ∥ us ∥ +cdr
get-cdr D ⦅ u , V ⦆ (+cdr-car +cdr) = 
  get-cdr (car ⟨ D , ptt ⟩) u +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-here +cdr) = 
  get-cdr (cdr ⟨ D , ptt ⟩) v +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-there +cdr) = 
  get-cdr D ⦅ u , V ⦆ +cdr

get-cdr-mono : ∀ {D D'} u {v u+v} (+cdr : add2cdr u v u+v) 
             → D' ⊆ D' → get-cdr D u +cdr ⊆ get-cdr D u +cdr
get-cdr-mono (V ↦ u) (+cdr-↦ +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono ⦅ u , V ⦆ +cdr-pair D⊆ u+v u+v∈ = HOLE
get-cdr-mono ⦅ u , V ⦆ (+cdr-car +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-here +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-there +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-head +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-tail +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono (left u) (+cdr-left +cdr) D⊆ u+v u+v∈ = HOLE
get-cdr-mono (right u) (+cdr-right +cdr) D⊆ u+v u+v∈ = HOLE

+cdr-closed : (D : 𝒫 Value) → Set
+cdr-closed D = ∀ u v u+v 
              → (+cdr : add2cdr u v u+v)
              → u ∈ D → v ∈ get-cdr D u +cdr
              → u+v ∈ D

cdr-closure-n : ℕ → (D : 𝒫 Value) → 𝒫 Value
cdr-closure-n zero D = D
cdr-closure-n (suc n) D d+v = 
  Σ[ d ∈ Value ] Σ[ v ∈ Value ] Σ[ +cdr ∈ add2cdr d v d+v ] 
     (d ∈ (cdr-closure-n n D) × v ∈ get-cdr (cdr-closure-n n D) d +cdr)

cdr-closure : 𝒫 Value → 𝒫 Value
cdr-closure D d = Σ[ n ∈ ℕ ] cdr-closure-n n D d

cdr-closure-closed : ∀ D → +cdr-closed (cdr-closure D)
cdr-closure-closed D u v u+v +cdr ⟨ n , u∈ ⟩ v∈ = 
   ⟨ suc n , ⟨ u , ⟨ v , ⟨ +cdr , ⟨ u∈ , HOLE ⟩ ⟩ ⟩ ⟩ ⟩

cdr-closure-⊆ : ∀ D → D ⊆ cdr-closure D
cdr-closure-⊆ D d d∈ = ⟨ zero , d∈ ⟩
-}

{-

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn

-}   
{-
cdr-closure-n : ∀ (n : ℕ) → (D : 𝒫 Value) → 𝒫 Value
cdr-closure zero D = D
cdr-closure (suc n) D d+v = 
  Σ[ d ∈ Value ] Σ[ v ∈ Value ] Σ[ +cdr ∈ add2cdr d v d+v ] (d ∈ D × v ∈ get-cdr D d +cdr)

smash-closed : (D : 𝒫 Value) → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value) → 𝒫 Value
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value ] Σ[ u2 ∈ Value ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value) → 𝒫 Value
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

-}
{-
+cdr-⟦⟧' : ∀ M' ρ' 
         → (ρ'~ : ∀ i → +cdr-closed (ρ' i))
          → +cdr-closed (⟦ M' ⟧' ρ')
+cdr-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
+cdr-⟦⟧' (lit B k ⦅ Nil ⦆') ρ' ρ'~ (const k') v u+v ()
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ u , v ∷ V ⦆) 
  +cdr-pair u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ _ , V ⦆) 
  (+cdr-car +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-here +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-there +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fst-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (snd-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left u) v (left u+v) (+cdr-left +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right u) v (right u+v) (+cdr-right +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (tuple n ⦅ args' ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ' ρ'~ 
  (FV ↦ (V ↦ w)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) ⟨ ⟨ w∈N , neV ⟩ , neFV ⟩ v∈cdr 
  = ⟨ ⟨ +cdr-⟦⟧' N {!   !} {!   !} w v u+v +cdr w∈N {!   !} , neV ⟩ , neFV ⟩
+cdr-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr 
  ⟨ V , ⟨ ⟨ FV , ⟨ u∈L' , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ v∈cdr = 
  ⟨ V , ⟨ ⟨ FV , ⟨ {!   !}  , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩
  where
  G : (FV ↦ (V ↦ u+v)) ∈ ⟦ L' ⟧' ρ'
  G = +cdr-⟦⟧' L' ρ' ρ'~ (FV ↦ (V ↦ u)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) 
      u∈L' {!  !}

keylemma : ∀ D → +cdr-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma D ccD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma D ccD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD = 
  ccD ⦅ f , V' ++ V ⦆ v ⦅ f , v ∷ V' ++ V ⦆ +cdr-pair 
      (keylemma D ccD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 
      (V'⊆cdrD v (here refl))
-}

{- =============================================================================
   Current attempt
   =============================================================================
This get-cdr formulation is ugly.  Instead of adding a value to a cdr
and checking elsewhere that the value sits in an appropriate denotation, we'll
join values of similar shape, and this will ensure things sit in the right places.
-}


{- I want to start simple with consistent/joinable arrows... let's not worry 
   just yet about whether there are cases where we can "join" domains of arrows -}

data _≈≈_ : List Value → List Value → Set
data _~∥~_ : List Value → List Value → Set
data _~~_ : Value → Value → Set where
  ~~-const : ∀ {B k} → const {B} k ~~ const k
  ~~-ω : ω ~~ ω
  ~~-ν-ν : ν ~~ ν
  ~~-ν-↦ : ∀ {V w} → ν ~~ (V ↦ w)
  ~~-↦-ν : ∀ {V w} → (V ↦ w) ~~ ν
  ~~-↦-↦ : ∀ {V w w'} 
          → (w~ : w ~~ w')
          → (V ↦ w) ~~ (V ↦ w')
  ~~-left : ∀ {d d'}
          → (d~ : d ~~ d')
          → left d ~~ left d'
  ~~-right : ∀ {d d'}
          → (d~ : d ~~ d')
          → right d ~~ right d'
  ~~-tup : ∀ {ds ds'}
          → (ds~ : ds ~∥~ ds')
          → ∥ ds ∥ ~~ ∥ ds' ∥
  ~~-pair : ∀ {u u' V V'}
          → (u~ : u ~~ u')
          → (V≈ : V ≈≈ V')
          → ⦅ u , V ⦆ ~~ ⦅ u' , V' ⦆
data _~∥~_ where
   [] : [] ~∥~ []
   _∷_ : ∀ {d d' ds ds'}
       → (d~ : d ~~ d')
       → (ds~ : ds ~∥~ ds')
       → (d ∷ ds) ~∥~ (d' ∷ ds')

data _≈≈_ where
  ≈≈[] : ∀ {V'} → [] ≈≈ V'
  ≈≈∷ : ∀ {v V V'}
     → All (v ~~_) V'
     → V ≈≈ V'
     → (v ∷ V) ≈≈ V'

_⊔cdr_[_] : (u v : Value) → u ~~ v → Value
_⊔cdr∥_[_] : (ds ds' : List Value) → ds ~∥~ ds' → List Value
_⨆cdr_[_] : (V V' : List Value) → V ≈≈ V' → List Value
(const k) ⊔cdr .(const _) [ ~~-const ] = const k
.ω ⊔cdr .ω [ ~~-ω ] = ω
.ν ⊔cdr .ν [ ~~-ν-ν ] = ν
.ν ⊔cdr (V ↦ w) [ ~~-ν-↦ ] = V ↦ w
(V ↦ w) ⊔cdr .ν [ ~~-↦-ν ] = V ↦ w
(V ↦ w) ⊔cdr (V ↦ w') [ ~~-↦-↦ w~ ] = V ↦ (w ⊔cdr w' [ w~ ])
(left d) ⊔cdr (left d') [ ~~-left d~ ] = left (d ⊔cdr d' [ d~ ])
(right d) ⊔cdr (right d') [ ~~-right d~ ] = right (d ⊔cdr d' [ d~ ])
(∥ ds ∥) ⊔cdr (∥ ds' ∥) [ ~~-tup ds~ ] = ∥ ds ⊔cdr∥ ds' [ ds~ ] ∥
⦅ u , V ⦆ ⊔cdr ⦅ u' , V' ⦆ [ ~~-pair u~ V≈ ] = 
   ⦅ u ⊔cdr u' [ u~ ] , V ⨆cdr V' [ V≈ ] ⦆
.[] ⊔cdr∥ .[] [ [] ] = []
(d ∷ ds) ⊔cdr∥ (d' ∷ ds') [ d~ ∷ ds~ ] = d ⊔cdr d' [ d~ ] ∷ (ds ⊔cdr∥ ds' [ ds~ ])
.[] ⨆cdr V' [ ≈≈[] ] = V'
(v ∷ V) ⨆cdr V' [ ≈≈∷ v~ V≈ ] = 
   reduce (λ {x} v~~x → v ⊔cdr x [ v~~x ]) v~ ++ (V ⨆cdr V' [ V≈ ]) 

{-
 : Value → Value → Value → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆
-}


{- =============================================================================
   ACTUAL Current attempt
   =============================================================================
The ~~ relation was not useful on its own, and I don't really want
join to be a function (because the way it maps in the ≈≈ case explodes and is gross).

So we want to define something similar, but that is just join as a relation.
-}



data _▹_◃_ : Value → Value → Value → Set where
    smash-pair-L : ∀ {u1 u2 V1 V2 v2}
            → v2 ∈ mem V2
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u1 , v2 ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-pair-R : ∀ {u1 u2 V1 V2 v1}
            → v1 ∈ mem V1
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v1 ∷ V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-↦ : ∀ {V w1 w2 w} 
            → w1 ▹ w ◃ w2  
            → (V ↦ w1) ▹ (V ↦ w) ◃ (V ↦ w2)
    smash-left : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → left v1 ▹ left v ◃ left v2
    smash-right : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → right v1 ▹ right v ◃ right v2
    smash-car-L : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-car-R : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-L : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v2∈ : v2 ∈ mem V2)
            → ⦅ u1 , v1 ∷ V1 ⦆ ▹ ⦅ u1 , v ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-R : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v1∈ : v1 ∈ mem V1)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v ∷ V1 ⦆ ◃ ⦅ u2 , v2 ∷ V2 ⦆
    smash-cdr-there-L : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , v ∷ V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-there-R : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , v ∷ V2 ⦆
    smash-nil : ∥ [] ∥ ▹ ∥ [] ∥ ◃ ∥ [] ∥
    smash-cons : ∀ {d1 d2 d ds1 ds2 ds}
            → (d⊔ : d1 ▹ d ◃ d2)
            → (ds⊔ : ∥ ds1 ∥ ▹ ∥ ds ∥ ◃ ∥ ds2 ∥)
            → ∥ d1 ∷ ds1 ∥ ▹ ∥ d ∷ ds ∥ ◃ ∥ d2 ∷ ds2 ∥
  {-
    smash-head : ∀ {v1 v2 v vs} → v1 ▹ v ◃ v2
            → ∥ v1 ∷ vs ∥ ▹ ∥ v ∷ vs ∥ ◃ ∥ v2 ∷ vs ∥
    smash-tail : ∀ {v vs1 vs2 vs} → ∥ vs1 ∥ ▹ ∥ vs ∥ ◃ ∥ vs2 ∥
            → ∥ v ∷ vs1 ∥  ▹ ∥ v ∷ vs ∥ ◃ ∥ v ∷ vs2 ∥
    -}

data _▹[_]◃_ : List Value → List Value → List Value → Set where
    [] : [] ▹[ [] ]◃ []
    _∷_ : ∀ {d1 d2 d ds1 ds2 ds}
        → (d⊔ : d1 ▹ d ◃ d2)
        → (ds⊔ : ds1 ▹[ ds ]◃ ds2)
        → (d1 ∷ ds1) ▹[ (d ∷ ds) ]◃ (d2 ∷ ds2)
data _▹▹_◃◃_ : List Value → List Value → List Value → Set where
    ▹[]◃ : ∀ {V2} → [] ▹▹ V2 ◃◃ V2
    ▹∷◃ : ∀ {v1 V1 V2 V}
        → (V⨆ : V1 ▹▹ V ◃◃ V2)
        → (v1 ∷ V1) ▹▹ V ◃◃ V2


smash-mem : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → d1 ∈ mem FV1 → d2 ∈ mem FV2 → List Value
smash-mem {d1} {d2} {d} smash {FV1 = d1 ∷ FV1} (here refl) d2∈ = d ∷ FV1
smash-mem {d1} {d2} {d} smash {FV1 = d' ∷ FV1} (there d1∈) d2∈ = 
   d' ∷ smash-mem smash d1∈ d2∈

smash-mem-ne : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → d ∈ mem (smash-mem smash d1∈ d2∈)
smash-mem-ne smash (here refl) d2∈ = here refl
smash-mem-ne smash (there d1∈) d2∈ = there (smash-mem-ne smash d1∈ d2∈)

smash-cdr-L : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {u1 u2 FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → ⦅ u1 , FV1 ⦆ ▹ ⦅ u1 , smash-mem smash d1∈ d2∈ ⦆ ◃ ⦅ u2 , FV2 ⦆
smash-cdr-L smash (here refl) d2∈ = smash-cdr-here-L smash d2∈
smash-cdr-L smash (there d1∈) d2∈ = smash-cdr-there-L (smash-cdr-L smash d1∈ d2∈)

smash-closed : (D : 𝒫 Value) → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value) → 𝒫 Value
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value ] Σ[ u2 ∈ Value ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value) → 𝒫 Value
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn


smash-⟦⟧' : ∀ M' ρ' 
          → (ρ'~ : ∀ i → smash-closed (ρ' i))
          → smash-closed (⟦ M' ⟧' ρ')
smash-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ V1 ⦆) 
          (smash-pair-L x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u2 , _ ∷ V2 ⦆) 
          (smash-pair-R x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V1 ⦆) 
          (smash-car-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V2 ⦆) 
          (smash-car-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ _ ⦆) 
          (smash-cdr-here-L smash v2∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ u2 , _ ∷ V1 ⦆) 
          (smash-cdr-here-R smash v1∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
          ⟨ FV1 , ⟨ p1∈ , neFV1 ⟩ ⟩ ⟨ FV2 , ⟨ p2∈ , neFV2 ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ d1 , FV1 ⦆ ⦅ d2 , FV2 ⦆ ⦅ d , FV1 ⦆ 
                 (smash-car-L smash) p1∈ p2∈
... | IH
    = ⟨ FV1 , ⟨ IH , neFV1 ⟩ ⟩
smash-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
  ⟨ f1 , ⟨ FV1 , ⟨ p1∈ , d1∈ ⟩ ⟩ ⟩  ⟨ f2 , ⟨ FV2 , ⟨ p2∈ , d2∈ ⟩ ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ f1 , FV1 ⦆ ⦅ f2 , FV2 ⦆
                 ⦅ f1 , smash-mem smash d1∈ d2∈ ⦆
                 (smash-cdr-L smash d1∈ d2∈) p1∈ p2∈
... | IH
    = ⟨ f1 , ⟨ smash-mem smash d1∈ d2∈ , ⟨ IH , smash-mem-ne smash d1∈ d2∈ ⟩ ⟩ ⟩

smash-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left d1) (left d2) (left d)
    (smash-left smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right d1) (right d2) (right d)
    (smash-right smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  with smash-⟦⟧' M' ((mem (v1 ∷ V1 ++ v2 ∷ V2)) • ρ') {!   !} d1 d2 d smash 
                   {! d1∈M'  !} {! d2∈M'  !}
... | IH = inj₁ ⟨ v1 , ⟨ V1 ++ (v2 ∷ V2) , ⟨ {!   !} , IH ⟩ ⟩ ⟩
  {- in the IH, expand each of the environments for the d1∈ d2∈ premises -}
  {- even-worse... we have to extend the environment by the 
     smash-closure of v1 ∷ V1 ++ v2 ∷ V2... -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩) (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = inj₂ {!   !}  {- similar to first case -}
smash-⟦⟧' (fun-op ⦅ args ⦆') ρ' ρ'~ = {!   !}
smash-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (tuple n ⦅ args ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ d1 d2 smash d1∈ d2∈ = {!   !}



keylemma' : ∀ D → smash-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ OpTarget.cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma' D scD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma' D scD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD with V'⊆cdrD v (here refl)
... | ⟨ f' , ⟨ FV , ⟨ p∈ , v∈FV ⟩ ⟩ ⟩ = 
  scD ⦅ f' , FV ⦆ ⦅ f , V' ++ V ⦆ ⦅ f , v ∷ V' ++ V ⦆ (smash-pair-R v∈FV) 
      p∈ 
      (keylemma' D scD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 


fros : List Value → List Value
fro : Value → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ⦅ ν , FV ⦆ = fros ν
fro ⦅ V ↦ ν , FV ⦆ = fros ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆ with FV' d≟ FV
... | yes FV'≡FV =  fros FV' ⊢ fros V ↦ fro w
... | no FV'≡FV = fros ν
fro ⦅ u , v ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value → 𝒫 Value
fro-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (OpTarget.nth V i) ≡ OpSource.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)


delay-reflect' : ∀ M ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ 
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ ρ~ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ ν , FV ⦆ 
  ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  = ?
{-

  with FV' mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → LangTarget.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → LangSource.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → LangSource.init))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
-}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ with FV↦[V↦d]∈carM'
... | ⟨ FV' , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ = 
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect'-⊆ N ρ ρ~ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ ρ~) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros  fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM = ?
{- with FV mem⊆? (FV ++ FV') | delay-reflect' M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV)) -}
delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect' (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ ρ~ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ~ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect' M (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (left b) (LV∈ b b∈)
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect' N (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (right b) (RV∈ b b∈)
delay-reflect'-⊆ M ρ ρ~ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ ρ~ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ ρ~ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ ρ~ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ ρ~ = 
  ⟨ lift (delay-reflect' M ρ ρ~) , del-map-args-reflect' args ρ ρ~ ⟩


{-






delay-reflect : ∀ M (ρ' : Env Value) (ρ : Env Value)
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value ] D ⊢ d' ~fro d)
              → ∀ d'
              → d' ∈ ⟦ delay M ⟧' ρ' 
              → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value ] D ⊢ d' ~fro d
delay-reflect-⊆ : ∀ M ρ' ρ 
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value ] D ⊢ d' ~fro d)
              → ∀ V'
              → mem V' ⊆ ⟦ delay M ⟧' ρ'
              → Σ[ V ∈ List Value ] mem V ⊆ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value ] D ⊢ V' ~fros V
delay-reflect (` i) ρ' ρ ρ~ d' d'∈ = ρ~ d'∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (left d') d'∈ 
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ OpTarget.ℒ ⟨ D , ptt ⟩ , fro-left ~d ⟩ ⟩ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (right d') d'∈
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ OpTarget.ℛ ⟨ D , ptt ⟩ , fro-right ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) 
  with delay-reflect-⊆ L ρ' ρ ρ~ (v' ∷ V') {! V'⊆   !}
... | ⟨ V , ⟨ V⊆ , ⟨ DV , ~V ⟩ ⟩ ⟩
  with (delay-reflect M (mem (v' ∷ V') • ρ') {!   !} {!   !} d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ Dd , ~d ⟩ ⟩ ⟩ = 
  ⟨ d , ⟨ inj₁ ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , d∈ ⟩ ⟩ ⟩ , ⟨ Dd , ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) = {!   !}
delay-reflect M ρ' ρ ρ~ d' d'∈ = {!   !}
delay-reflect-⊆ M ρ' ρ ρ~ [] V'⊆ = ⟨ [] , ⟨ (λ d ()) , ⟨ ⟦ delay M ⟧' ρ' , [] ⟩ ⟩ ⟩
delay-reflect-⊆ M ρ' ρ ρ~ (d' ∷ V') V'⊆
  with delay-reflect M ρ' ρ ρ~ d' (V'⊆ d' (here refl)) 
     | delay-reflect-⊆ M ρ' ρ ρ~ V' (λ d z → V'⊆ d (there z))
... | ⟨ d , ⟨ d∈ , ⟨ D1 , ~d ⟩ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , ⟨ D2 , ~V ⟩ ⟩ ⟩ 
    = ⟨ d ∷ V , ⟨ G , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
  where
  G : mem (d ∷ V) ⊆ ⟦ M ⟧ ρ
  G d' (here refl) = d∈
  G d' (there d'∈) = V⊆ d' d'∈

{-
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
-}







{-
need to check for equality of fv' with fv
and FV' with FV

-}

{-






fro-mem-rewrite : ∀ V ρ → env-map fro (mem V • ρ) ⊆ₑ (mem (fros V)) • env-map fro ρ
fro-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = fro-∈-mem a∈V
fro-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx

fro-⊆-mem : ∀ {V' V} → mem V' ⊆ mem V → mem (fros V') ⊆ (mem (fros V))
fro-⊆-mem V⊆ d d∈ with ∈-mem-fros d∈ 
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem (V⊆ a a∈)

{-
data _⊑_⊔_ : Value → Value → Value → Set where
  ⊑-clos-L : ∀ {f₁} f₂ {fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₁ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  ⊑-clos-R : ∀ f₁ {f₂ fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₂ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  {- the next case is probably not good enough, 
     but I can workshop it while working on the theorem -}
  ⊑-↦-L : ∀ {v₁ V₁ w₁ v₂ V₂ w₂ w a A b B}
       → w ⊑ w₁ ⊔ w₂
       → (a , A ⊢ v₁ , V₁ ↦ w) ⊑ (a , A ⊢ v₁ , V₁ ↦ w₁) ⊔ (b , B ⊢ v₂ , V₂ ↦ w₂)
  {- also need other cases; will add as needed -}


⊔-⊑-closed : ∀ M ρ v₁ v₂ d
           {- insert same closed condition on ρ -}
            → v₁ ∈ ⟦ delay M ⟧' ρ
            → v₂ ∈ ⟦ delay M ⟧' ρ
            → d ⊑ v₁ ⊔ v₂
            → d ∈ ⟦ delay M ⟧' ρ
⊔-⊑-closed (` x) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
  ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (app ⦅ M ,, N ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (lit B k ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple zero ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple (suc n) ⦅ M ,, Ms ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (get i ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inl-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inr-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
-}

{-crucial lemma: closures-are-products -}
{-
closures-are-products : ∀ M ρ f fv FV fv' FV'
                      → mem FV ⊆ cdr ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ 
                      → ⦅ f ∣ fv' ∷ fV' ⦆ ∈ ⟦ delay M ⟧' ρ
                      → ⦅ f ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
closures-are-products M ρ f fv FV fv' FV' FV⊆ f∈ = 
  ⊔-⊑-closed M ρ ⦅ f ∣ fv' ∷ fV' ⦆ ⦅ proj₁ G ∣ fv ∷ fV ⦆ ⦅ f ∣ fv ∷ fV ⦆ 
                  f∈ (proj₂ G) (⊑-clos-R (proj₁ G) (λ d d∈ → inj₂ d∈))
  where 
  G : Σ[ f' ∈ Value ] ⦅ f' ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
  G = HOLE
  {- this proof is bad so far... just need to recur on FV and use f directly as the f'
    with base case using ⦅ f ∣ fv' ∷ fV' ⦆ -}
-}


delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d d∈ = {!   !}

{-
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ( ⦅ ν , fv' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv'∈ ⟩ ⟩ 
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ ⦅ fv' ∷ FV' ↦ ν , fv'' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv''∈ ⟩ ⟩
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ ⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩
   with (fv' ∷ FV') mem⊆? FV
... | no FV'⊈ = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ ⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩ | yes FV'⊆ = 
   ⟨ G3 (fro fv') (fro-∈-mem (FV'⊆ fv' (here refl))) , ⟨ (λ d' d'∈ → G3 d' (fro-⊆-mem FV'⊆ d' (there d'∈))) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv' ∷ FV') • λ x → LangTarget.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → LangSource.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → LangSource.init))
  G1 = LangSource.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem (v ∷ V) • mem (fv' ∷ FV') • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ OpTarget.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ OpSource.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
-}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ v , ⟨ V , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ with inner-app
... | ⟨ v' , ⟨ V' , ⟨ q , V'⊆sndM' ⟩ ⟩ ⟩    = {!  q !}

{-
   with delay-reflect' M ρ (fv' ∷ FV' ⊢⦅ fv ∷ FV ↦ (v ∷ V ↦ d) , fv'' ⦆) ⦅FV↦V↦d∣FV'⦆∈M
... | IHM with FV mem⊆? (fv' ∷ FV')
... | yes FV⊆ =
   ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ IHM , delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩
... | no ¬FV⊆ = HOLE
-}
{- should be a contradiction -}
   {- the codomain isn't a subset of the annotation -}
   {- not a contradiction, but we know that this can't ALWAYS be true -}  

   
   
     {-
  ⟨ fro v , ⟨ fros V , ⟨ G1+IH , G2 ⟩ ⟩ ⟩
  where
  G1 : (fv ∷ ⦅ ( fv ∷ FV ↦ (v ∷ V ↦ d)) , fv ⦆) ∈ ⟦ delay M ⟧' ρ
  G1 = {! FV⊆sndM' !}
  G1+IH : (fro v ∷ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  G1+IH with delay-reflect' M ρ (fv ∷ ⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d)) , fv ⦆) G1 
  ... | ihres with FV mem⊆? FV
  ... | no neq = ⊥-elim (neq λ z z∈ → z∈)
  ... | yes eq = ihres
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
  -}

{-



-}


{-
    with FV mem⊆? (fv' ∷ FV') | delay-reflect' M ρ ⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d) ∣ fv' ∷ fV' ⦆ U∈M'
... | no FV⊈ |  q = ⊥-elim (FV⊈ G)
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  G : mem FV ⊆ (mem (fv' ∷ FV'))
  G d' d'∈ with FV⊆sndM' d' d'∈ 
  ... | ⟨ q , ⟨ p , ⟨ P , ⟨ qP∈M , d'∈P ⟩ ⟩ ⟩ ⟩ = HOLE
  {-
  G1 : {!   !}
  G1 = {! delay-reflect' M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ HOLE , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' {- delay-reflect' M ρ ⦅ (fv' ∷ fV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}
-}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ FV ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with FV mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros  fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros ν


-}

delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = {! d∈   !}
delay-reflect' (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (left v) LV∈ 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , LangSource.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩ -}
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect' M ρ) , del-map-args-reflect' args ρ ⟩


-}

-}

-}

-}
-}
-}


-}



-}