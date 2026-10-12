open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)

open import Framework.abt.ScopedTuple hiding (𝒫)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.abt.Sig
open import Framework.Syntax.SyntaxUtil
open import Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties
open import Framework.GraphModel.Env

module Framework.GraphModel.Semantics (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
open import Framework.abt.Fold2 Op sig


{- =================== Monotonic Semantics ================================= -}

record Semantics {A : Set} : Set₁ where
  field 
    error : A 
    interp-op : DOpSig (𝒫 A) sig

  init : 𝒫 A
  init = ⌈ error ⌉

  ⟦_⟧ : ABT → Env A → 𝒫 A
  ⟦ M ⟧ ρ = fold interp-op init ρ M

  ⟦_⟧ₐ : ∀{b} → Arg b → Env A → Result (𝒫 A) b
  ⟦ arg ⟧ₐ ρ = fold-arg interp-op init ρ arg

  ⟦_⟧₊ : ∀{bs} → Args bs → Env A → Tuple bs (Result (𝒫 A))
  ⟦ args ⟧₊ ρ = fold-args interp-op init ρ args

  field 
    mono-op : 𝕆-monotone sig interp-op

open Semantics {{...}}

{- =================== Continuous Semantics ====================== -}

continuous-arg : ∀ {A} {{_ : Semantics {A}}} (ρ : Env A) (NE-ρ : nonempty-env ρ)
    → ∀ b → (arg : Arg b) → Set₁
continuous-arg ρ NE-ρ ■ (ast M) = continuous-env ⟦ M ⟧ ρ
continuous-arg ρ NE-ρ (ν b) (bind arg) =
    ∀ V → (ne : V ≢ [])
    → continuous-arg (mem V • ρ)
          (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem ne)) b arg
continuous-arg ρ NE-ρ (∁ b) (clear arg) =
      continuous-arg (λ x → init) (λ i → ⟨ error , refl ⟩) b arg

continuous-args : ∀ {A} {{_ : Semantics {A}}} (ρ : Env A) (NE-ρ : nonempty-env ρ)
    → ∀ bs → (args : Args bs) → Set₁
continuous-args ρ NE-ρ [] Nil = pTrue
continuous-args ρ NE-ρ (b ∷ bs) (! arg ,, args) = 
  continuous-arg ρ NE-ρ b arg × continuous-args ρ NE-ρ bs args

record ContinuousSemantics {A : Set} : Set₁ where
  field 
    {{Sem}} : Semantics {A}
    continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ 
        → continuous-args ρ NE-ρ (sig op) args
        → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)

open ContinuousSemantics {{...}}


{- Preservation of a relation, e.g. ⊆ or consistency ---------------------------}

module _ {A} {{_ : Semantics {A}}} (R : 𝒫 A → 𝒫 A → Set)
    (R-op : opsig-rel-pres R sig interp-op interp-op) (R-init : R init init) where
  ⟦⟧-pres : ∀ {ρ ρ′} (M : ABT) → ρ ~ₑ[ R ] ρ′ → R (⟦ M ⟧ ρ) (⟦ M ⟧ ρ′)
  ⟦⟧-pres-arg : ∀ {b}{ρ ρ′} (arg : Arg b)
    → ρ ~ₑ[ R ] ρ′ → result-rel-pres R b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
  ⟦⟧-pres-args : ∀ {bs}{ρ ρ′} (args : Args bs)
    → ρ ~ₑ[ R ] ρ′ → results-rel-pres R bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)

  ⟦⟧-pres (` x) ρR = ρR x
  ⟦⟧-pres {ρ}{ρ′} (op ⦅ args ⦆) ρR = lower (R-op op (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′) (⟦⟧-pres-args args ρR))
  ⟦⟧-pres-arg (ast M) ρR = lift (⟦⟧-pres M ρR)
  ⟦⟧-pres-arg (bind arg) ρR X D XR = ⟦⟧-pres-arg arg (•-~ R ρR XR)
  ⟦⟧-pres-arg (clear arg) ρR = ⟦⟧-pres-arg arg (λ x → R-init)
  ⟦⟧-pres-args nil ρR = lift tt
  ⟦⟧-pres-args (cons arg args) ρR = ⟨ ⟦⟧-pres-arg arg ρR , ⟦⟧-pres-args args ρR ⟩

{- Monotone -------------------------------------------------------------------}

⟦⟧-monotone : ∀{A} {{_ : Semantics {A}}} {ρ ρ′} (M : ABT)
  →  ρ ⊆ₑ ρ′ →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-monotone = ⟦⟧-pres _⊆_ mono-op (λ d z → z)

⟦⟧-monotone-arg : ∀{A} {{_ : Semantics {A}}} {b}{ρ ρ′} (arg : Arg b)
  →  ρ ⊆ₑ ρ′ →  result-rel-pres _⊆_ b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-monotone-arg = ⟦⟧-pres-arg _⊆_ mono-op (λ d z → z)

{- Continuous -----------------------------------------------------------------}

⟦⟧-continuous : ∀{A} {{_ : ContinuousSemantics{A}}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → continuous-env ⟦ M ⟧ ρ 
⟦⟧-cont-env-arg : ∀{A}{{_ : ContinuousSemantics{A}}}
    {ρ}{NE-ρ : nonempty-env ρ} {b}(arg : Arg b)
  → continuous-arg ρ NE-ρ b arg 
⟦⟧-cont-env-args : ∀{A}{{_ : ContinuousSemantics{A}}}
    {ρ}{NE-ρ : nonempty-env ρ}{bs} (args : Args bs)
  → continuous-args ρ NE-ρ bs args

⟦⟧-continuous {A}{ρ}{NE-ρ} (` x) v v∈⟦M⟧ρ =
   ⟨ (single-env x ⌈ v ⌉ ρ NE-ρ) , ⟨ (single-fin {A}{v}{x}) , ⟨ (single-⊆ v∈⟦M⟧ρ) ,
     (v∈single[xv]x {A}{v}{x}) ⟩ ⟩ ⟩

⟦⟧-continuous {A}{ρ}{NE-ρ} (op ⦅ args ⦆) v v∈⟦M⟧ρ =
    continuous-op{NE-ρ = NE-ρ} v∈⟦M⟧ρ (⟦⟧-cont-env-args {A}{ρ}{NE-ρ} args)
⟦⟧-cont-env-arg {A}{ρ} {NE-ρ} {■} (ast M) v v∈⟦M⟧ρ =
    ⟦⟧-continuous {A}{ρ}{NE-ρ = NE-ρ} M v v∈⟦M⟧ρ
⟦⟧-cont-env-arg {A}{ρ} {NE-ρ} {ν b} (bind arg) V V≢[] =
    let NE-V•ρ = (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem V≢[])) in
    ⟦⟧-cont-env-arg {A}{mem V • ρ}{NE-V•ρ} {b} arg
⟦⟧-cont-env-arg {A}{ρ} {NE-ρ} {∁ b} (clear arg) =
    ⟦⟧-cont-env-arg {A}{λ x → init} {λ x → ⟨ error , refl ⟩}{b} arg

⟦⟧-cont-env-args {A} {ρ} {NE-ρ} {[]} nil = lift tt
⟦⟧-cont-env-args {A} {ρ} {NE-ρ} {b ∷ bs} (cons arg args) =
    ⟨ ⟦⟧-cont-env-arg {A} {ρ}{NE-ρ}{b} arg ,
      ⟦⟧-cont-env-args {A} {ρ} {NE-ρ} {bs} args ⟩


