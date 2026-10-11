open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)

open import abt.ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import abt.Sig
open import NewSyntaxUtil
open import NewDOpSig
open import NewDenotProperties
open import NewEnv

module NewSemantics (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig
open import abt.Fold2 Op sig


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


{- Monotone -------------------------------------------------------------------}

⟦⟧-monotone : ∀{A} {{_ : Semantics {A}}} {ρ ρ′} (M : ABT)
  →  ρ ⊆ₑ ρ′ →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-monotone-arg : ∀{A} {{_ : Semantics {A}}} {b}{ρ ρ′} (arg : Arg b)
  →  ρ ⊆ₑ ρ′ →  result-rel-pres _⊆_ b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-monotone-args : ∀{A} {{_ : Semantics {A}}} {bs}{ρ ρ′} (args : Args bs)
  →  ρ ⊆ₑ ρ′ → results-rel-pres _⊆_ bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)
  
⟦⟧-monotone {A}{ρ}{ρ′} (` x) ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {A}{ρ}{ρ′} (op ⦅ args ⦆) ρ<ρ′ = lower (mono-op op (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′) (⟦⟧-monotone-args  args ρ<ρ′))

⟦⟧-monotone-arg {A} {■} (ast M) ρ<ρ′ = lift (⟦⟧-monotone M ρ<ρ′)
⟦⟧-monotone-arg {A} {ν b}{ρ}{ρ′} (bind arg) ρ<ρ′ X D X⊆D =
   ⟦⟧-monotone-arg {A}{b}{X • ρ}{D • ρ′} arg (•-~ _⊆_ ρ<ρ′ X⊆D)
⟦⟧-monotone-arg {A} {∁ b} (clear arg) ρ<ρ′ =
    ⟦⟧-monotone-arg {A}{b}{λ x → init}{λ x → init} arg λ x d z → z

⟦⟧-monotone-args {A} {bs = []} nil ρ<ρ′ = lift tt
⟦⟧-monotone-args {A} {bs = b ∷ bs} (cons arg args) ρ<ρ′ =
  ⟨ ⟦⟧-monotone-arg arg ρ<ρ′ , ⟦⟧-monotone-args args ρ<ρ′ ⟩

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


