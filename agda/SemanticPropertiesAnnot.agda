open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s; _+_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import PValueCBVAnnot
open import ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import Sig
open import Syntax hiding (⌈_⌉)
open import Utilities using (extensionality)

module SemanticPropertiesAnnot (Op : Set) (sig : Op → List Sig) where

open Syntax.OpSig Op sig
open import Fold2 Op sig

all-args : (∀ b → Arg b → Set₁) → ∀ bs → Args bs → Set₁
all-args P [] args = Lift (lsuc lzero) True
all-args P (b ∷ bs) (cons arg args) = P b arg × all-args P bs args

record Semantics : Set₁ where
  field interp-op  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value

  init : 𝒫 Value
  init = ⌈ ν ⌉

  ⟦_⟧ : ABT → Env → 𝒫 Value
  ⟦ M ⟧ ρ = fold interp-op init ρ M

  ⟦_⟧ₐ : ∀{b} → Arg b → Env  → Result (𝒫 Value) b
  ⟦ arg ⟧ₐ ρ = fold-arg interp-op init ρ arg

  ⟦_⟧₊ : ∀{bs} → Args bs → Env  → Tuple bs (Result (𝒫 Value))
  ⟦ args ⟧₊ ρ = fold-args interp-op init ρ args

  field mono-op : ∀{op}{xs}{ys} → ⊆-results (sig op) xs ys → interp-op op xs ⊆ interp-op op ys

  Cont-Env-Arg : ∀ {{_ : Semantics}} (ρ : Env) (NE-ρ : nonempty-env ρ)
    → ∀ b → (arg : Arg b)  → Set₁
  Cont-Env-Arg ρ NE-ρ ■ (ast M) = continuous-env ⟦ M ⟧ ρ
  Cont-Env-Arg ρ NE-ρ (ν b) (bind arg) =
    ∀ V → (ne : V ≢ [])
    → Cont-Env-Arg (mem V • ρ)
          (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem ne)) b arg
  Cont-Env-Arg ρ NE-ρ (∁ b) (clear arg) =
      Cont-Env-Arg (λ x → init) (λ x → ⟨ ν , refl ⟩) b arg

open Semantics {{...}}

record ContinuousSemantics : Set₁ where
  field {{Sem}} : Semantics
  field continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args  →   Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)

open ContinuousSemantics {{...}}

{- Monotone -------------------------------------------------------------------}

⟦⟧-monotone : ∀{{_ : Semantics}} {ρ ρ′} (M : ABT)
  →  ρ ⊆ₑ ρ′ →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-monotone-arg : ∀{{_ : Semantics}} {b}{ρ ρ′} (arg : Arg b)
  →  ρ ⊆ₑ ρ′ →  ⊆-result b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-monotone-args : ∀{{_ : Semantics}} {bs}{ρ ρ′} (args : Args bs)
  →  ρ ⊆ₑ ρ′  →  ⊆-results bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)
  
⟦⟧-monotone {ρ}{ρ′} (` x) ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {ρ}{ρ′} (op ⦅ args ⦆) ρ<ρ′ = mono-op (⟦⟧-monotone-args  args ρ<ρ′)

⟦⟧-monotone-arg {■} (ast M) ρ<ρ′ = lift (⟦⟧-monotone M ρ<ρ′)
⟦⟧-monotone-arg {ν b}{ρ}{ρ′} (bind arg) ρ<ρ′ X =
    ⟦⟧-monotone-arg {b}{X • ρ}{X • ρ′} arg (env-ext ρ<ρ′)
⟦⟧-monotone-arg {∁ b} (clear arg) ρ<ρ′ =
    ⟦⟧-monotone-arg {b}{λ x → init}{λ x → init} arg λ x d z → z

⟦⟧-monotone-args {bs = []} nil ρ<ρ′ = lift tt
⟦⟧-monotone-args {bs = b ∷ bs} (cons arg args) ρ<ρ′ =
  ⟨ ⟦⟧-monotone-arg arg ρ<ρ′ , ⟦⟧-monotone-args args ρ<ρ′ ⟩

⟦⟧-monotone-one : ∀{{_ : Semantics}}{N : ABT}{ρ}
   → monotone (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-monotone-one {N}{ρ} D₁ D₂ D12 = ⟦⟧-monotone N G
  where G : (x : Var) → (D₁ • ρ) x ⊆ (D₂ • ρ) x
        G zero = D12
        G (suc x) = λ v z → z


{- Continuous -----------------------------------------------------------------}

⟦⟧-continuous : ∀{{_ : ContinuousSemantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → continuous-env ⟦ M ⟧ ρ 
⟦⟧-cont-env-arg : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ} {b}(arg : Arg b)
  → Cont-Env-Arg ρ NE-ρ b arg 
⟦⟧-cont-env-args : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ}{bs} (args : Args bs)
  → all-args (Cont-Env-Arg ρ NE-ρ) bs args

⟦⟧-continuous {ρ}{NE-ρ} (` x) v v∈⟦M⟧ρ =
   ⟨ (single-env x ⌈ v ⌉ ρ NE-ρ) , ⟨ (single-fin {v}{x}) , ⟨ (single-⊆ v∈⟦M⟧ρ) ,
     (v∈single[xv]x {v}{x}) ⟩ ⟩ ⟩

⟦⟧-continuous {ρ}{NE-ρ} (op ⦅ args ⦆) v v∈⟦M⟧ρ =
    continuous-op{NE-ρ = NE-ρ} v∈⟦M⟧ρ (⟦⟧-cont-env-args {ρ}{NE-ρ} args)
⟦⟧-cont-env-arg {ρ} {NE-ρ} {■} (ast M) v v∈⟦M⟧ρ =
    ⟦⟧-continuous {ρ}{NE-ρ = NE-ρ} M v v∈⟦M⟧ρ
⟦⟧-cont-env-arg {ρ} {NE-ρ} {ν b} (bind arg) V V≢[] =
    let NE-V•ρ = (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem V≢[])) in
    ⟦⟧-cont-env-arg {mem V • ρ}{NE-V•ρ} {b} arg
⟦⟧-cont-env-arg {ρ} {NE-ρ} {∁ b} (clear arg) =
    ⟦⟧-cont-env-arg {λ x → init} {λ x → ⟨ ν , refl ⟩}{b} arg

⟦⟧-cont-env-args {ρ} {NE-ρ} {[]} nil = lift tt
⟦⟧-cont-env-args {ρ} {NE-ρ} {b ∷ bs} (cons arg args) =
    ⟨ ⟦⟧-cont-env-arg {ρ}{NE-ρ}{b} arg ,
      ⟦⟧-cont-env-args {ρ} {NE-ρ} {bs} args ⟩

⟦⟧-continuous-⊆  : ∀{{_ : ContinuousSemantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → ∀ V → mem V ⊆ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ ⟦ M ⟧ ρ′
⟦⟧-continuous-⊆ {ρ}{NE-ρ} M V V⊆Eρ =
    continuous-∈⇒⊆ ⟦ M ⟧ ρ NE-ρ (⟦⟧-monotone M) V V⊆Eρ
        (λ v v∈V → ⟦⟧-continuous {NE-ρ = NE-ρ} M v)

⟦⟧-continuous-one : ∀{{_ : ContinuousSemantics}}{N : ABT}
    {ρ}{NE-ρ : nonempty-env ρ}
  → continuous (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-continuous-one {N}{ρ}{NE-ρ} X E E⊆⟦N⟧X•ρ NE-X
    with ⟦⟧-continuous-⊆ {X • ρ}{extend-nonempty-env NE-ρ NE-X} N E E⊆⟦N⟧X•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆X•ρ , E⊆⟦N⟧ρ′ ⟩ ⟩ ⟩
    with fρ′ 0
... | ⟨ D , ⟨ ρ′x=D , NE-D ⟩ ⟩ =
    ⟨ D , ⟨ (λ v v∈D → ρ′⊆X•ρ 0 v ((proj₂ ρ′x=D) v v∈D)) ,
    ⟨ (λ d d∈E → ⟦⟧-monotone {ρ′}{mem D • ρ} N G d (E⊆⟦N⟧ρ′ d d∈E)) , NE-D ⟩ ⟩ ⟩
    where
    G : (x : Var) → ρ′ x ⊆ (mem D • ρ) x
    G zero d d∈ρ0 = (proj₁ ρ′x=D) d d∈ρ0 
    G (suc x) d m = ρ′⊆X•ρ (suc x) d m

Λ⟦⟧-▪-id : ∀ {{_ : ContinuousSemantics}}{N : ABT}{ρ}{NE-ρ : nonempty-env ρ}
    {X : 𝒫 Value}
  → nonempty X
  → (Λ λ X → ⟦ N ⟧ (X • ρ)) ▪ X ≃ ⟦ N ⟧ (X • ρ)
Λ⟦⟧-▪-id {N}{ρ}{NE-ρ}{X} NE-X =
    Λ-▪-id {λ D → ⟦ N ⟧ (D • ρ)} (⟦⟧-continuous-one{N}{ρ}{NE-ρ})
        (⟦⟧-monotone-one{N}) NE-X

{- The following is annoying. Can it be simplified? -}
all-Cont-Env-Arg⇒cont-envs : ∀{{_ : Semantics}}
    {n}{args : Args (replicate n ■)}{ρ}{NE-ρ}
    → all-args (Cont-Env-Arg ρ NE-ρ) (replicate n ■) args
    → continuous-envs (⟦ args ⟧₊) ρ
all-Cont-Env-Arg⇒cont-envs {zero} {nil}{ρ}{NE-ρ} (lift tt) v v∈𝒯nil =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ , v∈𝒯nil ⟩ ⟩ ⟩
all-Cont-Env-Arg⇒cont-envs {suc n} {cons (ast M) args}{ρ}{NE-ρ}
    ⟨ cM , cont-args ⟩ ⟬ v ∷ vs ⟭ ⟨ v∈ , vs∈ ⟩
    with all-Cont-Env-Arg⇒cont-envs {n} {args}{ρ}{NE-ρ} cont-args ⟬ vs ⟭ vs∈
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯argsρ₁ ⟩ ⟩ ⟩
    with cM v v∈
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈𝒯Mρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ ⊔ₑ ρ₂ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
    ⟨ ⟦⟧-monotone M (λ x d z → inj₂ z) v v∈𝒯Mρ₂ ,
      𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆
       (⟦⟧-monotone-args args (λ x d z → inj₁ z))) ⟬ vs ⟭ vs∈𝒯argsρ₁ ⟩ ⟩ ⟩ ⟩


