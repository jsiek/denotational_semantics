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
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import abt.Sig
open import abt.Var
open import abt.GSubst using (_•_)
open import NewSigUtil
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

{- =================== Consistent Semantics =============================== -}

record ConsistentSemantics {A : Set} : Set₁ where
  field 
    {{Sem}} : Semantics {A}
    consistency : A → A → Set
    consistent-op : 𝕆-consistent consistency sig (Semantics.interp-op Sem)

open ConsistentSemantics {{...}}

{- =================== Continuous Semantics ====================== -}

continuous-∈ : ∀ {A} → (Env A → 𝒫 A) → Env A → A → Set₁
continuous-∈ {A} D ρ v = v ∈ D ρ
   → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

continuous-env : ∀ {A} → (Env A → 𝒫 A) → Env A → Set₁
continuous-env {A} D ρ = ∀ v → v ∈ D ρ
                     → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′


continuous-∈⇒⊆ : ∀ {A} E (ρ : Env A) (NE-ρ : nonempty-env ρ)
   → monotone-env E
   → ∀ V → mem V ⊆ E ρ
   → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
   → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′
continuous-∈⇒⊆ E ρ NE-ρ mE [] V⊆E ∀v∈V⇒cont =
   ⟨ initial-finiteNE-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
   ⟨ initial-fin-⊆ ρ NE-ρ , (λ d ()) ⟩ ⟩ ⟩
continuous-∈⇒⊆ {A} E ρ NE-ρ mE (v ∷ V) v∷V⊆Eρ v∈V⇒cont
    with continuous-∈⇒⊆ E ρ NE-ρ mE V (λ d z → v∷V⊆Eρ d (there z))
                (λ w w∈V w∈Mρ → v∈V⇒cont w (there w∈V) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V⊆Eρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷V⊆Eρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-finiteNE-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : A) → mem (v ∷ V) d → d ∈ E ρ₃
    G d (here refl) = mE {ρ₂}{ρ₃} join-⊆-right v v∈Eρ₂
    G d (there m) = mE {ρ₁}{ρ₃} join-⊆-left d (V⊆Eρ₁ d m)



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


{- an attempt at defining a property for monotonicity 
   that can be proved for the op cases without a Semantics -}
continuous-arg-D : ∀ {A} (E : ∀ b → Env A → Result (𝒫 A) b) (ρ∁ : Env A) (NE-ρ∁ : nonempty-env ρ∁) (ρ : Env A) (NE-ρ : nonempty-env ρ)
   → ∀ (b : Sig) → Set₁
continuous-arg-D E ρ∁ NE-ρ∁ ρ NE-ρ ■ = continuous-env (E ■) ρ
continuous-arg-D E ρ∁ NE-ρ∁ ρ NE-ρ (ν b) = ∀ V → (neV : V ≢ []) → continuous-arg-D E ρ∁ NE-ρ∁ (mem V • ρ) (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem neV)) b
continuous-arg-D E ρ∁ NE-ρ∁ ρ NE-ρ (∁ b) = continuous-arg-D E ρ∁ NE-ρ∁ ρ∁ NE-ρ∁ b




{-
all-results-tracebound : ∀ {A} b F ρ (ρ∁ : Env A) → finiteNE-env ρ → finiteNE-env ρ∁ → tracebound-result b F ρ ρ∁
all-results-tracebound ■ F ρ ρ∁ fin-ρ fin-ρ∁ d d∈ = ⟨ ρ , ⟨ fin-ρ , ⟨ (λ i d d∈ρi → d∈ρi) , d∈ ⟩ ⟩ ⟩
all-results-tracebound (ν b) F ρ ρ∁ fin-ρ fin-ρ∁ V Vne = 
  all-results-tracebound b (λ ρ → F ρ (mem V)) (mem V • ρ) ρ∁ 
                         (extend-finiteNE-env fin-ρ ⟨ V , ⟨ ≃-refl , Vne ⟩ ⟩) fin-ρ∁
all-results-tracebound (∁ b) F ρ ρ∁ fin-ρ fin-ρ∁ = all-results-tracebound b F ρ∁ ρ∁ fin-ρ∁ fin-ρ∁
-}


{- here I'm hoping that all semantics are continuous...
   or at least that the type signature for continuous-op can be much simplified.

all-args : (∀ b → Arg b → Set₁) → ∀ bs → Args bs → Set₁
all-args P [] args = Lift (lsuc lzero) True
all-args P (b ∷ bs) (cons arg args) = P b arg × all-args P bs args


record ContinuousSemantics {A : Set} : Set₁ where
  field 
    {{Sem}} : Semantics {A}

    {- continuous-op : ∀{op}{ρ : Env A}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → all-args (continuous-arg ρ NE-ρ) (sig op) args → Σ[ ρ′ ∈ Env A ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
    -}

open ContinuousSemantics {{...}}
-}








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

⟦⟧-monotone-bind : ∀{A} {{_ : Semantics {A}}}{N : ABT}{ρ}
   D E → D ⊆ E → ⟦ N ⟧ (D • ρ) ⊆ ⟦ N ⟧ (E • ρ)
⟦⟧-monotone-bind {A}{N}{ρ} D₁ D₂ D12 = ⟦⟧-monotone N G
  where G : (x : Var) → (D₁ • ρ) x ⊆ (D₂ • ρ) x
        G zero = D12
        G (suc x) = λ v z → z



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



⟦⟧-continuous-⊆  : ∀{A} {{_ : ContinuousSemantics {A}}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → ∀ V → mem V ⊆ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ ⟦ M ⟧ ρ′
⟦⟧-continuous-⊆ {A}{ρ}{NE-ρ} M V V⊆Eρ =
    continuous-∈⇒⊆ ⟦ M ⟧ ρ NE-ρ (⟦⟧-monotone M) V V⊆Eρ
        (λ v v∈V → ⟦⟧-continuous {NE-ρ = NE-ρ} M v)
 





{-

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X E → mem E ⊆ F X → nonempty X
    → Σ[ D ∈ List Value ] mem D ⊆ X  ×  mem E ⊆ F (mem D)  ×  D ≢ []

continuous function:
 F is continuous when
   forall X E,
      mem E ⊆ F X → neX → exists D ⊆ X, D finite, amd E ⊆ F D

continuous-arg : ∀ {A} {{_ : Semantics {A}}} (ρ : Env A) (NE-ρ : nonempty-env ρ)
    → ∀ b → (arg : Arg b) → Set₁
continuous-arg ρ NE-ρ ■ (ast M) = continuous-env ⟦ M ⟧ ρ
continuous-arg ρ NE-ρ (ν b) (bind arg) =
    ∀ V → (ne : V ≢ [])
    → continuous-arg (mem V • ρ)
          (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem ne)) b arg
continuous-arg ρ NE-ρ (∁ b) (clear arg) =
      continuous-arg (λ x → init) (λ i → ⟨ error , refl ⟩) b arg


continuous-∈⇒⊆ : ∀ {A} E (ρ : Env A) (NE-ρ : nonempty-env ρ)
   → monotone-env E
   → ∀ V → mem V ⊆ E ρ
   → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
   → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′
continuous-∈⇒⊆ E ρ NE-ρ mE [] V⊆E ∀v∈V⇒cont =
   ⟨ initial-finiteNE-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
   ⟨ initial-fin-⊆ ρ NE-ρ , (λ d ()) ⟩ ⟩ ⟩
continuous-∈⇒⊆ {A} E ρ NE-ρ mE (v ∷ V) v∷V⊆Eρ v∈V⇒cont
    with continuous-∈⇒⊆ E ρ NE-ρ mE V (λ d z → v∷V⊆Eρ d (there z))
                (λ w w∈V w∈Mρ → v∈V⇒cont w (there w∈V) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V⊆Eρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷V⊆Eρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-finiteNE-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : A) → mem (v ∷ V) d → d ∈ E ρ₃
    G d (here refl) = mE {ρ₂}{ρ₃} join-⊆-right v v∈Eρ₂
    G d (there m) = mE {ρ₁}{ρ₃} join-⊆-left d (V⊆Eρ₁ d m)


-}

{-
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
all-continuous-arg⇒cont-envs : ∀{{_ : Semantics}}
    {n}{args : Args (replicate n ■)}{ρ}{NE-ρ}
    → all-args (continuous-arg ρ NE-ρ) (replicate n ■) args
    → continuous-envs (⟦ args ⟧₊) ρ
all-continuous-arg⇒cont-envs {zero} {nil}{ρ}{NE-ρ} (lift tt) v v∈𝒯nil =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ , v∈𝒯nil ⟩ ⟩ ⟩
all-continuous-arg⇒cont-envs {suc n} {cons (ast M) args}{ρ}{NE-ρ}
    ⟨ cM , cont-args ⟩ ⟬ v ∷ vs ⟭ ⟨ v∈ , vs∈ ⟩
    with all-continuous-arg⇒cont-envs {n} {args}{ρ}{NE-ρ} cont-args ⟬ vs ⟭ vs∈
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯argsρ₁ ⟩ ⟩ ⟩
    with cM v v∈
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈𝒯Mρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ ⊔ₑ ρ₂ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
    ⟨ ⟦⟧-monotone M (λ x d z → inj₂ z) v v∈𝒯Mρ₂ ,
      𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆
       (⟦⟧-monotone-args args (λ x d z → inj₁ z))) ⟬ vs ⟭ vs∈𝒯argsρ₁ ⟩ ⟩ ⟩ ⟩

-}
