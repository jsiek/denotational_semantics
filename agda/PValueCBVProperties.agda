{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import PValueCBV
open import ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import Sig
open import Syntax hiding (⌈_⌉)
open import Utilities using (extensionality)

module PValueCBVProperties (Op : Set) (sig : Op → List Sig) where

open import Fold2 Op sig
open Syntax.OpSig Op sig
open import WellScoped Op sig using (WF-plug) 

{- environments whose codomain are finite nonempty sets -}
fin-env : Env → Set
fin-env ρ = ∀ x → Σ[ E ∈ List Value ] ρ x ≃ mem E × E ≢ []

infix 6 _⊔ₑ_
_⊔ₑ_ : Env → Env → Env
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-fin-env : ∀{ρ₁ ρ₂}  → fin-env ρ₁  →  fin-env ρ₂  →  fin-env (ρ₁ ⊔ₑ ρ₂)
join-fin-env {ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ⟨ ρ₁=E1 , NE-E1 ⟩ ⟩
    with f2 x
... | ⟨ E2 , ⟨ ρ₂=E2 , NE-E2 ⟩ ⟩ =
    ⟨ (E1 ++ E2) , ⟨ ⟨ G , (H {E1} λ d z → z) ⟩ ,
      (λ E12=[] → NE-E1 (++-conicalˡ E1 E2 E12=[])) ⟩ ⟩
    where
    G : (v : Value) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = ∈-++⁺ˡ ((proj₁ ρ₁=E1) v ρ1x)
    G v (inj₂ ρ2x) = ∈-++⁺ʳ E1 ((proj₁ ρ₂=E2) v ρ2x)

    H : ∀{E} → mem E ⊆ mem E1 → mem (E ++ E2) ⊆ (λ v → ρ₁ x v ⊎ ρ₂ x v)
    H {[]} E<E1 v v∈E++E2 = inj₂ ((proj₂ ρ₂=E2) v v∈E++E2)
    H {x ∷ E} E<E1 .x (here refl) = inj₁ ((proj₂ ρ₁=E1) x (E<E1 x (here refl)))
    H {x ∷ E} E<E1 v (there v∈E++E2) =
       H (λ v z → E<E1 v (there z)) v v∈E++E2

join-lub : ∀{ρ ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{ρ₁ ρ₂} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z



rel-args : ∀{ℓ}{T : Set ℓ}
   → (∀ b → ArgTy T b → ArgTy T b → Set₁)
   → ∀ bs → Tuple bs (ArgTy T)
   → Tuple bs (ArgTy T) → Set₁
rel-args R [] xs ys = Lift (lsuc lzero) True
rel-args R (b ∷ bs) ⟨ x , xs ⟩ ⟨ y , ys ⟩ = (R b x y) × (rel-args R bs xs ys)

⊆-arg : ∀ b → ArgTy (𝒫 Value) b → ArgTy (𝒫 Value) b → Set₁
⊆-arg ■ x y = Lift (lsuc lzero) (x ⊆ y)
⊆-arg (ν b) f g = ∀ X → ⊆-arg b (f X) (g X)
⊆-arg (∁ b) x y = ⊆-arg b x y

⊆-args = rel-args ⊆-arg

pred-args : (∀ b → Arg b → Set₁) → ∀ bs → Args bs → Set₁
pred-args P [] args = Lift (lsuc lzero) True
pred-args P (b ∷ bs) (cons arg args) = P b arg × pred-args P bs args

continuous-∈ : (Env → 𝒫 Value) → Env → Value → Set₁
continuous-∈ D ρ v = v ∈ D ρ → Σ[ ρ′ ∈ Env ] fin-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′
     
record Semantics : Set₁ where
  field interp-op  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
  
  ⟦_⟧ : ABT → Env → 𝒫 Value
  ⟦ M ⟧ ρ = fold interp-op ∅ ρ M

  ⟦_⟧ₐ : ∀{b} → Arg b → Env  → ArgTy (𝒫 Value) b
  ⟦ arg ⟧ₐ ρ = fold-arg interp-op ∅ ρ arg

  ⟦_⟧₊ : ∀{bs} → Args bs → Env  → Tuple bs (ArgTy (𝒫 Value))
  ⟦ args ⟧₊ ρ = fold-args interp-op ∅ ρ args

  field mono-op : ∀{op}{xs}{ys} → ⊆-args (sig op) xs ys → interp-op op xs ⊆ interp-op op ys

  Cont-Env-Arg : ∀ {{_ : Semantics}} (ρ : Env) (NE-ρ : nonempty-env ρ)
    → ∀ b → (arg : Arg b)  → Set₁
  Cont-Env-Arg ρ NE-ρ ■ (ast M) = ∀ v → continuous-∈ ⟦ M ⟧ ρ v
  Cont-Env-Arg ρ NE-ρ (ν b) (bind arg) =
    ∀ V → (ne : V ≢ [])
    → Cont-Env-Arg (mem V • ρ)
          (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem ne)) b arg
  Cont-Env-Arg ρ NE-ρ (∁ b) (clear arg) = Lift (lsuc lzero) True

open Semantics {{...}}

record ContinuousSemantics : Set₁ where
  field {{Sem}} : Semantics
  field continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → pred-args (Cont-Env-Arg ρ NE-ρ) (sig op) args  →   Σ[ ρ′ ∈ Env ] fin-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)

open ContinuousSemantics {{...}}

{- Monotone -------------------------------------------------------------------}

monotone-env : (Env → 𝒫 Value) → Set₁
monotone-env D = ∀ {ρ ρ′} → (∀ x → ρ x ⊆ ρ′ x)  →  D ρ ⊆ D ρ′
  
⟦⟧-monotone : ∀{{_ : Semantics}} {ρ ρ′} (M : ABT)
  →  ρ ⊆ₑ ρ′ →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-monotone-arg : ∀{{_ : Semantics}} {b}{ρ ρ′} (arg : Arg b)
  →  ρ ⊆ₑ ρ′ →  ⊆-arg b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-monotone-args : ∀{{_ : Semantics}} {bs}{ρ ρ′} (args : Args bs)
  →  ρ ⊆ₑ ρ′  →  ⊆-args bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)
  
⟦⟧-monotone {ρ}{ρ′} (` x) ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {ρ}{ρ′} (op ⦅ args ⦆) ρ<ρ′ = mono-op (⟦⟧-monotone-args  args ρ<ρ′)

⟦⟧-monotone-arg {■} (ast M) ρ<ρ′ = lift (⟦⟧-monotone M ρ<ρ′)
⟦⟧-monotone-arg {ν b}{ρ}{ρ′} (bind arg) ρ<ρ′ X =
    ⟦⟧-monotone-arg {b}{X • ρ}{X • ρ′} arg (env-ext ρ<ρ′)
⟦⟧-monotone-arg {∁ b} (clear arg) ρ<ρ′ =
    ⟦⟧-monotone-arg {b}{λ x → ∅}{λ x → ∅} arg λ x d z → z

⟦⟧-monotone-args {bs = []} nil ρ<ρ′ = lift tt
⟦⟧-monotone-args {bs = b ∷ bs} (cons arg args) ρ<ρ′ =
  ⟨ ⟦⟧-monotone-arg arg ρ<ρ′ , ⟦⟧-monotone-args args ρ<ρ′ ⟩

{- Continuous -----------------------------------------------------------------}

{- creates an environment that maps each variable x to
   a singleton set of some element in ρ x.  -}
initial-fin-env : (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
initial-fin-env ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ = ⌈ v ⌉

initial-fin : (ρ : Env) → (NE-ρ : nonempty-env ρ)
   → fin-env (initial-fin-env ρ NE-ρ)
initial-fin ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ =
      ⟨ v ∷ [] ,
      ⟨ ⟨ (λ {w refl → (here refl)}) , (λ {w (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

initial-fin-⊆ : (ρ : Env) → (NE-ρ : nonempty-env ρ)
  → initial-fin-env ρ NE-ρ ⊆ₑ ρ
initial-fin-⊆ ρ NE-ρ x v v∈initial
    with NE-ρ x
... | ⟨ w , w∈ρx ⟩ rewrite v∈initial = w∈ρx

{- single-env maps x to D and any other variable y to something in ρ y. -}
single-env : Var → 𝒫 Value → (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
single-env x D ρ NE-ρ y
    with x ≟ y
... | yes refl = D
... | no neq
    with NE-ρ y
... | ⟨ v , v∈ρy ⟩ = ⌈ v ⌉    

single-fin : ∀{v}{x}{ρ}{NE-ρ} → fin-env (single-env x ⌈ v ⌉ ρ NE-ρ)
single-fin {v}{x}{ρ}{NE-ρ} y
    with x ≟ y
... | yes refl =
    ⟨ v ∷ [] ,
    ⟨ ⟨ (λ { v₁ refl → (here refl)}) , (λ{ v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩
... | no neq
    with NE-ρ y
... | ⟨ w , w∈ρy ⟩ =
    ⟨ w ∷ [] ,
    ⟨ ⟨ (λ { v₁ refl → here refl}) , (λ { v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

single-⊆ : ∀{ρ x v}{NE-ρ : nonempty-env ρ}
  →  v ∈ ρ x  →  single-env x ⌈ v ⌉ ρ NE-ρ ⊆ₑ ρ
single-⊆ {ρ}{x}{v}{NE-ρ} v∈ρx y w sing 
    with x ≟ y
... | yes refl rewrite sing = v∈ρx
... | no neq
    with NE-ρ y
... | ⟨ u , u∈ρy ⟩ rewrite sing = u∈ρy

v∈single[xv]x : ∀{v}{x}{ρ}{NE-ρ} → v ∈ single-env x ⌈ v ⌉ ρ NE-ρ x
v∈single[xv]x {v}{x}
    with x ≟ x
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

continuous-⊆ : (Env → 𝒫 Value) → Env → Set₁
continuous-⊆ E ρ = ∀ V → mem V ⊆ E ρ
                     → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
                     → Σ[ ρ′ ∈ Env ] fin-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′

▪-continuous : ∀{D E : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{w}
  → w ∈ (D ρ) ▪ (E ρ)
  → (∀ v → continuous-∈ D ρ v) → (∀ v → continuous-∈ E ρ v)
  → monotone-env D → monotone-env E → continuous-⊆ E ρ
  → Σ[ ρ₃ ∈ Env ] fin-env ρ₃ × ρ₃ ⊆ₑ ρ × w ∈ (D ρ₃) ▪ (E ρ₃)
▪-continuous {D}{E}{ρ}{NE-ρ}{w} ⟨ V , ⟨ V↦w∈Dρ , ⟨ V⊆Eρ , V≢[] ⟩ ⟩ ⟩
    IH-D IH-E mD mE cE
    with IH-D (V ↦ w) V↦w∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V↦w∈Dρ₁ ⟩ ⟩ ⟩
    with (cE V V⊆Eρ (λ v v∈V → IH-E v))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , V⊆Eρ₂ ⟩ ⟩ ⟩ =
   ⟨ ρ₃ , ⟨ join-fin-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ , w∈D▪Eρ₃ ⟩ ⟩ ⟩ 
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    V↦w∈Dρ₃ : V ↦ w ∈ D ρ₃
    V↦w∈Dρ₃ = mD ρ₁⊆ρ₃ (V ↦ w) V↦w∈Dρ₁
    ρ₂⊆ρ₄ = λ x v z → inj₂ z
    V⊆Eρ₃ : mem V ⊆ E ρ₃
    V⊆Eρ₃ v v∈V = mE ρ₂⊆ρ₄ v (V⊆Eρ₂ v v∈V)
    w∈D▪Eρ₃ : w ∈ (D ρ₃) ▪ (E ρ₃)
    w∈D▪Eρ₃ = ⟨ V , ⟨ V↦w∈Dρ₃ , ⟨ V⊆Eρ₃ , V≢[] ⟩ ⟩ ⟩

Λ-continuous : ∀{E : Env  → 𝒫 Value}{ρ}{NE-ρ}{v}
  → v ∈ Λ (λ D → E (D • ρ))
  → (∀ V → V ≢ [] → (v : Value)
     → continuous-∈ E (mem V • ρ) v)
  → monotone-env E
  → Σ[ ρ′ ∈ Env ] fin-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ Λ (λ D → E (D • ρ′))
Λ-continuous {E}{ρ}{NE-ρ}{V ↦ w} ⟨ w∈EV•ρ , V≢[] ⟩ IH mE
    with IH V V≢[] w w∈EV•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆V•ρ , w∈Eρ′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → ρ′ (suc x)) , ⟨ (λ x → fρ′ (suc x)) , ⟨ (λ x → ρ′⊆V•ρ (suc x)) ,
    ⟨ mE{ρ′}{mem V • (λ x → ρ′ (suc x))} G w w∈Eρ′ , V≢[] ⟩ ⟩ ⟩ ⟩
    where G : (x : Var) → ρ′ x ⊆ (mem V • (λ x₁ → ρ′ (suc x₁))) x
          G zero v v∈ρ′x = ρ′⊆V•ρ 0 v v∈ρ′x
          G (suc x) v v∈ρ′x = v∈ρ′x
Λ-continuous {E}{ρ}{NE-ρ}{ν} v∈Λ IH mE =
  ⟨ initial-fin-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
      tt ⟩ ⟩ ⟩

⟦⟧-continuous-⊆ : ∀{{_ : Semantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT) → continuous-⊆ ⟦ M ⟧ ρ
⟦⟧-continuous-⊆ {ρ = ρ} {NE-ρ} M [] V⊆⟦M⟧ρ v∈V⇒cont =
  ⟨ initial-fin-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
    (λ d ()) ⟩ ⟩ ⟩
⟦⟧-continuous-⊆ {ρ = ρ} {NE-ρ} M (v ∷ E) v∷E⊆⟦M⟧ρ v∈V⇒cont
    with ⟦⟧-continuous-⊆ {ρ = ρ}{NE-ρ} M E (λ d z → v∷E⊆⟦M⟧ρ d (there z))
                (λ w w∈E w∈Mρ → v∈V⇒cont w (there w∈E) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , E⊆⟦M⟧ρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷E⊆⟦M⟧ρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈⟦M⟧ρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-fin-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : Value) → mem (v ∷ E) d → d ∈ ⟦ M ⟧ ρ₃
    G d (here refl) = ⟦⟧-monotone {ρ₂}{ρ₃} M join-⊆-right v v∈⟦M⟧ρ₂
    G d (there m) = ⟦⟧-monotone {ρ₁}{ρ₃} M join-⊆-left d (E⊆⟦M⟧ρ₁ d m)

{- the main lemma -}
⟦⟧-continuous-env : ∀{{_ : ContinuousSemantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → ∀ v → continuous-∈ ⟦ M ⟧ ρ v
⟦⟧-cont-env-arg : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ} {b}(arg : Arg b)
  → Cont-Env-Arg ρ NE-ρ b arg 
⟦⟧-cont-env-args : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ}{bs} (args : Args bs)
  → pred-args (Cont-Env-Arg ρ NE-ρ) bs args

⟦⟧-continuous-env {ρ}{NE-ρ} (` x) v v∈⟦M⟧ρ =
   ⟨ (single-env x ⌈ v ⌉ ρ NE-ρ) , ⟨ (single-fin {v}{x}) , ⟨ (single-⊆ v∈⟦M⟧ρ) ,
     (v∈single[xv]x {v}{x}) ⟩ ⟩ ⟩

⟦⟧-continuous-env {ρ}{NE-ρ} (op ⦅ args ⦆) v v∈⟦M⟧ρ =
    continuous-op{NE-ρ = NE-ρ} v∈⟦M⟧ρ (⟦⟧-cont-env-args {ρ}{NE-ρ} args)
⟦⟧-cont-env-arg {ρ} {NE-ρ} {■} (ast M) v v∈⟦M⟧ρ =
    ⟦⟧-continuous-env {ρ}{NE-ρ = NE-ρ} M v v∈⟦M⟧ρ
⟦⟧-cont-env-arg {ρ} {NE-ρ} {ν b} (bind arg) V V≢[] =
   let NE-V•ρ = (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem V≢[])) in
   ⟦⟧-cont-env-arg {mem V • ρ}{NE-V•ρ} {b} arg
⟦⟧-cont-env-arg {ρ} {NE-ρ} {∁ b} (clear arg) = lift tt

⟦⟧-cont-env-args {ρ} {NE-ρ} {[]} nil = lift tt
⟦⟧-cont-env-args {ρ} {NE-ρ} {b ∷ bs} (cons arg args) =
    ⟨ ⟦⟧-cont-env-arg {ρ}{NE-ρ}{b} arg ,
      ⟦⟧-cont-env-args {ρ} {NE-ρ} {bs} args ⟩



