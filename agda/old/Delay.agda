module Delay where

open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit renaming (tt to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)

open import Primitives
open import ISWIMAnnot
open import ClosLang
open import Sig
open import GraphModel
open import ModelISWIM
open import ScopedTuple using (Tuple)

delay : ISWIMAnn → Clos
delay-arg : ∀{b} → Arg b → Argᵪ b
delay-args : ∀{bs} → Args bs → Argsᵪ bs

delay (` x) = % x
delay (ƛ n (cons N fvs)) =
  〔 fun ⦑ consᵪ (delay-arg N) nilᵪ ⦒ , tuple n ⦑ delay-args fvs ⦒  〕
delay (L · M) =
  ((delay L ❲ 0 ❳) ▫ (delay L ❲ 1 ❳)) ▫ delay M
delay (papp p k ⦅ args ⦆) = papp p k ⦑ delay-args args ⦒

delay-arg {■} (ast M) = astᵪ (delay M)
delay-arg {ν b} (bind arg) = bindᵪ (delay-arg {b} arg)
delay-arg {∁ b} (clear arg) = clearᵪ (delay-arg {b} arg)

delay-args {[]} nil = nilᵪ
delay-args {b ∷ bs} (cons arg args) = consᵪ (delay-arg arg) (delay-args args)

infix 5 _≅_
data _≅_ : Value → Value → Set where
   ≅-const : ∀ {B} (k : base-rep B)
          → const {B} k ≅ const {B} k
   ≅-⊔ : ∀{u u' v v'}
       → u ≅ u' → v ≅ v'
       → u ⊔ v ≅ u' ⊔ v'
   ≅-↦ : ∀{u v w v' w'}
       → v ≅ v' → w ≅ w'
       → v ↦ w ≅ ((const 0 ↦ (u ↦ (v' ↦ w'))) ⊔ (const 1 ↦ u))
   ≅-bot : ∀{u}
       {- 
       A non-terminating function is related to a closure that,
       when applied to the tuple of values of the free variables, 
       returns a non-terminating function.
       -}
       → ⊥ ≅ ((const 0 ↦ (u ↦ ⊥)) ⊔ (const 1 ↦ u))

infix 5 _⪅_
_⪅_ : (𝒫 Value) → (𝒫 Value) → Set
D₁ ⪅ D₂ = ∀ u → D₁ u → Σ[ v ∈ Value ] D₂ v × u ≅ v

infix 5 _⪆_
_⪆_ : (𝒫 Value) → (𝒫 Value) → Set
D₁ ⪆ D₂ = ∀ v → D₂ v → Σ[ u ∈ Value ] D₁ u × u ≅ v

infix 5 _≈_
_≈_ : (𝒫 Value) → (𝒫 Value) → Set 
D₁ ≈ D₂ = D₁ ⪅ D₂ × D₁ ⪆ D₂

infix 5 _≈ₐ_
data _≈ₐ_ : ∀ {b} → ArgTy (𝒫 Value) b
          → ArgTy (𝒫 Value) b → Set₁ where
    ≈ₐ-■ : ∀{D₁ D₂ : 𝒫 Value} → D₁ ≈ D₂ → _≈ₐ_{■} D₁  D₂
    ≈ₐ-ν : ∀{b}{D₁ D₂} → (∀ d₁ d₂ → d₁ ≈ d₂ → _≈ₐ_{b} (D₁ d₁) (D₂ d₂))
         → _≈ₐ_{ν b} D₁ D₂

infix 5 _≈₊_
data _≈₊_ : ∀ {bs} → Tuple bs (ArgTy (𝒫 Value))
          → Tuple bs (ArgTy (𝒫 Value)) → Set₁ where
    ≈₊-nil : tt ≈₊ tt
    ≈₊-cons : ∀ {b bs}{D₁ D₂ : ArgTy (𝒫 Value) b}
                {Ds₁ Ds₂ : Tuple bs (ArgTy (𝒫 Value))}
       → _≈ₐ_ {b} D₁ D₂ → Ds₁ ≈₊ Ds₂
       → _≈₊_ {b ∷ bs} ⟨ D₁ , Ds₁ ⟩  ⟨ D₂ , Ds₂ ⟩

≈-env : (Var → 𝒫 Value) → (Var → 𝒫 Value) → Set
≈-env ρ ρ′ = ∀ x → ρ x ≈ ρ′ x

⟬⟭-≈ : ∀{n}{args₁ args₂ : Tuple (replicate n ■) (ArgTy (𝒫 Value))}
     → args₁ ≈₊ args₂
     → ⟬ args₁ ⟭ ≈ ⟬ args₂ ⟭
⟬⟭-≈ args≈ = {!!}


delay-correct : ∀ {M : ISWIMAnn} {ρ ρ′ : Var → 𝒫 Value}
  → ≈-env ρ ρ′
  → (ℐ⟦ M ⟧ ρ) ≈ (𝒞⟦ delay M ⟧ ρ′)

delay-arg-correct : ∀ {b}{arg : Arg b} {ρ ρ′ : Var → 𝒫 Value}
  → ≈-env ρ ρ′
  → _≈ₐ_ {b} (ℐ⟦ arg ⟧ₐ ρ) (𝒞⟦ delay-arg arg ⟧ₐ ρ′)

delay-args-correct : ∀ {bs}{args : Args bs} {ρ ρ′ : Var → 𝒫 Value}
  → ≈-env ρ ρ′
  → (ℐ⟦ args ⟧₊ ρ) ≈₊ (𝒞⟦ delay-args args ⟧₊ ρ′)

fwd-tuple : ∀ {v₁ : Value}
  {n}{args₁ args₂ : Tuple (replicate n ■) (ArgTy (𝒫 Value))}
  → args₁ ≈₊ args₂  →  ⟬ args₁ ⟭ v₁
  → Σ[ v₂ ∈ Value ] ⟬ args₂ ⟭ v₂ × v₁ ≅ v₂
fwd-tuple = {!!}

bkwd-tuple : ∀ {v₂ : Value}
  {n}{args₁ args₂ : Tuple (replicate n ■) (ArgTy (𝒫 Value))}
  → args₁ ≈₊ args₂  →  ⟬ args₂ ⟭ v₂
  → Σ[ v₁ ∈ Value ] ⟬ args₁ ⟭ v₁ × v₁ ≅ v₂
bkwd-tuple = {!!}

≅↓≈ : ∀ {v₁ v₂ : Value}
  → v₁ ≅ v₂
  → ↓ v₁ ≈ ↓ v₂
≅↓≈ {v₁} {v₂} v12 = {!!}

≈-apply : ∀{n}{N₁ N₂ : ArgTy (𝒫 Value) (ℕ→sig (suc n))}{D₁ D₂ : 𝒫 Value}
    → _≈ₐ_{b = (ℕ→sig (suc n))} N₁ N₂ → D₁ ≈ D₂ → _≈ₐ_{b = (ℕ→sig n)}
        (N₁ D₁) (N₂ D₂)
≈-apply N12 D12 = {!!}

{-
≈-abstract : ∀{D₁ D₂}
    D₁ ≈ₐ D₂
  → 𝐺 D₁ ≈ 𝐺 D₂
  → 
-}

≈-apply-∃ : ∀{w₁ w₁′ : Value}{N₁ N₂ : (𝒫 Value) → (𝒫 Value)}
  → _≈ₐ_{b = ν ■} N₁ N₂
  → N₁ (↓ w₁) w₁′
  → Σ[ w₂ ∈ Value ] Σ[ w₂′ ∈ Value ]
    N₂ (↓ w₂) w₂′ × w₁ ≅ w₂ × w₁′ ≅ w₂′
≈-apply-∃ = {!!}  

delay-lam : ∀{N₁ N₂ : ArgTy (𝒫 Value) (ν (ν ■))}
  {n}{args₁ args₂ : Tuple (replicate n ■) (ArgTy (𝒫 Value))}
  → _≈ₐ_{(ν (ν ■))} N₁ N₂
  → args₁ ≈₊ args₂
  → (𝐺-iter 2 N₁) ▪ ⟬ args₁ ⟭ ≈ ⟬ ⟨ 𝐺-iter 2 N₂ , ⟨ ⟬ args₂ ⟭ , tt ⟩ ⟩ ⟭
delay-lam {N₁}{N₂}{n}{args₁}{args₂} N1≈N2 args≈ = ⟨ fwd , bkwd ⟩
  where
  fwd : 𝐺-iter 2 N₁ ▪ ⟬ args₁ ⟭ ⪅ ⟬ ⟨ 𝐺-iter 2 N₂ , ⟨ ⟬ args₂ ⟭ , tt ⟩ ⟩ ⟭
  fwd ⊥ ⟨ v₁ , ⟨ wfv₁ , ⟨ w₁∈GN₁↓v₁ , v₁∈⟬args₁⟭ ⟩ ⟩ ⟩
      with fwd-tuple args≈ v₁∈⟬args₁⟭
  ... | ⟨ v₂ , ⟨ v₂∈args₂ , v₁=v₂ ⟩ ⟩ =
      ⟨ const zero ↦ v₂ ↦ ⊥ ⊔ const 1 ↦ v₂ ,
      ⟨ ⟨ ⟨ v₂ ↦ ⊥ , ⟨ True , inj₁ refl ⟩ ⟩ ,
      ⟨ ⟨ v₂ , ⟨ v₂∈args₂ , (inj₂ refl) ⟩ ⟩ , True ⟩ ⟩ , ≅-bot ⟩ ⟩
  fwd (w₁ ↦ w₁′) ⟨ v₁ , ⟨ wfv₁ , ⟨ w₁∈GN₁↓v₁ , v₁∈⟬args₁⟭ ⟩ ⟩ ⟩
      with fwd-tuple args≈ v₁∈⟬args₁⟭
  ... | ⟨ v₂ , ⟨ v₂∈args₂ , v₁=v₂ ⟩ ⟩
      with ≈-apply-∃ (≈-apply N1≈N2 (≅↓≈ v₁=v₂)) w₁∈GN₁↓v₁
  ... | ⟨ w₂ , ⟨ w₂′ , ⟨ w₂′∈N₂ , ⟨ w12 , w12′ ⟩ ⟩ ⟩ ⟩  =
    ⟨ const zero ↦ v₂ ↦ w₂ ↦ w₂′ ⊔ const 1 ↦ v₂ ,
    ⟨ ⟨ ⟨ v₂ ↦ w₂ ↦ w₂′ , ⟨ w₂′∈N₂ , inj₁ refl ⟩ ⟩ ,
    ⟨ ⟨ v₂ , ⟨ v₂∈args₂ , inj₂ refl ⟩ ⟩ , _ ⟩ ⟩ ,
    (≅-↦ {u = v₂} w12 w12′) ⟩ ⟩
  fwd (w₁ ⊔ w₁′)
      ⟨ v₁ , ⟨ wfv₁ , ⟨ ⟨ w₁∈GN₁↓v₁ , w₁′∈GN₁↓v₁ ⟩ , v₁∈⟬args₁⟭ ⟩ ⟩ ⟩
      with fwd w₁ ⟨ v₁ , ⟨ wfv₁ , ⟨ w₁∈GN₁↓v₁ , v₁∈⟬args₁⟭ ⟩ ⟩ ⟩
  ... | ⟨ w₂ , ⟨ ⟨ ⟨ u₂ , ⟨ u₂∈GGN₂ , 0↦u₂∈w₂ ⟩ ⟩ ,
        ⟨ ⟨ u₂′ , ⟨ xx , 1↦u₂′∈w₂ ⟩ ⟩ , _ ⟩ ⟩ , w1≈w2 ⟩ ⟩
      with fwd w₁′ ⟨ v₁ , ⟨ wfv₁ , ⟨ w₁′∈GN₁↓v₁ , v₁∈⟬args₁⟭ ⟩ ⟩ ⟩
  ... | ⟨ w₂′ , ⟨ yy1 , w1′≈w2′ ⟩ ⟩ =
    ⟨ w₂ ⊔ w₂′ ,
    ⟨ ⟨ ⟨ u₂ , ⟨ u₂∈GGN₂ , inj₁ 0↦u₂∈w₂ ⟩ ⟩ ,
    ⟨ ⟨ u₂′ , ⟨ xx , inj₁ 1↦u₂′∈w₂ ⟩ ⟩ , _ ⟩ ⟩ ,
      ≅-⊔ w1≈w2 w1′≈w2′ ⟩ ⟩

  bkwd : 𝐺 (λ D → 𝐺 (λ D₁ → N₁ D D₁)) ▪ ⟬ args₁ ⟭ ⪆
            ⟬ ⟨ 𝐺 (λ D → 𝐺 (λ D₁ → N₂ D D₁)) , ⟨ ⟬ args₂ ⟭ , tt ⟩ ⟩ ⟭
  bkwd v₂ ⟨ ⟨ v₂′ , ⟨ v₂′∈GGN₂ , 0↦v2′∈v₂ ⟩ ⟩ ,
          ⟨ ⟨ w₂ , ⟨ w2∈args₂ , 1↦w₂∈v₂ ⟩ ⟩ , tt ⟩ ⟩ 
      with bkwd-tuple args≈ w2∈args₂
  ... | ⟨ v₁ , ⟨ v₁∈args₁ , v₁=v₂ ⟩ ⟩ =
            ⟨ {!!} , ⟨ ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩ ⟩ , {!!} ⟩ ⟩
  
delay-app : ∀{L₁ L₂ M₁ M₂ : 𝒫 Value}
   → L₁ ≈ L₂
   → M₁ ≈ M₂
   → L₁ ▪ M₁ ≈ ((ℕth L₂ 0) ▪ ℕth L₂ 1) ▪ M₂
delay-app L12 M12 = {!!}


delay-correct {` x}{ρ}{ρ′} ρ≈ρ′ = ρ≈ρ′ x
delay-correct {lam n ⦅ cons N args ⦆}{ρ}{ρ′} ρ≈ρ′ =
  let IH1 = delay-arg-correct {arg = N} ρ≈ρ′ in
  let IH2 = delay-args-correct {args = args} ρ≈ρ′ in
  delay-lam IH1 IH2
delay-correct {L · M}{ρ}{ρ′} ρ≈ρ′ =
   let IH1 = delay-correct {L}{ρ}{ρ′} ρ≈ρ′ in
   let IH2 = delay-correct {M}{ρ}{ρ′} ρ≈ρ′ in
   delay-app IH1 IH2
delay-correct {papp p k ⦅ args ⦆}{ρ}{ρ′} ρ≈ρ′ =
   let IH = delay-args-correct {args = args} ρ≈ρ′ in
   {!!}
   {-
   𝐹-iter-≈{arity p} (≈-refl (℘ {p} k)) (⟬⟭-≈ IH)
   -}

delay-arg-correct ρ≈ρ′ = {!!}

delay-args-correct ρ≈ρ′ = {!!}


