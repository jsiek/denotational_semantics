module DelayClos where

open import ISWIMClos1
open import ISWIMClos2
  renaming (Term to Term₂; Arg to Arg₂; Args to Args₂; `_ to #_;
      pair to pair₂; fst to fst₂; snd to snd₂; tuple to tuple₂;
      $ to %; _❲_❳ to _❲_❳₂; inl to inl₂; inr to inr₂; case to case₂;
      cons to cons₂; ast to ast₂; nil to nil₂; _⦅_⦆ to _⦅_⦆₂;
      ⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧₂ₐ; ⟦_⟧₊ to ⟦_⟧₂₊)
open import Primitives
open import PValueCBVAnnot
open import ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import Sig

open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit renaming (tt to True)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)

delay : Term → Term₂
delay-args : ∀{n} → Args (replicate n ■) → Args₂ (replicate n ■)

delay (` x) = # x
delay (clos n N fvs) = pair₂ (fun (delay N)) (tuple₂ n ⦅ delay-args fvs ⦆₂)
delay (L · M) = let dL = delay L in (fst₂ dL) ⦉ snd₂ dL , delay M ⦊
delay ($ B k) = % B k
delay (pair M N) = pair₂ (delay M) (delay N)
delay (fst M) = fst₂ (delay M)
delay (snd M) = snd₂ (delay M)
delay (tuple n ⦅ args ⦆) = tuple₂ n ⦅ delay-args args ⦆₂
delay (M ❲ i ❳) = (delay M) ❲ i ❳₂
delay (inl M) = inl₂ (delay M)
delay (inr M) = inr₂ (delay M)
delay (case L M N) = case₂ (delay L) (delay M) (delay N)

delay-args {zero} nil = nil₂
delay-args {suc n} (cons (ast M) args) =
    cons₂ (ast₂ (delay M)) (delay-args args)

infix 6 _≊_
data _≊_ : List Value → List Value → Set

infix 6 _≅_
data _≅_ : Value → Value → Set where
   ≅-const : ∀ {B} (k : base-rep B)
          → const {B} k ≅ const {B} k
   ≅-↦ : ∀{fvs fvs′ FVS V V′}{w w′}
      → V ≊ V′  →   w ≅ w′   →   fvs ≊ fvs′   →  ⟬ fvs′ ⟭ ∈ mem FVS
      → fvs ⊢ V ↦ w ≅ ❲ [] ⊢ FVS ↦ ([] ⊢ V′ ↦ w′) , ⟬ fvs′ ⟭ ❳
   ≅-ν : ∀{u} → ν ≅ ❲ ν , u ❳ {- needs work -}
   ≅-pair : ∀{u u′ v v′}
      → u ≅ u′  →  v ≅ v′ 
      → ❲ u , v ❳ ≅ ❲ u′ , v′ ❳
   ≅-tuple : ∀{V V′} 
      → V ≊ V′ 
      → ⟬ V ⟭ ≅ ⟬ V′ ⟭
   ≅-left : ∀{V V′}
      → V ≊ V′ 
      → left V ≅ left V′
   ≅-right : ∀{V V′}
      → V ≊ V′ 
      → right V ≅ right V′

data _≊_ where
  ≊-nil : [] ≊ []
  ≊-cons : ∀{v v′}{vs vs′}
     → v ≅ v′  →   vs ≊ vs′ 
     → (v ∷ vs) ≊ (v′ ∷ vs′)

tos : List Value → List Value

to : Value → Value
to (const k) = const k
to (fvs ⊢ V ↦ w) =
    ❲ [] ⊢ (⟬ tos fvs ⟭ ∷ []) ↦ ([] ⊢ tos V ↦ to w) , ⟬ tos fvs ⟭ ❳
to ν = ❲ ν , const 0 ❳ {- needs work -}
to ❲ u , v ❳ = ❲ to u , to v ❳
to ⟬ vs ⟭ = ⟬ tos vs ⟭
to (left V) = left (tos V)
to (right V) = right (tos V)

tos [] = []
tos (v ∷ vs) = (to v) ∷ (tos vs)

to⇒≅ : (v : Value) → v ≅ to v
tos⇒≊ : (vs : List Value) → vs ≊ tos vs

to⇒≅ (const k) = ≅-const k
to⇒≅ (fvs ⊢ V ↦ w) = ≅-↦ (tos⇒≊ V) (to⇒≅ w) (tos⇒≊ fvs) (here refl)
to⇒≅ ν = ≅-ν
to⇒≅ ❲ u , v ❳ = ≅-pair (to⇒≅ u) (to⇒≅ v)
to⇒≅ ⟬ vs ⟭ = ≅-tuple (tos⇒≊ vs)
to⇒≅ (left V) = ≅-left (tos⇒≊ V)
to⇒≅ (right V) = ≅-right (tos⇒≊ V)
tos⇒≊ [] = ≊-nil
tos⇒≊ (v ∷ vs) = ≊-cons (to⇒≅ v) (tos⇒≊ vs)


infix 5 _≲_
_≲_ : (𝒫 Value) → (𝒫 Value) → Set
D ≲ E = ∀ u → D u → Σ[ v ∈ Value ] E v × u ≅ v

infix 5 _≳_
_≳_ : (𝒫 Value) → (𝒫 Value) → Set
D ≳ E = ∀ v → E v → Σ[ u ∈ Value ] D u × u ≅ v

infix 5 _≈_
_≈_ : (𝒫 Value) → (𝒫 Value) → Set 
D₁ ≈ D₂ = D₁ ≲ D₂ × D₁ ≳ D₂

infix 5 _≈ₐ_
data _≈ₐ_ : ∀ {b} → Result (𝒫 Value) b
          → Result (𝒫 Value) b → Set₁ where
    ≈ₐ-■ : ∀{D₁ D₂ : 𝒫 Value} → D₁ ≈ D₂ → _≈ₐ_{■} D₁  D₂
    ≈ₐ-ν : ∀{b}{D₁ D₂} → (∀ d₁ d₂ → d₁ ≈ d₂ → _≈ₐ_{b} (D₁ d₁) (D₂ d₂))
         → _≈ₐ_{ν b} D₁ D₂

infix 5 _≈₊_
data _≈₊_ : ∀ {bs} → Tuple bs (Result (𝒫 Value))
          → Tuple bs (Result (𝒫 Value)) → Set₁ where
    ≈₊-nil : tt ≈₊ tt
    ≈₊-cons : ∀ {b bs}{D₁ D₂ : Result (𝒫 Value) b}
                {Ds₁ Ds₂ : Tuple bs (Result (𝒫 Value))}
       → _≈ₐ_ {b} D₁ D₂ → Ds₁ ≈₊ Ds₂
       → _≈₊_ {b ∷ bs} ⟨ D₁ , Ds₁ ⟩  ⟨ D₂ , Ds₂ ⟩

≲-env : (Var → 𝒫 Value) → (Var → 𝒫 Value) → Set
≲-env ρ ρ′ = ∀ x → ρ x ≲ ρ′ x

tos≢[] : ∀{vs} → vs ≢ [] → tos vs ≢ []
tos≢[] {[]} xx _ = xx refl
tos≢[] {v ∷ vs} xx = λ ()

delay-correct : ∀ {ρ ρ′ : Var → 𝒫 Value} (M : Term)
  → ≲-env ρ ρ′
  → (⟦ M ⟧ ρ) ≲ (⟦ delay M ⟧₂ ρ′)
delay-correct {ρ}{ρ′} (` x) ρ≲ρ′ = ρ≲ρ′ x
delay-correct {ρ}{ρ′} (clos n N fvs) ρ≲ρ′ ν
    ⟨ V , ⟨ FVS , ⟨ ⟨ w∈ΛN , V≢[] ⟩ , ⟨ V⊆𝒯fvsρ , _ ⟩ ⟩ ⟩ ⟩ =
    ⟨ to ν , ⟨ ⟨ True , {!!} ⟩ , (to⇒≅ ν) ⟩ ⟩
delay-correct {ρ}{ρ′} (clos n N fvs) ρ≲ρ′ (FVS₁ ⊢ V₂ ↦ w)
    ⟨ Vᶠ , ⟨ [] , ⟨ ⟨ ⟨ w∈N[V₂•Vᶠ] , ⟨ V₂≢[] , FVS₁∈𝒯fvs ⟩ ⟩ , ⟨ Vᶠ≢[] , refl ⟩ ⟩ ,
           ⟨ Vᶠ⊆𝒯fvsρ , _ ⟩ ⟩ ⟩ ⟩ =
    ⟨ to (FVS₁ ⊢ V₂ ↦ w) , ⟨ ⟨ F , G ⟩ , (to⇒≅ (FVS₁ ⊢ V₂ ↦ w)) ⟩ ⟩
    where
    ρ₁ = (mem V₂ • mem (⟬ FVS₁ ⟭ ∷ []) • (λ x → ⌈ ν ⌉))
    ρ₁′ = (mem (tos V₂) • mem (⟬ tos FVS₁ ⟭ ∷ []) • (λ x → ⌈ ν ⌉))
    ρ₁<ρ₁′ : ≲-env ρ₁ ρ₁′
    ρ₁<ρ₁′ = {!!}
    IH-N : ⟦ N ⟧ ρ₁ ≲ ⟦ delay N ⟧₂ ρ₁′
    IH-N = delay-correct {ρ₁}{ρ₁′} N ρ₁<ρ₁′
    w′∈⟦dN⟧ρ₁ : to w ∈ ⟦ delay N ⟧₂ ρ₁
    w′∈⟦dN⟧ρ₁
        with IH-N w {!w∈N[V₂•Vᶠ]!} {- Vᶠ != (⟬ FVS₁ ⟭ ∷ []) -}
    ... | ⟨ w′ , ⟨ w′∈dN , w≅w′ ⟩ ⟩ = {!!}

    F = ⟨ ⟨ {!!} , {- Use IH on w∈N[V₂•Vᶠ] -}
          ⟨ tos≢[] V₂≢[] ,
            refl ⟩ ⟩ , ⟨ (λ ()) , refl ⟩ ⟩
    G = {!!} {- Use IH on FVS₁∈𝒯fvs -}
delay-correct {ρ}{ρ′} (L · M) ρ≲ρ′ v v∈ = {!!}
delay-correct {ρ}{ρ′} M ρ≲ρ′ v v∈ = {!!}

{-
≈-env : (Var → 𝒫 Value) → (Var → 𝒫 Value) → Set
≈-env ρ ρ′ = ∀ x → ρ x ≈ ρ′ x

delay-correct : ∀ {ρ ρ′ : Var → 𝒫 Value} (M : Term)
  → ≈-env ρ ρ′
  → (⟦ M ⟧ ρ) ≈ (⟦ delay M ⟧₂ ρ′)

delay-args-correct : ∀ {ρ ρ′ : Var → 𝒫 Value} n (args : Args (replicate n ■))
  → ≈-env ρ ρ′
  → (⟦ args ⟧₊ ρ) ≈₊ (⟦ delay-args args ⟧₂₊ ρ′)

delay-correct (` x) ρ≈ρ′ = ρ≈ρ′ x
delay-correct {ρ}{ρ′} (clos n N fvs) ρ≈ρ′ = ⟨ G , {!!} ⟩
  where
  
  G : ⟦ clos n N fvs ⟧ ρ ≲
      ⟦ pair₂ (fun (delay N)) (tuple₂ n ⦅ delay-args fvs ⦆₂) ⟧₂ ρ′
  G (E ↦ w) ⟨ [] , ⟨ ⟨ ⟨ w∈N[E•D•v] , E≢[] ⟩ , _ ⟩ , ⟨ D⊆𝒯fvs , D≢[] ⟩ ⟩ ⟩ =
      ⊥-elim (D≢[] refl)
  G (E ↦ w) ⟨ d ∷ D , ⟨ ⟨ ⟨ w∈N[E•D•v] , E≢[] ⟩ , _ ⟩ , ⟨ D⊆𝒯fvs , D≢[] ⟩ ⟩ ⟩
      with v∈𝒯⇒v≡⟬vs⟭ (D⊆𝒯fvs d (here refl))
  ... | ⟨ vs , refl ⟩ =
      let ρ₁ = mem E • mem D • (λ x → ⌈ ν ⌉)
      let ρ₂ = mem E • mem D • (λ x → ⌈ ν ⌉)
      let IH = delay-correct{ρ₁}{?} N ? in

      ⟨ ❲ {!!} , {!!} ❳ , ⟨ ⟨ {!!} , {!!} ⟩ , {!!} ⟩ ⟩


  G ν ⟨ V , ⟨ ⟨ V↦w∈D , _ ⟩ , ⟨ V⊆E , V≢[] ⟩ ⟩ ⟩ =
      ⟨ ❲ {!!} , {!!} ❳ , ⟨ {!!} , {!!} ⟩ ⟩
  
delay-correct (L · M) ρ≈ρ′ = {!!}
delay-correct {ρ}{ρ′} ($ B k) ρ≈ρ′ = ⟨ G , H ⟩
  where
  G : ⟦ $ B k ⟧ ρ ≲ ⟦ % B k ⟧₂ ρ′
  G v v∈
      with v∈ℬk⇒v≡k{v}{B}{k} v∈
  ... | refl = ⟨ v , ⟨ v∈ , ≅-const k ⟩ ⟩
  H : ⟦ $ B k ⟧ ρ ≳ ⟦ % B k ⟧₂ ρ′
  H v v∈
      with v∈ℬk⇒v≡k{v}{B}{k} v∈
  ... | refl = ⟨ v , ⟨ v∈ , ≅-const k ⟩ ⟩
delay-correct (pair M N) ρ≈ρ′ = {!!}
delay-correct (fst M) ρ≈ρ′ = {!!}
delay-correct (snd M) ρ≈ρ′ = {!!}
delay-correct (tuple n ⦅ args ⦆) ρ≈ρ′ = {!!}
delay-correct (M ❲ i ❳) ρ≈ρ′ = {!!}
delay-correct (inl M) ρ≈ρ′ = {!!}
delay-correct (inr M) ρ≈ρ′ = {!!}
delay-correct (case L M N) ρ≈ρ′ = {!!}

delay-args-correct zero nil = {!!}
delay-args-correct (suc n) (cons (ast M) args) = {!!}
-}
