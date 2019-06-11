open import Agda.Primitive using (lzero)
open import Data.Nat using (ℕ; suc ; zero; _+_; _<_; _≤_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
         +-mono-≤-<; +-mono-<-≤; +-comm; n≤1+n;
         ≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Maybe
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; inspect; [_])

open import Variables
open import Primitives
open import ValueBCDConst
open import Structures
open DomainAux domain
open OrderingAux domain ordering
open import BelowBCDConst

module FunInverseBCDConst where


{------------------------------
  Function Inversion
 -------------------------------}

not-u₁⊔u₂∈v : ∀{v u₁ u₂}{c} → ¬ ((u₁ ⊔ u₂){c}) ∈ v
not-u₁⊔u₂∈v {⊥} ()
not-u₁⊔u₂∈v {const x} ()
not-u₁⊔u₂∈v {v ↦ v₁} ()
not-u₁⊔u₂∈v {v ⊔ v₁} (inj₁ x) = not-u₁⊔u₂∈v x
not-u₁⊔u₂∈v {v ⊔ v₁} (inj₂ y) = not-u₁⊔u₂∈v y


∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {⊥} {⊥} u∈v = ⊑-⊥
∈→⊑ {⊥} {v} u∈v = ⊑-⊥
∈→⊑ {u} {⊥} u∈v rewrite u∈v = ⊑-⊥
∈→⊑ {const {B} k} {const {B′} k′} u∈v rewrite u∈v = ⊑-refl
∈→⊑ {const {B} k} {v ↦ w} ()
∈→⊑ {v ↦ w} {const k} ()
∈→⊑ {v ↦ w} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)
∈→⊑ {u₁ ⊔ u₂} {v} u∈v = ⊥-elim (contradiction u∈v not-u₁⊔u₂∈v)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-⊥
⊆→⊑ {const {B} k} s with s {const {B} k} refl
... | x = ∈→⊑ x
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

⊔⊆-inv : ∀{u v w : Value}{c}
       → ((u ⊔ v){c}) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

↦⊆→∈ : ∀{v w u : Value}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl 

not-Fun-k : ∀{B : Base}{k : base-rep B} → ¬ Fun (const {B} k)
not-Fun-k {B} {k} (fun ())

Funs : Value → Set
Funs v = ∀{u} → u ∈ v → Fun u

Funs⊥ : Value → Set
Funs⊥ v = ∀{u} → u ∈ v → Fun⊥ u

¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())

Funs∈ : ∀{u}
      → Funs u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {const {B} k} f = ⊥-elim (not-Fun-k (f refl))
Funs∈ {v ↦ w} f = ⟨ v , ⟨ w , refl ⟩ ⟩
Funs∈ {u ⊔ u′} f
    with Funs∈ λ z → f (inj₁ z)
... | ⟨ v , ⟨ w , m ⟩ ⟩ = ⟨ v , ⟨ w , (inj₁ m) ⟩ ⟩


↦∈→⊆dom : ∀{u u′ v w : Value}
      → (v ↦ w) ∈ u
      → dom u ≡ just u′
        ----------------------------
      → v ⊆ u′
↦∈→⊆dom {⊥} () eq 
↦∈→⊆dom {const {B} k} () eq
↦∈→⊆dom {u₁ ↦ u₂}{u′}{v}{w} refl refl u∈v = u∈v
↦∈→⊆dom {(u₁ ⊔ u₂) {c}} {u′} {v} {w} (inj₁ v↦w∈u₁) eq {v'} v'∈v
    with dom u₁ | inspect dom u₁ | dom u₂ | inspect dom u₂
... | just v₁ | [ domu₁≡v₁ ] | just v₂ | [ domu₂≡v₂ ]
    with consistent? v₁ v₂ 
... | yes v₁~v₂
    with eq
... | refl =
      inj₁ (↦∈→⊆dom {u₁}{v₁} v↦w∈u₁ domu₁≡v₁ v'∈v)
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₁ v↦w∈u₁) eq {v'} v'∈v
    | just v₁ | [ domu₁≡v₁ ] | just v₂ | [ domu₂≡v₂ ] | no v₁~̸v₂ 
    with eq
... | ()
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₁ v↦w∈u₁) eq {v'} v'∈v
    | nothing | [ _ ] | _ | [ _ ]
    with eq
... | ()
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₁ v↦w∈u₁) eq {v'} v'∈v
    | just v₁ | [ domu₁≡v₁ ] | nothing | [ _ ]
    with eq
... | ()

↦∈→⊆dom {(u₁ ⊔ u₂) {c}} {u′} {v} {w} (inj₂ v↦w∈u₂) eq {v'} v'∈v
    with dom u₁ | inspect dom u₁ | dom u₂ | inspect dom u₂
... | just v₁ | [ domu₁≡v₁ ] | just v₂ | [ domu₂≡v₂ ]
    with consistent? v₁ v₂ 
... | yes v₁~v₂
    with eq
... | refl =
      inj₂ (↦∈→⊆dom {u₂}{v₂} v↦w∈u₂ domu₂≡v₂ v'∈v)
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₂ v↦w∈u₂) eq {v'} v'∈v
    | just v₁ | [ domu₁≡v₁ ] | just v₂ | [ domu₂≡v₂ ] | no v₁~̸v₂ 
    with eq
... | ()
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₂ v↦w∈u₂) eq {v'} v'∈v
    | nothing | [ _ ] | _ | [ _ ]
    with eq
... | ()
↦∈→⊆dom {(u₁ ⊔ u₂){c}} {u′} {v} {w} (inj₂ v↦w∈u₂) eq {v'} v'∈v
    | just v₁ | [ domu₁≡v₁ ] | nothing | [ _ ]
    with eq
... | ()


⊆↦→cod⊆ : ∀{u u′ v w : Value}
        → u ⊆ v ↦ w
        → cod u ≡ just u′ 
          --------------
        → u′ ⊆ w
⊆↦→cod⊆ {⊥} s ()
⊆↦→cod⊆ {const {B} k} u⊆v↦w ()
⊆↦→cod⊆ {C ↦ C′} s refl
    with s {C ↦ C′} refl
... | refl = λ z → z
⊆↦→cod⊆ {u₁ ⊔ u₂}{u′}{v}{w} u⊆v↦w codu≡u′ {v′} v′∈u′
    with cod u₁ | inspect cod u₁ | cod u₂ | inspect cod u₂
... | just v₁ | [ codu₁≡v₁ ] | just v₂ | [ codu₂≡v₂ ]
    with consistent? v₁ v₂
... | yes v₁~v₂
    with codu≡u′
... | refl
    with v′∈u′
... | inj₁ v′∈v₁ =     
      ⊆↦→cod⊆ (λ x → u⊆v↦w (inj₁ x)) codu₁≡v₁ v′∈v₁
... | inj₂ v′∈v₂ =
      ⊆↦→cod⊆ (λ x → u⊆v↦w (inj₂ x)) codu₂≡v₂ v′∈v₂
⊆↦→cod⊆ {u₁ ⊔ u₂}{u′}{v}{w} u⊆v↦w codu≡u′ {v′} v′∈u′
    | just v₁ | [ codu₁≡v₁ ] | just v₂ | [ codu₂≡v₂ ]
    | no v₁~̸v₂
    with codu≡u′
... | ()
⊆↦→cod⊆ {u₁ ⊔ u₂}{u′}{v}{w} u⊆v↦w codu≡u′ {v′} v′∈u′
    | just v₁ | [ codu₁≡v₁ ] | nothing | [ _ ]
    with codu≡u′
... | ()
⊆↦→cod⊆ {u₁ ⊔ u₂}{u′}{v}{w} u⊆v↦w codu≡u′ {v′} v′∈u′
    | nothing | [ _ ] | _ | [ _ ]
    with codu≡u′
... | ()


dom-u⊔v→dom-u×dom-v : ∀{u v w}{c}
         → dom ((u ⊔ v){c}) ≡ just w
         → Σ[ u′ ∈ Value ] Σ[ v′ ∈ Value ] Σ[ c′ ∈ u′ ~ v′ ]
            dom u ≡ just u′ × dom v ≡ just v′ × w ≡ (u′ ⊔ v′) {c′}
dom-u⊔v→dom-u×dom-v {u}{v}{w}{c} dom-u⊔v
    with dom u | dom v
... | just u′  | just v′
    with consistent? u′ v′
... | yes u′~v′
    with dom-u⊔v
... | refl = ⟨ u′ , ⟨ v′ , ⟨ u′~v′  , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ ⟩
dom-u⊔v→dom-u×dom-v {u}{v}{w}{c} () | just u′  | just v′ | no u′~̸v′
dom-u⊔v→dom-u×dom-v {u}{v}{w}{c} () | nothing  | _
dom-u⊔v→dom-u×dom-v {u}{v}{w}{c} () | just u′  | nothing


cod-u⊔v→cod-u×cod-v : ∀{u v w}{c}
         → cod ((u ⊔ v){c}) ≡ just w
         → Σ[ u′ ∈ Value ] Σ[ v′ ∈ Value ] Σ[ c′ ∈ u′ ~ v′ ]
           cod u ≡ just u′ × cod v ≡ just v′ × w ≡ (u′ ⊔ v′) {c′}
cod-u⊔v→cod-u×cod-v {u}{v}{w}{c} cod-u⊔v
    with cod u | cod v
... | just u′  | just v′
    with consistent? u′ v′
... | yes u′~v′
    with cod-u⊔v
... | refl = ⟨ u′ , ⟨ v′ , ⟨ u′~v′ , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ ⟩
cod-u⊔v→cod-u×cod-v {u}{v}{w}{c} () | just u′  | just v′ | no u′~̸v′
cod-u⊔v→cod-u×cod-v {u}{v}{w}{c} () | nothing  | _
cod-u⊔v→cod-u×cod-v {u}{v}{w}{c} () | just u′  | nothing


u⊆w→v⊆w→u~v : ∀{u v w} → u ⊆ w → v ⊆ w → u ~ v
u⊆w→v⊆w→u~v {u}{v}{w} u⊆w v⊆w = atoms→consistent{u}{v} G
   where
   G : {u′ v′ : Value} → u′ ∈ u → v′ ∈ v → u′ ~ v′
   G {u′}{v′} u′∈u v′∈v =
     let u′∈w = u⊆w u′∈u in
     let v′∈w = v⊆w v′∈v in
     let w~w = ~-refl {w} in
     consistent→atoms{w}{w} w~w u′∈w v′∈w



factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = Σ[ du ∈ Value ] Σ[ cu ∈ Value ]
                  Funs u′ × u′ ⊆ u
                  × dom u′ ≡ just du × du ⊑ v
                  × cod u′ ≡ just cu × w ⊑ cu

sub-inv-trans : ∀{u′ u₂ u du cu : Value}
    → Funs u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
    → dom u′ ≡ just du  → cod u′ ≡ just cu
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ du cu
sub-inv-trans {⊥} {u₂} {u} fu′ u′⊆u IH =
   ⊥-elim (contradiction (fu′ refl) ¬Fun⊥)
sub-inv-trans {const {B} k} fu′ u′⊆u IH = ⊥-elim (not-Fun-k (fu′ refl))
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fg u′⊆u IH refl refl = IH (↦⊆→∈ u′⊆u)
sub-inv-trans {(u₁′ ⊔ u₂′){u₁′~u₂′}} {u₂} {u}{du}{cu} fg u′⊆u IH du≡ cu≡
    with ⊔⊆-inv{c = u₁′~u₂′} u′⊆u | dom-u⊔v→dom-u×dom-v {u₁′}{u₂′}{du}{u₁′~u₂′} du≡
                            | cod-u⊔v→cod-u×cod-v {u₁′}{u₂′}{cu}{u₁′~u₂′} cu≡
... | ⟨ u₁′⊆u , u₂′⊆u ⟩
    | ⟨ du₁ , ⟨ du₂ , ⟨ du₁~du₂ , ⟨ du₁≡ , ⟨ du₂≡ , du≡′ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ cu₁ , ⟨ cu₂ , ⟨ cu₁~cu₂ , ⟨ cu₁≡ , ⟨ cu₂≡ , cu≡′ ⟩ ⟩ ⟩ ⟩ ⟩
    rewrite du≡′ | cu≡′ 
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v′} z → fg (inj₁ z)) u₁′⊆u IH du₁≡ cu₁≡
       | sub-inv-trans {u₂′} {u₂} {u} (λ {v′} z → fg (inj₂ z)) u₂′⊆u IH du₂≡ cu₂≡
... | ⟨ u₃₁ , ⟨ du31 , ⟨ cu31 , ⟨ fu21' , ⟨ u₃₁⊆u₂ , ⟨ du31≡ , ⟨ du₃₁⊑du₁′ ,
        ⟨ cu21≡ , cu₁′⊑cu₃₁ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₃₂ , ⟨ du32 , ⟨ cu32 , ⟨ fu22' , ⟨ u₃₂⊆u₂ , ⟨ du32≡ , ⟨ du₃₂⊑du₂′ ,
        ⟨ cu22≡ , cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃₁ ⊔ u₃₂) {u⊆w→v⊆w→u~v u₃₁⊆u₂ u₃₂⊆u₂} ,
      ⟨ (du31 ⊔ du32) {{!!}} ,  {- need consistent-⊑ ! -}
      ⟨ (cu31 ⊔ cu32) {{!!}} ,
      ⟨ fu₂′ ,
      ⟨ u₂′⊆u₂ ,
      ⟨ {!!} ,
      ⟨ {!!} {- ⊔⊑⊔ du₃₁⊑du₁′ du₃₂⊑du₂′ -} ,
      ⟨ {!!} ,
        {!!} {- ⊔⊑⊔ cu₁′⊑cu₃₁ cu₁′⊑cu₃₂ -} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where fu₂′ : {v′ : Value} → v′ ∈ u₃₁ ⊎ v′ ∈ u₃₂ → Fun v′
          fu₂′ {v′} (inj₁ x) = {!!} {- fu21' x -}
          fu₂′ {v′} (inj₂ y) = {!!} {- fu22' y -}
          u₂′⊆u₂ : {C : Value} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂′⊆u₂ {C} (inj₁ x) = {!!} {- u₃₁⊆u₂ x -}
          u₂′⊆u₂ {C} (inj₂ y) = {!!} {- u₃₂⊆u₂ y -}


{-
sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
sub-inv {⊥} {u₂} ⊑-⊥ {v} {w} ()
sub-inv {const {B} k} ⊑-const {v} {w} ()
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₁ x) = sub-inv lt1 x
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₂ y) = sub-inv lt2 y
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {v} {w} m
    with sub-inv lt m  
... | ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ u₃₁⊆u₂₁ , ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ (λ {w} z → inj₁ (u₃₁⊆u₂₁ z)) ,
                                   ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {v} {w} m
    with sub-inv lt m  
... | ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ u₃₂⊆u₂₂ , ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ (λ {C} z → inj₂ (u₃₂⊆u₂₂ z)) ,
                                   ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂} (⊑-trans{v = u} u₁⊑u u⊑u₂) {v} {w} v↦w∈u₁
    with sub-inv u₁⊑u v↦w∈u₁
... | ⟨ u′ , ⟨ fu′ , ⟨ u′⊆u , ⟨ domu′⊑v , w⊑codu′ ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans {u′} fu′ u′⊆u (sub-inv u⊑u₂) 
... | ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ domu₃⊑domu′ , codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ ⊑-trans domu₃⊑domu′ domu′⊑v ,
                                    ⊑-trans w⊑codu′ codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁₁ ↦ u₁₂} {u₂₁ ↦ u₂₂} (⊑-fun lt1 lt2) refl =
    ⟨ u₂₁ ↦ u₂₂ , ⟨ (λ {w} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {u₂₁ ↦ (u₂₂ ⊔ u₂₃)} {u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃} ⊑-dist
    {.u₂₁} {.(u₂₂ ⊔ u₂₃)} refl =
    ⟨ u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃ , ⟨ f , ⟨ g ,
    ⟨ ⊑-conj-L ⊑-refl ⊑-refl , ⊑-refl ⟩ ⟩ ⟩ ⟩
  where f : Funs (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃) ⊆ (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y

sub-inv-fun : ∀{v w u₁ : Value}
    → (v ↦ w) ⊑ u₁
      -----------------------------------------------------
    → Σ[ u₂ ∈ Value ] Funs u₂ × u₂ ⊆ u₁
        × (∀{v′ w′} → (v′ ↦ w′) ∈ u₂ → v′ ⊑ v) × w ⊑ cod u₂
sub-inv-fun{v}{w}{u₁} abc
    with sub-inv abc {v}{w} refl
... | ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ u₂ → D ⊑ v
         G{D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆dom m)) db


↦⊑↦-inv : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′
          -----------------
        → v′ ⊑ v × w ⊑ w′
↦⊑↦-inv{v}{w}{v′}{w′} lt
    with sub-inv-fun lt  
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
    with Γ⊆v34 u↦u′∈Γ
... | refl =    
  let codΓ⊆w′ = ⊆↦→cod⊆ Γ⊆v34 in
  ⟨ lt1 u↦u′∈Γ , ⊑-trans lt2 (⊆→⊑ codΓ⊆w′) ⟩


AboveFun : Value → Set
AboveFun u = Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ⊑ u

AboveFun-⊑ : ∀{u u' : Value}
      → AboveFun u → u ⊑ u'
        -------------------
      → AboveFun u'
AboveFun-⊑ ⟨ v , ⟨ w , lt' ⟩ ⟩ lt = ⟨ v , ⟨ w , ⊑-trans lt' lt ⟩ ⟩

AboveFun⊥ : ¬ AboveFun ⊥
AboveFun⊥ ⟨ v , ⟨ w , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆⊥ m
... | ()

AboveFun-⊔ : ∀{u u'}
           → AboveFun (u ⊔ u')
           → AboveFun u ⊎ AboveFun u'
AboveFun-⊔{u}{u'} ⟨ v , ⟨ w , v↦w⊑u⊔u' ⟩ ⟩ 
    with sub-inv-fun v↦w⊑u⊔u'
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆u⊔u' , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆u⊔u' m
... | inj₁ x = inj₁ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩

not-AboveFun-⊔ : ∀{u u' : Value}
               → ¬ AboveFun u → ¬ AboveFun u'
               → ¬ AboveFun (u ⊔ u')
not-AboveFun-⊔ naf1 naf2 af12
    with AboveFun-⊔ af12
... | inj₁ af1 = contradiction af1 naf1
... | inj₂ af2 = contradiction af2 naf2

not-AboveFun-⊔-inv : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u')
              → ¬ AboveFun u × ¬ AboveFun u'
not-AboveFun-⊔-inv af = ⟨ f af , g af ⟩
  where
    f : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u') → ¬ AboveFun u
    f{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R1 lt ⟩ ⟩ af12
    g : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u') → ¬ AboveFun u'
    g{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R2 lt ⟩ ⟩ af12

AboveFun? : (v : Value) → Dec (AboveFun v)
AboveFun? ⊥ = no AboveFun⊥
AboveFun? (const {B} k) = no G
  where
  G : ¬ AboveFun (const k)
  G ⟨ v , ⟨ w , v↦w⊑k ⟩ ⟩ = ⊥-elim (⊑k→BelowConstk v↦w⊑k)
AboveFun? (v ↦ w) = yes ⟨ v , ⟨ w , ⊑-refl ⟩ ⟩
AboveFun? (u ⊔ u')
    with AboveFun? u | AboveFun? u'
... | yes ⟨ v , ⟨ w , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ w , (⊑-conj-R1 lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ w , lt ⟩ ⟩ = yes ⟨ v , ⟨ w , (⊑-conj-R2 lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)




-}
