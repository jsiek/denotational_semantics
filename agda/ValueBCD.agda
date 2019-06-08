open import Variables
open import Structures
import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)


module ValueBCD where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

domain : Domain
domain = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

open DomainAux domain

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}
    → ℱ D γ ⊥
ℱ-⊥ = tt

ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} = λ _ → tt
ℱ-≲ D≲D′ {v ↦ w} = D≲D′
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
    ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩

  
infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-conj-L : ∀ {u v w}
      → v ⊑ u
      → w ⊑ u
        -----------
      → (v ⊔ w) ⊑ u

  ⊑-conj-R1 : ∀ {u v w}
     → u ⊑ v
       -----------
     → u ⊑ (v ⊔ w)

  ⊑-conj-R2 : ∀ {u v w}
     → u ⊑ w
       -----------
     → u ⊑ (v ⊔ w)

  ⊑-trans : ∀ {u v w}
     → u ⊑ v
     → v ⊑ w
       -----
     → u ⊑ w

  ⊑-fun : ∀ {v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)

  ⊑-dist : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

ordering : ValueOrdering domain
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             ; ⊑-refl = ⊑-refl
             }

open OrderingAux domain ordering

wf : Value → Set
wf = λ v → ⊤

consistent : Consistent domain ordering
consistent = record { wf = wf ;
                      _~_ = λ u v → ⊤ ;
                      ~-refl = λ {v} wfv → tt ;
                      ~-⊑ = λ {u} {v} {u′} {v′} _ _ _ → tt ;
                      ~-↦ = λ {v} {w} {v′} {w′} _ → inj₁ ⟨ tt , tt ⟩ }

open WFDenotMod domain ordering consistent
open ModelMod domain ordering consistent
open ConsistentAux domain ordering consistent

ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D → WFEnv γ → wf v
       → ℱ D γ v → w ⊑ v → ℱ D γ w
ℱ-⊑ d wfγ wfv ℱDγv ⊑-⊥ = tt
ℱ-⊑ d wfγ wfv ℱDγv (⊑-conj-L w⊑v w⊑v₁) =
    ⟨ (ℱ-⊑ d (λ {x} → wfγ{x}) wfv ℱDγv w⊑v) ,
      (ℱ-⊑ d (λ {x} → wfγ{x}) wfv ℱDγv w⊑v₁) ⟩
ℱ-⊑ d wfγ wfv ℱDγv (⊑-conj-R1 w⊑v) =
    ℱ-⊑ d (λ {x} → wfγ{x}) wfv (proj₁ ℱDγv) w⊑v
ℱ-⊑ d wfγ wfv ℱDγv (⊑-conj-R2 w⊑v) =
    ℱ-⊑ d (λ {x} → wfγ{x}) wfv (proj₂ ℱDγv) w⊑v
ℱ-⊑ d wfγ wfv ℱDγv (⊑-trans w⊑v w⊑v₁) =
    ℱ-⊑ d (λ {x} → wfγ{x}) wfv (ℱ-⊑ d (λ {x} → wfγ{x}) wfv ℱDγv w⊑v₁) w⊑v
ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d wfγ wfv ℱDγv (⊑-fun v⊑v' w'⊑w) =
  WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
  where b : (γ `, v) `⊑ (γ `, v')
        b Z = v⊑v'
        b (S x) = ⊑-refl 
ℱ-⊑ {γ = γ} d wfγ wfv ℱDγv (⊑-dist{v = v}) =
    WFDenot.⊔-closed d (λ {x} → G {x}) (proj₁ ℱDγv) (proj₂ ℱDγv)
    where
    G : WFEnv (γ `, v)
    G {Z} = tt
    G {S x} = tt


model_curry : ModelCurry ℱ
model_curry = record { ℱ-≲ = ℱ-≲ ; ℱ-⊑ = ℱ-⊑ ;
                       ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
                       ℱ-⊥ = λ {Γ}{D}{γ} → ℱ-⊥ {Γ}{D}{γ} }
                       
{-

This is not used. -Jeremy

ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
      → ℱ D γ u
      → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ] D (γ `, v) w × v ↦ w ⊑ u)
ℱ-inv {u = ⊥} tt = inj₁ ⊑-refl
ℱ-inv {u = v ↦ w} ℱDγu = inj₂ ⟨ v , ⟨ w , ⟨ ℱDγu , ⊑-refl ⟩ ⟩ ⟩
ℱ-inv {u = u ⊔ v} ⟨ fst , snd ⟩
    with ℱ-inv{u = u} fst | ℱ-inv{u = v} snd
... | inj₁ u⊑⊥ | inj₁ v⊑⊥ = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
... | inj₁ u⊑⊥ | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R2 v'↦w'⊑v ⟩ ⟩ ⟩
... | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ | _ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R1 v'↦w'⊑v ⟩ ⟩ ⟩
-}

{------------------------------
  Function Inversion
 -------------------------------}

infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w

∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {.⊥} {⊥} refl = ⊑-⊥
∈→⊑ {v ↦ w} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-⊥
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

↦⊆→∈ : ∀{v w u : Value}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl 

data Fun : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun u

Funs : Value → Set
Funs v = ∀{u} → u ∈ v → Fun u

¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())

Funs∈ : ∀{u}
      → Funs u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {v ↦ w} f = ⟨ v , ⟨ w , refl ⟩ ⟩
Funs∈ {u ⊔ u′} f
    with Funs∈ λ z → f (inj₁ z)
... | ⟨ v , ⟨ w , m ⟩ ⟩ = ⟨ v , ⟨ w , (inj₁ m) ⟩ ⟩


dom : (u : Value) → Value
dom ⊥  = ⊥
dom (v ↦ w) = v
dom (u ⊔ u′) = dom u ⊔ dom u′

cod : (u : Value) → Value
cod ⊥  = ⊥
cod (v ↦ w) = w
cod (u ⊔ u′) = cod u ⊔ cod u′


↦∈→⊆dom : ∀{u v w : Value}
          → Funs u  →  (v ↦ w) ∈ u
            ----------------------
          → v ⊆ dom u
↦∈→⊆dom {⊥} fg () u∈v
↦∈→⊆dom {v ↦ w} fg refl u∈v = u∈v
↦∈→⊆dom {u ⊔ u′} fg (inj₁ v↦w∈u) u∈v =
   let ih = ↦∈→⊆dom (λ z → fg (inj₁ z)) v↦w∈u in
   inj₁ (ih u∈v)
↦∈→⊆dom {u ⊔ u′} fg (inj₂ v↦w∈u′) u∈v =
   let ih = ↦∈→⊆dom (λ z → fg (inj₂ z)) v↦w∈u′ in
   inj₂ (ih u∈v)


⊆↦→cod⊆ : ∀{u v w : Value}
        → u ⊆ v ↦ w
          ---------
        → cod u ⊆ w
⊆↦→cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→cod⊆ {C ↦ C′} s m with s {C ↦ C′} refl
... | refl = m
⊆↦→cod⊆ {u ⊔ u′} s (inj₁ x) = ⊆↦→cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→cod⊆ {u ⊔ u′} s (inj₂ y) = ⊆↦→cod⊆ (λ {C} z → s (inj₂ z)) y


factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = Funs u′ × u′ ⊆ u × dom u′ ⊑ v × w ⊑ cod u′

sub-inv-trans : ∀{u′ u₂ u : Value}
    → Funs u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (dom u′) (cod u′)
sub-inv-trans {⊥} {u₂} {u} fu′ u′⊆u IH =
   ⊥-elim (contradiction (fu′ refl) ¬Fun⊥)
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fg u′⊆u IH = IH (↦⊆→∈ u′⊆u)
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} fg u′⊆u IH
    with ⊔⊆-inv u′⊆u
... | ⟨ u₁′⊆u , u₂′⊆u ⟩
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v′} z → fg (inj₁ z)) u₁′⊆u IH
       | sub-inv-trans {u₂′} {u₂} {u} (λ {v′} z → fg (inj₂ z)) u₂′⊆u IH
... | ⟨ u₃₁ , ⟨ fu21' , ⟨ u₃₁⊆u₂ , ⟨ du₃₁⊑du₁′ , cu₁′⊑cu₃₁ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₃₂ , ⟨ fu22' , ⟨ u₃₂⊆u₂ , ⟨ du₃₂⊑du₂′ , cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃₁ ⊔ u₃₂) , ⟨ fu₂′ , ⟨ u₂′⊆u₂ ,
      ⟨ ⊔⊑⊔ du₃₁⊑du₁′ du₃₂⊑du₂′ ,
        ⊔⊑⊔ cu₁′⊑cu₃₁ cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩
    where fu₂′ : {v′ : Value} → v′ ∈ u₃₁ ⊎ v′ ∈ u₃₂ → Fun v′
          fu₂′ {v′} (inj₁ x) = fu21' x
          fu₂′ {v′} (inj₂ y) = fu22' y
          u₂′⊆u₂ : {C : Value} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂′⊆u₂ {C} (inj₁ x) = u₃₁⊆u₂ x
          u₂′⊆u₂ {C} (inj₂ y) = u₃₂⊆u₂ y


sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
sub-inv {⊥} {u₂} ⊑-⊥ {v} {w} ()
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
         G{D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆dom f m)) db


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
AboveFun? (v ↦ w) = yes ⟨ v , ⟨ w , ⊑-refl ⟩ ⟩
AboveFun? (u ⊔ u')
    with AboveFun? u | AboveFun? u'
... | yes ⟨ v , ⟨ w , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ w , (⊑-conj-R1 lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ w , lt ⟩ ⟩ = yes ⟨ v , ⟨ w , (⊑-conj-R2 lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)
