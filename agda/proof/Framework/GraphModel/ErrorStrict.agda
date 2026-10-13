{-

  Error-propagating operators as strict operators: an element of the
  operator is ω because its operands err left to right, or needs every
  operand to have a value (ErrsOp), with the instances for the operators
  of ErrorOps.agda; and sets of values without ω (Vals). Used to bind an
  operand by a let without changing what errs (rco).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (Dec; yes; no)

module proof.Framework.GraphModel.ErrorStrict where


{- a set of values without ω -}
Vals : 𝒫 Value → Set
Vals D = val∈ D × Clean D

Vals-≃ : ∀ {D E} → D ≃ E → Vals D → Vals E
Vals-≃ D≃ ⟨ v , cl ⟩ = ⟨ val∈-mono (proj₁ D≃) v , (λ d d∈ → cl d (proj₂ D≃ d d∈)) ⟩

{- a finite, nonempty set without ω, in D, is a value of D -}
ne-noerr-val : ∀ {D} V → mem V ⊆ D → V ≢ [] → NoErr V → val∈ D
ne-noerr-val [] _ ne _ = ⊥-elim (ne refl)
ne-noerr-val (v ∷ V) V⊆ _ n = ⟨ v , ⟨ V⊆ v (here refl) , (λ { refl → n (here refl) }) ⟩ ⟩

NoErr-Vals : ∀ V → V ≢ [] → NoErr V → Vals (mem V)
NoErr-Vals V ne n = ⟨ ne-noerr-val V (λ d d∈ → d∈) ne n , (λ { .ω ω∈ refl → n ω∈ }) ⟩

vals-head : ∀ {n D Ds} → vals (suc n) ⟨ D , Ds ⟩ → val∈ D
vals-head vs = vs zero

vals-tail : ∀ {n D Ds} → vals (suc n) ⟨ D , Ds ⟩ → vals n Ds
vals-tail vs i = vs (suc i)

vals-cons : ∀ {n D Ds} → val∈ D → vals n Ds → vals (suc n) ⟨ D , Ds ⟩
vals-cons v vs zero = v
vals-cons v vs (suc i) = vs i

{- an operator on n operands that is strict in them, left to right: an
   element is ω from an error in its operands, in order (errs), or needs
   all of them to have values (vals); and such an error is ω in it -}
record ErrsOp (n : ℕ) : Set₁ where
  field
    op : Results (𝒫 Value) (replicate n ■) → 𝒫 Value
    mono : ∀ {Ds Es} → results-rel-pres _⊆_ (replicate n ■) Ds Es → op Ds ⊆ op Es
    split : ∀ Ds w → w ∈ op Ds → (w ≡ ω × errs n Ds) ⊎ vals n Ds
    err : ∀ Ds → errs n Ds → ω ∈ op Ds
open ErrsOp public

cong-op : ∀ {n} (O : ErrsOp n) {Ds Es} → RRs (replicate n ■) Ds Es → op O Ds ≃ op O Es
cong-op O eq = ⟨ mono O (proj₁ (RRs⇒⊆ eq)) , mono O (proj₂ (RRs⇒⊆ eq)) ⟩

⊆-refl* : ∀ {n} (Ds : Results (𝒫 Value) (replicate n ■)) → results-rel-pres _⊆_ (replicate n ■) Ds Ds
⊆-refl* Ds = proj₁ (RRs⇒⊆ (RRs-refl Ds))

{- the operator with its first operand fixed to a set of values D -}
_▷_ : ∀ {n} → (Σ[ D ∈ 𝒫 Value ] Vals D) → ErrsOp (suc n) → ErrsOp n
_▷_ {n} ⟨ D , ⟨ vD , clD ⟩ ⟩ O = record
  { op = λ Ds → op O ⟨ D , Ds ⟩
  ; mono = λ s → mono O ⟨ up (λ d d∈ → d∈) , s ⟩
  ; split = λ Ds w w∈ → F Ds w (split O _ w w∈)
  ; err = λ Ds e → err O _ (inj₂ ⟨ vD , e ⟩)
  }
  where
  F : ∀ Ds w → (w ≡ ω × errs (suc n) ⟨ D , Ds ⟩) ⊎ vals (suc n) ⟨ D , Ds ⟩ → (w ≡ ω × errs n Ds) ⊎ vals n Ds
  F Ds w (inj₁ ⟨ eq , inj₁ ω∈ ⟩) = ⊥-elim (clD ω ω∈ refl)
  F Ds w (inj₁ ⟨ eq , inj₂ ⟨ _ , e ⟩ ⟩) = inj₁ ⟨ eq , e ⟩
  F Ds w (inj₂ vs) = inj₂ (vals-tail vs)

{- The operators -------------------------------------------------------------------}

call-op : ErrsOp 3
call-op = record { op = callᵉ ; mono = λ {Ds} {Es} s → lower (callᵉ-mono Ds Es s) ; split = S ; err = λ Ds e → inj₂ ⟨ refl , inj₁ e ⟩ }
  where
  S : ∀ Ds w → w ∈ callᵉ Ds → (w ≡ ω × errs 3 Ds) ⊎ vals 3 Ds
  S ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ w (inj₁ ⟨ V , ⟨ U , ⟨ e∈ , ⟨ V⊆ , ⟨ U⊆ , ⟨ neV , ⟨ neU , ⟨ nV , nU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) =
    inj₂ (vals-cons ⟨ _ , ⟨ e∈ , (λ ()) ⟩ ⟩ (vals-cons (ne-noerr-val V V⊆ neV nV) (vals-cons (ne-noerr-val U U⊆ neU nU) (λ ()))))
  S Ds w (inj₂ ⟨ refl , inj₁ e ⟩) = inj₁ ⟨ refl , e ⟩
  S ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ w (inj₂ ⟨ refl , inj₂ ⟨ ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ , ⟨ vm , vn ⟩ ⟩ ⟩) =
    inj₂ (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (vals-cons vm (vals-cons vn (λ ()))))

pair-op′ : ErrsOp 2
pair-op′ = record { op = pairᵉ ; mono = λ {Ds} {Es} s → lower (pairᵉ-mono Ds Es s) ; split = S ; err = R }
  where
  S : ∀ Ds w → w ∈ pairᵉ Ds → (w ≡ ω × errs 2 Ds) ⊎ vals 2 Ds
  S ⟨ D , ⟨ E , _ ⟩ ⟩ w w∈ with pairᵉ-inv w w∈
  ... | inj₁ ⟨ u , ⟨ v , ⟨ refl , ⟨ u∈ , ⟨ v∈ , ⟨ u≢ , v≢ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₂ (vals-cons ⟨ u , ⟨ u∈ , u≢ ⟩ ⟩ (vals-cons ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ (λ ())))
  ... | inj₂ ⟨ refl , e ⟩ = inj₁ ⟨ refl , e ⟩
  R : ∀ Ds → errs 2 Ds → ω ∈ pairᵉ Ds
  R ⟨ D , ⟨ E , _ ⟩ ⟩ e = e

car-op : ErrsOp 1
car-op = record { op = carᵉ ; mono = λ {Ds} {Es} s → lower (carᵉ-mono Ds Es s) ; split = S ; err = E }
  where
  S : ∀ Ds w → w ∈ carᵉ Ds → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ u (inj₁ ⟨ v , p∈ ⟩) = inj₂ (vals-cons ⟨ _ , ⟨ p∈ , (λ ()) ⟩ ⟩ (λ ()))
  S ⟨ D , _ ⟩ u (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  S ⟨ D , _ ⟩ u (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ ⟩) = inj₂ (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (λ ()))
  E : ∀ Ds → errs 1 Ds → ω ∈ carᵉ Ds
  E ⟨ D , _ ⟩ (inj₁ ω∈) = inj₂ ⟨ refl , inj₁ ω∈ ⟩
  E ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

cdr-op : ErrsOp 1
cdr-op = record { op = cdrᵉ ; mono = λ {Ds} {Es} s → lower (cdrᵉ-mono Ds Es s) ; split = S ; err = E }
  where
  S : ∀ Ds w → w ∈ cdrᵉ Ds → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ v (inj₁ ⟨ u , p∈ ⟩) = inj₂ (vals-cons ⟨ _ , ⟨ p∈ , (λ ()) ⟩ ⟩ (λ ()))
  S ⟨ D , _ ⟩ v (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  S ⟨ D , _ ⟩ v (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ ⟩) = inj₂ (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (λ ()))
  E : ∀ Ds → errs 1 Ds → ω ∈ cdrᵉ Ds
  E ⟨ D , _ ⟩ (inj₁ ω∈) = inj₂ ⟨ refl , inj₁ ω∈ ⟩
  E ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

tuple-op : ∀ n → ErrsOp n
tuple-op n = record { op = 𝒯ᵉ n ; mono = λ {Ds} {Es} s → lower (𝒯ᵉ-mono n Ds Es s) ; split = S ; err = R }
  where
  S : ∀ Ds w → w ∈ 𝒯ᵉ n Ds → (w ≡ ω × errs n Ds) ⊎ vals n Ds
  S Ds w w∈ with 𝒯ᵉ-inv n w w∈
  ... | inj₁ ⟨ refl , e ⟩ = inj₁ ⟨ refl , e ⟩
  ... | inj₂ (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , vs ⟩ ⟩ ⟩ ⟩) = inj₂ vs
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = inj₂ (λ ())
  R : ∀ Ds → errs n Ds → ω ∈ 𝒯ᵉ n Ds
  R Ds e = e

get-op : ∀ {n} (i : Fin n) → ErrsOp 1
get-op i = record { op = projᵉ i ; mono = λ {Ds} {Es} s → lower (projᵉ-mono i Ds Es s) ; split = S ; err = E }
  where
  S : ∀ Ds w → w ∈ projᵉ i Ds → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ d (inj₁ t∈) = inj₂ (vals-cons ⟨ _ , ⟨ t∈ , (λ ()) ⟩ ⟩ (λ ()))
  S ⟨ D , _ ⟩ d (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  S ⟨ D , _ ⟩ d (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , _ ⟩ ⟩ ⟩ ⟩) = inj₂ (vals-cons ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ (λ ()))
  E : ∀ Ds → errs 1 Ds → ω ∈ projᵉ i Ds
  E ⟨ D , _ ⟩ (inj₁ ω∈) = inj₂ ⟨ refl , inj₁ ω∈ ⟩
  E ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

inl-op′ : ErrsOp 1
inl-op′ = record { op = inlᵉ ; mono = λ {Ds} {Es} s → lower (inlᵉ-mono Ds Es s) ; split = S ; err = E }
  where
  S : ∀ Ds w → w ∈ inlᵉ Ds → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ w w∈ with inlᵉ-inv w w∈
  ... | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = inj₂ (vals-cons ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ (λ ()))
  ... | inj₂ ⟨ refl , ω∈ ⟩ = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  E : ∀ Ds → errs 1 Ds → ω ∈ inlᵉ Ds
  E ⟨ D , _ ⟩ (inj₁ ω∈) = ω∈
  E ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

inr-op′ : ErrsOp 1
inr-op′ = record { op = inrᵉ ; mono = λ {Ds} {Es} s → lower (inrᵉ-mono Ds Es s) ; split = S ; err = E }
  where
  S : ∀ Ds w → w ∈ inrᵉ Ds → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ w w∈ with inrᵉ-inv w w∈
  ... | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = inj₂ (vals-cons ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ (λ ()))
  ... | inj₂ ⟨ refl , ω∈ ⟩ = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  E : ∀ Ds → errs 1 Ds → ω ∈ inrᵉ Ds
  E ⟨ D , _ ⟩ (inj₁ ω∈) = ω∈
  E ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

{- case on its first operand, with the branches E and F -}
case-mono : ∀ {D D' E F} → D ⊆ D' → 𝒞ᵉ ⟨ D , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ ⊆ 𝒞ᵉ ⟨ D' , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩
case-mono D⊆ w (inj₁ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩) = inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊆ _ (all d d∈)) , r ⟩ ⟩ ⟩
case-mono D⊆ w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩)) = inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊆ _ (all d d∈)) , r ⟩ ⟩ ⟩)
case-mono D⊆ w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₂ (inj₂ ⟨ refl , inj₁ (D⊆ ω ω∈) ⟩)
case-mono D⊆ w (inj₂ (inj₂ ⟨ refl , inj₂ wr ⟩)) = inj₂ (inj₂ ⟨ refl , inj₂ (wrong-mono D⊆ wr) ⟩)

case-op′ : (E F : 𝒫 Value → 𝒫 Value) → ErrsOp 1
case-op′ E F = record { op = λ Ds → 𝒞ᵉ ⟨ proj₁ Ds , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩
  ; mono = λ s → case-mono {E = E} {F} (lower (proj₁ s)) ; split = S ; err = R }
  where
  S : ∀ Ds w → w ∈ 𝒞ᵉ ⟨ proj₁ Ds , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ → (w ≡ ω × errs 1 Ds) ⊎ vals 1 Ds
  S ⟨ D , _ ⟩ w (inj₁ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩) = inj₂ (vals-cons ⟨ _ , ⟨ all v (here refl) , (λ ()) ⟩ ⟩ (λ ()))
  S ⟨ D , _ ⟩ w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩)) = inj₂ (vals-cons ⟨ _ , ⟨ all v (here refl) , (λ ()) ⟩ ⟩ (λ ()))
  S ⟨ D , _ ⟩ w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₁ ⟨ refl , inj₁ ω∈ ⟩
  S ⟨ D , _ ⟩ w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ ⟩)) = inj₂ (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (λ ()))
  R : ∀ Ds → errs 1 Ds → ω ∈ 𝒞ᵉ ⟨ proj₁ Ds , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩
  R ⟨ D , _ ⟩ (inj₁ ω∈) = inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
  R ⟨ D , _ ⟩ (inj₂ ⟨ _ , () ⟩)

