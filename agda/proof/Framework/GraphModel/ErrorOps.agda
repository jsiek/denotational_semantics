{-

  The error-propagating operators (Framework/GraphModel/ErrorOps.agda):
  their monotonicity, consistency, congruences and β laws. (Their
  continuity is in ErrorContinuity.agda.)

  Consistency rests on ω being consistent only with itself: a consistent
  set that holds ω holds nothing else, so an operand cannot both yield ω
  (an error) and a value; and the binders bind no ω, so an application
  cannot both pass on the error of its argument and run its body.

-}

module proof.Framework.GraphModel.ErrorOps where

open import Framework.GraphModel.ErrorOps public

open import Framework.Primitives
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (lift; lower)
open import Relation.Nullary using (¬_; yes; no)

{- ω and consistency ----------------------------------------------------------}

~ω : ∀ v → v ~ ω → v ≡ ω
~ω ω _ = refl
~ω (const k) ()
~ω (V ↦ w) ()
~ω ν ()
~ω ⦅ u , v ⦆ ()
~ω (tup[ i ] d) ()
~ω (left d) ()
~ω (right d) ()
~ω ⟨⟩ ()

ω~ : ∀ v → ω ~ v → v ≡ ω
ω~ ω _ = refl
ω~ (const k) ()
ω~ (V ↦ w) ()
ω~ ν ()
ω~ ⦅ u , v ⦆ ()
ω~ (tup[ i ] d) ()
ω~ (left d) ()
ω~ (right d) ()
ω~ ⟨⟩ ()

{- a set consistent with one that has a value has no ω, and the other way -}
val-ω : ∀ {D E} → Every _~_ D E → val∈ D → ω ∈ E → False
val-ω D~ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ ω∈ = d≢ (~ω d (D~ d ω d∈ ω∈))

ω-val : ∀ {D E} → Every _~_ D E → ω ∈ D → val∈ E → False
ω-val D~ ω∈ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = d≢ (ω~ d (D~ ω d ω∈ d∈))

{- a nonempty set without ω, in a set consistent with one that holds ω -}
noerr-ω : ∀ {E E'} → Every _~_ E E' → ∀ V → mem V ⊆ E → V ≢ [] → NoErr V → ω ∈ E' → False
noerr-ω E~ [] V⊆ ne noe ω∈ = ne refl
noerr-ω E~ (v ∷ V) V⊆ ne noe ω∈ =
  noe (subst (λ x → x ∈ mem (v ∷ V)) (~ω v (E~ v ω (V⊆ v (here refl)) ω∈)) (here refl))

ω-noerr : ∀ {E E'} → Every _~_ E E' → ∀ V → mem V ⊆ E' → V ≢ [] → NoErr V → ω ∈ E → False
ω-noerr E~ [] V⊆ ne noe ω∈ = ne refl
ω-noerr E~ (v ∷ V) V⊆ ne noe ω∈ =
  noe (subst (λ x → x ∈ mem (v ∷ V)) (ω~ v (E~ ω v ω∈ (V⊆ v (here refl)))) (here refl))

{- the kinds of the values consistent with a value of a kind -}
fun~ : ∀ {V u} d → (V ↦ u) ~ d → IsFun d
fun~ (V ↦ w) _ = tt
fun~ ν _ = tt
fun~ ω ()
fun~ (const k) ()
fun~ ⦅ u , v ⦆ ()
fun~ (tup[ i ] d) ()
fun~ (left d) ()
fun~ (right d) ()
fun~ ⟨⟩ ()

~fun : ∀ {V u} d → d ~ (V ↦ u) → IsFun d
~fun (V ↦ w) _ = tt
~fun ν _ = tt
~fun ω ()
~fun (const k) ()
~fun ⦅ u , v ⦆ ()
~fun (tup[ i ] d) ()
~fun (left d) ()
~fun (right d) ()
~fun ⟨⟩ ()

inl~ : ∀ {v} d → left v ~ d → IsInj d
inl~ (left d) _ = tt
inl~ (right d) ()
inl~ ω ()
inl~ (const k) ()
inl~ (V ↦ w) ()
inl~ ν ()
inl~ ⦅ u , v ⦆ ()
inl~ (tup[ i ] d) ()
inl~ ⟨⟩ ()

~inl : ∀ {v} d → d ~ left v → IsInj d
~inl (left d) _ = tt
~inl (right d) ()
~inl ω ()
~inl (const k) ()
~inl (V ↦ w) ()
~inl ν ()
~inl ⦅ u , v ⦆ ()
~inl (tup[ i ] d) ()
~inl ⟨⟩ ()

inr~ : ∀ {v} d → right v ~ d → IsInj d
inr~ (right d) _ = tt
inr~ (left d) ()
inr~ ω ()
inr~ (const k) ()
inr~ (V ↦ w) ()
inr~ ν ()
inr~ ⦅ u , v ⦆ ()
inr~ (tup[ i ] d) ()
inr~ ⟨⟩ ()

~inr : ∀ {v} d → d ~ right v → IsInj d
~inr (right d) _ = tt
~inr (left d) ()
~inr ω ()
~inr (const k) ()
~inr (V ↦ w) ()
~inr ν ()
~inr ⦅ u , v ⦆ ()
~inr (tup[ i ] d) ()
~inr ⟨⟩ ()

tup~ : ∀ {n} {i : Fin n} {d} e → (tup[ i ] d) ~ e → IsTup n e
tup~ (tup[ j ] e) ⟨ refl , _ ⟩ = refl
tup~ ω ()
tup~ (const k) ()
tup~ (V ↦ w) ()
tup~ ν ()
tup~ ⦅ u , v ⦆ ()
tup~ (left d) ()
tup~ (right d) ()
tup~ ⟨⟩ ()

~tup : ∀ {n} {i : Fin n} {d} e → e ~ (tup[ i ] d) → IsTup n e
~tup (tup[ j ] e) ⟨ refl , _ ⟩ = refl
~tup ω ()
~tup (const k) ()
~tup (V ↦ w) ()
~tup ν ()
~tup ⦅ u , v ⦆ ()
~tup (left d) ()
~tup (right d) ()
~tup ⟨⟩ ()

{- an error in operands consistent with ones that all have values -}
errs-vals : ∀ n (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres (Every _~_) (replicate n ■) Ds Es → errs n Ds → vals n Es → False
errs-vals (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D~ , _ ⟩ (inj₁ ω∈) vs = ω-val D~ ω∈ (vs zero)
errs-vals (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds~ ⟩ (inj₂ ⟨ _ , e ⟩) vs =
  errs-vals n Ds Es Ds~ e (λ i → vs (suc i))

vals-errs : ∀ n (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres (Every _~_) (replicate n ■) Ds Es → vals n Ds → errs n Es → False
vals-errs (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D~ , _ ⟩ vs (inj₁ ω∈) = val-ω D~ (vs zero) ω∈
vals-errs (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds~ ⟩ vs (inj₂ ⟨ _ , e ⟩) =
  vals-errs n Ds Es Ds~ (λ i → vs (suc i)) e

{- Sets without errors ----------------------------------------------------------}

Clean : 𝒫 Value → Set
Clean D = ∀ d → d ∈ D → d ≢ ω

Clean-NoErr : ∀ {D} V → Clean D → mem V ⊆ D → NoErr V
Clean-NoErr V c V⊆ ω∈ = c ω (V⊆ ω ω∈) refl

{- n operands without errors have no error -}
errs-clean : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → (∀ i → Clean (nthD Ds i)) → errs n Ds → False
errs-clean (suc n) ⟨ D , Ds ⟩ cs (inj₁ ω∈) = cs zero ω ω∈ refl
errs-clean (suc n) ⟨ D , Ds ⟩ cs (inj₂ ⟨ _ , e ⟩) = errs-clean n Ds (λ i → cs (suc i)) e

Λᵉ-clean : ∀ {F} → Clean (Λᵉ ⟨ F , ptt ⟩)
Λᵉ-clean ω () refl

Λᵉ-fun : ∀ {F} d → d ∈ Λᵉ ⟨ F , ptt ⟩ → IsFun d
Λᵉ-fun (V ↦ w) _ = tt
Λᵉ-fun ν _ = tt

ℬ-clean : ∀ {B k} → Clean (ℬ B k ptt)
ℬ-clean ω () refl

{- Inversions -------------------------------------------------------------------}

𝒯ᵉ-inv : ∀ n {Ds} d → d ∈ 𝒯ᵉ n Ds
  → (d ≡ ω × errs n Ds)
  ⊎ (Σ[ i ∈ Fin n ] Σ[ d' ∈ Value ] d ≡ tup[ i ] d' × d' ∈ nthD Ds i × vals n Ds)
  ⊎ (n ≡ 0 × d ≡ ⟨⟩)
𝒯ᵉ-inv n ω e = inj₁ ⟨ refl , e ⟩
𝒯ᵉ-inv zero ⟨⟩ _ = inj₂ (inj₂ ⟨ refl , refl ⟩)
𝒯ᵉ-inv (suc n) (tup[ i ] d) ⟨ refl , ⟨ d∈ , vs ⟩ ⟩ = inj₂ (inj₁ ⟨ i , ⟨ d , ⟨ refl , ⟨ d∈ , vs ⟩ ⟩ ⟩ ⟩)
𝒯ᵉ-inv zero (const k) ()
𝒯ᵉ-inv zero (V ↦ w) ()
𝒯ᵉ-inv zero ν ()
𝒯ᵉ-inv zero ⦅ u , v ⦆ ()
𝒯ᵉ-inv zero (tup[ i ] d) ()
𝒯ᵉ-inv zero (left d) ()
𝒯ᵉ-inv zero (right d) ()
𝒯ᵉ-inv (suc n) (const k) ()
𝒯ᵉ-inv (suc n) (V ↦ w) ()
𝒯ᵉ-inv (suc n) ν ()
𝒯ᵉ-inv (suc n) ⦅ u , v ⦆ ()
𝒯ᵉ-inv (suc n) (left d) ()
𝒯ᵉ-inv (suc n) (right d) ()
𝒯ᵉ-inv (suc n) ⟨⟩ ()

inlᵉ-inv : ∀ {D} d → d ∈ inlᵉ ⟨ D , ptt ⟩ → (Σ[ v ∈ Value ] d ≡ left v × v ∈ D × v ≢ ω) ⊎ (d ≡ ω × ω ∈ D)
inlᵉ-inv (left v) ⟨ v∈ , v≢ ⟩ = inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩
inlᵉ-inv ω ω∈ = inj₂ ⟨ refl , ω∈ ⟩
inlᵉ-inv (const k) ()
inlᵉ-inv (V ↦ w) ()
inlᵉ-inv ν ()
inlᵉ-inv ⦅ u , v ⦆ ()
inlᵉ-inv (tup[ i ] d) ()
inlᵉ-inv (right d) ()
inlᵉ-inv ⟨⟩ ()

inrᵉ-inv : ∀ {D} d → d ∈ inrᵉ ⟨ D , ptt ⟩ → (Σ[ v ∈ Value ] d ≡ right v × v ∈ D × v ≢ ω) ⊎ (d ≡ ω × ω ∈ D)
inrᵉ-inv (right v) ⟨ v∈ , v≢ ⟩ = inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩
inrᵉ-inv ω ω∈ = inj₂ ⟨ refl , ω∈ ⟩
inrᵉ-inv (const k) ()
inrᵉ-inv (V ↦ w) ()
inrᵉ-inv ν ()
inrᵉ-inv ⦅ u , v ⦆ ()
inrᵉ-inv (tup[ i ] d) ()
inrᵉ-inv (left d) ()
inrᵉ-inv ⟨⟩ ()

{- Monotonicity ---------------------------------------------------------------------}

val∈-mono : ∀ {D E} → D ⊆ E → val∈ D → val∈ E
val∈-mono D⊆ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩

wrong-mono : ∀ {P D E} → D ⊆ E → wrong P D → wrong P E
wrong-mono D⊆ ⟨ d , ⟨ d∈ , r ⟩ ⟩ = ⟨ d , ⟨ D⊆ d d∈ , r ⟩ ⟩

errs-mono : ∀ n (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres _⊆_ (replicate n ■) Ds Es → errs n Ds → errs n Es
errs-mono (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D⊆ , _ ⟩ (inj₁ ω∈) = inj₁ (D⊆ ω ω∈)
errs-mono (suc n) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D⊆ , Ds⊆ ⟩ (inj₂ ⟨ v , e ⟩) =
  inj₂ ⟨ val∈-mono D⊆ v , errs-mono n Ds Es Ds⊆ e ⟩

vals-mono : ∀ n (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres _⊆_ (replicate n ■) Ds Es → vals n Ds → vals n Es
vals-mono n Ds Es Ds⊆ vs i = val∈-mono (nthD-mono Ds Es Ds⊆ i) (vs i)

⋆ᵉ-mono : monotone (■ ∷ ■ ∷ []) ■ ⋆ᵉ
⋆ᵉ-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : ⋆ᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ ⋆ᵉ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G w (inj₁ ⟨ V , ⟨ f∈ , ⟨ V⊆ , r ⟩ ⟩ ⟩) = inj₁ ⟨ V , ⟨ D⊆ _ f∈ , ⟨ (λ d d∈ → E⊆ d (V⊆ d d∈)) , r ⟩ ⟩ ⟩
  G w (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = inj₂ ⟨ refl , inj₁ (D⊆ ω ω∈) ⟩
  G w (inj₂ ⟨ refl , inj₂ (inj₁ wr) ⟩) = inj₂ ⟨ refl , inj₂ (inj₁ (wrong-mono D⊆ wr)) ⟩
  G w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ f , ⟨ f∈ , isf ⟩ ⟩ , ω∈ ⟩) ⟩) =
    inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ f , ⟨ D⊆ f f∈ , isf ⟩ ⟩ , E⊆ ω ω∈ ⟩) ⟩

Λᵉ-mono : monotone (ν ■ ∷ []) ■ Λᵉ
Λᵉ-mono ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F⊆ , _ ⟩ = lift G
  where
  G : Λᵉ ⟨ F , ptt ⟩ ⊆ Λᵉ ⟨ F' , ptt ⟩
  G (V ↦ w) ⟨ w∈ , r ⟩ = ⟨ lower (F⊆ (mem V) (mem V) (λ d z → z)) w w∈ , r ⟩
  G ν _ = tt

𝒯ᵉ-mono : ∀ n → monotone (replicate n ■) ■ (𝒯ᵉ n)
𝒯ᵉ-mono n Ds Es Ds⊆ = lift (G n Ds Es Ds⊆)
  where
  G : ∀ n Ds Es → results-rel-pres _⊆_ (replicate n ■) Ds Es → 𝒯ᵉ n Ds ⊆ 𝒯ᵉ n Es
  G n Ds Es Ds⊆ d d∈ with 𝒯ᵉ-inv n d d∈
  ... | inj₁ ⟨ refl , e ⟩ = errs-mono n Ds Es Ds⊆ e
  ... | inj₂ (inj₂ ⟨ refl , refl ⟩) = tt
  G (suc n) Ds Es Ds⊆ d d∈ | inj₂ (inj₁ ⟨ i , ⟨ d' , ⟨ refl , ⟨ d'∈ , vs ⟩ ⟩ ⟩ ⟩) =
    ⟨ refl , ⟨ nthD-mono Ds Es Ds⊆ i d' d'∈ , vals-mono (suc n) Ds Es Ds⊆ vs ⟩ ⟩

projᵉ-mono : ∀ {n} (i : Fin n) → monotone (■ ∷ []) ■ (projᵉ i)
projᵉ-mono i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D⊆ , _ ⟩ = lift G
  where
  G : projᵉ i ⟨ D , ptt ⟩ ⊆ projᵉ i ⟨ D' , ptt ⟩
  G d (inj₁ t∈) = inj₁ (D⊆ _ t∈)
  G d (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = inj₂ ⟨ refl , inj₁ (D⊆ ω ω∈) ⟩
  G d (inj₂ ⟨ refl , inj₂ wr ⟩) = inj₂ ⟨ refl , inj₂ (wrong-mono D⊆ wr) ⟩

inlᵉ-mono : monotone (■ ∷ []) ■ inlᵉ
inlᵉ-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D⊆ , _ ⟩ = lift G
  where
  G : inlᵉ ⟨ D , ptt ⟩ ⊆ inlᵉ ⟨ D' , ptt ⟩
  G d d∈ with inlᵉ-inv d d∈
  ... | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = ⟨ D⊆ v v∈ , v≢ ⟩
  ... | inj₂ ⟨ refl , ω∈ ⟩ = D⊆ ω ω∈

inrᵉ-mono : monotone (■ ∷ []) ■ inrᵉ
inrᵉ-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D⊆ , _ ⟩ = lift G
  where
  G : inrᵉ ⟨ D , ptt ⟩ ⊆ inrᵉ ⟨ D' , ptt ⟩
  G d d∈ with inrᵉ-inv d d∈
  ... | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = ⟨ D⊆ v v∈ , v≢ ⟩
  ... | inj₂ ⟨ refl , ω∈ ⟩ = D⊆ ω ω∈

𝒞ᵉ-mono : monotone (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞ᵉ
𝒞ᵉ-mono ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩
       ⟨ lift D⊆ , ⟨ FL⊆ , ⟨ FR⊆ , _ ⟩ ⟩ ⟩ = lift G
  where
  G : 𝒞ᵉ ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩ ⊆ 𝒞ᵉ ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩
  G d (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ d∈ , r ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (left d) (V⊆ d z))
         , ⟨ lower (FL⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ , r ⟩ ⟩ ⟩ ⟩
  G d (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ d∈ , r ⟩ ⟩ ⟩ ⟩)) =
    inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (right d) (V⊆ d z))
         , ⟨ lower (FR⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ , r ⟩ ⟩ ⟩ ⟩)
  G d (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₂ (inj₂ ⟨ refl , inj₁ (D⊆ ω ω∈) ⟩)
  G d (inj₂ (inj₂ ⟨ refl , inj₂ wr ⟩)) = inj₂ (inj₂ ⟨ refl , inj₂ (wrong-mono D⊆ wr) ⟩)

letᵉ-mono : monotone (■ ∷ ν ■ ∷ []) ■ letᵉ
letᵉ-mono ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D⊆ , ⟨ F⊆ , _ ⟩ ⟩ =
  ⋆ᵉ-mono ⟨ Λᵉ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λᵉ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
          ⟨ Λᵉ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F⊆ , ptt ⟩ , ⟨ D⊆ , ptt ⟩ ⟩

guardᵉ-n-mono : ∀ n {Ds Es D E} → results-rel-pres _⊆_ (replicate n ■) Ds Es → D ⊆ E
  → guardᵉ-n n Ds D ⊆ guardᵉ-n n Es E
guardᵉ-n-mono n {Ds} {Es} Ds⊆ D⊆ w (inj₁ ⟨ refl , e ⟩) = inj₁ ⟨ refl , errs-mono n Ds Es Ds⊆ e ⟩
guardᵉ-n-mono n {Ds} {Es} Ds⊆ D⊆ w (inj₂ ⟨ vs , w∈ ⟩) = inj₂ ⟨ vals-mono n Ds Es Ds⊆ vs , D⊆ w w∈ ⟩

{- Consistency ----------------------------------------------------------------------}

⋆ᵉ-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ ⋆ᵉ
⋆ᵉ-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (⋆ᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩) (⋆ᵉ ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G u w (inj₁ ⟨ V , ⟨ u∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩) (inj₁ ⟨ V' , ⟨ w∈ , ⟨ V⊆' , _ ⟩ ⟩ ⟩) =
    D~ (V ↦ u) (V' ↦ w) u∈ w∈ (Every⇒≈ V V' (Every-⊆ E~ V⊆ V⊆'))
  G u w (inj₁ ⟨ V , ⟨ u∈ , ⟨ V⊆ , ⟨ ne , noe ⟩ ⟩ ⟩ ⟩) (inj₂ ⟨ refl , e ⟩) = ⊥-elim (H e)
    where
    H : _ → False
    H (inj₁ ω∈) with D~ _ _ u∈ ω∈
    ... | ()
    H (inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩)) = nf (fun~ d (D~ _ _ u∈ d∈))
    H (inj₂ (inj₂ ⟨ _ , ω∈ ⟩)) = noerr-ω E~ V V⊆ ne noe ω∈
  G u w (inj₂ ⟨ refl , e ⟩) (inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , ⟨ ne , noe ⟩ ⟩ ⟩ ⟩) = ⊥-elim (H e)
    where
    H : _ → False
    H (inj₁ ω∈) with D~ _ _ ω∈ w∈
    ... | ()
    H (inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩)) = nf (~fun d (D~ _ _ d∈ w∈))
    H (inj₂ (inj₂ ⟨ _ , ω∈ ⟩)) = ω-noerr E~ V V⊆ ne noe ω∈
  G u w (inj₂ ⟨ refl , _ ⟩) (inj₂ ⟨ refl , _ ⟩) = tt

Λᵉ-consis : consistent _~_ (ν ■ ∷ []) ■ Λᵉ
Λᵉ-consis ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F~ , _ ⟩ = lift G
  where
  G : Every _~_ (Λᵉ ⟨ F , ptt ⟩) (Λᵉ ⟨ F' , ptt ⟩)
  G ν (V ↦ w) _ _ = tt
  G ν ν _ _ = tt
  G (V ↦ w) ν _ _ = tt
  G (V ↦ w) (V' ↦ w') ⟨ w∈ , _ ⟩ ⟨ w∈' , _ ⟩ = λ V≈V' →
    lower (F~ (mem V) (mem V') (≈⇒Every V V' V≈V')) w w' w∈ w∈'

𝒯ᵉ-consis : ∀ n → consistent _~_ (replicate n ■) ■ (𝒯ᵉ n)
𝒯ᵉ-consis n Ds Es Ds~ = lift G
  where
  G : Every _~_ (𝒯ᵉ n Ds) (𝒯ᵉ n Es)
  G a b a∈ b∈ with 𝒯ᵉ-inv n a a∈ | 𝒯ᵉ-inv n b b∈
  ... | inj₁ ⟨ refl , _ ⟩ | inj₁ ⟨ refl , _ ⟩ = tt
  ... | inj₁ ⟨ refl , e ⟩ | inj₂ (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , vs ⟩ ⟩ ⟩ ⟩) = ⊥-elim (errs-vals n Ds Es Ds~ e vs)
  ... | inj₁ ⟨ refl , e ⟩ | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim e
  ... | inj₂ (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , vs ⟩ ⟩ ⟩ ⟩) | inj₁ ⟨ refl , e ⟩ = ⊥-elim (vals-errs n Ds Es Ds~ vs e)
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) | inj₁ ⟨ refl , e ⟩ = ⊥-elim e
  ... | inj₂ (inj₂ ⟨ refl , refl ⟩) | inj₂ (inj₂ ⟨ _ , refl ⟩) = tt
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) | inj₂ (inj₁ ⟨ () , _ ⟩)
  ... | inj₂ (inj₁ ⟨ () , _ ⟩) | inj₂ (inj₂ ⟨ refl , _ ⟩)
  ... | inj₂ (inj₁ ⟨ i , ⟨ d , ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ ⟩ ⟩) | inj₂ (inj₁ ⟨ j , ⟨ d' , ⟨ refl , ⟨ d'∈ , _ ⟩ ⟩ ⟩ ⟩)
      with i fin≟ j
  ...   | yes refl = ⟨ refl , inj₂ ⟨ refl , nthD-consis Ds Es Ds~ i d d' d∈ d'∈ ⟩ ⟩
  ...   | no neq = ⟨ refl , inj₁ neq ⟩

projᵉ-consis : ∀ {n} (i : Fin n) → consistent _~_ (■ ∷ []) ■ (projᵉ i)
projᵉ-consis {n} i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D~ , _ ⟩ = lift G
  where
  G : Every _~_ (projᵉ i ⟨ D , ptt ⟩) (projᵉ i ⟨ D' , ptt ⟩)
  G d d' (inj₁ d∈) (inj₁ d'∈) with D~ (tup[ i ] d) (tup[ i ] d') d∈ d'∈
  ... | ⟨ refl , inj₁ neq ⟩ = ⊥-elim (neq refl)
  ... | ⟨ refl , inj₂ ⟨ _ , d~ ⟩ ⟩ = d~
  G d d' (inj₁ d∈) (inj₂ ⟨ refl , inj₁ ω∈ ⟩) with D~ _ _ d∈ ω∈
  ... | ()
  G d d' (inj₁ d∈) (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , nt ⟩ ⟩ ⟩ ⟩) = ⊥-elim (nt (tup~ e (D~ _ _ d∈ e∈)))
  G d d' (inj₂ ⟨ refl , inj₁ ω∈ ⟩) (inj₁ d'∈) with D~ _ _ ω∈ d'∈
  ... | ()
  G d d' (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , nt ⟩ ⟩ ⟩ ⟩) (inj₁ d'∈) = ⊥-elim (nt (~tup e (D~ _ _ e∈ d'∈)))
  G d d' (inj₂ ⟨ refl , _ ⟩) (inj₂ ⟨ refl , _ ⟩) = tt

inlᵉ-consis : consistent _~_ (■ ∷ []) ■ inlᵉ
inlᵉ-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D~ , _ ⟩ = lift G
  where
  G : Every _~_ (inlᵉ ⟨ D , ptt ⟩) (inlᵉ ⟨ D' , ptt ⟩)
  G a b a∈ b∈ with inlᵉ-inv a a∈ | inlᵉ-inv b b∈
  ... | inj₁ ⟨ u , ⟨ refl , ⟨ u∈ , _ ⟩ ⟩ ⟩ | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , _ ⟩ ⟩ ⟩ = D~ u v u∈ v∈
  ... | inj₁ ⟨ u , ⟨ refl , ⟨ u∈ , u≢ ⟩ ⟩ ⟩ | inj₂ ⟨ refl , ω∈ ⟩ = ⊥-elim (u≢ (~ω u (D~ u ω u∈ ω∈)))
  ... | inj₂ ⟨ refl , ω∈ ⟩ | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = ⊥-elim (v≢ (ω~ v (D~ ω v ω∈ v∈)))
  ... | inj₂ ⟨ refl , _ ⟩ | inj₂ ⟨ refl , _ ⟩ = tt

inrᵉ-consis : consistent _~_ (■ ∷ []) ■ inrᵉ
inrᵉ-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D~ , _ ⟩ = lift G
  where
  G : Every _~_ (inrᵉ ⟨ D , ptt ⟩) (inrᵉ ⟨ D' , ptt ⟩)
  G a b a∈ b∈ with inrᵉ-inv a a∈ | inrᵉ-inv b b∈
  ... | inj₁ ⟨ u , ⟨ refl , ⟨ u∈ , _ ⟩ ⟩ ⟩ | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , _ ⟩ ⟩ ⟩ = D~ u v u∈ v∈
  ... | inj₁ ⟨ u , ⟨ refl , ⟨ u∈ , u≢ ⟩ ⟩ ⟩ | inj₂ ⟨ refl , ω∈ ⟩ = ⊥-elim (u≢ (~ω u (D~ u ω u∈ ω∈)))
  ... | inj₂ ⟨ refl , ω∈ ⟩ | inj₁ ⟨ v , ⟨ refl , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ = ⊥-elim (v≢ (ω~ v (D~ ω v ω∈ v∈)))
  ... | inj₂ ⟨ refl , _ ⟩ | inj₂ ⟨ refl , _ ⟩ = tt

𝒞ᵉ-consis : consistent _~_ (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞ᵉ
𝒞ᵉ-consis ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩
       ⟨ lift D~ , ⟨ FL~ , ⟨ FR~ , _ ⟩ ⟩ ⟩ = lift G
  where
  G : Every _~_ (𝒞ᵉ ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩) (𝒞ᵉ ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) =
    lower (FL~ (mem (v ∷ V)) (mem (v' ∷ V')) (λ d d' d∈ d'∈ → D~ (left d) (left d') (V⊆ d d∈) (V⊆' d' d'∈))) u w u∈ w∈
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩) (inj₂ (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , _ ⟩ ⟩ ⟩)) =
    ⊥-elim (D~ (left v) (right v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩)) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , _ ⟩ ⟩ ⟩) =
    ⊥-elim (D~ (right v) (left v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩)) (inj₂ (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)) =
    lower (FR~ (mem (v ∷ V)) (mem (v' ∷ V')) (λ d d' d∈ d'∈ → D~ (right d) (right d') (V⊆ d d∈) (V⊆' d' d'∈))) u w u∈ w∈
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩) (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = ⊥-elim (D~ _ _ (V⊆ v (here refl)) ω∈)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩) (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) =
    ⊥-elim (ni (inl~ e (D~ _ _ (V⊆ v (here refl)) e∈)))
  G u w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩)) (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = ⊥-elim (D~ _ _ (V⊆ v (here refl)) ω∈)
  G u w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩)) (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) =
    ⊥-elim (ni (inr~ e (D~ _ _ (V⊆ v (here refl)) e∈)))
  G u w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩) = ⊥-elim (D~ _ _ ω∈ (V⊆ v (here refl)))
  G u w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩) =
    ⊥-elim (ni (~inl e (D~ _ _ e∈ (V⊆ v (here refl)))))
  G u w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩)) = ⊥-elim (D~ _ _ ω∈ (V⊆ v (here refl)))
  G u w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩)) (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , _ ⟩ ⟩ ⟩)) =
    ⊥-elim (ni (~inr e (D~ _ _ e∈ (V⊆ v (here refl)))))
  G u w (inj₂ (inj₂ ⟨ refl , _ ⟩)) (inj₂ (inj₂ ⟨ refl , _ ⟩)) = tt

letᵉ-consis : consistent _~_ (■ ∷ ν ■ ∷ []) ■ letᵉ
letᵉ-consis ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆ᵉ-consis ⟨ Λᵉ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λᵉ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
            ⟨ Λᵉ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

guardᵉ-n-consis : ∀ n {Ds Es D E} → results-rel-pres (Every _~_) (replicate n ■) Ds Es
  → Every _~_ D E → Clean D → Clean E → Every _~_ (guardᵉ-n n Ds D) (guardᵉ-n n Es E)
guardᵉ-n-consis n Ds~ D~ cD cE u w (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
guardᵉ-n-consis n {Ds} {Es} Ds~ D~ cD cE u w (inj₁ ⟨ refl , e ⟩) (inj₂ ⟨ vs , _ ⟩) =
  ⊥-elim (errs-vals n Ds Es Ds~ e vs)
guardᵉ-n-consis n {Ds} {Es} Ds~ D~ cD cE u w (inj₂ ⟨ vs , _ ⟩) (inj₁ ⟨ refl , e ⟩) =
  ⊥-elim (vals-errs n Ds Es Ds~ vs e)
guardᵉ-n-consis n Ds~ D~ cD cE u w (inj₂ ⟨ _ , u∈ ⟩) (inj₂ ⟨ _ , w∈ ⟩) = D~ u w u∈ w∈

{- Congruences ----------------------------------------------------------------------}

⋆ᵉ-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → ⋆ᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ᵉ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
⋆ᵉ-≃ D≃ E≃ = mono-≃ ⋆ᵉ-mono ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

𝒯ᵉ-≃ : ∀ n {Ds Es} → (∀ i → nthD Ds i ≃ nthD Es i) → 𝒯ᵉ n Ds ≃ 𝒯ᵉ n Es
𝒯ᵉ-≃ n {Ds} {Es} eq = mono-≃ (𝒯ᵉ-mono n) (nthD⇒RRs Ds Es eq)

projᵉ-≃ : ∀ {n} (i : Fin n) {D E} → D ≃ E → projᵉ i ⟨ D , ptt ⟩ ≃ projᵉ i ⟨ E , ptt ⟩
projᵉ-≃ i D≃ = mono-≃ (projᵉ-mono i) ⟨ lift D≃ , ptt ⟩

inlᵉ-≃ : ∀ {D E} → D ≃ E → inlᵉ ⟨ D , ptt ⟩ ≃ inlᵉ ⟨ E , ptt ⟩
inlᵉ-≃ D≃ = mono-≃ inlᵉ-mono ⟨ lift D≃ , ptt ⟩

inrᵉ-≃ : ∀ {D E} → D ≃ E → inrᵉ ⟨ D , ptt ⟩ ≃ inrᵉ ⟨ E , ptt ⟩
inrᵉ-≃ D≃ = mono-≃ inrᵉ-mono ⟨ lift D≃ , ptt ⟩

{- Λᵉ F ≃ Λᵉ F' when F and F' agree on the finite, nonempty, consistent
   sets without ω -}
Λᵉ-≃ : ∀ {F F'} → (∀ V → V ≢ [] → V ≈ V → NoErr V → F (mem V) ≃ F' (mem V))
  → Λᵉ ⟨ F , ptt ⟩ ≃ Λᵉ ⟨ F' , ptt ⟩
Λᵉ-≃ {F} {F'} eq = ⟨ G (λ V ne c n → proj₁ (eq V ne c n)) , G (λ V ne c n → proj₂ (eq V ne c n)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value} → (∀ V → V ≢ [] → V ≈ V → NoErr V → A (mem V) ⊆ B (mem V))
    → Λᵉ ⟨ A , ptt ⟩ ⊆ Λᵉ ⟨ B , ptt ⟩
  G A⊆ ν _ = tt
  G A⊆ (V ↦ w) ⟨ w∈ , ⟨ ne , ⟨ c , n ⟩ ⟩ ⟩ = ⟨ A⊆ V ne c n w w∈ , ⟨ ne , ⟨ c , n ⟩ ⟩ ⟩

letᵉ-≃ : ∀ {D D' F F'} → D ≃ D' → (∀ V → V ≢ [] → V ≈ V → NoErr V → F (mem V) ≃ F' (mem V))
  → letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letᵉ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letᵉ-≃ {F = F} {F'} D≃ F≃ = ⋆ᵉ-≃ (Λᵉ-≃ {F} {F'} F≃) D≃

{- case analysis, whose branches are compared on nonempty consistent finite
   sets without ω -}
𝒞ᵉ-≃ : ∀ {D D' F F' G G'} → D ≃ D'
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → NoErr (v ∷ V) → F (mem (v ∷ V)) ≃ F' (mem (v ∷ V)))
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → NoErr (v ∷ V) → G (mem (v ∷ V)) ≃ G' (mem (v ∷ V)))
  → 𝒞ᵉ ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞ᵉ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞ᵉ-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  ⟨ H {B = F} {F'} {G} {G'} (proj₁ D≃) (λ v V c n → proj₁ (F≃ v V c n)) (λ v V c n → proj₁ (G≃ v V c n))
  , H {B = F'} {F} {G'} {G} (proj₂ D≃) (λ v V c n → proj₂ (F≃ v V c n)) (λ v V c n → proj₂ (G≃ v V c n)) ⟩
  where
  H : ∀ {A A' B B' C C'} → A ⊆ A'
    → (∀ v V → (v ∷ V) ≈ (v ∷ V) → NoErr (v ∷ V) → B (mem (v ∷ V)) ⊆ B' (mem (v ∷ V)))
    → (∀ v V → (v ∷ V) ≈ (v ∷ V) → NoErr (v ∷ V) → C (mem (v ∷ V)) ⊆ C' (mem (v ∷ V)))
    → 𝒞ᵉ ⟨ A , ⟨ B , ⟨ C , ptt ⟩ ⟩ ⟩ ⊆ 𝒞ᵉ ⟨ A' , ⟨ B' , ⟨ C' , ptt ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ⟨ c , n ⟩ ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (left d) (all d d∈)) , ⟨ B⊆ v V c n w w∈ , ⟨ c , n ⟩ ⟩ ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ⟨ c , n ⟩ ⟩ ⟩ ⟩ ⟩)) =
    inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (right d) (all d d∈)) , ⟨ C⊆ v V c n w w∈ , ⟨ c , n ⟩ ⟩ ⟩ ⟩ ⟩)
  H A⊆ B⊆ C⊆ w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₂ (inj₂ ⟨ refl , inj₁ (A⊆ ω ω∈) ⟩)
  H A⊆ B⊆ C⊆ w (inj₂ (inj₂ ⟨ refl , inj₂ wr ⟩)) = inj₂ (inj₂ ⟨ refl , inj₂ (wrong-mono A⊆ wr) ⟩)

{- β laws ------------------------------------------------------------------------------}

{- (λx. F x) D means F D, for D consistent and without ω -}
letᵉ-β : ∀ {F D} → Mono₁ F → Finitary F D → Con D → Clean D → letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ F D
letᵉ-β {F} {D} m fin cD clD = ⟨ G , H ⟩
  where
  G : letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ ⊆ F D
  G w (inj₁ ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩) = m V⊆ w w∈
  G w (inj₂ ⟨ refl , inj₁ () ⟩)
  G w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  G w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) = ⊥-elim (clD ω ω∈ refl)
  H : F D ⊆ letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩
  H w w∈ with fin w w∈
  ... | ⟨ V , ⟨ ne , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ =
    inj₁ ⟨ V , ⟨ ⟨ w∈′ , ⟨ ne , ⟨ Con⇒≈ V cD V⊆ , Clean-NoErr V clD V⊆ ⟩ ⟩ ⟩ , ⟨ V⊆ , ⟨ ne , Clean-NoErr V clD V⊆ ⟩ ⟩ ⟩ ⟩

{- a case on a left injection of D takes its left branch on D -}
𝒞ᵉ-inl-β : ∀ {D F G} → Mono₁ F → Finitary F D → Con D → Clean D
  → 𝒞ᵉ ⟨ inlᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ F D
𝒞ᵉ-inl-β {D} {F} {G} m fin cD clD = ⟨ A , B ⟩
  where
  A : 𝒞ᵉ ⟨ inlᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⊆ F D
  A w (inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = m (λ d d∈ → proj₁ (ls d d∈)) w w∈
  A w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ rs , _ ⟩ ⟩ ⟩)) = ⊥-elim (rs v (here refl))
  A w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = ⊥-elim (clD ω ω∈ refl)
  A w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) with inlᵉ-inv d d∈
  ... | inj₁ ⟨ _ , ⟨ refl , _ ⟩ ⟩ = ⊥-elim (ni tt)
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  B : F D ⊆ 𝒞ᵉ ⟨ inlᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
  B w w∈ with fin w w∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⟨ V⊆ d d∈ , clD d (V⊆ d d∈) ⟩)
         , ⟨ w∈′ , ⟨ Con⇒≈ (v ∷ V) cD V⊆ , Clean-NoErr (v ∷ V) clD V⊆ ⟩ ⟩ ⟩ ⟩ ⟩

𝒞ᵉ-inr-β : ∀ {D F G} → Mono₁ G → Finitary G D → Con D → Clean D
  → 𝒞ᵉ ⟨ inrᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ G D
𝒞ᵉ-inr-β {D} {F} {G} m fin cD clD = ⟨ A , B ⟩
  where
  A : 𝒞ᵉ ⟨ inrᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⊆ G D
  A w (inj₁ ⟨ v , ⟨ V , ⟨ ls , _ ⟩ ⟩ ⟩) = ⊥-elim (ls v (here refl))
  A w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)) = m (λ d d∈ → proj₁ (rs d d∈)) w w∈
  A w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = ⊥-elim (clD ω ω∈ refl)
  A w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) with inrᵉ-inv d d∈
  ... | inj₁ ⟨ _ , ⟨ refl , _ ⟩ ⟩ = ⊥-elim (ni tt)
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  B : G D ⊆ 𝒞ᵉ ⟨ inrᵉ ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
  B w w∈ with fin w w∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ =
    inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⟨ V⊆ d d∈ , clD d (V⊆ d d∈) ⟩)
         , ⟨ w∈′ , ⟨ Con⇒≈ (v ∷ V) cD V⊆ , Clean-NoErr (v ∷ V) clD V⊆ ⟩ ⟩ ⟩ ⟩ ⟩)

{- a projection from a tuple of sets that have values and no ω -}
projᵉ-𝒯ᵉ : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → vals n Ds → (∀ j → Clean (nthD Ds j))
  → (i : Fin n) → projᵉ i ⟨ 𝒯ᵉ n Ds , ptt ⟩ ≃ nthD Ds i
projᵉ-𝒯ᵉ (suc n) Ds vs cs i = ⟨ G , (λ d d∈ → inj₁ ⟨ refl , ⟨ d∈ , vs ⟩ ⟩) ⟩
  where
  G : projᵉ i ⟨ 𝒯ᵉ (suc n) Ds , ptt ⟩ ⊆ nthD Ds i
  G d (inj₁ ⟨ refl , ⟨ d∈ , _ ⟩ ⟩) = d∈
  G d (inj₂ ⟨ refl , inj₁ e ⟩) = ⊥-elim (errs-clean (suc n) Ds cs e)
  G d (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , nt ⟩ ⟩ ⟩ ⟩) with 𝒯ᵉ-inv (suc n) e e∈
  ... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (e≢ refl)
  ... | inj₂ (inj₁ ⟨ _ , ⟨ _ , ⟨ refl , _ ⟩ ⟩ ⟩) = ⊥-elim (nt refl)
  ... | inj₂ (inj₂ ⟨ () , _ ⟩)
