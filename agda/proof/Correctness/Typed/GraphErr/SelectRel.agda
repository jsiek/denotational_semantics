{-

  The relation between the values of CFGᵀ and of CFGᵀ with the X86
  checks (SelectCheck.agda), in both directions: d ⊑ D, a value of one
  is approximated by the set D of the other.

  The two differ only where a check of X86 fires, on a value of the
  wrong kind, and so only in the entries of code at inputs of the wrong
  kind. So the relation is the identity on first-order data, it never
  relates an error inside a value (Inner), and code is related by what
  it does on related inputs whose environment has the kind its pair says
  (Code): an entry at inputs of the wrong kind is related to anything,
  since no inputs relate to them.

-}

module proof.Correctness.Typed.GraphErr.SelectRel where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.DomainUtilBase using (Nth; Lefts; Rights; Data; flat-const; flat-⟨⟩)
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr)
open import proof.Framework.GraphModel.ErrorMonad

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤′; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

Cars Cdrs : 𝒫 Value → 𝒫 Value
Cars D = car ⟨ D , ptt ⟩
Cdrs D = cdr ⟨ D , ptt ⟩

{- the elements of D of kind k -}
_⇂ₖ_ : 𝒫 Value → Kind → 𝒫 Value
D ⇂ₖ k = D ⇂ λ e → kind e ≡ k

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
Inner : Value → 𝒫 Value → Set₁
Code : Kind → Value → 𝒫 Value → Set₁

ω ⊑ D = Lift (lsuc lzero) (ω ∈ D)
const k ⊑ D = Lift (lsuc lzero) (const k ∈ D)
⟨⟩ ⊑ D = Lift (lsuc lzero) (⟨⟩ ∈ D)
ν ⊑ D = Lift (lsuc lzero) (ν ∈ D)
(V ↦ w) ⊑ D = Lift (lsuc lzero) ((V ↦ w) ∈ D)
(tup[ i ] d) ⊑ D = Inner d (Nth i D)
left d ⊑ D = Inner d (Lefts D)
right d ⊑ D = Inner d (Rights D)
⦅ u , v ⦆ ⊑ D = Code (kind v) u (Cars D) × Inner v (Cdrs D)

Inner d D = Lift (lsuc lzero) (d ≢ ω) × d ⊑ D

[] ⊑* D = ⊤′
(v ∷ V) ⊑* D = v ⊑ D × V ⊑* D

Code k ν C = ⊤′
Code k (V ↦ ν) C = ⊤′
Code k (V ↦ (U ↦ w)) C = ∀ E X → Con E → Con X → Clean E → Clean X → V ⊑* (E ⇂ₖ k) → U ⊑* X
  → w ⊑ ⋆ ⟨ ⋆ ⟨ C , ⟨ E ⇂ₖ k , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
Code k (V ↦ _) C = ⊤′
Code k _ C = Lift (lsuc lzero) ⊥

{- Monotone ----------------------------------------------------------------------------}

⊑-mono : ∀ d {D D'} → D ⊆ D' → d ⊑ D → d ⊑ D'
⊑*-mono : ∀ V {D D'} → D ⊆ D' → V ⊑* D → V ⊑* D'
code-mono : ∀ k u {C C'} → C ⊆ C' → Code k u C → Code k u C'

⊑-mono ω D⊆ (lift d∈) = lift (D⊆ _ d∈)
⊑-mono (const k) D⊆ (lift d∈) = lift (D⊆ _ d∈)
⊑-mono ⟨⟩ D⊆ (lift d∈) = lift (D⊆ _ d∈)
⊑-mono ν D⊆ (lift d∈) = lift (D⊆ _ d∈)
⊑-mono (V ↦ w) D⊆ (lift d∈) = lift (D⊆ _ d∈)
⊑-mono (tup[ i ] d) D⊆ ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e → D⊆ (tup[ i ] e)) r ⟩
⊑-mono (left d) D⊆ ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e → D⊆ (left e)) r ⟩
⊑-mono (right d) D⊆ ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e → D⊆ (right e)) r ⟩
⊑-mono ⦅ u , v ⦆ D⊆ ⟨ c , ⟨ n , r ⟩ ⟩ =
  ⟨ code-mono (kind v) u (λ { e ⟨ x , p∈ ⟩ → ⟨ x , D⊆ _ p∈ ⟩ }) c , ⟨ n , ⊑-mono v (λ { e ⟨ x , p∈ ⟩ → ⟨ x , D⊆ _ p∈ ⟩ }) r ⟩ ⟩

⊑*-mono [] D⊆ _ = ptt
⊑*-mono (v ∷ V) D⊆ ⟨ r , rs ⟩ = ⟨ ⊑-mono v D⊆ r , ⊑*-mono V D⊆ rs ⟩

code-mono k ν C⊆ c = c
code-mono k (V ↦ ν) C⊆ c = c
code-mono k (V ↦ (U ↦ w)) {C} {C'} C⊆ c E X cE cX clE clX rV rU =
  ⊑-mono w (λ { y ⟨ W , ⟨ ⟨ W' , ⟨ e∈ , ⟨ W'⊆ , ne' ⟩ ⟩ ⟩ , ⟨ W⊆ , ne ⟩ ⟩ ⟩ → ⟨ W , ⟨ ⟨ W' , ⟨ C⊆ _ e∈ , ⟨ W'⊆ , ne' ⟩ ⟩ ⟩ , ⟨ W⊆ , ne ⟩ ⟩ ⟩ })

    (c E X cE cX clE clX rV rU)
code-mono k (V ↦ const _) C⊆ c = c
code-mono k (V ↦ ω) C⊆ c = c
code-mono k (V ↦ ⦅ _ , _ ⦆) C⊆ c = c
code-mono k (V ↦ (tup[ _ ] _)) C⊆ c = c
code-mono k (V ↦ left _) C⊆ c = c
code-mono k (V ↦ right _) C⊆ c = c
code-mono k (V ↦ ⟨⟩) C⊆ c = c
code-mono k (const _) C⊆ c = c
code-mono k ω C⊆ c = c
code-mono k ⦅ _ , _ ⦆ C⊆ c = c
code-mono k (tup[ _ ] _) C⊆ c = c
code-mono k (left _) C⊆ c = c
code-mono k (right _) C⊆ c = c
code-mono k ⟨⟩ C⊆ c = c

{- A related value is witnessed by an element of its kind ---------------------------}

⊑-wit : ∀ d {D} → d ⊑ D → d ≢ ω → Σ[ e ∈ Value ] e ∈ D × kind e ≡ kind d
⊑-ne : ∀ d {D} → d ⊑ D → nonempty D
⊑-ne ω (lift d∈) = ⟨ ω , d∈ ⟩
⊑-ne d {D} r with ω? d
... | inj₁ refl = ⟨ ω , lower r ⟩
... | inj₂ d≢ = let ⟨ e , ⟨ e∈ , _ ⟩ ⟩ = ⊑-wit d r d≢ in ⟨ e , e∈ ⟩
⊑-wit ω _ ne = ⊥-elim (ne refl)
⊑-wit (const k) (lift d∈) _ = ⟨ _ , ⟨ d∈ , refl ⟩ ⟩
⊑-wit ⟨⟩ (lift d∈) _ = ⟨ _ , ⟨ d∈ , refl ⟩ ⟩
⊑-wit ν (lift d∈) _ = ⟨ _ , ⟨ d∈ , refl ⟩ ⟩
⊑-wit (V ↦ w) (lift d∈) _ = ⟨ _ , ⟨ d∈ , refl ⟩ ⟩
⊑-wit (tup[ i ] d) ⟨ _ , r ⟩ _ = let ⟨ e , e∈ ⟩ = ⊑-ne d r in ⟨ tup[ i ] e , ⟨ e∈ , refl ⟩ ⟩
⊑-wit (left d) ⟨ _ , r ⟩ _ = let ⟨ e , e∈ ⟩ = ⊑-ne d r in ⟨ left e , ⟨ e∈ , refl ⟩ ⟩
⊑-wit (right d) ⟨ _ , r ⟩ _ = let ⟨ e , e∈ ⟩ = ⊑-ne d r in ⟨ right e , ⟨ e∈ , refl ⟩ ⟩
⊑-wit ⦅ u , v ⦆ ⟨ _ , ⟨ _ , r ⟩ ⟩ _ = let ⟨ e , ⟨ x , p∈ ⟩ ⟩ = ⊑-ne v r in ⟨ ⦅ x , e ⦆ , ⟨ p∈ , refl ⟩ ⟩

kind-ω : ∀ {d} → kind d ≡ error → d ≡ ω
kind-ω {ω} _ = refl
kind-ω {const _} ()
kind-ω {_ ↦ _} ()
kind-ω {ν} ()
kind-ω {⦅ _ , _ ⦆} ()
kind-ω {tup[ _ ] _} ()
kind-ω {left _} ()
kind-ω {right _} ()
kind-ω {⟨⟩} ()

⊑-val : ∀ d {D} → d ≢ ω → d ⊑ D → Conv D
⊑-val d d≢ r with ⊑-wit d r d≢
... | ⟨ e , ⟨ e∈ , k ⟩ ⟩ = ⟨ e , ⟨ e∈ , (λ { refl → d≢ (kind-ω (sym k)) }) ⟩ ⟩


⊑-lift : LiftRel _⊑_
⊑-lift = record { ω→ = lower ; →ω = lift ; S-mono = λ {d} → ⊑-mono d ; S-val = λ {d} d≢ r → ⊑-val d d≢ r }

{- only the elements of D of the kind of d matter -}
⊑-⇂ : ∀ d {D P} → (∀ e → e ∈ D → kind e ≡ kind d → P e) → d ⊑ D → d ⊑ (D ⇂ P)
⊑-⇂ ω h (lift d∈) = lift ⟨ d∈ , h _ d∈ refl ⟩
⊑-⇂ (const k) h (lift d∈) = lift ⟨ d∈ , h _ d∈ refl ⟩
⊑-⇂ ⟨⟩ h (lift d∈) = lift ⟨ d∈ , h _ d∈ refl ⟩
⊑-⇂ ν h (lift d∈) = lift ⟨ d∈ , h _ d∈ refl ⟩
⊑-⇂ (V ↦ w) h (lift d∈) = lift ⟨ d∈ , h _ d∈ refl ⟩
⊑-⇂ (tup[ i ] d) h ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e e∈ → ⟨ e∈ , h _ e∈ refl ⟩) r ⟩
⊑-⇂ (left d) h ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e e∈ → ⟨ e∈ , h _ e∈ refl ⟩) r ⟩
⊑-⇂ (right d) h ⟨ n , r ⟩ = ⟨ n , ⊑-mono d (λ e e∈ → ⟨ e∈ , h _ e∈ refl ⟩) r ⟩
⊑-⇂ ⦅ u , v ⦆ h ⟨ c , ⟨ n , r ⟩ ⟩ =
  ⟨ code-mono (kind v) u (λ { e ⟨ x , p∈ ⟩ → ⟨ x , ⟨ p∈ , h _ p∈ refl ⟩ ⟩ }) c
  , ⟨ n , ⊑-mono v (λ { e ⟨ x , p∈ ⟩ → ⟨ x , ⟨ p∈ , h _ p∈ refl ⟩ ⟩ }) r ⟩ ⟩

{- of the right kind, and not ω -}
⊑-kind : ∀ d {D} → d ⊑ D → d ⊑ (D ⇂ₖ kind d)
⊑-kind d = ⊑-⇂ d (λ e e∈ k → k)

⊑-⌊⌋ : ∀ d {D} → d ≢ ω → d ⊑ D → d ⊑ ⌊ D ⌋
⊑-⌊⌋ d d≢ = ⊑-⇂ d (λ { e e∈ k refl → d≢ (kind-ω (sym k)) })


{- Code ------------------------------------------------------------------------------}

{- the entries of code (a closed function of two arguments) are related
   when its body is -}
code-ΛΛ : ∀ {k F C} → (∀ V U w → V ≢ [] → U ≢ [] → V ≈ V → U ≈ U → NoErr V → NoErr U → w ∈ F (mem V) (mem U)
    → Code k (V ↦ (U ↦ w)) C)
  → ∀ u → u ∈ ΛΛᵐ ⟨ F , ptt ⟩ → Code k u C
code-ΛΛ h ν _ = ptt
code-ΛΛ h (V ↦ ν) _ = ptt
code-ΛΛ h (V ↦ (U ↦ w)) ⟨ ⟨ ⟨ w∈ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , cV ⟩ ⟩ , ⟨ nV , nU ⟩ ⟩ = h V U w neV neU cV cU nV nU w∈
code-ΛΛ h (V ↦ const _) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ ω) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ ⦅ _ , _ ⦆) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ (tup[ _ ] _)) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ left _) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ right _) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (V ↦ ⟨⟩) ⟨ ⟨ () , _ ⟩ , _ ⟩
code-ΛΛ h (const _) ⟨ () , _ ⟩
code-ΛΛ h ω ⟨ () , _ ⟩
code-ΛΛ h ⦅ _ , _ ⦆ ⟨ () , _ ⟩
code-ΛΛ h (tup[ _ ] _) ⟨ () , _ ⟩
code-ΛΛ h (left _) ⟨ () , _ ⟩
code-ΛΛ h (right _) ⟨ () , _ ⟩
code-ΛΛ h ⟨⟩ ⟨ () , _ ⟩

{- the code of no definition: its call errs, on related sets that are not empty -}

app-single : ∀ {C E X e x w} → ((e ∷ []) ↦ ((x ∷ []) ↦ w)) ∈ C → e ∈ E → x ∈ X → w ∈ ⋆ ⟨ ⋆ ⟨ C , ⟨ E , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
app-single c∈ e∈ x∈ = ⟨ _ ∷ [] , ⟨ ⟨ _ ∷ [] , ⟨ c∈ , ⟨ (λ { _ (here refl) → e∈ }) , (λ ()) ⟩ ⟩ ⟩ , ⟨ (λ { _ (here refl) → x∈ }) , (λ ()) ⟩ ⟩ ⟩

errcode-rel : ∀ k u → u ∈ errcode → Code k u errcode
errcode-rel k = code-ΛΛ λ { [] U w neV _ _ _ _ _ _ → ⊥-elim (neV refl) ; V [] w _ neU _ _ _ _ _ → ⊥-elim (neU refl)
  ; (v ∷ V) (u ∷ U) .ω _ _ _ _ _ _ refl E X cE cX clE clX ⟨ rv , _ ⟩ ⟨ ru , _ ⟩ →
    let ⟨ e , e∈ ⟩ = ⊑-ne v rv ; ⟨ x , x∈ ⟩ = ⊑-ne u ru
        e≢ = clE e (proj₁ e∈) ; x≢ = clX x x∈ in
    lift (app-single {errcode} {E ⇂ₖ k} {X} {e} {x} {ω} ⟨ ⟨ ⟨ refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩

                                 , ⟨ (λ { (here eq) → e≢ (sym eq) }) , (λ { (here eq) → x≢ (sym eq) }) ⟩ ⟩ e∈ x∈) }
