{-

  The binders of the semantics of intrinsically typed syntax in the
  graph model with errors (Semantics/GraphErr/Typed/), for any language:

  * n binds of sets of values, or of equal operands (binds-val-≃,
    binds-≃₂);
  * code, a closed function of two arguments (ΛΛᵐ) whose body is Ok
    (code-ok), and its β laws: applied to an environment T it is the
    function of the body on T (ΛΛᵐ-⋆), and applied to T and E it
    contains the body on them (ΛΛᵐ-call);
  * the existential binder of a closure: a bind of a set of pairs P into
    a family of bodies B n on its cdr and car, for the lengths n of the
    tuples in its cdr (Unpack). It is Ok (unpack-ok): continuous because
    finitely many pairs give the finite parts of car and cdr the body
    uses, and consistent because a consistent P has one length.

-}

module proof.Framework.GraphModel.TypedBinders where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr; ΛΛ-β; nthD)
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; _~ₑ[_]_; _⊆ₑ_; •-~; extend-nonempty-env)
open import proof.Framework.GraphModel.TypedOk using (Ok; const-ok)

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

{- n binds ------------------------------------------------------------------------}

⌊⌋-≃ : ∀ {D D'} → D ≃ D' → ⌊ D ⌋ ≃ ⌊ D' ⌋
⌊⌋-≃ D≃ = ⟨ ⌊⌋-mono (proj₁ D≃) , ⌊⌋-mono (proj₂ D≃) ⟩

{- of sets of values: the continuation, on sets equal to them -}
binds-val-≃ : ∀ n {Ds K A} → AllVal n Ds → (∀ {Xs} → (∀ i → nthD Xs i ≃ nthD Ds i) → K Xs ≃ A) → binds n Ds K ≃ A
binds-val-≃ zero _ h = h (λ ())
binds-val-≃ (suc n) {⟨ D , Ds ⟩} {K} vs h =
  ≃-trans (≫=-val-β {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (vs zero))
    (binds-val-≃ n (λ i → vs (suc i)) λ r → h λ { zero → ⟨ ⌊⌋-⊆ , ⌊⌋-clean (proj₁ (vs zero)) ⟩ ; (suc i) → r i })

{- of equal operands, into continuations equal on equal values -}
binds-≃₂ : ∀ n {Ds Es K K'} → (∀ i → nthD Ds i ≃ nthD Es i)
  → (∀ {Xs Ys} → (∀ i → nthD Xs i ≃ nthD Ys i × Val (nthD Ys i) × nthD Ys i ⊆ nthD Es i) → K Xs ≃ K' Ys)
  → binds n Ds K ≃ binds n Es K'
binds-≃₂ zero _ h = h (λ ())
binds-≃₂ (suc n) {⟨ D , Ds ⟩} {⟨ E , Es ⟩} {K} {K'} eq h =
  ≫=-≃ {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {λ X → binds n Es (λ Xs → K' ⟨ X , Xs ⟩)} (eq zero) λ _ c → binds-≃₂ n (λ i → eq (suc i))
    λ r → h λ { zero → ⟨ ⌊⌋-≃ (eq zero) , ⟨ ⌊⌋-val c , ⌊⌋-⊆ ⟩ ⟩ ; (suc i) → r i }

{- Code -------------------------------------------------------------------------}

code-ok : ∀ {E} → Ok E → Ok (λ _ → ΛΛᵐ ⟨ (λ X Y → E (Y • X • λ _ → ⌈ ω ⌉)) , ptt ⟩)
code-ok o = const-ok (ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ o) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))

{- code applied to its environment T, when the body uses a finite part of T -}
ΛΛᵐ-⋆ : ∀ {F T} → Con T → Val T → (∀ {X X' Y} → X ⊆ X' → F X Y ⊆ F X' Y)
  → (∀ U w → U ≢ [] → w ∈ F T (mem U) → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ T × w ∈ F (mem V) (mem U))
  → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ≃ Λᵐ ⟨ F T , ptt ⟩
ΛΛᵐ-⋆ {F} {T} cT ⟨ clT , ⟨ t , t∈ ⟩ ⟩ m fin = ⟨ H , G ⟩
  where
  G : Λᵐ ⟨ F T , ptt ⟩ ⊆ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν _ = ⟨ t ∷ [] , ⟨ ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ { (here eq) → clT t t∈ (sym eq) }) , tt ⟩ ⟩
          , ⟨ (λ { _ (here refl) → t∈ }) , (λ ()) ⟩ ⟩ ⟩
  G (U ↦ x) ⟨ ⟨ x∈ , ⟨ neU , cU ⟩ ⟩ , nU ⟩ with fin U x neU x∈
  ... | ⟨ V , ⟨ neV , ⟨ V⊆ , x∈′ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ ⟨ ⟨ ⟨ x∈′ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , nU ⟩ ⟩
          , ⟨ V⊆ , neV ⟩ ⟩ ⟩
  H : ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ⊆ Λᵐ ⟨ F T , ptt ⟩
  H ν _ = ⟨ tt , tt ⟩
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ ⟨ x∈ , r ⟩ , _ ⟩ , ⟨ _ , nU ⟩ ⟩ , ⟨ V⊆T , _ ⟩ ⟩ ⟩ = ⟨ ⟨ m V⊆T x x∈ , r ⟩ , nU ⟩

{- code, applied to sets of values T and E, contains its body on them -}
ΛΛᵐ-call : ∀ {F T E} → Con T → Con E → Clean T → Clean E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ ⋆ ⟨ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
ΛΛᵐ-call {F} cT cE clT clE fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩

{- Unpack -----------------------------------------------------------------------}

car-witness : ∀ {L} C → mem C ⊆ car ⟨ L , ptt ⟩ → Σ[ P ∈ List Value ] mem P ⊆ L × mem C ⊆ car ⟨ mem P , ptt ⟩
car-witness [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
car-witness (c ∷ C) C⊆ with C⊆ c (here refl) | car-witness C (λ d d∈ → C⊆ d (there d∈))
... | ⟨ t , p∈ ⟩ | ⟨ P , ⟨ P⊆ , C⊆P ⟩ ⟩ =
  ⟨ ⦅ c , t ⦆ ∷ P , ⟨ (λ { _ (here refl) → p∈ ; d (there d∈) → P⊆ d d∈ })
  , (λ { _ (here refl) → ⟨ t , here refl ⟩ ; d (there d∈) → let ⟨ t′ , i ⟩ = C⊆P d d∈ in ⟨ t′ , there i ⟩ }) ⟩ ⟩

private
  ++⊆ : ∀ {A B : List Value} {D} → mem A ⊆ D → mem B ⊆ D → mem (A ++ B) ⊆ D
  ++⊆ {A} A⊆ B⊆ d d∈ with ∈-++⁻ A d∈
  ... | inj₁ i = A⊆ d i
  ... | inj₂ i = B⊆ d i

{- the closures P with an environment of length n, and the body B n on them -}
Unpack : (∀ n → Env Value → 𝒫 Value) → Env Value → 𝒫 Value → 𝒫 Value
Unpack B ρ P w = Σ[ n ∈ ℕ ] (Σ[ t ∈ Value ] t ∈ cdr ⟨ P , ptt ⟩ × kind t ≡ tup n)
  × w ∈ B n (cdr ⟨ P , ptt ⟩ • car ⟨ P , ptt ⟩ • ρ)

unpack-ok : ∀ {E B} → Ok E → (∀ n → Ok (B n)) → Ok (λ ρ → E ρ ≫= Unpack B ρ)
unpack-ok {E} {B} ⟨ mE , ⟨ kE , cE ⟩ ⟩ oB =
  ⟨ (λ ρ⊆ → ≫=-mono (mE ρ⊆) (mU ρ⊆)) , ⟨ (λ NE → ≫=-cont′ mE (kE NE) mU (body NE)) , (λ ρ~ → ≫=-consis (cE ρ~) (cU ρ~)) ⟩ ⟩
  where
  mU : ∀ {ρ ρ' P P'} → ρ ⊆ₑ ρ' → P ⊆ P' → Unpack B ρ P ⊆ Unpack B ρ' P'
  mU ρ⊆ P⊆ w ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , p∈ ⟩ , tk ⟩ ⟩ , w∈ ⟩ ⟩ =
    ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , P⊆ _ p∈ ⟩ , tk ⟩ ⟩ , proj₁ (oB n) (•-~ _⊆_ (•-~ _⊆_ ρ⊆ (λ { c ⟨ v , q ⟩ → ⟨ v , P⊆ _ q ⟩ }))
                                                     (λ { v ⟨ c , q ⟩ → ⟨ c , P⊆ _ q ⟩ })) w w∈ ⟩ ⟩
  cU : ∀ {ρ ρ' P P'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ P P' → Every _~_ (Unpack B ρ P) (Unpack B ρ' P')
  cU ρ~ P~ w w' ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , p∈ ⟩ , tk ⟩ ⟩ , w∈ ⟩ ⟩ ⟨ n' , ⟨ ⟨ t' , ⟨ ⟨ u' , p∈' ⟩ , tk' ⟩ ⟩ , w∈' ⟩ ⟩
      with trans (sym tk) (trans (~-kind t t' (proj₂ (P~ _ _ p∈ p∈'))) tk')
  ... | refl = proj₂ (proj₂ (oB n)) (•-~ (Every _~_) (•-~ (Every _~_) ρ~ (λ a b a∈ b∈ → proj₁ (P~ _ _ (proj₂ a∈) (proj₂ b∈))))
                                       (λ a b a∈ b∈ → proj₂ (P~ _ _ (proj₂ a∈) (proj₂ b∈)))) w w' w∈ w∈'
  body : ∀ {ρ} → nonempty-env ρ → Conv (E ρ) → Cont (λ ρ → Unpack B ρ ⌊ E ρ ⌋) ρ
  body {ρ} NE _ w ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , p∈ ⟩ , tk ⟩ ⟩ , w∈ ⟩ ⟩
      with proj₁ (proj₂ (oB n)) (extend-nonempty-env (extend-nonempty-env NE ⟨ u , ⟨ t , p∈ ⟩ ⟩) ⟨ t , ⟨ u , p∈ ⟩ ⟩) w w∈
  ... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩
      with cdr-witness (proj₁ (f 0)) (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈))
         | car-witness (proj₁ (f 1)) (λ d d∈ → s 1 d (proj₂ (proj₁ (proj₂ (f 1))) d d∈))
  ... | ⟨ PT , ⟨ PT⊆ , T⊆ ⟩ ⟩ | ⟨ PC , ⟨ PC⊆ , C⊆ ⟩ ⟩
      with many (λ ρ → ⌊ E ρ ⌋) NE (λ ρ⊆ → ⌊⌋-mono (mE ρ⊆)) (⌊⌋-cont (kE NE)) (⦅ u , t ⦆ ∷ (PT ++ PC))
             (λ { _ (here refl) → p∈ ; d (there d∈) → ++⊆ {PT} PT⊆ PC⊆ d d∈ })
  ... | ⟨ a , Ps⊆ ⟩ = done (λ ρ → Unpack B ρ ⌊ E ρ ⌋) (approx-join a b) w
                         ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , Q _ (here refl) ⟩ , tk ⟩ ⟩ , proj₁ (oB n) env⊆ w w∈′ ⟩ ⟩
    where
    b = approx (λ x → ρ′ (suc (suc x))) (λ x → f (suc (suc x))) (λ x → s (suc (suc x)))
    Q : mem (⦅ u , t ⦆ ∷ (PT ++ PC)) ⊆ ⌊ E (env (approx-join a b)) ⌋
    Q d d∈ = ⌊⌋-mono (mE (join-l a b)) d (Ps⊆ d d∈)
    env⊆ : ρ′ ⊆ₑ _
    env⊆ zero d d∈ = let ⟨ c , q ⟩ = T⊆ d (proj₁ (proj₁ (proj₂ (f 0))) d d∈) in ⟨ c , Q _ (there (∈-++⁺ˡ q)) ⟩
    env⊆ (suc zero) d d∈ = let ⟨ v , q ⟩ = C⊆ d (proj₁ (proj₁ (proj₂ (f 1))) d d∈) in ⟨ v , Q _ (there (∈-++⁺ʳ PT q)) ⟩
    env⊆ (suc (suc x)) = join-r a b x
