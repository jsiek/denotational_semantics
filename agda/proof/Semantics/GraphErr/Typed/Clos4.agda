{-

  Lemmas about the semantics of Clos4ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos4.agda): its denotations are monotone,
  continuous and consistent (Ok, as for Clos3ᵀ in
  proof/Semantics/GraphErr/Typed/Clos3.agda). Each operator is Good but
  unpack, a bind into its body on the car and cdr of the closure: it is
  continuous because finitely many pairs of the closure give the finite
  parts of its car and cdr that the body uses, and consistent because a
  consistent closure has one length n. And a body uses finite parts of
  the sets it is given (fin₁, fin₂), for any Ok denotation.

-}

module proof.Semantics.GraphErr.Typed.Clos4 where

open import Semantics.GraphErr.Typed.Clos4 public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr; ΛΛ-β)
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness)
open import proof.Framework.GraphModel.Continuity using (⋆₂-good)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; _~ₑ[_]_; _⊆ₑ_; •-~; extend-nonempty-env)
open import proof.Semantics.GraphErr.Typed.Clos2 using (get-good; case-good; prim-good; project-good)
open import proof.Semantics.GraphErr.Typed.Clos3
  using (Ok; Oks; ok-op; Ok-≃; var-ok; const-ok; let-ok)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type using (Any; tup; idx) renaming (⟪_⟫ to ⟪_⟫ᵗ)
open import Language.Typed.Clos4

open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

{- unpack -------------------------------------------------------------------------}

car-witness : ∀ {L} C → mem C ⊆ car ⟨ L , ptt ⟩ → Σ[ P ∈ List Value ] mem P ⊆ L × mem C ⊆ car ⟨ mem P , ptt ⟩
car-witness [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
car-witness (c ∷ C) C⊆ with C⊆ c (here refl) | car-witness C (λ d d∈ → C⊆ d (there d∈))
... | ⟨ t , p∈ ⟩ | ⟨ P , ⟨ P⊆ , C⊆P ⟩ ⟩ =
  ⟨ ⦅ c , t ⦆ ∷ P , ⟨ (λ { _ (here refl) → p∈ ; d (there d∈) → P⊆ d d∈ })
  , (λ { _ (here refl) → ⟨ t , here refl ⟩ ; d (there d∈) → let ⟨ t′ , i ⟩ = C⊆P d d∈ in ⟨ t′ , there i ⟩ }) ⟩ ⟩

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

{- The terms of Clos4ᵀ ------------------------------------------------------------}

bodies : ∀ {Γ n} → Vec (Tm Γ Any) n → Bodies (replicate n ■)
bodies [] = ptt
bodies (M ∷ Ms) = ⟨ ⟦ M ⟧ , bodies Ms ⟩

bodies-≡ : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) ρ → ⟪ replicate n ■ ⟫₊ (bodies Ms) ρ ≡ ⟦ Ms ⟧s ρ
bodies-≡ [] ρ = refl
bodies-≡ (M ∷ Ms) ρ = cong ⟨ ⟦ M ⟧ ρ ,_⟩ (bodies-≡ Ms ρ)

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Oks (replicate n ■) (bodies Ms)

ok (` x) = var-ok (idx x)
ok (code N) = const-ok (ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ (ok N)) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
ok (call L M N) = ok-op (binds-good 3 ⋆₂-good) ⟨ ⟦ L ⟧ , ⟨ ⟦ M ⟧ , ⟨ ⟦ N ⟧ , ptt ⟩ ⟩ ⟩ ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
ok (pack L M) = ok-op pairᵐ-good ⟨ ⟦ L ⟧ , ⟨ ⟦ M ⟧ , ptt ⟩ ⟩ ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
ok (unpack L B) = unpack-ok (ok L) (λ n → ok (B n))
ok (lit B c) = ok-op (ℬ-good B c) ptt ptt
ok (tuple {n = n} Ms) = Ok-≃ (λ ρ → ≃-reflexive (cong (𝒯ᵐ n) (bodies-≡ Ms ρ))) (ok-op (𝒯ᵐ-good n) (bodies Ms) (oks Ms))
ok (get i M) = ok-op (get-good i) ⟨ ⟦ M ⟧ , ptt ⟩ ⟨ ok M , ptt ⟩
ok (inl M) = ok-op inlᵐ-good ⟨ ⟦ M ⟧ , ptt ⟩ ⟨ ok M , ptt ⟩
ok (inr M) = ok-op inrᵐ-good ⟨ ⟦ M ⟧ , ptt ⟩ ⟨ ok M , ptt ⟩
ok (case L M N) = ok-op case-good ⟨ ⟦ L ⟧ , ⟨ ⟦ M ⟧ , ⟨ ⟦ N ⟧ , ptt ⟩ ⟩ ⟩ ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
ok (prim p L M) = ok-op (prim-good p) ⟨ ⟦ L ⟧ , ⟨ ⟦ M ⟧ , ptt ⟩ ⟩ ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
ok (let′ M N) = let-ok (ok M) (ok N)
ok (inject G M) = ok M
ok (project G M) = ok-op (project-good _) ⟨ ⟦ M ⟧ , ptt ⟩ ⟨ ok M , ptt ⟩

oks [] = ptt
oks (M ∷ Ms) = ⟨ ok M , oks Ms ⟩

con : ∀ {Γ A} (M : Tm Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
con M c = proj₂ (proj₂ (ok M)) c

{- Bodies use finite parts of their arguments, for any Ok denotation ----------------}

fin₁ : ∀ {E} → Ok E → ∀ {ρ X} → nonempty-env ρ → nonempty X → Finitary (λ X → E (X • ρ)) X
fin₁ ⟨ m , ⟨ k , _ ⟩ ⟩ {ρ} NE neX w w∈ with k (extend-nonempty-env NE neX) w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
  ⟨ proj₁ (f 0) , ⟨ proj₂ (proj₂ (f 0)) , ⟨ (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈)) , m env⊆ w w∈′ ⟩ ⟩ ⟩
  where
  env⊆ : ρ′ ⊆ₑ (mem (proj₁ (f 0)) • ρ)
  env⊆ zero = proj₁ (proj₁ (proj₂ (f 0)))
  env⊆ (suc x) = s (suc x)

{- the body of code, on its environment T and argument E -}
fin₂ : ∀ {E} → Ok E → ∀ {T X} → nonempty T → nonempty X → ∀ w → w ∈ E (X • T • λ _ → init)
  → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ] V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ X × w ∈ E (mem U • mem V • λ _ → init)
fin₂ ⟨ m , ⟨ k , _ ⟩ ⟩ neT neX w w∈
    with k (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) neT) neX) w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
  ⟨ proj₁ (f 1) , ⟨ proj₁ (f 0) , ⟨ proj₂ (proj₂ (f 1)) , ⟨ proj₂ (proj₂ (f 0))
  , ⟨ (λ d d∈ → s 1 d (proj₂ (proj₁ (proj₂ (f 1))) d d∈)) , ⟨ (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈))
  , m env⊆ w w∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  env⊆ : ρ′ ⊆ₑ (mem (proj₁ (f 0)) • mem (proj₁ (f 1)) • λ _ → init)
  env⊆ zero = proj₁ (proj₁ (proj₂ (f 0)))
  env⊆ (suc zero) = proj₁ (proj₁ (proj₂ (f 1)))
  env⊆ (suc (suc x)) = s (suc (suc x))

{- code, applied to sets of values T and E, contains its body on them -}
ΛΛᵐ-call : ∀ {F T E} → Con T → Con E → Clean T → Clean E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ ⋆ ⟨ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
ΛΛᵐ-call {F} cT cE clT clE fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩
