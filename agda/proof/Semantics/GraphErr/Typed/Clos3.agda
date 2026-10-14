{-

  Lemmas about the semantics of Clos3ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos3.agda).

  * The code of a closure, applied to the tuple T of its free variables,
    is the function of the body on T (ΛΛᵐ-⋆), when the body uses only a
    finite, consistent part of T: so the denotations of Clos3ᵀ terms
    must be monotone, continuous and consistent (Ok). Each operator is
    the error monad's kernel under binds (Good, proof/Framework/
    GraphModel/ErrorMonad.agda), which preserves these (ok-op); let is
    a bind into its body, whose continuity is shown here (let-ok).

-}

module proof.Semantics.GraphErr.Typed.Clos3 where

open import Semantics.GraphErr.Typed.Clos3 public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Ops using (⋆)
open import proof.Framework.GraphModel.Continuity using (⋆-good)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env
  using (Env; nonempty-env; _~ₑ[_]_; _⊆ₑ_; •-~; extend-nonempty-env; single-env; single-fin; single-⊆; v∈single[xv]x)
open import proof.Semantics.GraphErr.Typed.Clos2 using (app-good; get-good; case-good; prim-good; project-good)
open import Semantics.GraphErr.Typed.Ops
open import Language.Typed.Type using (Any; tup; idx) renaming (⟪_⟫ to ⟪_⟫ᵗ)
open import Language.Typed.Clos3
open import Framework.abt.Sig using (∁)

open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to ⊤′)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

{- Code applied to its environment ---------------------------------------------------}

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

{- Monotone, continuous, consistent denotations --------------------------------------}

Ok : (Env Value → 𝒫 Value) → Set₁
Ok E = Mono E × (∀ {ρ} → nonempty-env ρ → Cont E ρ)
       × (∀ {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ (E ρ) (E ρ'))

Oks : ∀ bs → Bodies bs → Set₁
Oks [] _ = ⊤′
Oks (b ∷ bs) ⟨ E , Es ⟩ = Ok E × Oks bs Es

private
  {- the operands preserve a relation on environments -}
  Pres : (𝒫 Value → 𝒫 Value → Set) → (Env Value → 𝒫 Value) → Set₁
  Pres R E = ∀ {ρ ρ'} → ρ ~ₑ[ R ] ρ' → R (E ρ) (E ρ')

  pres : ∀ R → R ⌈ ω ⌉ ⌈ ω ⌉ → ∀ b {E} → Pres R E → ∀ {ρ ρ'} → ρ ~ₑ[ R ] ρ'
    → result-rel-pres R b (⟪ b ⟫ E ρ) (⟪ b ⟫ E ρ')
  pres R r ■ h ρR = lift (h ρR)
  pres R r (ν b) h ρR X Y XR = pres R r b h (•-~ R ρR XR)
  pres R r (∁ b) h ρR = pres R r b h (λ _ → r)

  pres₊ : ∀ R → R ⌈ ω ⌉ ⌈ ω ⌉ → (∀ {E} → Ok E → Pres R E) → ∀ bs Es → Oks bs Es
    → ∀ {ρ ρ'} → ρ ~ₑ[ R ] ρ' → results-rel-pres R bs (⟪ bs ⟫₊ Es ρ) (⟪ bs ⟫₊ Es ρ')
  pres₊ R r sel [] _ _ ρR = ptt
  pres₊ R r sel (b ∷ bs) ⟨ E , Es ⟩ ⟨ o , os ⟩ ρR = ⟨ pres R r b (sel o) ρR , pres₊ R r sel bs Es os ρR ⟩

  bc : ∀ b {E} → Ok E → ∀ {ρ} → nonempty-env ρ → BodyCont b E ρ
  bc ■ o NE = proj₁ (proj₂ o) NE
  bc (ν b) o NE V ne = bc b o (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne))
  bc (∁ b) o NE = bc b o (λ _ → ⟨ ω , refl ⟩)

  bcs : ∀ bs Es → Oks bs Es → ∀ {ρ} → nonempty-env ρ → OK bs Es ρ
  bcs [] _ _ _ = ptt
  bcs (b ∷ bs) ⟨ E , Es ⟩ ⟨ o , os ⟩ NE = ⟨ ⟨ proj₁ o , bc b o NE ⟩ , bcs bs Es os NE ⟩

ok-op : ∀ {bs g} → Good ⊤ bs g → ∀ Es → Oks bs Es → Ok (λ ρ → g (⟪ bs ⟫₊ Es ρ))
ok-op {bs} G Es os =
  ⟨ (λ ρ⊆ → lower (mono G _ _ (pres₊ _⊆_ (λ _ z → z) proj₁ bs Es os ρ⊆)))
  , ⟨ (λ NE → cont G Es NE (bcs bs Es os NE))
    , (λ ρ~ → lower (consis G tt _ _ (pres₊ (Every _~_) (Con-⌈⌉ ω) (λ o → proj₂ (proj₂ o)) bs Es os ρ~))) ⟩ ⟩

Ok-≃ : ∀ {E E'} → (∀ ρ → E ρ ≃ E' ρ) → Ok E → Ok E'
Ok-≃ eq ⟨ m , ⟨ c , k ⟩ ⟩ =
  ⟨ (λ ρ⊆ d d∈ → proj₁ (eq _) d (m ρ⊆ d (proj₂ (eq _) d d∈)))
  , ⟨ (λ {ρ} NE v v∈ → let r = c NE v (proj₂ (eq ρ) v v∈) in
         ⟨ proj₁ r , ⟨ proj₁ (proj₂ r) , ⟨ proj₁ (proj₂ (proj₂ r)) , proj₁ (eq _) v (proj₂ (proj₂ (proj₂ r))) ⟩ ⟩ ⟩)
    , (λ ρ~ a b a∈ b∈ → k ρ~ a b (proj₂ (eq _) a a∈) (proj₂ (eq _) b b∈)) ⟩ ⟩

var-ok : ∀ k → Ok (λ ρ → ρ k)
var-ok k = ⟨ (λ ρ⊆ → ρ⊆ k) , ⟨ (λ {ρ} NE v v∈ → ⟨ single-env k ⌈ v ⌉ ρ NE
           , ⟨ single-fin {x = k} {NE-ρ = NE} , ⟨ single-⊆ {x = k} v∈ , v∈single[xv]x {x = k} ⟩ ⟩ ⟩) , (λ ρ~ → ρ~ k) ⟩ ⟩

const-ok : ∀ {C} → Con C → Ok (λ _ → C)
const-ok c = ⟨ (λ _ _ z → z) , ⟨ const-cont , (λ _ → c) ⟩ ⟩

{- a bind into a body -}
let-ok : ∀ {E N} → Ok E → Ok N → Ok (λ ρ → E ρ ≫= λ X → N (X • ρ))
let-ok {E} {N} ⟨ mE , ⟨ kE , cE ⟩ ⟩ ⟨ mN , ⟨ kN , cN ⟩ ⟩ =
  ⟨ (λ ρ⊆ → ≫=-mono (mE ρ⊆) (λ X⊆ → mN (•-~ _⊆_ ρ⊆ X⊆)))
  , ⟨ (λ NE → ≫=-cont′ mE (kE NE) (λ ρ⊆ X⊆ → mN (•-~ _⊆_ ρ⊆ X⊆)) (body NE))
    , (λ ρ~ → ≫=-consis (cE ρ~) (λ X~ → cN (•-~ (Every _~_) ρ~ X~))) ⟩ ⟩
  where
  body : ∀ {ρ} → nonempty-env ρ → Conv (E ρ) → Cont (λ ρ → N (⌊ E ρ ⌋ • ρ)) ρ
  body NE cv w w∈ with kN (extend-nonempty-env NE cv) w w∈
  ... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩
      with many (λ ρ → ⌊ E ρ ⌋) NE (λ ρ⊆ → ⌊⌋-mono (mE ρ⊆)) (⌊⌋-cont (kE NE)) (proj₁ (f 0))
             (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈))
  ... | ⟨ a , V⊆ ⟩ = done (λ ρ → N (⌊ E ρ ⌋ • ρ)) (approx-join a b) w (mN env⊆ w w∈′)
    where
    b = approx (λ x → ρ′ (suc x)) (λ x → f (suc x)) (λ x → s (suc x))
    env⊆ : ρ′ ⊆ₑ (⌊ E (env (approx-join a b)) ⌋ • env (approx-join a b))
    env⊆ zero d d∈ = ⌊⌋-mono (mE (join-l a b)) d (V⊆ d (proj₁ (proj₁ (proj₂ (f 0))) d d∈))
    env⊆ (suc x) d d∈ = join-r a b x d d∈

{- The terms of Clos3ᵀ ------------------------------------------------------------}

bodies : ∀ {Γ n} → Vec (Tm Γ Any) n → Bodies (replicate n ■)
bodies [] = ptt
bodies (M ∷ Ms) = ⟨ ⟦ M ⟧ , bodies Ms ⟩

bodies-≡ : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) ρ → ⟪ replicate n ■ ⟫₊ (bodies Ms) ρ ≡ ⟦ Ms ⟧s ρ
bodies-≡ [] ρ = refl
bodies-≡ (M ∷ Ms) ρ = cong ⟨ ⟦ M ⟧ ρ ,_⟩ (bodies-≡ Ms ρ)

{- the code of a closure -}
⟦_⟧ᶜ : ∀ {Γ A} → Tm Γ A → 𝒫 Value
⟦ clos N Ms ⟧ᶜ = ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • λ _ → init)) , ptt ⟩
⟦ _ ⟧ᶜ = ⌈ ω ⌉

ok : ∀ {Γ A} (M : Tm Γ A) → Ok ⟦ M ⟧
oks : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Oks (replicate n ■) (bodies Ms)

tuple-ok : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Ok (λ ρ → 𝒯ᵐ n (⟦ Ms ⟧s ρ))
tuple-ok {n = n} Ms =
  Ok-≃ (λ ρ → ≃-reflexive (cong (𝒯ᵐ n) (bodies-≡ Ms ρ))) (ok-op (𝒯ᵐ-good n) (bodies Ms) (oks Ms))

ok (` x) = var-ok (idx x)
ok (clos N Ms) = ok-op (strict₂-good ⋆-good) ⟨ (λ _ → ⟦ clos N Ms ⟧ᶜ) , ⟨ (λ ρ → 𝒯ᵐ _ (⟦ Ms ⟧s ρ)) , ptt ⟩ ⟩
  ⟨ const-ok (ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ (ok N)) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
  , ⟨ tuple-ok Ms , ptt ⟩ ⟩
ok (app L M) = ok-op app-good ⟨ ⟦ L ⟧ , ⟨ ⟦ M ⟧ , ptt ⟩ ⟩ ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
ok (lit B c) = ok-op (ℬ-good B c) ptt ptt
ok (tuple Ms) = tuple-ok Ms
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

{- the code of a closure uses a finite part of the tuple of its free variables -}
code-fin : ∀ {n} (N : Tm (Any ∷ ⟪ tup n ⟫ᵗ ∷ []) Any) {T} → nonempty T → ∀ U w → U ≢ []
  → w ∈ ⟦ N ⟧ (mem U • T • λ _ → init)
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ T × w ∈ ⟦ N ⟧ (mem U • mem V • λ _ → init)
code-fin N neT U w neU w∈
    with proj₁ (proj₂ (ok N)) (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) neT)
                                  (E≢[]⇒nonempty-mem neU)) w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
  ⟨ proj₁ (f 1) , ⟨ proj₂ (proj₂ (f 1)) , ⟨ (λ d d∈ → s 1 d (proj₂ (proj₁ (proj₂ (f 1))) d d∈))
  , proj₁ (ok N) env⊆ w w∈′ ⟩ ⟩ ⟩
  where
  env⊆ : ρ′ ⊆ₑ (mem U • mem (proj₁ (f 1)) • λ _ → init)
  env⊆ zero = s 0
  env⊆ (suc zero) = proj₁ (proj₁ (proj₂ (f 1)))
  env⊆ (suc (suc x)) = s (suc (suc x))
