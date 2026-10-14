{-

  Monotone, continuous and consistent denotations (Ok), for semantics of
  intrinsically typed syntax in the graph model with errors, defined by
  direct recursion on the terms (Semantics/GraphErr/Typed/): the
  analogue of GoodSemantics (SemanticsCore.agda) without an ABT, so a
  language proves Ok of each term by structural induction, one line per
  constructor, from the facts of this module:

  * an operator that is Good (ContinuityBase.agda) preserves Ok
    (ok-op), also on the operands of a vector of terms (ok-vec, through
    split, the bodies of a function to Results); variables and
    constants are Ok, and so is a bind into a body (let-ok); the check
    of a kind is Good (check-kind-good);
  * a body under one or two binders uses only finite parts of the sets
    it is given (fin₁, fin₂, fin-code).

-}

module proof.Framework.GraphModel.TypedOk where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (Finitary)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env
  using (Env; nonempty-env; _~ₑ[_]_; _⊆ₑ_; •-~; extend-nonempty-env; single-env; single-fin; single-⊆; v∈single[xv]x)
open import Framework.abt.Sig using (∁)

open import Data.List using (List; []; _∷_; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to ⊤′)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

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

{- a Good operator on Ok operands -}
ok-op : ∀ {bs g} → Good ⊤ bs g → ∀ {Es} → Oks bs Es → Ok (λ ρ → g (⟪ bs ⟫₊ Es ρ))
ok-op {bs} G {Es} os =
  ⟨ (λ ρ⊆ → lower (mono G _ _ (pres₊ _⊆_ (λ _ z → z) proj₁ bs Es os ρ⊆)))
  , ⟨ (λ NE → cont G Es NE (bcs bs Es os NE))
    , (λ ρ~ → lower (consis G tt _ _ (pres₊ (Every _~_) (Con-⌈⌉ ω) (λ o → proj₂ (proj₂ o)) bs Es os ρ~))) ⟩ ⟩

Ok-≃ : ∀ {E E'} → (∀ ρ → E ρ ≃ E' ρ) → Ok E → Ok E'
Ok-≃ eq ⟨ m , ⟨ c , k ⟩ ⟩ =
  ⟨ (λ ρ⊆ d d∈ → proj₁ (eq _) d (m ρ⊆ d (proj₂ (eq _) d d∈)))
  , ⟨ (λ {ρ} NE v v∈ → let r = c NE v (proj₂ (eq ρ) v v∈) in
         ⟨ proj₁ r , ⟨ proj₁ (proj₂ r) , ⟨ proj₁ (proj₂ (proj₂ r)) , proj₁ (eq _) v (proj₂ (proj₂ (proj₂ r))) ⟩ ⟩ ⟩)
    , (λ ρ~ a b a∈ b∈ → k ρ~ a b (proj₂ (eq _) a a∈) (proj₂ (eq _) b b∈)) ⟩ ⟩

{- the bodies of the n results of a function of the environment (the
   meaning of a vector of terms) -}
split : ∀ n → (Env Value → Results (𝒫 Value) (replicate n ■)) → Bodies (replicate n ■)
split zero _ = ptt
split (suc n) Es = ⟨ (λ ρ → proj₁ (Es ρ)) , split n (λ ρ → proj₂ (Es ρ)) ⟩

split-≡ : ∀ n Es ρ → ⟪ replicate n ■ ⟫₊ (split n Es) ρ ≡ Es ρ
split-≡ zero Es ρ = refl
split-≡ (suc n) Es ρ = cong ⟨ proj₁ (Es ρ) ,_⟩ (split-≡ n (λ ρ → proj₂ (Es ρ)) ρ)

ok-vec : ∀ {n g} → Good ⊤ (replicate n ■) g → ∀ {Es} → Oks (replicate n ■) (split n Es) → Ok (λ ρ → g (Es ρ))
ok-vec {n} {g} G {Es} os = Ok-≃ (λ ρ → ≃-reflexive (cong g (split-≡ n Es ρ))) (ok-op G os)

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

{- the check that keeps the elements of kind k (the kernel of a project) -}
check-kind-good : ∀ k → Good ⊤ (■ ∷ []) (λ Ds → checked k (proj₁ Ds) (proj₁ Ds ⇂ λ d → kind d ≡ k))
check-kind-good k = mk-good (λ { _ _ ⟨ lift X⊆ , _ ⟩ → lift (checked-mono X⊆ (⇂-mono X⊆)) })
  (λ { _ _ ⟨ lift X~ , _ ⟩ → lift (checked-consis X~ (⇂-~ X~) needs needs) })
  (λ { _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ → checked-cont c (⇂-cont c) })
  where needs : ∀ {X} → Needs k X (X ⇂ λ d → kind d ≡ k)
        needs w ⟨ w∈ , wk ⟩ = inj₂ ⟨ w , ⟨ w∈ , wk ⟩ ⟩

{- Bodies use finite parts of their arguments --------------------------------------}

fin₁ : ∀ {E} → Ok E → ∀ {ρ X} → nonempty-env ρ → nonempty X → Finitary (λ X → E (X • ρ)) X
fin₁ ⟨ m , ⟨ k , _ ⟩ ⟩ {ρ} NE neX w w∈ with k (extend-nonempty-env NE neX) w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
  ⟨ proj₁ (f 0) , ⟨ proj₂ (proj₂ (f 0)) , ⟨ (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈)) , m env⊆ w w∈′ ⟩ ⟩ ⟩
  where
  env⊆ : ρ′ ⊆ₑ (mem (proj₁ (f 0)) • ρ)
  env⊆ zero = proj₁ (proj₁ (proj₂ (f 0)))
  env⊆ (suc x) = s (suc x)

{- the body of code, on its environment T and argument X -}
fin₂ : ∀ {E} → Ok E → ∀ {T X} → nonempty T → nonempty X → ∀ w → w ∈ E (X • T • λ _ → ⌈ ω ⌉)
  → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ] V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ X × w ∈ E (mem U • mem V • λ _ → ⌈ ω ⌉)
fin₂ ⟨ m , ⟨ k , _ ⟩ ⟩ neT neX w w∈
    with k (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) neT) neX) w w∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
  ⟨ proj₁ (f 1) , ⟨ proj₁ (f 0) , ⟨ proj₂ (proj₂ (f 1)) , ⟨ proj₂ (proj₂ (f 0))
  , ⟨ (λ d d∈ → s 1 d (proj₂ (proj₁ (proj₂ (f 1))) d d∈)) , ⟨ (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈))
  , m env⊆ w w∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  env⊆ : ρ′ ⊆ₑ (mem (proj₁ (f 0)) • mem (proj₁ (f 1)) • λ _ → ⌈ ω ⌉)
  env⊆ zero = proj₁ (proj₁ (proj₂ (f 0)))
  env⊆ (suc zero) = proj₁ (proj₁ (proj₂ (f 1)))
  env⊆ (suc (suc x)) = s (suc (suc x))

{- the body of code, on a finite argument U, uses a finite part of its environment T -}
FinCode : (Env Value → 𝒫 Value) → Set₁
FinCode E = ∀ {T} → nonempty T → ∀ U w → U ≢ [] → w ∈ E (mem U • T • λ _ → ⌈ ω ⌉)
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ T × w ∈ E (mem U • mem V • λ _ → ⌈ ω ⌉)

fin-code : ∀ {E} → Ok E → FinCode E
fin-code o neT U w neU w∈ with fin₂ o neT (E≢[]⇒nonempty-mem neU) w w∈
... | ⟨ V , ⟨ U′ , ⟨ neV , ⟨ _ , ⟨ V⊆ , ⟨ U′⊆ , w∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ neV , ⟨ V⊆ , proj₁ o (•-~ _⊆_ (λ _ _ z → z) U′⊆) w w∈′ ⟩ ⟩ ⟩
