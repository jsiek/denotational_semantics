{-

  The properties of whole terms, once for every graph-model semantics,
  whatever its operators (the β laws of the binders of the graph model
  are added in SemanticsUtil.agda):

  - Laws: for any continuous semantics, the finite parts of the
    environment that an element of a term's denotation needs, and the β
    laws of the binders on bodies of terms;
  - GoodSemantics: the semantics whose operators are 𝕆, given that each
    of them is Good (monotone, consistent and continuous, Continuity.agda):
    its Semantics and ContinuousSemantics instances, and the consistency
    of its denotations.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (Mono₁; Finitary)
open import proof.Framework.GraphModel.ContinuityBase
  using (Mono; Good; mono; consis; cont; Bodies; ⟪_⟫; ⟪_⟫₊; BodyCont; OK)
open import proof.Framework.GraphModel.Env
  using (Env; nonempty-env; finiteNE-env; extend-nonempty-env; •-~; _~ₑ[_]_; _⊆ₑ_)

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module proof.Framework.GraphModel.SemanticsCore (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
open import proof.Framework.GraphModel.Semantics Op sig

module Laws (C : ContinuousSemantics {Value}) where
  private
    S = ContinuousSemantics.Sem C
    ⟦_⟧ = Semantics.⟦_⟧ S
    ⟦⟧-mono : ∀ (M : ABT) {ρ ρ′} → ρ ⊆ₑ ρ′ → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
    ⟦⟧-mono M = ⟦⟧-monotone {{S}} M

  {- every element of a term's denotation is produced by finite, nonempty
     parts of the environment -}
  term-continuous : ∀ (M : ABT) (ρ : Env Value) → nonempty-env ρ → ∀ v → v ∈ ⟦ M ⟧ ρ
    → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x) × v ∈ ⟦ M ⟧ (λ x → mem (Vs x))
  term-continuous M ρ NE v v∈ with ⟦⟧-continuous {{C}} {ρ} {NE} M v v∈
  ... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , v∈′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → proj₁ (fin x))
    , ⟨ (λ x → ⟨ proj₂ (proj₂ (fin x)) , (λ d d∈ → ρ′⊆ x d (proj₂ (proj₁ (proj₂ (fin x))) d d∈)) ⟩)
      , ⟦⟧-mono M (λ x d d∈ → proj₁ (proj₁ (proj₂ (fin x))) d d∈) v v∈′ ⟩ ⟩

  {- a body under one binder -}
  body-mono : ∀ (N : ABT) ρ → Mono₁ (λ X → ⟦ N ⟧ (X • ρ))
  body-mono N ρ X⊆ = ⟦⟧-mono N (•-~ _⊆_ (λ _ _ d∈ → d∈) X⊆)

  {- a body uses only a finite, nonempty part of its argument -}
  body-continuous : ∀ (N : ABT) (ρ : Env Value) → nonempty-env ρ → ∀ (X : 𝒫 Value) → nonempty X
    → Finitary (λ X → ⟦ N ⟧ (X • ρ)) X
  body-continuous N ρ NE X neX d d∈ with term-continuous N (X • ρ) (extend-nonempty-env NE neX) d d∈
  ... | ⟨ Vs , ⟨ ok , d∈′ ⟩ ⟩ = ⟨ Vs 0 , ⟨ proj₁ (ok 0) , ⟨ proj₂ (ok 0) , ⟦⟧-mono N env⊆ d d∈′ ⟩ ⟩ ⟩
    where
    env⊆ : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • ρ) x
    env⊆ zero = λ d d∈ → d∈
    env⊆ (suc x) = proj₂ (ok (suc x))

  {- a body under two binders uses only finite, nonempty parts of both -}
  body2-continuous : ∀ (N : ABT) ρ → nonempty-env ρ → ∀ {T E} → nonempty T → nonempty E
    → ∀ w → w ∈ ⟦ N ⟧ (E • T • ρ) → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ ⟦ N ⟧ (mem U • mem V • ρ)
  body2-continuous N ρ NE neT neE w w∈
      with term-continuous N _ (extend-nonempty-env (extend-nonempty-env NE neT) neE) w w∈
  ... | ⟨ Vs , ⟨ ok , w∈′ ⟩ ⟩ =
    ⟨ Vs 1 , ⟨ Vs 0 , ⟨ proj₁ (ok 1) , ⟨ proj₁ (ok 0) , ⟨ proj₂ (ok 1) , ⟨ proj₂ (ok 0)
    , ⟦⟧-mono N env⊆ w w∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    env⊆ : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • mem (Vs 1) • ρ) x
    env⊆ zero = λ d d∈ → d∈
    env⊆ (suc zero) = λ d d∈ → d∈
    env⊆ (suc (suc x)) = proj₂ (ok (suc (suc x)))


module GoodSemantics (P : Set) (𝕆 : DOpSig (𝒫 Value) sig) (good : ∀ op → Good P (sig op) (𝕆 op)) where

  Sem : Semantics {Value}
  Sem = record { error = ω ; interp-op = 𝕆 ; mono-op = λ op → mono (good op) }

  private
    ⟦_⟧ = Semantics.⟦_⟧ Sem
    ⟦_⟧ₐ = Semantics.⟦_⟧ₐ Sem
    ⟦_⟧₊ = Semantics.⟦_⟧₊ Sem

    {- the bodies of the operands -}
    body : ∀ {b} → Arg b → Env Value → 𝒫 Value
    body (ast M) = ⟦ M ⟧
    body (bind a) = body a
    body (clear a) = body a

    bodies : ∀ {bs} → Args bs → Bodies bs
    bodies nil = ptt
    bodies (cons a as) = ⟨ body a , bodies as ⟩

    body-mono : ∀ {b} (a : Arg b) → Mono (body a)
    body-mono (ast M) = ⟦⟧-monotone {{Sem}} M
    body-mono (bind a) = body-mono a
    body-mono (clear a) = body-mono a

    {- the operands and their bodies agree -}
    arg⊆ : ∀ {b} (a : Arg b) {ρ ρ′} → ρ ⊆ₑ ρ′
      → result-rel-pres _⊆_ b (⟦ a ⟧ₐ ρ) (⟪ b ⟫ (body a) ρ′) × result-rel-pres _⊆_ b (⟪ b ⟫ (body a) ρ) (⟦ a ⟧ₐ ρ′)
    arg⊆ (ast M) ρ⊆ = ⟨ lift (⟦⟧-monotone {{Sem}} M ρ⊆) , lift (⟦⟧-monotone {{Sem}} M ρ⊆) ⟩
    arg⊆ (bind a) ρ⊆ = ⟨ (λ X Y X⊆ → proj₁ (arg⊆ a (•-~ _⊆_ ρ⊆ X⊆))) , (λ X Y X⊆ → proj₂ (arg⊆ a (•-~ _⊆_ ρ⊆ X⊆))) ⟩
    arg⊆ (clear a) ρ⊆ = arg⊆ a (λ _ _ d∈ → d∈)

    args⊆ : ∀ {bs} (as : Args bs) {ρ ρ′} → ρ ⊆ₑ ρ′
      → results-rel-pres _⊆_ bs (⟦ as ⟧₊ ρ) (⟪ bs ⟫₊ (bodies as) ρ′)
      × results-rel-pres _⊆_ bs (⟪ bs ⟫₊ (bodies as) ρ) (⟦ as ⟧₊ ρ′)
    args⊆ nil ρ⊆ = ⟨ ptt , ptt ⟩
    args⊆ (cons a as) ρ⊆ = ⟨ ⟨ proj₁ (arg⊆ a ρ⊆) , proj₁ (args⊆ as ρ⊆) ⟩ , ⟨ proj₂ (arg⊆ a ρ⊆) , proj₂ (args⊆ as ρ⊆) ⟩ ⟩

    ok : ∀ {b} (a : Arg b) {ρ NE} → continuous-arg {{Sem}} ρ NE b a → BodyCont b (body a) ρ
    ok (ast M) c = c
    ok (bind a) {NE = NE} c V ne = ok a {NE = extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)} (c V ne)
    ok (clear a) c = ok a {NE = λ _ → ⟨ ω , refl ⟩} c

    oks : ∀ {bs} (as : Args bs) {ρ NE} → continuous-args {{Sem}} ρ NE bs as → OK bs (bodies as) ρ
    oks nil _ = ptt
    oks (cons a as) {NE = NE} ⟨ c , cs ⟩ = ⟨ ⟨ body-mono a , ok a {NE = NE} c ⟩ , oks as {NE = NE} cs ⟩

    cont-op : ∀ op {ρ} {NE : nonempty-env ρ} {v} (as : Args (sig op)) → v ∈ ⟦ op ⦅ as ⦆ ⟧ ρ
      → continuous-args {{Sem}} ρ NE (sig op) as
      → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ as ⦆ ⟧ ρ′
    cont-op op {ρ} {NE} {v} as v∈ cs
        with cont (good op) (bodies as) NE (oks as {NE = NE} cs) v
               (lower (mono (good op) (⟦ as ⟧₊ ρ) (⟪ sig op ⟫₊ (bodies as) ρ) (proj₁ (args⊆ as (λ _ _ d∈ → d∈)))) v v∈)
    ... | ⟨ ρ′ , ⟨ f , ⟨ s , v∈′ ⟩ ⟩ ⟩ =
      ⟨ ρ′ , ⟨ f , ⟨ s , lower (mono (good op) (⟪ sig op ⟫₊ (bodies as) ρ′) (⟦ as ⟧₊ ρ′)
                                 (proj₂ (args⊆ as (λ _ _ d∈ → d∈)))) v v∈′ ⟩ ⟩ ⟩

  Cont-Sem : ContinuousSemantics {Value}
  Cont-Sem = record { Sem = Sem ; continuous-op = λ {op} {ρ} {NE} {v} {args} → cont-op op {ρ} {NE} {v} args }

  {- under P, consistent environments give consistent denotations -}
  con-env : P → ∀ M {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ (⟦ M ⟧ ρ) (⟦ M ⟧ ρ')
  con-env p M = ⟦⟧-pres {{Sem}} (Every _~_) (λ op → consis (good op) p) (Con-⌈⌉ ω) M

  con : P → ∀ M {ρ} → Con-env ρ → Con (⟦ M ⟧ ρ)
  con p M = con-env p M

  open Laws Cont-Sem public
