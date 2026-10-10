{-

  Correctness of the globalize pass (Clos4 → Clos5).

  Clos4 and Clos5 use the same values: globalize only moves the code of
  each function into a table of global definitions. So the pass preserves
  denotations exactly, which gives both the forward and the backward
  direction. The proof has three parts:

  - glob-shape: the definitions only grow, and the result refers only to
    definitions that exist when it is made (RB);
  - stab: the meaning of a term does not change when the table grows, as
    long as it refers only to the older definitions, because their
    entries in the table do not change (table-ext);
  - glob-sem: ⟦ M ⟧ ρ ≃ ⟦ M' ⟧[ table ds' ] ρ' when ρ and ρ' agree.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos4
import Compiler.Lang.Clos5 as L5
open import Compiler.Model.Graph.Sem.Clos4Iswim
open import Compiler.Model.Graph.Sem.Clos5Iswim
  using (Table; ⟦_⟧[_]; ⟦_⟧ₐ[_]; ⟦_⟧₊[_]; code; table; ⟦_⟧ₚ) renaming (init to init₅)
open import Compiler.Compile.Globalize
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; ρ₀)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect using (⋆-≃; 𝒯-≃; proj-≃; ℒ-≃; ℛ-≃)

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; <-irrefl; n<1+n; m≤n+m; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.GlobalizeCorrect where

{- Environments and results that agree ----------------------------------------}

EnvRel : Env → Env → Set
EnvRel ρ ρ' = ∀ x → ρ x ≃ ρ' x

rel-ext : ∀ {ρ ρ' X X'} → EnvRel ρ ρ' → X ≃ X' → EnvRel (X • ρ) (X' • ρ')
rel-ext rel X≃ zero = X≃
rel-ext rel X≃ (suc x) = rel x

RR : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁
RR = result-rel-pres _≃_

RRs : ∀ bs → Results (𝒫 Value) bs → Results (𝒫 Value) bs → Set₁
RRs = results-rel-pres _≃_

rr-trans : ∀ b (f g h : Result (𝒫 Value) b) → RR b f g → RR b g h → RR b f h
rr-trans ■ f g h p q = lift (≃-trans (lower p) (lower q))
rr-trans (ν b) f g h p q = λ a₁ a₂ r → rr-trans b (f a₁) (g a₂) (h a₂) (p a₁ a₂ r) (q a₂ a₂ ≃-refl)
rr-trans (∁ b) f g h p q = rr-trans b f g h p q

nthD-≃ : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■)) → RRs (replicate n ■) Ds Es
  → ∀ i → nthD Ds i ≃ nthD Es i
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D≃ , _ ⟩ zero = lower D≃
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds≃ ⟩ (suc i) = nthD-≃ Ds Es Ds≃ i

{- Congruence of the operators that Clos4 and Clos5 share ----------------------}

app-≃ : ∀ {L M N L' M' N'} → RRs (■ ∷ ■ ∷ ■ ∷ []) ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ⟨ L' , ⟨ M' , ⟨ N' , ptt ⟩ ⟩ ⟩
  → ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩ ≃ ⋆ ⟨ ⋆ ⟨ L' , ⟨ M' , ptt ⟩ ⟩ , ⟨ N' , ptt ⟩ ⟩
app-≃ ⟨ L≃ , ⟨ M≃ , ⟨ N≃ , _ ⟩ ⟩ ⟩ = ⋆-≃ (⋆-≃ (lower L≃) (lower M≃)) (lower N≃)

pair-≃ : ∀ {D E D' E'} → RRs (■ ∷ ■ ∷ []) ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  → pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
pair-≃ {D} {E} {D'} {E'} ⟨ lift ⟨ D⊆ , D⊇ ⟩ , ⟨ lift ⟨ E⊆ , E⊇ ⟩ , _ ⟩ ⟩ = ⟨ G D⊆ E⊆ , G D⊇ E⊇ ⟩
  where
  G : ∀ {A B A' B'} → A ⊆ A' → B ⊆ B' → pair ⟨ A , ⟨ B , ptt ⟩ ⟩ ⊆ pair ⟨ A' , ⟨ B' , ptt ⟩ ⟩
  G A⊆ B⊆ ⦅ f ∣ ⟨ FV , ⟨ f∈ , ⟨ FV⊆ , ne ⟩ ⟩ ⟩ =
    ⟨ FV , ⟨ A⊆ f f∈ , ⟨ (λ d d∈ → B⊆ d (FV⊆ d d∈)) , ne ⟩ ⟩ ⟩
  G A⊆ B⊆ ∣ FV ⦆ ⟨ f , ⟨ f∈ , ⟨ FV⊆ , ne ⟩ ⟩ ⟩ =
    ⟨ f , ⟨ A⊆ f f∈ , ⟨ (λ d d∈ → B⊆ d (FV⊆ d d∈)) , ne ⟩ ⟩ ⟩

car-≃ : ∀ {D D'} → RRs (■ ∷ []) ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ → car ⟨ D , ptt ⟩ ≃ car ⟨ D' , ptt ⟩
car-≃ ⟨ lift ⟨ D⊆ , D⊇ ⟩ , _ ⟩ = ⟨ (λ f → D⊆ ⦅ f ∣) , (λ f → D⊇ ⦅ f ∣) ⟩

cdr-≃ : ∀ {D D'} → RRs (■ ∷ []) ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ → cdr ⟨ D , ptt ⟩ ≃ cdr ⟨ D' , ptt ⟩
cdr-≃ ⟨ lift ⟨ D⊆ , D⊇ ⟩ , _ ⟩ =
  ⟨ (λ { fv ⟨ FV , ⟨ e∈ , fv∈ ⟩ ⟩ → ⟨ FV , ⟨ D⊆ ∣ FV ⦆ e∈ , fv∈ ⟩ ⟩ })
  , (λ { fv ⟨ FV , ⟨ e∈ , fv∈ ⟩ ⟩ → ⟨ FV , ⟨ D⊇ ∣ FV ⦆ e∈ , fv∈ ⟩ ⟩ }) ⟩

case-≃ : ∀ {D F G D' F' G'}
  → RRs (■ ∷ ν ■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
  → 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
case-≃ {D} {F} {G} {D'} {F'} {G'} ⟨ lift ⟨ D⊆ , D⊇ ⟩ , ⟨ F≃ , ⟨ G≃ , _ ⟩ ⟩ ⟩ = ⟨ H₁ , H₂ ⟩
  where
  H₁ : 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
  H₁ w (inj₁ ⟨ v , ⟨ V , ⟨ all , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊆ (left d) (all d d∈))
                     , proj₁ (lower (F≃ (mem (v ∷ V)) (mem (v ∷ V)) ≃-refl)) w w∈ ⟩ ⟩ ⟩
  H₁ w (inj₂ ⟨ v , ⟨ V , ⟨ all , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊆ (right d) (all d d∈))
                     , proj₁ (lower (G≃ (mem (v ∷ V)) (mem (v ∷ V)) ≃-refl)) w w∈ ⟩ ⟩ ⟩
  H₂ : 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
  H₂ w (inj₁ ⟨ v , ⟨ V , ⟨ all , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊇ (left d) (all d d∈))
                     , proj₂ (lower (F≃ (mem (v ∷ V)) (mem (v ∷ V)) ≃-refl)) w w∈ ⟩ ⟩ ⟩
  H₂ w (inj₂ ⟨ v , ⟨ V , ⟨ all , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → D⊇ (right d) (all d d∈))
                     , proj₂ (lower (G≃ (mem (v ∷ V)) (mem (v ∷ V)) ≃-refl)) w w∈ ⟩ ⟩ ⟩

{- let x = D in F x, which means (λx. F x) D -}
let-≃ : ∀ {D F D' F'} → RRs (■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ptt ⟩ ⟩ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
  → ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ≃ ⋆ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
let-≃ {D} {F} {D'} {F'} ⟨ D≃ , ⟨ F≃ , _ ⟩ ⟩ = ⋆-≃ ⟨ G₁ , G₂ ⟩ (lower D≃)
  where
  G₁ : Λ ⟨ F , ptt ⟩ ⊆ Λ ⟨ F' , ptt ⟩
  G₁ ν tt = tt
  G₁ (V ↦ w) ⟨ w∈ , ne ⟩ = ⟨ proj₁ (lower (F≃ (mem V) (mem V) ≃-refl)) w w∈ , ne ⟩
  G₂ : Λ ⟨ F' , ptt ⟩ ⊆ Λ ⟨ F , ptt ⟩
  G₂ ν tt = tt
  G₂ (V ↦ w) ⟨ w∈ , ne ⟩ = ⟨ proj₂ (lower (F≃ (mem V) (mem V) ≃-refl)) w w∈ , ne ⟩

{- the code of a function: Λ X. Λ Y. F X Y -}
ΛΛ-≃ : ∀ {F F' : 𝒫 Value → 𝒫 Value → 𝒫 Value} → (∀ X Y → F X Y ≃ F' X Y)
  → Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ≃ Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩
ΛΛ-≃ {F} {F'} eq = ⟨ G (λ X Y → proj₁ (eq X Y)) , G (λ X Y → proj₂ (eq X Y)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value → 𝒫 Value} → (∀ X Y → A X Y ⊆ B X Y)
    → Λ ⟨ (λ X → Λ ⟨ A X , ptt ⟩) , ptt ⟩ ⊆ Λ ⟨ (λ X → Λ ⟨ B X , ptt ⟩) , ptt ⟩
  G A⊆ ν tt = tt
  G A⊆ (V ↦ ν) ⟨ tt , neV ⟩ = ⟨ tt , neV ⟩
  G A⊆ (V ↦ (U ↦ x)) ⟨ ⟨ x∈ , neU ⟩ , neV ⟩ = ⟨ ⟨ A⊆ (mem V) (mem U) x x∈ , neU ⟩ , neV ⟩

{- References to older definitions ----------------------------------------------}

RB : ℕ → L5.AST → Set
RB-arg : ∀ {b} → ℕ → L5.Arg b → Set
RB-args : ∀ {bs} → ℕ → L5.Args bs → Set

RB n (L5.` x) = ⊤
RB n (L5.fun-ref k L5.⦅ args ⦆) = k < n
RB n (op L5.⦅ args ⦆) = RB-args n args

RB-arg n (L5.ast M) = RB n M
RB-arg n (L5.bind a) = RB-arg n a
RB-arg n (L5.clear a) = RB-arg n a

RB-args n L5.nil = ⊤
RB-args n (L5.cons a args) = RB-arg n a × RB-args n args

RB-mono : ∀ {n m} (M : L5.AST) → n ≤ m → RB n M → RB m M
RB-arg-mono : ∀ {n m b} (a : L5.Arg b) → n ≤ m → RB-arg n a → RB-arg m a
RB-args-mono : ∀ {n m bs} (args : L5.Args bs) → n ≤ m → RB-args n args → RB-args m args

RB-mono (L5.` x) n≤m tt = tt
RB-mono (L5.fun-ref k L5.⦅ args ⦆) n≤m k<n = <-≤-trans k<n n≤m
RB-mono (L5.app L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.lit B k L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.pair-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.fst-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.snd-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.tuple x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.get x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inl-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inr-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.case-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.let-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r

RB-arg-mono (L5.ast M) n≤m r = RB-mono M n≤m r
RB-arg-mono (L5.bind a) n≤m r = RB-arg-mono a n≤m r
RB-arg-mono (L5.clear a) n≤m r = RB-arg-mono a n≤m r

RB-args-mono L5.nil n≤m tt = tt
RB-args-mono (L5.cons a args) n≤m ⟨ ra , rs ⟩ = ⟨ RB-arg-mono a n≤m ra , RB-args-mono args n≤m rs ⟩

{- The table only grows ----------------------------------------------------------}

Extends : Defs → Defs → Set
Extends ds ds' = Σ[ more ∈ Defs ] ds' ≡ more ++ ds

ext-trans : ∀ {ds₁ ds₂ ds₃} → Extends ds₁ ds₂ → Extends ds₂ ds₃ → Extends ds₁ ds₃
ext-trans {ds₁} ⟨ m₁ , refl ⟩ ⟨ m₂ , refl ⟩ = ⟨ m₂ ++ m₁ , sym (Data.List.Properties.++-assoc m₂ m₁ ds₁) ⟩

ext-length : ∀ {ds ds'} → Extends ds ds' → length ds ≤ length ds'
ext-length {ds} ⟨ more , refl ⟩ = subst (length ds ≤_) (sym (length-++ more)) (m≤n+m (length ds) (length more))

{- the entries for the older definitions do not change -}
table-ext : ∀ (more ds : Defs) k → k < length ds → table (more ++ ds) k ≡ table ds k
table-ext [] ds k k< = refl
table-ext (N ∷ more) ds k k< with k ≟ length (more ++ ds)
... | yes refl = ⊥-elim (<-irrefl refl (<-≤-trans k< (ext-length {ds} ⟨ more , refl ⟩)))
... | no _ = table-ext more ds k k<

table-top : ∀ (N : L5.AST) (Ns : Defs) → table (N ∷ Ns) (length Ns) ≡ code (table Ns) N
table-top N Ns with length Ns ≟ length Ns
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

Agree : ℕ → Table → Table → Set
Agree n T T' = ∀ k → k < n → T k ≃ T' k

agree-ext : ∀ {ds ds'} → Extends ds ds' → Agree (length ds) (table ds) (table ds')
agree-ext {ds} ⟨ more , refl ⟩ k k< = ≃-reflexive (sym (table-ext more ds k k<))

{- Stability: growing the table does not change older meanings ------------------}

stab : ∀ n T T' (M : L5.AST) ρ ρ' → Agree n T T' → RB n M → EnvRel ρ ρ'
  → ⟦ M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ'
stab-arg : ∀ n T T' {b} (a : L5.Arg b) ρ ρ' → Agree n T T' → RB-arg n a → EnvRel ρ ρ'
  → RR b (⟦ a ⟧ₐ[ T ] ρ) (⟦ a ⟧ₐ[ T' ] ρ')
stab-args : ∀ n T T' {bs} (args : L5.Args bs) ρ ρ' → Agree n T T' → RB-args n args
  → EnvRel ρ ρ' → RRs bs (⟦ args ⟧₊[ T ] ρ) (⟦ args ⟧₊[ T' ] ρ')

stab n T T' (L5.` x) ρ ρ' ag r rel = rel x
stab n T T' (L5.fun-ref k L5.⦅ args ⦆) ρ ρ' ag k<n rel = ag k k<n
stab n T T' (L5.app L5.⦅ args ⦆) ρ ρ' ag r rel = app-≃ (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.lit B k L5.⦅ args ⦆) ρ ρ' ag r rel = ≃-refl
stab n T T' (L5.pair-op L5.⦅ args ⦆) ρ ρ' ag r rel = pair-≃ (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.fst-op L5.⦅ args ⦆) ρ ρ' ag r rel = car-≃ (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.snd-op L5.⦅ args ⦆) ρ ρ' ag r rel = cdr-≃ (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.tuple x L5.⦅ args ⦆) ρ ρ' ag r rel =
  𝒯-≃ x (nthD-≃ _ _ (stab-args n T T' args ρ ρ' ag r rel))
stab n T T' (L5.get i L5.⦅ args ⦆) ρ ρ' ag r rel =
  proj-≃ i (lower (proj₁ (stab-args n T T' args ρ ρ' ag r rel)))
stab n T T' (L5.inl-op L5.⦅ args ⦆) ρ ρ' ag r rel =
  ℒ-≃ (lower (proj₁ (stab-args n T T' args ρ ρ' ag r rel)))
stab n T T' (L5.inr-op L5.⦅ args ⦆) ρ ρ' ag r rel =
  ℛ-≃ (lower (proj₁ (stab-args n T T' args ρ ρ' ag r rel)))
stab n T T' (L5.case-op L5.⦅ args ⦆) ρ ρ' ag r rel = case-≃ (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.let-op L5.⦅ args ⦆) ρ ρ' ag r rel = let-≃ (stab-args n T T' args ρ ρ' ag r rel)

stab-arg n T T' (L5.ast M) ρ ρ' ag r rel = lift (stab n T T' M ρ ρ' ag r rel)
stab-arg n T T' (L5.bind a) ρ ρ' ag r rel =
  λ X X' X≃ → stab-arg n T T' a (X • ρ) (X' • ρ') ag r (rel-ext rel X≃)
stab-arg n T T' (L5.clear a) ρ ρ' ag r rel =
  stab-arg n T T' a (λ _ → init₅) (λ _ → init₅) ag r (λ x → ≃-refl)

stab-args n T T' L5.nil ρ ρ' ag tt rel = ptt
stab-args n T T' (L5.cons a args) ρ ρ' ag ⟨ ra , rs ⟩ rel =
  ⟨ stab-arg n T T' a ρ ρ' ag ra rel , stab-args n T T' args ρ ρ' ag rs rel ⟩

{- The shape of the result ------------------------------------------------------}

Shape : Defs → L5.AST × Defs → Set
Shape ds r = Extends ds (proj₂ r) × RB (length (proj₂ r)) (proj₁ r)

glob-shape : ∀ (M : AST) ds → Shape ds (glob M ds)
glob-shape-arg : ∀ {b} (a : Arg b) ds
  → Extends ds (proj₂ (glob-arg a ds)) × RB-arg (length (proj₂ (glob-arg a ds))) (proj₁ (glob-arg a ds))
glob-shape-args : ∀ {bs} (args : Args bs) ds
  → Extends ds (proj₂ (glob-args args ds))
    × RB-args (length (proj₂ (glob-args args ds))) (proj₁ (glob-args args ds))

glob-shape (` x) ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds =
  ⟨ ext-trans (proj₁ (glob-shape N ds)) ⟨ proj₁ (glob N ds) ∷ [] , refl ⟩
  , n<1+n (length (proj₂ (glob N ds))) ⟩
glob-shape (app ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (lit B k ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (pair-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (fst-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (snd-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (tuple n ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (get i ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inl-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inr-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (case-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (let-op ⦅ args ⦆) ds = glob-shape-args args ds

glob-shape-arg (ast M) ds = glob-shape M ds
glob-shape-arg (bind a) ds = glob-shape-arg a ds
glob-shape-arg (clear a) ds = glob-shape-arg a ds

glob-shape-args nil ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape-args (cons a args) ds =
  ⟨ ext-trans (proj₁ sa) (proj₁ ss)
  , ⟨ RB-arg-mono (proj₁ (glob-arg a ds)) (ext-length (proj₁ ss)) (proj₂ sa) , proj₂ ss ⟩ ⟩
  where
  sa = glob-shape-arg a ds
  ss = glob-shape-args args (proj₂ (glob-arg a ds))

{- The main lemma -------------------------------------------------------------}

glob-sem : ∀ (M : AST) ds ρ ρ' → EnvRel ρ ρ'
  → ⟦ M ⟧ ρ ≃ ⟦ proj₁ (glob M ds) ⟧[ table (proj₂ (glob M ds)) ] ρ'
glob-sem-arg : ∀ {b} (a : Arg b) ds ρ ρ' → EnvRel ρ ρ'
  → RR b (⟦ a ⟧ₐ ρ) (⟦ proj₁ (glob-arg a ds) ⟧ₐ[ table (proj₂ (glob-arg a ds)) ] ρ')
glob-sem-args : ∀ {bs} (args : Args bs) ds ρ ρ' → EnvRel ρ ρ'
  → RRs bs (⟦ args ⟧₊ ρ) (⟦ proj₁ (glob-args args ds) ⟧₊[ table (proj₂ (glob-args args ds)) ] ρ')

glob-sem (` x) ds ρ ρ' rel = rel x
glob-sem (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds ρ ρ' rel
  rewrite table-top (proj₁ (glob N ds)) (proj₂ (glob N ds)) =
  ΛΛ-≃ (λ X Y → glob-sem N ds (Y • X • (λ _ → init₅)) (Y • X • (λ _ → init₅)) (λ x → ≃-refl))
glob-sem (app ⦅ args ⦆) ds ρ ρ' rel = app-≃ (glob-sem-args args ds ρ ρ' rel)
glob-sem (lit B k ⦅ args ⦆) ds ρ ρ' rel = ≃-refl
glob-sem (pair-op ⦅ args ⦆) ds ρ ρ' rel = pair-≃ (glob-sem-args args ds ρ ρ' rel)
glob-sem (fst-op ⦅ args ⦆) ds ρ ρ' rel = car-≃ (glob-sem-args args ds ρ ρ' rel)
glob-sem (snd-op ⦅ args ⦆) ds ρ ρ' rel = cdr-≃ (glob-sem-args args ds ρ ρ' rel)
glob-sem (tuple n ⦅ args ⦆) ds ρ ρ' rel = 𝒯-≃ n (nthD-≃ _ _ (glob-sem-args args ds ρ ρ' rel))
glob-sem (get i ⦅ args ⦆) ds ρ ρ' rel = proj-≃ i (lower (proj₁ (glob-sem-args args ds ρ ρ' rel)))
glob-sem (inl-op ⦅ args ⦆) ds ρ ρ' rel = ℒ-≃ (lower (proj₁ (glob-sem-args args ds ρ ρ' rel)))
glob-sem (inr-op ⦅ args ⦆) ds ρ ρ' rel = ℛ-≃ (lower (proj₁ (glob-sem-args args ds ρ ρ' rel)))
glob-sem (case-op ⦅ args ⦆) ds ρ ρ' rel = case-≃ (glob-sem-args args ds ρ ρ' rel)
glob-sem (let-op ⦅ args ⦆) ds ρ ρ' rel = let-≃ (glob-sem-args args ds ρ ρ' rel)

glob-sem-arg (ast M) ds ρ ρ' rel = lift (glob-sem M ds ρ ρ' rel)
glob-sem-arg (bind a) ds ρ ρ' rel =
  λ X X' X≃ → glob-sem-arg a ds (X • ρ) (X' • ρ') (rel-ext rel X≃)
glob-sem-arg (clear a) ds ρ ρ' rel = glob-sem-arg a ds (λ _ → init₅) (λ _ → init₅) (λ x → ≃-refl)

glob-sem-args nil ds ρ ρ' rel = ptt
glob-sem-args {b ∷ bs} (cons a args) ds ρ ρ' rel =
  ⟨ rr-trans b _ _ _ (glob-sem-arg a ds ρ ρ' rel)
      (stab-arg (length ds₁) (table ds₁) (table ds₂) a' ρ' ρ'
         (agree-ext (proj₁ (glob-shape-args args ds₁))) (proj₂ (glob-shape-arg a ds)) (λ x → ≃-refl))
  , glob-sem-args args ds₁ ρ ρ' rel ⟩
  where
  a' = proj₁ (glob-arg a ds)
  ds₁ = proj₂ (glob-arg a ds)
  ds₂ = proj₂ (glob-args args ds₁)

{- The end theorem ------------------------------------------------------------}

globalize-correct : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ globalize M ⟧ₚ
globalize-correct M = glob-sem M [] ρ₀ ρ₀ (λ x → ≃-refl)
