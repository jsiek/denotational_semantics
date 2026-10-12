{-

  Correctness of remove complex operands (Clos5 → Clos5,
  Compile/RCO.agda): the pass preserves denotations exactly.

    rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ    (ρ nonempty, T and ρ consistent)
    rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ

  The laws behind it:

  - let is strict, and otherwise substitutes the meaning of the
    right-hand side for the variable (let-strict, let-β; let-β uses
    continuity, hence a nonempty environment, and binds a finite part
    of the right-hand side, hence a consistent one);
  - renaming (RenameSem.agda), for the atoms and the operands that
    the lets put under more binders;
  - every operator of a construct whose operands rco names is strict
    (a Strict operator below), so binding an operand first by a strict
    let changes nothing (lift-≃, the let chain, stated once);

  after which each construct is one line, by the congruence of its
  operator.

-}

open import SetsAsPredicates
open import NewDOpSig
open import GraphModel.Domain
open import GraphModel.Ops
open import Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos5
open import Syntax.Rename Op sig using (rename; rename-args; ext)
open import Compiler.Compile.RCO
  using (rco; rco-args; rco-program; atom?; lift; case-on)
open import Compiler.Model.Graph.Sem.Clos5Iswim
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; code; table; ⟦_⟧ₚ; init)
open import Compiler.Model.Graph.Sem.Clos5IswimContinuous
  using (Clos5-Semantics; ⟦⟧[]-monotone; term-continuous; Clos5-con; table-con)
import RenameSem Op sig as RenameSem
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (RRs; nthD-≃; app-≃; pair-≃; car-≃; cdr-≃; prim-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.CompilerCorrect
  using (Same; Same-trans; ≃→Same; compile-same)
open import Compiler.Compile.Pipeline using (compile; compile-mon)
open import Compiler.Model.Graph.Sem.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Compiler.Lang.ISWIM as ISWIM
open import NewEnv using (Env; nonempty-env; extend-nonempty-env)
open import NewSyntaxUtil using (_,,_; ⟩_,,_; Nil)
open import Primitives using (base-rep)

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.RCOCorrect where

{- Laws of the semantics -------------------------------------------------------}

rename-≃ : ∀ T M r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → ⟦ rename r M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ'
rename-≃ T = RenameSem.rename-≃ {{Clos5-Semantics T}}

rename-args-≃ : ∀ T {n} (Ms : Args (replicate n ■)) r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → RRs (replicate n ■) (⟦ rename-args r Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T ] ρ')
rename-args-≃ T {zero} Nil r ρ ρ' rel = ptt
rename-args-≃ T {suc n} (M ,, Ms) r ρ ρ' rel =
  ⟨ up (rename-≃ T M r ρ ρ' rel) , rename-args-≃ T Ms r ρ ρ' rel ⟩

RRs-refl : ∀ {n} Ds → RRs (replicate n ■) Ds Ds
RRs-refl {zero} Ds = ptt
RRs-refl {suc n} ⟨ D , Ds ⟩ = ⟨ up ≃-refl , RRs-refl Ds ⟩

ne-mem : ∀ {V : List Value} {D} → V ≢ [] → mem V ⊆ D → nonempty D
ne-mem V≢[] V⊆ with E≢[]⇒nonempty-mem V≢[]
... | ⟨ v , v∈ ⟩ = ⟨ v , V⊆ v v∈ ⟩

{- A ≃ B when they are equal under P and an element of either gives P -}
strict-≃ : ∀ {P : Set} {A B : 𝒫 Value} → (∀ w → w ∈ A → P) → (∀ w → w ∈ B → P)
  → (P → A ≃ B) → A ≃ B
strict-≃ pA pB eq = ⟨ (λ w w∈ → proj₁ (eq (pA w w∈)) w w∈) , (λ w w∈ → proj₂ (eq (pB w w∈)) w w∈) ⟩

LET : AST → AST → AST
LET M N = let-op ⦅ M ,, ⟩ N ,, Nil ⦆

let-strict : ∀ T M N ρ w → w ∈ ⟦ LET M N ⟧[ T ] ρ → nonempty (⟦ M ⟧[ T ] ρ)
let-strict T M N ρ w ⟨ V , ⟨ _ , ⟨ V⊆ , V≢[] ⟩ ⟩ ⟩ = ne-mem V≢[] V⊆

let-β : ∀ T M N ρ → nonempty-env ρ → nonempty (⟦ M ⟧[ T ] ρ) → Con (⟦ M ⟧[ T ] ρ)
  → ⟦ LET M N ⟧[ T ] ρ ≃ ⟦ N ⟧[ T ] (⟦ M ⟧[ T ] ρ • ρ)
let-β T M N ρ NE neD cD = ⟨ G , H ⟩
  where
  G : ⟦ LET M N ⟧[ T ] ρ ⊆ ⟦ N ⟧[ T ] (⟦ M ⟧[ T ] ρ • ρ)
  G w ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ = ⟦⟧[]-monotone T N ⊆ₑ w w∈
    where ⊆ₑ : ∀ x → (mem V • ρ) x ⊆ (⟦ M ⟧[ T ] ρ • ρ) x
          ⊆ₑ zero = V⊆
          ⊆ₑ (suc x) d d∈ = d∈
  H : ⟦ N ⟧[ T ] (⟦ M ⟧[ T ] ρ • ρ) ⊆ ⟦ LET M N ⟧[ T ] ρ
  H w w∈ with term-continuous T N _ (extend-nonempty-env NE neD) w w∈
  ... | ⟨ Vs , ⟨ fin , w∈' ⟩ ⟩ =
    ⟨ Vs 0 , ⟨ ⟨ ⟦⟧[]-monotone T N ⊆ₑ w w∈' , ⟨ proj₁ (fin 0) , Con⇒≈ (Vs 0) cD (proj₂ (fin 0)) ⟩ ⟩
             , ⟨ proj₂ (fin 0) , proj₁ (fin 0) ⟩ ⟩ ⟩
    where ⊆ₑ : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • ρ) x
          ⊆ₑ zero d d∈ = d∈
          ⊆ₑ (suc x) = proj₂ (fin (suc x))

Λ-≃ : ∀ {F F'} → (∀ V → V ≢ [] → V ≈ V → F (mem V) ≃ F' (mem V)) → Λ ⟨ F , ptt ⟩ ≃ Λ ⟨ F' , ptt ⟩
Λ-≃ {F} {F'} eq = ⟨ G (λ V ne c → proj₁ (eq V ne c)) , G (λ V ne c → proj₂ (eq V ne c)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value} → (∀ V → V ≢ [] → V ≈ V → A (mem V) ⊆ B (mem V))
    → Λ ⟨ A , ptt ⟩ ⊆ Λ ⟨ B , ptt ⟩
  G A⊆ ν tt = tt
  G A⊆ (V ↦ w) ⟨ w∈ , ne ⟩ = ⟨ A⊆ V (proj₁ ne) (proj₂ ne) w w∈ , ne ⟩

{- Strict operators ----------------------------------------------------------------}

NEs : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
NEs zero _ = ⊤
NEs (suc n) ⟨ D , Ds ⟩ = nonempty D × NEs n Ds

{- an operator on n operands, a congruence, empty if one operand is -}
record Strict (n : ℕ) : Set₁ where
  field
    op : Results (𝒫 Value) (replicate n ■) → 𝒫 Value
    cong : ∀ {Ds Es} → RRs (replicate n ■) Ds Es → op Ds ≃ op Es
    strict : ∀ Ds w → w ∈ op Ds → NEs n Ds
open Strict

{- the operator with its first operand fixed to D -}
_▷_ : ∀ {n} → 𝒫 Value → Strict (suc n) → Strict n
D ▷ O = record { op = λ Ds → op O ⟨ D , Ds ⟩
               ; cong = λ eq → cong O ⟨ up ≃-refl , eq ⟩
               ; strict = λ Ds w w∈ → proj₂ (strict O _ w w∈) }

{- ρ' is ρ under k more bound variables -}
Ext : ℕ → Env Value → Env Value → Set
Ext k ρ' ρ = ∀ x → ρ' (k + x) ≃ ρ x

ext-suc : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → Ext (suc k) ρ' ρ
ext-suc {k} {ρ'} {ρ} e x = subst (λ y → ρ' y ≃ ρ x) (+-suc k x) (e (suc x))

ext-top : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → ρ' k ≃ D
ext-top {k} {ρ'} {ρ} {D} e = subst (λ y → ρ' y ≃ D) (+-identityʳ k) (e 0)

{- f k, on atoms in an environment ρ under k more bound variables, means O -}
Denotes : ∀ {n} → Table → (ℕ → Args (replicate n ■) → AST) → Strict n → Env Value → Set₁
Denotes T f O ρ = ∀ k ρ' As → Ext k ρ' ρ → ⟦ f k As ⟧[ T ] ρ' ≃ op O (⟦ As ⟧₊[ T ] ρ')

{- The let chain: binding the complex operands first does not change the
   meaning of a strict operator on them -}
lift-≃ : ∀ T (TC : ∀ k → Con (T k)) {n} f (Ms : Args (replicate n ■)) (O : Strict n) ρ → nonempty-env ρ
  → Con-env ρ → Denotes T f O ρ → ⟦ lift f Ms ⟧[ T ] ρ ≃ op O (⟦ Ms ⟧₊[ T ] ρ)
lift-≃ T TC {zero} f Nil O ρ NE C den = den 0 ρ Nil (λ x → ≃-refl)
lift-≃ T TC {suc n} f (M ,, Ms) O ρ NE C den with atom? M
... | yes _ = lift-≃ T TC (λ k As → f k (rename (k +_) M ,, As)) Ms (⟦ M ⟧[ T ] ρ ▷ O) ρ NE C
  λ k ρ' As e → ≃-trans (den k ρ' _ e) (cong O ⟨ up (rename-≃ T M (k +_) ρ' ρ e) , RRs-refl _ ⟩)
... | no _ = strict-≃ (let-strict T M B ρ) (λ w w∈ → proj₁ (strict O _ w w∈)) λ neD →
  ≃-trans (let-β T M B ρ NE neD cD)
  (≃-trans (lift-≃ T TC f' Ms' (D ▷ O) (D • ρ) (extend-nonempty-env NE neD) (Con-• cD C)
              λ k ρ' As e → ≃-trans (den (suc k) ρ' _ (ext-suc {k} {ρ'} {ρ} {D} e))
                                    (cong O ⟨ up (ext-top {k} {ρ'} {ρ} {D} e) , RRs-refl _ ⟩))
           (cong O ⟨ up ≃-refl , rename-args-≃ T Ms suc (D • ρ) ρ (λ x → ≃-refl) ⟩))
  where D = ⟦ M ⟧[ T ] ρ
        cD = Clos5-con T TC M C
        f' = λ k As → f (suc k) (` k ,, As)
        Ms' = rename-args suc Ms
        B = lift f' Ms'

{- The operators -----------------------------------------------------------------}

app-op : Strict 3
app-op = record { op = λ { ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ → ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩ }
  ; cong = app-≃
  ; strict = λ { _ w ⟨ V , ⟨ ⟨ U , ⟨ f∈ , ⟨ U⊆ , U≢[] ⟩ ⟩ ⟩ , ⟨ V⊆ , V≢[] ⟩ ⟩ ⟩ →
      ⟨ ⟨ _ , f∈ ⟩ , ⟨ ne-mem U≢[] U⊆ , ⟨ ne-mem V≢[] V⊆ , tt ⟩ ⟩ ⟩ } }

pair-op′ : Strict 2
pair-op′ = record { op = pair ; cong = pair-≃ ; strict = S }
  where S : ∀ Ds w → w ∈ pair Ds → NEs 2 Ds
        S _ ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩ = ⟨ ⟨ u , u∈ ⟩ , ⟨ ⟨ v , v∈ ⟩ , tt ⟩ ⟩

car-op : Strict 1
car-op = record { op = car ; cong = car-≃ ; strict = λ { _ u ⟨ v , ∈ ⟩ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ } }

cdr-op : Strict 1
cdr-op = record { op = cdr ; cong = cdr-≃ ; strict = λ { _ v ⟨ u , ∈ ⟩ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ } }

tuple-op : ∀ n → Strict n
tuple-op n = record { op = 𝒯 n ; cong = λ eq → 𝒯-≃ n (nthD-≃ _ _ eq) ; strict = S n }
  where
  all : ∀ n Ds → (∀ j → nonempty (nthD Ds j)) → NEs n Ds
  all zero Ds ne = tt
  all (suc n) ⟨ D , Ds ⟩ ne = ⟨ ne zero , all n Ds (λ j → ne (suc j)) ⟩
  S : ∀ n Ds w → w ∈ 𝒯 n Ds → NEs n Ds
  S zero Ds w _ = tt
  S (suc n) Ds (tup[ i ] d) ⟨ refl , ⟨ _ , ne ⟩ ⟩ = all (suc n) Ds ne

get-op : ∀ {n} (i : Fin n) → Strict 1
get-op i = record { op = proj i ; cong = λ eq → proj-≃ i (lower (proj₁ eq))
                  ; strict = λ _ d ∈ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ }

inl-op′ : Strict 1
inl-op′ = record { op = inl ; cong = λ eq → inl-≃ (lower (proj₁ eq)) ; strict = S }
  where S : ∀ Ds w → w ∈ inl Ds → NEs 1 Ds
        S _ (left v) ∈ = ⟨ ⟨ v , ∈ ⟩ , tt ⟩

inr-op′ : Strict 1
inr-op′ = record { op = inr ; cong = λ eq → inr-≃ (lower (proj₁ eq)) ; strict = S }
  where S : ∀ Ds w → w ∈ inr Ds → NEs 1 Ds
        S _ (right v) ∈ = ⟨ ⟨ v , ∈ ⟩ , tt ⟩

prim-op : ∀ p → Strict 2
prim-op p = record { op = primD p ; cong = prim-≃ p
  ; strict = λ { _ w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ → ⟨ ⟨ _ , n∈ ⟩ , ⟨ ⟨ _ , m∈ ⟩ , tt ⟩ ⟩ } }

{- case on D, with the branches E and F -}
case-op′ : (E F : 𝒫 Value → 𝒫 Value) → Strict 1
case-op′ E F = record { op = λ { ⟨ D , _ ⟩ → 𝒞 ⟨ D , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ }
  ; cong = λ eq → 𝒞-≃ {F = E} {E} {F} {F} (lower (proj₁ eq)) (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl)
  ; strict = λ { _ w (inj₁ ⟨ v , ⟨ V , ⟨ l∈ , _ ⟩ ⟩ ⟩) → ⟨ ⟨ _ , l∈ v (here refl) ⟩ , tt ⟩
               ; _ w (inj₂ ⟨ v , ⟨ V , ⟨ r∈ , _ ⟩ ⟩ ⟩) → ⟨ ⟨ _ , r∈ v (here refl) ⟩ , tt ⟩ } }

{- The pass preserves denotations ---------------------------------------------}

{- a construct c whose operator is O: its operands, under their lets -}
rco-op : ∀ T T' (TC : ∀ k → Con (T k)) {n} (c : Args (replicate n ■) → AST) (O : Strict n)
  (Ms : Args (replicate n ■)) ρ → nonempty-env ρ → Con-env ρ → (∀ T ρ As → ⟦ c As ⟧[ T ] ρ ≃ op O (⟦ As ⟧₊[ T ] ρ))
  → RRs (replicate n ■) (⟦ rco-args Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T' ] ρ)
  → ⟦ lift (λ _ → c) (rco-args Ms) ⟧[ T ] ρ ≃ ⟦ c Ms ⟧[ T' ] ρ
rco-op T T' TC c O Ms ρ NE C den IH =
  ≃-trans (lift-≃ T TC (λ _ → c) (rco-args Ms) O ρ NE C (λ k ρ' As _ → den T ρ' As))
          (≃-trans (cong O IH) (≃-sym (den T' ρ Ms)))

{- with the same meanings in the tables T and T' -}
rco-sem : ∀ T T' → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ M ρ → nonempty-env ρ → Con-env ρ
  → ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ
rco-args-sem : ∀ T T' → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ {n} (Ms : Args (replicate n ■)) ρ
  → nonempty-env ρ → Con-env ρ → RRs (replicate n ■) (⟦ rco-args Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T' ] ρ)

rco-sem T T' TC TT (` x) ρ NE C = ≃-refl
rco-sem T T' TC TT (fun-ref k ⦅ Nil ⦆) ρ NE C = TT k
rco-sem T T' TC TT (app ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (app ⦅_⦆) app-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (lit B k ⦅ Nil ⦆) ρ NE C = ≃-refl
rco-sem T T' TC TT (pair-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (pair-op ⦅_⦆) pair-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (fst-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (fst-op ⦅_⦆) car-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (snd-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (snd-op ⦅_⦆) cdr-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (tuple n ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (tuple n ⦅_⦆) (tuple-op n) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (get i ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (get i ⦅_⦆) (get-op i) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (inl-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (inl-op ⦅_⦆) inl-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (inr-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (inr-op ⦅_⦆) inr-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (prim p ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (prim p ⦅_⦆) (prim-op p) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ NE C =
  ≃-trans (lift-≃ T TC (case-on (rco M) (rco N)) (rco L ,, Nil) O ρ NE C den)
          (cong O ⟨ up (rco-sem T T' TC TT L ρ NE C) , ptt ⟩)
  where
  O = case-op′ (λ X → ⟦ M ⟧[ T' ] (X • ρ)) (λ X → ⟦ N ⟧[ T' ] (X • ρ))
  branch : ∀ k ρ' → Ext k ρ' ρ → ∀ B v V → (v ∷ V) ≈ (v ∷ V)
    → ⟦ rename (ext (k +_)) (rco B) ⟧[ T ] (mem (v ∷ V) • ρ') ≃ ⟦ B ⟧[ T' ] (mem (v ∷ V) • ρ)
  branch k ρ' e B v V c =
    ≃-trans (rename-≃ T (rco B) (ext (k +_)) (mem (v ∷ V) • ρ') (mem (v ∷ V) • ρ)
               λ { zero → ≃-refl ; (suc x) → e x })
            (rco-sem T T' TC TT B (mem (v ∷ V) • ρ) (extend-nonempty-env NE ⟨ v , here refl ⟩) (Con-• (≈⇒Con c) C))
  den : Denotes T (case-on (rco M) (rco N)) O ρ
  den k ρ' (A ,, Nil) e =
    𝒞-≃ {⟦ A ⟧[ T ] ρ'} {⟦ A ⟧[ T ] ρ'} {λ X → ⟦ rename (ext (k +_)) (rco M) ⟧[ T ] (X • ρ')} {λ X → ⟦ M ⟧[ T' ] (X • ρ)}
        {λ X → ⟦ rename (ext (k +_)) (rco N) ⟧[ T ] (X • ρ')} {λ X → ⟦ N ⟧[ T' ] (X • ρ)}
        ≃-refl (branch k ρ' e M) (branch k ρ' e N)
rco-sem T T' TC TT (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ NE C =
  ⋆-≃ (Λ-≃ {λ X → ⟦ rco N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ)} λ V ne c →
         rco-sem T T' TC TT N (mem V • ρ) (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con c) C))
      (rco-sem T T' TC TT M ρ NE C)

rco-args-sem T T' TC TT {zero} Nil ρ NE C = ptt
rco-args-sem T T' TC TT {suc n} (M ,, Ms) ρ NE C =
  ⟨ up (rco-sem T T' TC TT M ρ NE C) , rco-args-sem T T' TC TT Ms ρ NE C ⟩

rco-correct : ∀ T → (∀ k → Con (T k)) → ∀ M ρ → nonempty-env ρ → Con-env ρ
  → ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ
rco-correct T TC = rco-sem T T TC (λ k → ≃-refl)

{- Programs ---------------------------------------------------------------------}

code-≃ : ∀ {T T'} → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ N → code T (rco N) ≃ code T' N
code-≃ {T} {T'} TC TT N =
  Λ-≃ λ V neV cV → Λ-≃ λ U neU cU → rco-sem T T' TC TT N _
    (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV))
                         (E≢[]⇒nonempty-mem neU))
    (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω)))

table-rco : ∀ ds k → table (map rco ds) k ≃ table ds k
table-rco [] k = ≃-refl
table-rco (N ∷ Ns) k with k ≟ length (map rco Ns) | k ≟ length Ns
... | yes _ | yes _ = code-≃ (table-con (map rco Ns)) (table-rco Ns) N
... | no _ | no _ = table-rco Ns k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map rco Ns)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map rco Ns))))

rco-program-correct : ∀ P → ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ
rco-program-correct (program ds M) =
  rco-sem (table (map rco ds)) (table ds) (table-con (map rco ds)) (table-rco ds) M (λ _ → init)
    (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω)

{- The whole compiler, into monadic normal form --------------------------------

  compile-mon = rco-program ∘ compile (Compile/Pipeline.agda): as for
  compile (CompilerCorrect.agda), the result produces the same constants
  as the ISWIM program, and produces something exactly when it does. -}

compile-mon-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ⟦ compile-mon M ⟧ₚ
compile-mon-same M =
  Same-trans (compile-same M) (≃→Same (≃-sym (rco-program-correct (compile M))))

compile-mon-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ⟦ compile-mon M ⟧ₚ)
  × (const c ∈ ⟦ compile-mon M ⟧ₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-mon-correct-const M = proj₁ (compile-mon-same M)

compile-mon-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ⟦ compile-mon M ⟧ₚ)
  × (nonempty ⟦ compile-mon M ⟧ₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-mon-correct-nonempty M = proj₂ (compile-mon-same M)
