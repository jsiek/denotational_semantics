{-

  Soundness of the ISWIM machine with respect to the graph model with
  errors (Semantics/GraphErr/ISWIM.agda): what the machine computes is in
  the denotation of the program, and when it stops with an error, ω is.

  As in proof/Adequacy/Soundness.agda, each machine state denotes a set
  (𝒮), through denotations of values (𝒱), environments (𝓔) and
  continuations (𝒦), now built from the error-propagating operators, and
  each step can only shrink it (step-⊆). New here:

  * every value denotes a set with a value and without ω (𝒱-val,
    𝒱-noω), so that the binders, which bind no ω, can bind it (app-β);
  * a continuation passes on ω (𝒦-ω): the operands before the hole are
    values, which have values, as the error-propagating operators require
    to pass on an error of a later operand;
  * a state that stops with an error denotes a set that holds ω
    (final-err): an unbound variable means {ω}, and each check of the
    machine (a function, a tuple of the right size, an injection, two
    integers) fails on a value whose denotation has an element of the
    wrong kind.

-}

module proof.Adequacy.GraphErr.Soundness where

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Out; int; bool; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-env; Con-⌈⌉; Con⇒≈; ρ₀)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD; ℬ-consis)
open import proof.Framework.GraphModel.ErrorOps
  using (⋆ᵉ; Λᵉ; 𝒯ᵉ; projᵉ; inlᵉ; inrᵉ; 𝒞ᵉ; letᵉ; val∈; wrong; errs; vals; IsFun; IsInj; IsTup;
         Λᵉ-consis; inlᵉ-consis; inrᵉ-consis; Λᵉ-clean; ℬ-clean; Clean; Clean-NoErr;
         ⋆ᵉ-mono; projᵉ-mono; inlᵉ-mono; inrᵉ-mono; 𝒞ᵉ-mono)
open import proof.Semantics.GraphErr.Prim using (primᵉ; primᵉ-mono; IsInt) renaming (out to dout)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (yes; no; ¬_)
open import Level using (lift; lower)
open import Language.ISWIM
open import proof.Semantics.GraphErr.ISWIM using (⟦_⟧; ⟦_⟧₊; ⟦⟧-monotone; ISWIMᵉ-con-env; body-continuous)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Star; Terminates; next; stop)
open import proof.Framework.ListUtil
open import Semantics.CEK.ISWIM hiding (inl; inr)
import Semantics.CEK.ISWIM as T using (inl; inr)
open import proof.Adequacy.Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length; replicate; reverse; map)
open import Data.List.Base using (reverseAcc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

{- Tuples of sets ------------------------------------------------------------}

At : ∀ {n} → Fin n → List (𝒫 Value) → Value → Set
At {suc n} zero (D ∷ Ds) d = length Ds ≡ n × d ∈ D
At (suc i) (D ∷ Ds) d = At i Ds d
At _ [] d = ⊥

{- every component has a value -}
AllV : List (𝒫 Value) → Set
AllV [] = ⊤
AllV (D ∷ Ds) = val∈ D × AllV Ds

{- an error in the components, left to right -}
errsL : List (𝒫 Value) → Set
errsL [] = ⊥
errsL (D ∷ Ds) = ω ∈ D ⊎ (val∈ D × errsL Ds)

Null : List (𝒫 Value) → Set
Null [] = ⊤
Null (D ∷ Ds) = ⊥

{- the tuple of a list of sets (𝒯ᵉ, for lists) -}
𝒯L : List (𝒫 Value) → 𝒫 Value
𝒯L Ds ω = errsL Ds
𝒯L Ds ⟨⟩ = Null Ds
𝒯L Ds (tup[ i ] d) = At i Ds d × AllV Ds
𝒯L Ds _ = ⊥

infix 4 _⊆L_
_⊆L_ : List (𝒫 Value) → List (𝒫 Value) → Set
[] ⊆L [] = ⊤
(D ∷ Ds) ⊆L (E ∷ Es) = D ⊆ E × Ds ⊆L Es
_ ⊆L _ = ⊥

⊆L-refl : ∀ Ds → Ds ⊆L Ds
⊆L-refl [] = tt
⊆L-refl (D ∷ Ds) = ⟨ (λ d z → z) , ⊆L-refl Ds ⟩

val∈-⊆ : ∀ {D E} → D ⊆ E → val∈ D → val∈ E
val∈-⊆ D⊆ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ d , ⟨ D⊆ d d∈ , d≢ ⟩ ⟩

At-mono : ∀ {n} (i : Fin n) Ds Es d → Ds ⊆L Es → At i Ds d → At i Es d
At-mono {suc n} zero (D ∷ Ds) (E ∷ Es) d ⟨ D⊆ , Ds⊆ ⟩ ⟨ len , d∈ ⟩ =
  ⟨ len' Ds Es Ds⊆ len , D⊆ d d∈ ⟩
  where
  len' : ∀ {m} Ds Es → Ds ⊆L Es → length Ds ≡ m → length Es ≡ m
  len' [] [] _ refl = refl
  len' (D ∷ Ds) (E ∷ Es) ⟨ _ , s ⟩ refl = cong suc (len' Ds Es s refl)
At-mono (suc i) (D ∷ Ds) (E ∷ Es) d ⟨ _ , Ds⊆ ⟩ a = At-mono i Ds Es d Ds⊆ a

AllV-mono : ∀ Ds Es → Ds ⊆L Es → AllV Ds → AllV Es
AllV-mono [] [] _ _ = tt
AllV-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ ⟨ v , vs ⟩ = ⟨ val∈-⊆ D⊆ v , AllV-mono Ds Es s vs ⟩

errsL-mono : ∀ Ds Es → Ds ⊆L Es → errsL Ds → errsL Es
errsL-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ (inj₁ ω∈) = inj₁ (D⊆ ω ω∈)
errsL-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ (inj₂ ⟨ v , e ⟩) = inj₂ ⟨ val∈-⊆ D⊆ v , errsL-mono Ds Es s e ⟩

𝒯L-mono : ∀ Ds Es → Ds ⊆L Es → 𝒯L Ds ⊆ 𝒯L Es
𝒯L-mono Ds Es s ω e = errsL-mono Ds Es s e
𝒯L-mono [] [] s ⟨⟩ tt = tt
𝒯L-mono Ds Es s (tup[ i ] d) ⟨ a , av ⟩ = ⟨ At-mono i Ds Es d s a , AllV-mono Ds Es s av ⟩

{- Denotations of values, environments, continuations and states ------------}

𝒱 : Val → 𝒫 Value
𝒱s : List Val → List (𝒫 Value)
𝓔 : Env → VEnv

𝒱 (clo N γ) = Λᵉ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩
𝒱 (const B k) = ℬ B k ptt
𝒱 (tup vs) = 𝒯L (𝒱s vs)
𝒱 (T.inl v) = inlᵉ ⟨ 𝒱 v , ptt ⟩
𝒱 (T.inr v) = inrᵉ ⟨ 𝒱 v , ptt ⟩

𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝓔 [] x = ⌈ ω ⌉
𝓔 (v ∷ γ) zero = 𝒱 v
𝓔 (v ∷ γ) (suc x) = 𝓔 γ x

rev𝒱 : List Val → List (𝒫 Value) → List (𝒫 Value)
rev𝒱 [] Ds = Ds
rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

⟦_⟧* : List AST → VEnv → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ ρ ∷ ⟦ Ms ⟧* ρ

𝒦 : Cont → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (appL M γ κ) D = 𝒦 κ (⋆ᵉ ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (appR v κ) D = 𝒦 κ (⋆ᵉ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
𝒦 (getK i κ) D = 𝒦 κ (projᵉ i ⟨ D , ptt ⟩)
𝒦 (inlK κ) D = 𝒦 κ (inlᵉ ⟨ D , ptt ⟩)
𝒦 (inrK κ) D = 𝒦 κ (inrᵉ ⟨ D , ptt ⟩)
𝒦 (caseK M N γ κ) D =
  𝒦 κ (𝒞ᵉ ⟨ D , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
𝒦 (primL p M γ κ) D = 𝒦 κ (primᵉ p ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (primR p v κ) D = 𝒦 κ (primᵉ p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
𝒦 (letK N γ κ) D = 𝒦 κ (⋆ᵉ ⟨ 𝒱 (clo N γ) , ⟨ D , ptt ⟩ ⟩)

𝒮 : State → 𝒫 Value
𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ (𝓔 γ))
𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

{- Basic properties ----------------------------------------------------------}

rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
rev𝒱-mono [] Ds Es s = s
rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ (λ d z → z) , s ⟩

{- a hole of an operator, monotone in it -}
hole₁ : ∀ (f : 𝒫 Value → 𝒫 Value) → Set₁
hole₁ f = ∀ {D E} → D ⊆ E → f D ⊆ f E

⋆ᵉ-l : ∀ {E} → hole₁ (λ D → ⋆ᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩)
⋆ᵉ-l {E} {D} {D'} D⊆ = lower (⋆ᵉ-mono ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E , ptt ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩)

⋆ᵉ-r : ∀ {F} → hole₁ (λ D → ⋆ᵉ ⟨ F , ⟨ D , ptt ⟩ ⟩)
⋆ᵉ-r {F} {D} {D'} D⊆ = lower (⋆ᵉ-mono ⟨ F , ⟨ D , ptt ⟩ ⟩ ⟨ F , ⟨ D' , ptt ⟩ ⟩ ⟨ lift (λ d z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩)

prim-l : ∀ p {E} → hole₁ (λ D → primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩)
prim-l p {E} {D} {D'} D⊆ = lower (primᵉ-mono p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E , ptt ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩)

prim-r : ∀ p {F} → hole₁ (λ D → primᵉ p ⟨ F , ⟨ D , ptt ⟩ ⟩)
prim-r p {F} {D} {D'} D⊆ = lower (primᵉ-mono p ⟨ F , ⟨ D , ptt ⟩ ⟩ ⟨ F , ⟨ D' , ptt ⟩ ⟩ ⟨ lift (λ d z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩)

𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (appL M γ κ) D⊆ = 𝒦-mono κ (⋆ᵉ-l D⊆)
𝒦-mono (appR v κ) D⊆ = 𝒦-mono κ (⋆ᵉ-r D⊆)
𝒦-mono (tupK vs Ms γ κ) {D} {E} D⊆ =
  𝒦-mono κ (𝒯L-mono _ _ (rev𝒱-mono vs (D ∷ _) (E ∷ _) ⟨ D⊆ , ⊆L-refl _ ⟩))
𝒦-mono (getK i κ) {D} {E} D⊆ = 𝒦-mono κ (lower (projᵉ-mono i ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (inlK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (inlᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (inrK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (inrᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (caseK M N γ κ) {D} {E} D⊆ =
  𝒦-mono κ (lower (𝒞ᵉ-mono ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ E , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
                          ⟨ lift D⊆ , ⟨ (λ X Y X⊆ → lift (⟦⟧-monotone M (•ext X⊆))) ,
                                      ⟨ (λ X Y X⊆ → lift (⟦⟧-monotone N (•ext X⊆))) , ptt ⟩ ⟩ ⟩))
  where
  F = λ X → ⟦ M ⟧ (X • 𝓔 γ)
  G = λ X → ⟦ N ⟧ (X • 𝓔 γ)
  •ext : ∀ {X Y} → X ⊆ Y → ∀ x → (X • 𝓔 γ) x ⊆ (Y • 𝓔 γ) x
  •ext X⊆ zero = X⊆
  •ext X⊆ (suc x) = λ d z → z
𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (prim-l p D⊆)
𝒦-mono (primR p v κ) D⊆ = 𝒦-mono κ (prim-r p D⊆)
𝒦-mono (letK N γ κ) D⊆ = 𝒦-mono κ (⋆ᵉ-r D⊆)

{- every value denotes a set that has a value and no ω -}
𝒱-noω : ∀ v → ω ∈ 𝒱 v → ⊥
𝒱s-noω : ∀ vs → errsL (𝒱s vs) → ⊥
𝒱-noω (clo N γ) ()
𝒱-noω (const B k) ()
𝒱-noω (tup vs) e = 𝒱s-noω vs e
𝒱-noω (T.inl v) ω∈ = 𝒱-noω v ω∈
𝒱-noω (T.inr v) ω∈ = 𝒱-noω v ω∈
𝒱s-noω (v ∷ vs) (inj₁ ω∈) = 𝒱-noω v ω∈
𝒱s-noω (v ∷ vs) (inj₂ ⟨ _ , e ⟩) = 𝒱s-noω vs e

𝒱-clean : ∀ v → Clean (𝒱 v)
𝒱-clean v d d∈ refl = 𝒱-noω v d∈

length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
length-𝒱s [] = refl
length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)

𝒱-val : ∀ v → val∈ (𝒱 v)
𝒱s-val : ∀ vs → AllV (𝒱s vs)
𝒱-val (clo N γ) = ⟨ ν , ⟨ tt , (λ ()) ⟩ ⟩
𝒱-val (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩ ⟩
𝒱-val (tup []) = ⟨ ⟨⟩ , ⟨ tt , (λ ()) ⟩ ⟩
𝒱-val (tup (v ∷ vs)) =
  ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-val v))
  , ⟨ ⟨ ⟨ length-𝒱s vs , proj₁ (proj₂ (𝒱-val v)) ⟩ , ⟨ 𝒱-val v , 𝒱s-val vs ⟩ ⟩ , (λ ()) ⟩ ⟩
𝒱-val (T.inl v) with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , d≢ ⟩ , (λ ()) ⟩ ⟩
𝒱-val (T.inr v) with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , d≢ ⟩ , (λ ()) ⟩ ⟩
𝒱s-val [] = tt
𝒱s-val (v ∷ vs) = ⟨ 𝒱-val v , 𝒱s-val vs ⟩

𝒱-nonempty : ∀ v → nonempty (𝒱 v)
𝒱-nonempty v = ⟨ proj₁ (𝒱-val v) , proj₁ (proj₂ (𝒱-val v)) ⟩

𝓔-nonempty : ∀ γ → proof.Framework.GraphModel.Env.nonempty-env (𝓔 γ)
𝓔-nonempty [] x = ⟨ ω , refl ⟩
𝓔-nonempty (v ∷ γ) zero = 𝒱-nonempty v
𝓔-nonempty (v ∷ γ) (suc x) = 𝓔-nonempty γ x

𝓔-lookup : ∀ γ x {v} → γ ‼ x ≡ just v → 𝒱 v ⊆ 𝓔 γ x
𝓔-lookup (v ∷ γ) zero refl d d∈ = d∈
𝓔-lookup (v ∷ γ) (suc x) eq = 𝓔-lookup γ x eq

{- an unbound variable means {ω} -}
𝓔-nothing : ∀ γ x → γ ‼ x ≡ nothing → ω ∈ 𝓔 γ x
𝓔-nothing [] x _ = refl
𝓔-nothing (v ∷ γ) (suc x) eq = 𝓔-nothing γ x eq

𝓔-ext : ∀ v γ x → 𝓔 (v ∷ γ) x ⊆ (𝒱 v • 𝓔 γ) x
𝓔-ext v γ zero d d∈ = d∈
𝓔-ext v γ (suc x) d d∈ = d∈

{- β: the body of a function, run on a value, is in the application -}
body-in : ∀ N γ v d → d ∈ ⟦ N ⟧ (𝓔 (v ∷ γ))
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧ (mem V • 𝓔 γ)
body-in N γ v d d∈ =
  body-continuous N (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (𝒱-nonempty v) d
    (⟦⟧-monotone N (𝓔-ext v γ) d d∈)

{- Tuples --------------------------------------------------------------------}

𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
𝒱s-reverseAcc acc [] = refl
𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

At-args : ∀ {n} (args : Args (replicate n ■)) ρ (i : Fin n) d
  → At i (⟦ args→list args ⟧* ρ) d → d ∈ nthD (⟦ args ⟧₊ ρ) i
At-args {suc n} (M ,, args) ρ zero d ⟨ _ , d∈ ⟩ = d∈
At-args {suc n} (M ,, args) ρ (suc i) d a = At-args args ρ i d a

AllV-args : ∀ {n} (args : Args (replicate n ■)) ρ
  → AllV (⟦ args→list args ⟧* ρ) → vals n (⟦ args ⟧₊ ρ)
AllV-args {suc n} (M ,, args) ρ ⟨ v , _ ⟩ zero = v
AllV-args {suc n} (M ,, args) ρ ⟨ _ , vs ⟩ (suc i) = AllV-args args ρ vs i

errsL-args : ∀ {n} (args : Args (replicate n ■)) ρ → errsL (⟦ args→list args ⟧* ρ) → errs n (⟦ args ⟧₊ ρ)
errsL-args {suc n} (M ,, args) ρ (inj₁ ω∈) = inj₁ ω∈
errsL-args {suc n} (M ,, args) ρ (inj₂ ⟨ v , e ⟩) = inj₂ ⟨ v , errsL-args args ρ e ⟩

At-length : ∀ {m} (i : Fin m) Ds d → At i Ds d → length Ds ≡ m
At-length {suc m} zero (D ∷ Ds) d ⟨ len , _ ⟩ = cong suc len
At-length (suc i) (D ∷ Ds) d a = cong suc (At-length i Ds d a)

length-args : ∀ {n} (args : Args (replicate n ■)) ρ → length (⟦ args→list args ⟧* ρ) ≡ n
length-args {zero} Nil ρ = refl
length-args {suc n} (M ,, args) ρ = cong suc (length-args args ρ)

𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯ᵉ n (⟦ args ⟧₊ ρ)
𝒯L-args args ρ ω e = errsL-args args ρ e
𝒯L-args {zero} Nil ρ ⟨⟩ tt = tt
𝒯L-args {zero} Nil ρ (tup[ zero ] d) ⟨ () , _ ⟩
𝒯L-args {zero} Nil ρ (tup[ suc i ] d) ⟨ () , _ ⟩
𝒯L-args {suc n} (M ,, args) ρ ⟨⟩ ()
𝒯L-args {suc n} args ρ (tup[_]_ {m} i d) ⟨ a , av ⟩
    with At-length i _ d a
... | len with subst (λ k → k ≡ m) (length-args args ρ) len
... | refl = ⟨ refl , ⟨ At-args args ρ i d a , AllV-args args ρ av ⟩ ⟩

proj-𝒱s : ∀ {n} (i : Fin n) vs {v} → proj i vs ≡ just v → ∀ d → d ∈ 𝒱 v → At i (𝒱s vs) d
proj-𝒱s {suc n} zero (v ∷ vs) eq d d∈ with has-length n vs in h
proj-𝒱s {suc n} zero (v ∷ vs) refl d d∈ | true =
  ⟨ trans (length-𝒱s vs) (has-length→length n vs h) , d∈ ⟩
proj-𝒱s {suc n} zero (v ∷ vs) () d d∈ | false
proj-𝒱s (suc i) (v ∷ vs) eq d d∈ = proj-𝒱s i vs eq d d∈

{- a projection succeeds on a tuple of the right size -}
proj-length : ∀ {n} (i : Fin n) vs → length vs ≡ n → Σ[ v ∈ Val ] proj i vs ≡ just v
proj-length {suc n} zero (v ∷ vs) refl rewrite length→has-length n vs refl = ⟨ v , refl ⟩
proj-length {suc n} (suc i) (v ∷ vs) refl = proj-length i vs refl

{- Consistency ------------------------------------------------------------------}

AllCon : List (𝒫 Value) → Set
AllCon [] = ⊤
AllCon (D ∷ Ds) = Con D × AllCon Ds

At-con : ∀ {n} (i : Fin n) Ds {d d'} → AllCon Ds → At i Ds d → At i Ds d' → d ~ d'
At-con {suc n} zero (D ∷ Ds) ⟨ c , _ ⟩ ⟨ _ , d∈ ⟩ ⟨ _ , d'∈ ⟩ = c _ _ d∈ d'∈
At-con (suc i) (D ∷ Ds) ⟨ _ , cs ⟩ a a' = At-con i Ds cs a a'

At-[] : ∀ {n} (i : Fin n) {d} → At i [] d → ⊥
At-[] zero ()
At-[] (suc i) ()

𝒯L-con : ∀ Ds → AllCon Ds → (errsL Ds → ⊥) → Con (𝒯L Ds)
𝒯L-con Ds cs ne ω _ e _ = ⊥-elim (ne e)
𝒯L-con Ds cs ne _ ω _ e = ⊥-elim (ne e)
𝒯L-con Ds cs ne ⟨⟩ ⟨⟩ _ _ = tt
𝒯L-con Ds cs ne (tup[ i ] d) (tup[ j ] d') ⟨ a , _ ⟩ ⟨ a' , _ ⟩
    with trans (sym (At-length i Ds d a)) (At-length j Ds d' a')
... | refl with i fin≟ j
... | yes refl = ⟨ refl , inj₂ ⟨ refl , At-con i Ds cs a a' ⟩ ⟩
... | no neq = ⟨ refl , inj₁ neq ⟩
𝒯L-con [] cs ne ⟨⟩ (tup[ i ] d) _ ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
𝒯L-con [] cs ne (tup[ i ] d) ⟨⟩ ⟨ a , _ ⟩ _ = ⊥-elim (At-[] i a)

𝒱-con : ∀ v → Con (𝒱 v)
𝒱s-con : ∀ vs → AllCon (𝒱s vs)
𝓔-con : ∀ γ → Con-env (𝓔 γ)
𝒱-con (clo N γ) = lower (Λᵉ-consis _ _ ⟨ (λ X X' X~ → lift (ISWIMᵉ-con-env N (proof.Framework.GraphModel.Env.•-~ (Every _~_) (𝓔-con γ) X~))) , ptt ⟩)
𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
𝒱-con (tup vs) = 𝒯L-con (𝒱s vs) (𝒱s-con vs) (𝒱s-noω vs)
𝒱-con (T.inl v) = lower (inlᵉ-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (T.inr v) = lower (inrᵉ-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱s-con [] = tt
𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩
𝓔-con [] x = Con-⌈⌉ ω
𝓔-con (v ∷ γ) zero = 𝒱-con v
𝓔-con (v ∷ γ) (suc x) = 𝓔-con γ x

{- Primitives -------------------------------------------------------------------}

int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ 𝒱 v
int-in (const B k) refl = ⟨ refl , refl ⟩

𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
𝒱-out (bool true) (left ⟨⟩) _ = refl
𝒱-out (bool false) (right ⟨⟩) _ = refl
𝒱-out (bool true) (left (tup[ zero ] d)) ⟨ ⟨ () , _ ⟩ , _ ⟩
𝒱-out (bool true) (left (tup[ suc i ] d)) ⟨ ⟨ () , _ ⟩ , _ ⟩
𝒱-out (bool false) (right (tup[ zero ] d)) ⟨ ⟨ () , _ ⟩ , _ ⟩
𝒱-out (bool false) (right (tup[ suc i ] d)) ⟨ ⟨ () , _ ⟩ , _ ⟩

prim-⊆ : ∀ p v w r → δ? p (obs v) (obs w) ≡ just r → 𝒱 (out r) ⊆ primᵉ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
prim-⊆ p v w r e d d∈ with δ?-inv p (obs v) (obs w) e
... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ =
  inj₁ ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , 𝒱-out (δ p n m) d d∈ ⟩ ⟩ ⟩ ⟩

{- Steps shrink the denotation of the state --------------------------------}

app-β : ∀ N γ w → ⟦ N ⟧ (𝓔 (w ∷ γ)) ⊆ ⋆ᵉ ⟨ 𝒱 (clo N γ) , ⟨ 𝒱 w , ptt ⟩ ⟩
app-β N γ w d d∈ with body-in N γ w d d∈
... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
  inj₁ ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , ⟨ Con⇒≈ V (𝒱-con w) V⊆ , noe ⟩ ⟩ ⟩ , ⟨ V⊆ , ⟨ ne , noe ⟩ ⟩ ⟩ ⟩
  where noe = Clean-NoErr V (𝒱-clean w) V⊆

case-inl-β : ∀ M N γ v → ⟦ M ⟧ (𝓔 (v ∷ γ))
  ⊆ 𝒞ᵉ ⟨ inlᵉ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
case-inl-β M N γ v d d∈ with body-in M γ v d d∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
  inj₁ ⟨ u , ⟨ U , ⟨ (λ e e∈ → ⟨ V⊆ e e∈ , 𝒱-clean v e (V⊆ e e∈) ⟩)
       , ⟨ d∈′ , ⟨ Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ , Clean-NoErr (u ∷ U) (𝒱-clean v) V⊆ ⟩ ⟩ ⟩ ⟩ ⟩

case-inr-β : ∀ M N γ v → ⟦ N ⟧ (𝓔 (v ∷ γ))
  ⊆ 𝒞ᵉ ⟨ inrᵉ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
case-inr-β M N γ v d d∈ with body-in N γ v d d∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
  inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ (λ e e∈ → ⟨ V⊆ e e∈ , 𝒱-clean v e (V⊆ e e∈) ⟩)
       , ⟨ d∈′ , ⟨ Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ , Clean-NoErr (u ∷ U) (𝒱-clean v) V⊆ ⟩ ⟩ ⟩ ⟩ ⟩)

step-⊆ : ∀ s {s'} → step s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
step-⊆ (eval (` x) γ κ) eq with γ ‼ x in look
step-⊆ (eval (` x) γ κ) refl | just v = 𝒦-mono κ (𝓔-lookup γ x look)
step-⊆ (eval (` x) γ κ) () | nothing
step-⊆ (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (lit B k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (tuple n ⦅ args ⦆) γ κ) refl d d∈ =
  𝒦-mono κ (𝒯L-args args (𝓔 γ)) d (tuple-next-𝒮 [] (args→list args) γ κ d d∈)
step-⊆ (eval (get i ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (ret v halt) ()
step-⊆ (ret (clo N γ) (appL M γ' κ)) refl d d∈ = d∈
step-⊆ (ret (const B k) (appL M γ' κ)) ()
step-⊆ (ret (tup vs) (appL M γ' κ)) ()
step-⊆ (ret (T.inl v) (appL M γ' κ)) ()
step-⊆ (ret (T.inr v) (appL M γ' κ)) ()
step-⊆ (ret w (appR (clo N γ) κ)) refl = 𝒦-mono κ (app-β N γ w)
step-⊆ (ret w (appR (const B k) κ)) ()
step-⊆ (ret w (appR (tup vs) κ)) ()
step-⊆ (ret w (appR (T.inl v) κ)) ()
step-⊆ (ret w (appR (T.inr v) κ)) ()
step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
  𝒦-mono κ λ d d∈ → inj₁ ⟨ proj-𝒱s i vs p d d∈ , 𝒱s-val vs ⟩
step-⊆ (ret (tup vs) (getK i κ)) () | nothing
step-⊆ (ret (clo N γ) (getK i κ)) ()
step-⊆ (ret (const B k) (getK i κ)) ()
step-⊆ (ret (T.inl v) (getK i κ)) ()
step-⊆ (ret (T.inr v) (getK i κ)) ()
step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
step-⊆ (ret (T.inl v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inl-β M N γ v)
step-⊆ (ret (T.inr v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inr-β M N γ v)
step-⊆ (ret (clo N' γ') (caseK M N γ κ)) ()
step-⊆ (ret (const B k) (caseK M N γ κ)) ()
step-⊆ (ret (tup vs) (caseK M N γ κ)) ()
step-⊆ (ret v (primL p M γ κ)) refl d d∈ = d∈
step-⊆ (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
step-⊆ (ret w (primR p v κ)) refl | just r = 𝒦-mono κ (prim-⊆ p v w r e)
step-⊆ (ret w (primR p v κ)) () | nothing
step-⊆ (ret w (letK N γ κ)) refl = 𝒦-mono κ (app-β N γ w)

↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
↠-⊆ done d d∈ = d∈
↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

{- Errors: a continuation passes on ω -----------------------------------------}

{- a value that is not a closure has a value that is not a function -}
nonclo-wrong : ∀ v → (∀ N γ → v ≢ clo N γ) → wrong IsFun (𝒱 v)
nonclo-wrong (clo N γ) nc = ⊥-elim (nc N γ refl)
nonclo-wrong (const B k) nc = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nonclo-wrong (tup []) nc = ⟨ ⟨⟩ , ⟨ tt , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nonclo-wrong (tup (v ∷ vs)) nc = ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-val v)) , ⟨ proj₁ (proj₂ (𝒱-val (tup (v ∷ vs)))) , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nonclo-wrong (T.inl v) nc with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , d≢ ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nonclo-wrong (T.inr v) nc with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , d≢ ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩

{- an application of a value to ω is ω -}
app-ω : ∀ v {D} → ω ∈ D → ω ∈ ⋆ᵉ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩
app-ω (clo N γ) ω∈ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩
app-ω (const B k) ω∈ = inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (const B k) (λ _ _ ()))) ⟩
app-ω (tup vs) ω∈ = inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (tup vs) (λ _ _ ()))) ⟩
app-ω (T.inl v) ω∈ = inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inl v) (λ _ _ ()))) ⟩
app-ω (T.inr v) ω∈ = inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inr v) (λ _ _ ()))) ⟩

errsL-rev : ∀ vs Ds → errsL Ds → errsL (rev𝒱 vs Ds)
errsL-rev [] Ds e = e
errsL-rev (v ∷ vs) Ds e = errsL-rev vs (𝒱 v ∷ Ds) (inj₂ ⟨ 𝒱-val v , e ⟩)

𝒦-ω : ∀ κ {D} → ω ∈ D → ω ∈ 𝒦 κ D
𝒦-ω halt ω∈ = ω∈
𝒦-ω (appL M γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
𝒦-ω (appR v κ) ω∈ = 𝒦-ω κ (app-ω v ω∈)
𝒦-ω (tupK vs Ms γ κ) {D} ω∈ = 𝒦-ω κ (errsL-rev vs (D ∷ _) (inj₁ ω∈))
𝒦-ω (getK i κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
𝒦-ω (inlK κ) ω∈ = 𝒦-ω κ ω∈
𝒦-ω (inrK κ) ω∈ = 𝒦-ω κ ω∈
𝒦-ω (caseK M N γ κ) ω∈ = 𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩))
𝒦-ω (primL p M γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩)
𝒦-ω (primR p v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ 𝒱-val v , inj₁ ω∈ ⟩) ⟩)
𝒦-ω (letK N γ κ) ω∈ = 𝒦-ω κ (app-ω (clo N γ) ω∈)

{- a projection fails only on a tuple of another size -}
proj-nothing : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → length vs ≢ n
proj-nothing i vs eq len with proj-length i vs len
... | ⟨ v , eq' ⟩ with trans (sym eq) eq'
... | ()

Fin-pos : ∀ {n} → Fin n → n ≢ 0
Fin-pos zero ()
Fin-pos (suc i) ()

tup-wrong : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → wrong (IsTup n) (𝒱 (tup vs))
tup-wrong i [] eq = ⟨ ⟨⟩ , ⟨ tt , ⟨ (λ ()) , (λ z → Fin-pos i z) ⟩ ⟩ ⟩
tup-wrong {n} i (v ∷ vs) eq with 𝒱-val v
... | ⟨ d , ⟨ d∈ , _ ⟩ ⟩ =
  ⟨ tup[_]_ {suc (length vs)} zero d
  , ⟨ ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , 𝒱s-val (v ∷ vs) ⟩ , ⟨ (λ ()) , (λ len → proj-nothing i (v ∷ vs) eq len) ⟩ ⟩ ⟩

{- a value that is not a tuple has a value that is not a tuple -}
nontup-wrong : ∀ {n} v → (∀ vs → v ≢ tup vs) → wrong (IsTup n) (𝒱 v)
nontup-wrong (clo N γ) nt = ⟨ ν , ⟨ tt , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nontup-wrong (const B k) nt = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nontup-wrong (tup vs) nt = ⊥-elim (nt vs refl)
nontup-wrong (T.inl v) nt with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , d≢ ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
nontup-wrong (T.inr v) nt with 𝒱-val v
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , d≢ ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩

{- a value that is not an injection has a value that is not an injection -}
noninj-wrong : ∀ v → (∀ w → v ≢ T.inl w) → (∀ w → v ≢ T.inr w) → wrong IsInj (𝒱 v)
noninj-wrong (clo N γ) _ _ = ⟨ ν , ⟨ tt , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
noninj-wrong (const B k) _ _ = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
noninj-wrong (tup []) _ _ = ⟨ ⟨⟩ , ⟨ tt , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
noninj-wrong (tup (v ∷ vs)) _ _ = ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-val v)) , ⟨ proj₁ (proj₂ (𝒱-val (tup (v ∷ vs)))) , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
noninj-wrong (T.inl v) nl _ = ⊥-elim (nl v refl)
noninj-wrong (T.inr v) _ nr = ⊥-elim (nr v refl)

{- a value whose observation is not an integer has a value that is not one -}
shape-ω : ∀ o → ShapeOf o ω → ⊥
shape-ω (o-const B k) ()
shape-ω o-fun ()
shape-ω (o-tuple os) ()
shape-ω (o-inl o) ()
shape-ω (o-inr o) ()
shape-ω o-error ()


{- the denotation of a value has an element of the shape of its observation -}
𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
𝒱-shape (clo N γ) = ⟨ ν , ⟨ tt , tt ⟩ ⟩
𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
𝒱-shape (tup (v ∷ vs)) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ tup[_]_ {suc (length vs)} zero d
  , ⟨ ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , 𝒱s-val (v ∷ vs) ⟩ , ⟨ length-obs-list vs , sh ⟩ ⟩ ⟩
𝒱-shape (T.inl v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , (λ { refl → shape-ω (obs v) sh }) ⟩ , sh ⟩ ⟩
𝒱-shape (T.inr v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , (λ { refl → shape-ω (obs v) sh }) ⟩ , sh ⟩ ⟩

IsInt-inv : ∀ d → IsInt d → Σ[ n ∈ ℤ ] d ≡ dconst {Int} n
IsInt-inv (dconst {Int} n) _ = ⟨ n , refl ⟩

notint-wrong : ∀ v → (∀ n → obs v ≢ o-const Int n) → wrong IsInt (𝒱 v)
notint-wrong v ni with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ d∈ , ⟨ (λ { refl → shape-ω (obs v) sh }) , (λ isi → G (IsInt-inv d isi)) ⟩ ⟩ ⟩
  where
  G : (Σ[ n ∈ ℤ ] d ≡ dconst {Int} n) → ⊥
  G ⟨ n , refl ⟩ = ni n (shape-const sh)

{- a primitive is undefined when one operand is not an integer -}
δ?-none : ∀ p o₁ o₂ → δ? p o₁ o₂ ≡ nothing
  → (∀ n → o₁ ≢ o-const Int n) ⊎ (∀ m → o₂ ≢ o-const Int m)
δ?-none p (o-const Int n) (o-const Int m) ()
δ?-none p (o-const Int n) o₂ eq = inj₂ (λ m e → G (trans (sym eq) (cong (δ? p (o-const Int n)) e)))
  where
  G : ∀ {r : Out} → nothing ≡ just r → ⊥
  G ()
δ?-none p (o-const Nat k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const 𝔹 k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Unit k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Void k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Blame k) o₂ eq = inj₁ (λ n ())
δ?-none p o-fun o₂ eq = inj₁ (λ n ())
δ?-none p (o-tuple os) o₂ eq = inj₁ (λ n ())
δ?-none p (o-inl o) o₂ eq = inj₁ (λ n ())
δ?-none p (o-inr o) o₂ eq = inj₁ (λ n ())
δ?-none p o-error o₂ eq = inj₁ (λ n ())

prim-ω : ∀ p v w → δ? p (obs v) (obs w) ≡ nothing → ω ∈ primᵉ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
prim-ω p v w e with δ?-none p (obs v) (obs w) e
... | inj₁ ni = inj₂ ⟨ refl , inj₂ (inj₁ ⟨ notint-wrong v ni , 𝒱-val w ⟩) ⟩
... | inj₂ ni = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ 𝒱-val v , notint-wrong w ni ⟩) ⟩

{- Final states ----------------------------------------------------------------}

{- a state that stops with an error denotes a set that holds ω -}
final-err : ∀ s → step s ≡ stop o-error → ω ∈ 𝒮 s
final-err (eval (` x) γ κ) eq with γ ‼ x in look
final-err (eval (` x) γ κ) () | just v
final-err (eval (` x) γ κ) refl | nothing = 𝒦-ω κ (𝓔-nothing γ x look)
final-err (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) ()
final-err (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) ()
final-err (eval (lit B k ⦅ Nil ⦆) γ κ) ()
final-err (eval (tuple n ⦅ args ⦆) γ κ) ()
final-err (eval (get i ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
final-err (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) ()
final-err (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
final-err (ret (clo N γ) halt) ()
final-err (ret (const B k) halt) ()
final-err (ret (tup vs) halt) ()
final-err (ret (T.inl v) halt) ()
final-err (ret (T.inr v) halt) ()
final-err (ret (clo N γ) (appL M γ' κ)) ()
final-err (ret (const B k) (appL M γ' κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (const B k) (λ _ _ ()))) ⟩)
final-err (ret (tup vs) (appL M γ' κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (tup vs) (λ _ _ ()))) ⟩)
final-err (ret (T.inl v) (appL M γ' κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inl v) (λ _ _ ()))) ⟩)
final-err (ret (T.inr v) (appL M γ' κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inr v) (λ _ _ ()))) ⟩)
final-err (ret w (appR (clo N γ) κ)) ()
final-err (ret w (appR (const B k) κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (const B k) (λ _ _ ()))) ⟩)
final-err (ret w (appR (tup vs) κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (tup vs) (λ _ _ ()))) ⟩)
final-err (ret w (appR (T.inl v) κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inl v) (λ _ _ ()))) ⟩)
final-err (ret w (appR (T.inr v) κ)) refl =
  𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₁ (nonclo-wrong (T.inr v) (λ _ _ ()))) ⟩)
final-err (ret v (tupK vs Ms γ κ)) ()
final-err (ret (tup vs) (getK i κ)) eq with proj i vs in p
final-err (ret (tup vs) (getK i κ)) () | just v
final-err (ret (tup vs) (getK i κ)) refl | nothing = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (tup-wrong i vs p) ⟩)
final-err (ret (clo N γ) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nontup-wrong (clo N γ) (λ _ ())) ⟩)
final-err (ret (const B k) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nontup-wrong (const B k) (λ _ ())) ⟩)
final-err (ret (T.inl v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nontup-wrong (T.inl v) (λ _ ())) ⟩)
final-err (ret (T.inr v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nontup-wrong (T.inr v) (λ _ ())) ⟩)
final-err (ret v (inlK κ)) ()
final-err (ret v (inrK κ)) ()
final-err (ret (T.inl v) (caseK M N γ κ)) ()
final-err (ret (T.inr v) (caseK M N γ κ)) ()
final-err (ret (clo N' γ') (caseK M N γ κ)) refl =
  𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₂ (noninj-wrong (clo N' γ') (λ _ ()) (λ _ ())) ⟩))
final-err (ret (const B k) (caseK M N γ κ)) refl =
  𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₂ (noninj-wrong (const B k) (λ _ ()) (λ _ ())) ⟩))
final-err (ret (tup vs) (caseK M N γ κ)) refl =
  𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₂ (noninj-wrong (tup vs) (λ _ ()) (λ _ ())) ⟩))
final-err (ret v (primL p M γ κ)) ()
final-err (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
final-err (ret w (primR p v κ)) () | just r
final-err (ret w (primR p v κ)) refl | nothing = 𝒦-ω κ (prim-ω p v w e)
final-err (ret v (letK N γ κ)) ()

{- a state that stops with an answer has an element of that shape -}
final-shape : ∀ s {o} → step s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
final-shape (ret v halt) refl ans = 𝒱-shape v
final-shape (eval (` x) γ κ) {o} eq ans with γ ‼ x
final-shape (eval (` x) γ κ) () ans | just v
final-shape (eval (` x) γ κ) refl ans | nothing = ⊥-elim (ans refl)
final-shape (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
final-shape (eval (tuple n ⦅ args ⦆) γ κ) () ans
final-shape (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (ret (const B k) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (const B k) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (tup vs) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inl v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inr v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (getK i κ)) eq ans with proj i vs
final-shape (ret (tup vs) (getK i κ)) () ans | just v
final-shape (ret (tup vs) (getK i κ)) refl ans | nothing = ⊥-elim (ans refl)
final-shape (ret (clo N γ) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (clo N' γ') (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
final-shape (ret w (primR p v κ)) () ans | just r
final-shape (ret w (primR p v κ)) refl ans | nothing = ⊥-elim (ans refl)

{- Soundness ------------------------------------------------------------------}

{- a program that terminates with an answer o has an element of the shape
   of o in its denotation -}
soundness : ∀ M {o} → Terminates (sem M) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × ShapeOf o d
soundness M (⟨ s , ⟨ σ , fin ⟩ ⟩) ans
    with final-shape s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ ⟦⟧-monotone M (λ x d z → z) d (↠-⊆ (star→↠ σ) d d∈) , sh ⟩ ⟩

{- a program that stops with an error has ω in its denotation -}
sound-error : ∀ M → Terminates (sem M) o-error → ω ∈ ⟦ M ⟧ ρ₀
sound-error M ⟨ s , ⟨ σ , fin ⟩ ⟩ =
  ⟦⟧-monotone M (λ x d z → z) ω (↠-⊆ (star→↠ σ) ω (final-err s fin))
