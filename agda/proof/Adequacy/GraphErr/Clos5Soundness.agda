{-

  Soundness of the Clos5 machine with respect to the graph model with
  errors (Semantics/GraphErr/Clos5.agda): what the machine computes is in
  the denotation of the (well-formed) program, and when it stops with an
  error, ω is.

  As for ISWIM (Adequacy/GraphErr/Soundness.agda), each machine state
  denotes a set (𝒮), through denotations of values (𝒱), environments
  (𝓔) and continuations (𝒦) built from the error-propagating operators;
  each step can only shrink it (step-⊆), a continuation passes on ω
  (𝒦-ω), and a state that stops with an error denotes a set that holds ω
  (final-err). As for Clos5 in the graph model (Adequacy/Clos5Soundness.agda),
  a code pointer code k denotes the entry for k in the table of the
  program, and calling it is β for its two parameters, where the
  definition is interpreted with the table of the older ones (stab⊆).

  New here, compared to the graph model: every entry of the table holds ν
  (errcode too), so no ν needs to be added to the table (T⁺), and a call
  of a reference to no definition, which the machine stops at with an
  error, denotes ω: errcode's entries X ↦ (Y ↦ ω).

-}

module proof.Adequacy.GraphErr.Clos5Soundness where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Out; int; bool; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-⌈⌉; Con⇒≈)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD; ℬ-consis)
open import proof.Framework.GraphModel.ErrorOps
  using (⋆ᵉ; Λᵉ; 𝒯ᵉ; projᵉ; inlᵉ; inrᵉ; 𝒞ᵉ; letᵉ; callᵉ; pairᵉ; carᵉ; cdrᵉ; errcode;
         val∈; wrong; errs; vals; IsFun; IsInj; IsTup; IsPair; Clean; Clean-NoErr;
         inlᵉ-consis; inrᵉ-consis; pairᵉ-consis;
         ⋆ᵉ-mono; callᵉ-mono; pairᵉ-mono; carᵉ-mono; cdrᵉ-mono; projᵉ-mono; inlᵉ-mono; inrᵉ-mono; 𝒞ᵉ-mono)
open import proof.Semantics.GraphErr.Prim using (primᵉ; primᵉ-mono; IsInt) renaming (out to dout)
open import Language.Clos5
open import Semantics.GraphErr.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; ⟦_⟧ₚ; table; init) renaming (code to codeD)
open import proof.Semantics.GraphErr.Clos5 using (⟦⟧[]-monotone; term-continuous; table-con)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; next; stop)
open import proof.Framework.ListUtil
open import Semantics.CEK.Clos5
open import proof.Compiler.GlobalizeTable using (∷-⊑)
open import proof.Adequacy.Common using (ShapeOf; δ?-inv; has-length→length; shape-const)
open import proof.Adequacy.GraphErr.Soundness
  using (At; AllV; errsL; 𝒯L; _⊆L_; ⊆L-refl; 𝒯L-mono; At-length; AllCon; 𝒯L-con;
         shape-ω; IsInt-inv; δ?-none; Fin-pos)
open import proof.Adequacy.GraphErr.Clos5WF using (WF; DefsWF)
import proof.Adequacy.GraphErr.Clos5Common as Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

≡→⊆ : ∀ {D E : 𝒫 Value} → D ≡ E → D ⊆ E
≡→⊆ refl d d∈ = d∈

id⊆ : ∀ {D : 𝒫 Value} → D ⊆ D
id⊆ d d∈ = d∈

{- the operators, monotone in their operands -}
call⊆ : ∀ {L L' M M' N N'} → L ⊆ L' → M ⊆ M' → N ⊆ N'
  → callᵉ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ⊆ callᵉ ⟨ L' , ⟨ M' , ⟨ N' , ptt ⟩ ⟩ ⟩
call⊆ {L} {L'} {M} {M'} {N} {N'} a b c =
  lower (callᵉ-mono ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ⟨ L' , ⟨ M' , ⟨ N' , ptt ⟩ ⟩ ⟩ ⟨ lift a , ⟨ lift b , ⟨ lift c , ptt ⟩ ⟩ ⟩)

pair⊆ : ∀ {D D' E E'} → D ⊆ D' → E ⊆ E' → pairᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ pairᵉ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
pair⊆ {D} {D'} {E} {E'} a b = lower (pairᵉ-mono ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift a , ⟨ lift b , ptt ⟩ ⟩)

prim⊆ : ∀ p {D D' E E'} → D ⊆ D' → E ⊆ E' → primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ primᵉ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
prim⊆ p {D} {D'} {E} {E'} a b = lower (primᵉ-mono p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift a , ⟨ lift b , ptt ⟩ ⟩)

app⊆ : ∀ {F D E} → D ⊆ E → ⋆ᵉ ⟨ F , ⟨ D , ptt ⟩ ⟩ ⊆ ⋆ᵉ ⟨ F , ⟨ E , ptt ⟩ ⟩
app⊆ {F} {D} {E} a = lower (⋆ᵉ-mono ⟨ F , ⟨ D , ptt ⟩ ⟩ ⟨ F , ⟨ E , ptt ⟩ ⟩ ⟨ lift id⊆ , ⟨ lift a , ptt ⟩ ⟩)

module _ (ds : List AST) (wf : DefsWF ds) where

  open Common ds

  T : Table
  T = table ds

  ⟦_⟧ᵀ : AST → VEnv → 𝒫 Value
  ⟦ M ⟧ᵀ ρ = ⟦ M ⟧[ T ] ρ

  {- Denotations of values, environments, continuations and states ------------}

  𝒱 : Val → 𝒫 Value
  𝒱s : List Val → List (𝒫 Value)

  𝒱 (code k) = T k
  𝒱 (pair v w) = pairᵉ ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  𝒱 (const B k) = ℬ B k ptt
  𝒱 (tup vs) = 𝒯L (𝒱s vs)
  𝒱 (inl v) = inlᵉ ⟨ 𝒱 v , ptt ⟩
  𝒱 (inr v) = inrᵉ ⟨ 𝒱 v , ptt ⟩

  𝒱s [] = []
  𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

  𝓔 : Env → VEnv
  𝓔 [] x = init
  𝓔 (v ∷ γ) zero = 𝒱 v
  𝓔 (v ∷ γ) (suc x) = 𝓔 γ x

  rev𝒱 : List Val → List (𝒫 Value) → List (𝒫 Value)
  rev𝒱 [] Ds = Ds
  rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

  ⟦_⟧* : List AST → VEnv → List (𝒫 Value)
  ⟦ [] ⟧* ρ = []
  ⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ᵀ ρ ∷ ⟦ Ms ⟧* ρ

  𝒦 : Cont → 𝒫 Value → 𝒫 Value
  𝒦 halt D = D
  𝒦 (appF M N γ κ) D = 𝒦 κ (callᵉ ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ⟨ ⟦ N ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩ ⟩)
  𝒦 (appE f N γ κ) D = 𝒦 κ (callᵉ ⟨ 𝒱 f , ⟨ D , ⟨ ⟦ N ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩ ⟩)
  𝒦 (appA f e κ) D = 𝒦 κ (callᵉ ⟨ 𝒱 f , ⟨ 𝒱 e , ⟨ D , ptt ⟩ ⟩ ⟩)
  𝒦 (pairL M γ κ) D = 𝒦 κ (pairᵉ ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (pairR v κ) D = 𝒦 κ (pairᵉ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
  𝒦 (fstK κ) D = 𝒦 κ (carᵉ ⟨ D , ptt ⟩)
  𝒦 (sndK κ) D = 𝒦 κ (cdrᵉ ⟨ D , ptt ⟩)
  𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
  𝒦 (getK i κ) D = 𝒦 κ (projᵉ i ⟨ D , ptt ⟩)
  𝒦 (inlK κ) D = 𝒦 κ (inlᵉ ⟨ D , ptt ⟩)
  𝒦 (inrK κ) D = 𝒦 κ (inrᵉ ⟨ D , ptt ⟩)
  𝒦 (caseK M N γ κ) D =
    𝒦 κ (𝒞ᵉ ⟨ D , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
  𝒦 (primL p M γ κ) D = 𝒦 κ (primᵉ p ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (primR p v κ) D = 𝒦 κ (primᵉ p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
  𝒦 (letK N γ κ) D = 𝒦 κ (letᵉ ⟨ D , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩)

  𝒮 : State → 𝒫 Value
  𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ᵀ (𝓔 γ))
  𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

  {- Basic properties ----------------------------------------------------------}

  rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
  rev𝒱-mono [] Ds Es s = s
  rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ id⊆ , s ⟩

  𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (appF M N γ κ) D⊆ = 𝒦-mono κ (call⊆ D⊆ id⊆ id⊆)
  𝒦-mono (appE f N γ κ) D⊆ = 𝒦-mono κ (call⊆ id⊆ D⊆ id⊆)
  𝒦-mono (appA f e κ) D⊆ = 𝒦-mono κ (call⊆ id⊆ id⊆ D⊆)
  𝒦-mono (pairL M γ κ) D⊆ = 𝒦-mono κ (pair⊆ D⊆ id⊆)
  𝒦-mono (pairR v κ) D⊆ = 𝒦-mono κ (pair⊆ id⊆ D⊆)
  𝒦-mono (fstK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (carᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
  𝒦-mono (sndK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (cdrᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
  𝒦-mono (tupK vs Ms γ κ) {D} {E} D⊆ =
    𝒦-mono κ (𝒯L-mono _ _ (rev𝒱-mono vs (D ∷ _) (E ∷ _) ⟨ D⊆ , ⊆L-refl _ ⟩))
  𝒦-mono (getK i κ) {D} {E} D⊆ = 𝒦-mono κ (lower (projᵉ-mono i ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
  𝒦-mono (inlK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (inlᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
  𝒦-mono (inrK κ) {D} {E} D⊆ = 𝒦-mono κ (lower (inrᵉ-mono ⟨ D , ptt ⟩ ⟨ E , ptt ⟩ ⟨ lift D⊆ , ptt ⟩))
  𝒦-mono (caseK M N γ κ) {D} {E} D⊆ =
    𝒦-mono κ (lower (𝒞ᵉ-mono ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ E , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
                            ⟨ lift D⊆ , ⟨ (λ X Y X⊆ → lift (⟦⟧[]-monotone T M (•ext X⊆))) ,
                                        ⟨ (λ X Y X⊆ → lift (⟦⟧[]-monotone T N (•ext X⊆))) , ptt ⟩ ⟩ ⟩))
    where
    F = λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)
    G = λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)
    •ext : ∀ {X Y} → X ⊆ Y → ∀ x → (X • 𝓔 γ) x ⊆ (Y • 𝓔 γ) x
    •ext X⊆ zero = X⊆
    •ext X⊆ (suc x) = id⊆
  𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (prim⊆ p D⊆ id⊆)
  𝒦-mono (primR p v κ) D⊆ = 𝒦-mono κ (prim⊆ p id⊆ D⊆)
  𝒦-mono (letK N γ κ) D⊆ = 𝒦-mono κ (app⊆ D⊆)

  {- every value denotes a set that has a value, no ω, and is consistent -}
  𝒱-noω : ∀ v → ω ∈ 𝒱 v → ⊥
  𝒱s-noω : ∀ vs → errsL (𝒱s vs) → ⊥
  𝒱-noω (code k) ω∈ = table-clean ds k ω ω∈ refl
  𝒱-noω (pair v w) (inj₁ ω∈) = 𝒱-noω v ω∈
  𝒱-noω (pair v w) (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = 𝒱-noω w ω∈
  𝒱-noω (const B k) ()
  𝒱-noω (tup vs) e = 𝒱s-noω vs e
  𝒱-noω (inl v) ω∈ = 𝒱-noω v ω∈
  𝒱-noω (inr v) ω∈ = 𝒱-noω v ω∈
  𝒱s-noω (v ∷ vs) (inj₁ ω∈) = 𝒱-noω v ω∈
  𝒱s-noω (v ∷ vs) (inj₂ ⟨ _ , e ⟩) = 𝒱s-noω vs e

  𝒱-clean : ∀ v → Clean (𝒱 v)
  𝒱-clean v d d∈ refl = 𝒱-noω v d∈

  length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
  length-𝒱s [] = refl
  length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)

  𝒱-val : ∀ v → val∈ (𝒱 v)
  𝒱s-val : ∀ vs → AllV (𝒱s vs)
  𝒱-val (code k) = ⟨ ν , ⟨ table-ν ds k , (λ ()) ⟩ ⟩
  𝒱-val (pair v w) with 𝒱-val v | 𝒱-val w
  ... | ⟨ a , ⟨ a∈ , a≢ ⟩ ⟩ | ⟨ b , ⟨ b∈ , b≢ ⟩ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ⟨ a∈ , ⟨ b∈ , ⟨ a≢ , b≢ ⟩ ⟩ ⟩ , (λ ()) ⟩ ⟩
  𝒱-val (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩ ⟩
  𝒱-val (tup []) = ⟨ ⟨⟩ , ⟨ tt , (λ ()) ⟩ ⟩
  𝒱-val (tup (v ∷ vs)) =
    ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-val v))
    , ⟨ ⟨ ⟨ length-𝒱s vs , proj₁ (proj₂ (𝒱-val v)) ⟩ , ⟨ 𝒱-val v , 𝒱s-val vs ⟩ ⟩ , (λ ()) ⟩ ⟩
  𝒱-val (inl v) with 𝒱-val v
  ... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , d≢ ⟩ , (λ ()) ⟩ ⟩
  𝒱-val (inr v) with 𝒱-val v
  ... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , d≢ ⟩ , (λ ()) ⟩ ⟩
  𝒱s-val [] = tt
  𝒱s-val (v ∷ vs) = ⟨ 𝒱-val v , 𝒱s-val vs ⟩

  𝒱-nonempty : ∀ v → nonempty (𝒱 v)
  𝒱-nonempty v = ⟨ proj₁ (𝒱-val v) , proj₁ (proj₂ (𝒱-val v)) ⟩

  𝒱-con : ∀ v → Con (𝒱 v)
  𝒱s-con : ∀ vs → AllCon (𝒱s vs)
  𝒱-con (code k) = table-con ds k
  𝒱-con (pair v w) =
    lower (pairᵉ-consis ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟨ lift (𝒱-con v) , ⟨ lift (𝒱-con w) , ptt ⟩ ⟩)
  𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
  𝒱-con (tup vs) = 𝒯L-con (𝒱s vs) (𝒱s-con vs) (𝒱s-noω vs)
  𝒱-con (inl v) = lower (inlᵉ-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱-con (inr v) = lower (inrᵉ-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱s-con [] = tt
  𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩

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

  {- β for one parameter (case, let) -}
  body-in : ∀ N γ v d → d ∈ ⟦ N ⟧ᵀ (𝓔 (v ∷ γ))
    → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧ᵀ (mem V • 𝓔 γ)
  body-in N γ v d d∈ with term-continuous T N (𝓔 (v ∷ γ)) (𝓔-nonempty (v ∷ γ)) d d∈
  ... | ⟨ Vs , ⟨ ok , d∈′ ⟩ ⟩ =
    ⟨ Vs 0 , ⟨ proj₁ (ok 0) , ⟨ proj₂ (ok 0) , ⟦⟧[]-monotone T N G d d∈′ ⟩ ⟩ ⟩
    where
    G : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • 𝓔 γ) x
    G zero d d∈ = d∈
    G (suc x) = proj₂ (ok (suc x))

  {- β for the two parameters of code: calling code k, found in the table
     as B, on the environment e and the argument w -}
  call-⊆ : ∀ k {B} w e → global ds k ≡ just B
    → ⟦ B ⟧ᵀ (𝓔 (w ∷ e ∷ [])) ⊆ callᵉ ⟨ T k , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩
  call-⊆ k {B} w e g d d∈ with global-split k g
  ... | ⟨ Ns , ⟨ p , refl ⟩ ⟩
      with term-continuous (table Ns) B ρ (𝓔-nonempty (w ∷ e ∷ [])) d
             (stab⊆ (length Ns) T (table Ns) B ag (proj₁ (DefsWF-⊑ p wf)) (λ x → id⊆) d d∈)
    where
    ρ = 𝓔 (w ∷ e ∷ [])
    ag : Agree⊆ (length Ns) T (table Ns)
    ag j j< = ≡→⊆ (table-agree (∷-⊑ p) j j<)
  ... | ⟨ Vs , ⟨ ok , d∈′ ⟩ ⟩ =
    inj₁ ⟨ Vs 1 , ⟨ Vs 0 , ⟨ ≡→⊆ (sym (table-at p)) _ in-code
         , ⟨ proj₂ (ok 1) , ⟨ proj₂ (ok 0) , ⟨ proj₁ (ok 1) , ⟨ proj₁ (ok 0) , ⟨ n1 , n0 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    n0 = Clean-NoErr (Vs 0) (𝒱-clean w) (proj₂ (ok 0))
    n1 = Clean-NoErr (Vs 1) (𝒱-clean e) (proj₂ (ok 1))
    G : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • mem (Vs 1) • (λ _ → init)) x
    G zero d d∈ = d∈
    G (suc zero) d d∈ = d∈
    G (suc (suc x)) = proj₂ (ok (suc (suc x)))
    in-code : (Vs 1 ↦ (Vs 0 ↦ d)) ∈ codeD (table Ns) B
    in-code = ⟨ ⟨ ⟦⟧[]-monotone (table Ns) B G d d∈′
                , ⟨ proj₁ (ok 0) , ⟨ Con⇒≈ (Vs 0) (𝒱-con w) (proj₂ (ok 0)) , n0 ⟩ ⟩ ⟩
              , ⟨ proj₁ (ok 1) , ⟨ Con⇒≈ (Vs 1) (𝒱-con e) (proj₂ (ok 1)) , n1 ⟩ ⟩ ⟩

  {- a call of errcode is an error, once its operands have values -}
  errcode-ω : ∀ e w → ω ∈ callᵉ ⟨ errcode , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩
  errcode-ω e w with 𝒱-val e | 𝒱-val w
  ... | ⟨ a , ⟨ a∈ , _ ⟩ ⟩ | ⟨ b , ⟨ b∈ , _ ⟩ ⟩ =
    inj₁ ⟨ a ∷ [] , ⟨ b ∷ [] , ⟨ entry , ⟨ A⊆ , ⟨ B⊆ , ⟨ (λ ()) , ⟨ (λ ()) , ⟨ nA , nB ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    A⊆ : mem (a ∷ []) ⊆ 𝒱 e
    A⊆ d (here refl) = a∈
    A⊆ d (there ())
    B⊆ : mem (b ∷ []) ⊆ 𝒱 w
    B⊆ d (here refl) = b∈
    B⊆ d (there ())
    nA = Clean-NoErr (a ∷ []) (𝒱-clean e) A⊆
    nB = Clean-NoErr (b ∷ []) (𝒱-clean w) B⊆
    entry : ((a ∷ []) ↦ ((b ∷ []) ↦ ω)) ∈ errcode
    entry = ⟨ ⟨ refl , ⟨ (λ ()) , ⟨ Con⇒≈ (b ∷ []) (𝒱-con w) B⊆ , nB ⟩ ⟩ ⟩
            , ⟨ (λ ()) , ⟨ Con⇒≈ (a ∷ []) (𝒱-con e) A⊆ , nA ⟩ ⟩ ⟩

  {- Tuples --------------------------------------------------------------------}

  𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
  𝒱s-reverseAcc acc [] = refl
  𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

  tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
  tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
  tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

  At-args : ∀ {n} (args : Args (replicate n ■)) ρ (i : Fin n) d
    → At i (⟦ args→list args ⟧* ρ) d → d ∈ nthD (⟦ args ⟧₊[ T ] ρ) i
  At-args {suc n} (M ,, args) ρ zero d ⟨ _ , d∈ ⟩ = d∈
  At-args {suc n} (M ,, args) ρ (suc i) d a = At-args args ρ i d a

  AllV-args : ∀ {n} (args : Args (replicate n ■)) ρ
    → AllV (⟦ args→list args ⟧* ρ) → vals n (⟦ args ⟧₊[ T ] ρ)
  AllV-args {suc n} (M ,, args) ρ ⟨ v , _ ⟩ zero = v
  AllV-args {suc n} (M ,, args) ρ ⟨ _ , vs ⟩ (suc i) = AllV-args args ρ vs i

  errsL-args : ∀ {n} (args : Args (replicate n ■)) ρ → errsL (⟦ args→list args ⟧* ρ) → errs n (⟦ args ⟧₊[ T ] ρ)
  errsL-args {suc n} (M ,, args) ρ (inj₁ ω∈) = inj₁ ω∈
  errsL-args {suc n} (M ,, args) ρ (inj₂ ⟨ v , e ⟩) = inj₂ ⟨ v , errsL-args args ρ e ⟩

  length-args : ∀ {n} (args : Args (replicate n ■)) ρ → length (⟦ args→list args ⟧* ρ) ≡ n
  length-args {zero} Nil ρ = refl
  length-args {suc n} (M ,, args) ρ = cong suc (length-args args ρ)

  𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯ᵉ n (⟦ args ⟧₊[ T ] ρ)
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

  {- the denotation of a value has an element of the shape of its observation -}
  𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
  𝒱-shape (code k) = ⟨ ν , ⟨ table-ν ds k , tt ⟩ ⟩
  𝒱-shape (pair v w) with 𝒱-val v | 𝒱-val w
  ... | ⟨ a , ⟨ a∈ , a≢ ⟩ ⟩ | ⟨ b , ⟨ b∈ , b≢ ⟩ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ⟨ a∈ , ⟨ b∈ , ⟨ a≢ , b≢ ⟩ ⟩ ⟩ , tt ⟩ ⟩
  𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
  𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
  𝒱-shape (tup (v ∷ vs)) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
    ⟨ tup[_]_ {suc (length vs)} zero d
    , ⟨ ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , 𝒱s-val (v ∷ vs) ⟩ , ⟨ length-obs-list vs , sh ⟩ ⟩ ⟩
    where
    length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
    length-obs-list [] = refl
    length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)
  𝒱-shape (inl v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ ⟨ d∈ , (λ { refl → shape-ω (obs v) sh }) ⟩ , sh ⟩ ⟩
  𝒱-shape (inr v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ ⟨ d∈ , (λ { refl → shape-ω (obs v) sh }) ⟩ , sh ⟩ ⟩

  notint-wrong : ∀ v → (∀ n → obs v ≢ o-const Int n) → wrong IsInt (𝒱 v)
  notint-wrong v ni with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
    ⟨ d , ⟨ d∈ , ⟨ (λ { refl → shape-ω (obs v) sh }) , (λ isi → G (IsInt-inv d isi)) ⟩ ⟩ ⟩
    where
    G : (Σ[ n ∈ ℤ ] d ≡ dconst {Int} n) → ⊥
    G ⟨ n , refl ⟩ = ni n (shape-const sh)

  prim-ω : ∀ p v w → δ? p (obs v) (obs w) ≡ nothing → ω ∈ primᵉ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  prim-ω p v w e with δ?-none p (obs v) (obs w) e
  ... | inj₁ ni = inj₂ ⟨ refl , inj₂ (inj₁ ⟨ notint-wrong v ni , 𝒱-val w ⟩) ⟩
  ... | inj₂ ni = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ 𝒱-val v , notint-wrong w ni ⟩) ⟩

  {- Steps shrink the denotation of the state --------------------------------}

  case-inl-β : ∀ M N γ v → ⟦ M ⟧ᵀ (𝓔 (v ∷ γ))
    ⊆ 𝒞ᵉ ⟨ inlᵉ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  case-inl-β M N γ v d d∈ with body-in M γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
    inj₁ ⟨ u , ⟨ U , ⟨ (λ e e∈ → ⟨ V⊆ e e∈ , 𝒱-clean v e (V⊆ e e∈) ⟩)
         , ⟨ d∈′ , ⟨ Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ , Clean-NoErr (u ∷ U) (𝒱-clean v) V⊆ ⟩ ⟩ ⟩ ⟩ ⟩

  case-inr-β : ∀ M N γ v → ⟦ N ⟧ᵀ (𝓔 (v ∷ γ))
    ⊆ 𝒞ᵉ ⟨ inrᵉ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  case-inr-β M N γ v d d∈ with body-in N γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
    inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ (λ e e∈ → ⟨ V⊆ e e∈ , 𝒱-clean v e (V⊆ e e∈) ⟩)
         , ⟨ d∈′ , ⟨ Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ , Clean-NoErr (u ∷ U) (𝒱-clean v) V⊆ ⟩ ⟩ ⟩ ⟩ ⟩)

  let-β : ∀ N γ v → ⟦ N ⟧ᵀ (𝓔 (v ∷ γ)) ⊆ letᵉ ⟨ 𝒱 v , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩
  let-β N γ v d d∈ with body-in N γ v d d∈
  ... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
    inj₁ ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , ⟨ Con⇒≈ V (𝒱-con v) V⊆ , noe ⟩ ⟩ ⟩ , ⟨ V⊆ , ⟨ ne , noe ⟩ ⟩ ⟩ ⟩
    where noe = Clean-NoErr V (𝒱-clean v) V⊆

  step-⊆ : ∀ s {s'} → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
  step-⊆ (eval (` x) γ κ) eq with γ ‼ x in look
  step-⊆ (eval (` x) γ κ) refl | just v = 𝒦-mono κ (𝓔-lookup γ x look)
  step-⊆ (eval (` x) γ κ) () | nothing
  step-⊆ (eval (fun-ref k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (lit B k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (tuple n ⦅ args ⦆) γ κ) refl d d∈ =
    𝒦-mono κ (𝒯L-args args (𝓔 γ)) d (tuple-next-𝒮 [] (args→list args) γ κ d d∈)
  step-⊆ (eval (get i ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (ret v halt) ()
  step-⊆ (ret f (appF M N γ κ)) refl d d∈ = d∈
  step-⊆ (ret e (appE f N γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (appA (code k) e κ)) eq with global ds k in g
  step-⊆ (ret w (appA (code k) e κ)) refl | just B = 𝒦-mono κ (call-⊆ k w e g)
  step-⊆ (ret w (appA (code k) e κ)) () | nothing
  step-⊆ (ret w (appA (pair _ _) e κ)) ()
  step-⊆ (ret w (appA (const B k) e κ)) ()
  step-⊆ (ret w (appA (tup vs) e κ)) ()
  step-⊆ (ret w (appA (inl v) e κ)) ()
  step-⊆ (ret w (appA (inr v) e κ)) ()
  step-⊆ (ret v (pairL M γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (pairR v κ)) refl d d∈ = d∈
  step-⊆ (ret (pair v w) (fstK κ)) refl with 𝒱-val w
  ... | ⟨ b , ⟨ b∈ , b≢ ⟩ ⟩ = 𝒦-mono κ λ d d∈ → inj₁ ⟨ b , ⟨ d∈ , ⟨ b∈ , ⟨ 𝒱-clean v d d∈ , b≢ ⟩ ⟩ ⟩ ⟩
  step-⊆ (ret (code k) (fstK κ)) ()
  step-⊆ (ret (const B k) (fstK κ)) ()
  step-⊆ (ret (tup vs) (fstK κ)) ()
  step-⊆ (ret (inl v) (fstK κ)) ()
  step-⊆ (ret (inr v) (fstK κ)) ()
  step-⊆ (ret (pair v w) (sndK κ)) refl with 𝒱-val v
  ... | ⟨ a , ⟨ a∈ , a≢ ⟩ ⟩ = 𝒦-mono κ λ d d∈ → inj₁ ⟨ a , ⟨ a∈ , ⟨ d∈ , ⟨ a≢ , 𝒱-clean w d d∈ ⟩ ⟩ ⟩ ⟩
  step-⊆ (ret (code k) (sndK κ)) ()
  step-⊆ (ret (const B k) (sndK κ)) ()
  step-⊆ (ret (tup vs) (sndK κ)) ()
  step-⊆ (ret (inl v) (sndK κ)) ()
  step-⊆ (ret (inr v) (sndK κ)) ()
  step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
  step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
  step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
    𝒦-mono κ λ d d∈ → inj₁ ⟨ proj-𝒱s i vs p d d∈ , 𝒱s-val vs ⟩
  step-⊆ (ret (tup vs) (getK i κ)) () | nothing
  step-⊆ (ret (code k) (getK i κ)) ()
  step-⊆ (ret (pair v w) (getK i κ)) ()
  step-⊆ (ret (const B k) (getK i κ)) ()
  step-⊆ (ret (inl v) (getK i κ)) ()
  step-⊆ (ret (inr v) (getK i κ)) ()
  step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
  step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
  step-⊆ (ret (inl v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inl-β M N γ v)
  step-⊆ (ret (inr v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inr-β M N γ v)
  step-⊆ (ret (code k) (caseK M N γ κ)) ()
  step-⊆ (ret (pair v w) (caseK M N γ κ)) ()
  step-⊆ (ret (const B k) (caseK M N γ κ)) ()
  step-⊆ (ret (tup vs) (caseK M N γ κ)) ()
  step-⊆ (ret v (letK N γ κ)) refl = 𝒦-mono κ (let-β N γ v)
  step-⊆ (ret v (primL p M γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
  step-⊆ (ret w (primR p v κ)) refl | just r = 𝒦-mono κ (prim-⊆ p v w r e)
  step-⊆ (ret w (primR p v κ)) () | nothing

  ↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
  ↠-⊆ done d d∈ = d∈
  ↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

  {- Errors: a continuation passes on ω -----------------------------------------}

  errsL-rev : ∀ vs Ds → errsL Ds → errsL (rev𝒱 vs Ds)
  errsL-rev [] Ds e = e
  errsL-rev (v ∷ vs) Ds e = errsL-rev vs (𝒱 v ∷ Ds) (inj₂ ⟨ 𝒱-val v , e ⟩)

  𝒦-ω : ∀ κ {D} → ω ∈ D → ω ∈ 𝒦 κ D
  𝒦-ω halt ω∈ = ω∈
  𝒦-ω (appF M N γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩)
  𝒦-ω (appE f N γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ 𝒱-val f , inj₁ ω∈ ⟩) ⟩)
  𝒦-ω (appA f e κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ 𝒱-val f , inj₂ ⟨ 𝒱-val e , inj₁ ω∈ ⟩ ⟩) ⟩)
  𝒦-ω (pairL M γ κ) ω∈ = 𝒦-ω κ (inj₁ ω∈)
  𝒦-ω (pairR v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-val v , inj₁ ω∈ ⟩)
  𝒦-ω (fstK κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
  𝒦-ω (sndK κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
  𝒦-ω (tupK vs Ms γ κ) {D} ω∈ = 𝒦-ω κ (errsL-rev vs (D ∷ _) (inj₁ ω∈))
  𝒦-ω (getK i κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
  𝒦-ω (inlK κ) ω∈ = 𝒦-ω κ ω∈
  𝒦-ω (inrK κ) ω∈ = 𝒦-ω κ ω∈
  𝒦-ω (caseK M N γ κ) ω∈ = 𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩))
  𝒦-ω (primL p M γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩)
  𝒦-ω (primR p v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ 𝒱-val v , inj₁ ω∈ ⟩) ⟩)
  𝒦-ω (letK N γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩)

  {- The machine's checks fail on values whose denotations have an element
     of the wrong kind ---------------------------------------------------------}

  pair-elem : ∀ v w → Σ[ a ∈ Value ] Σ[ b ∈ Value ] ⦅ a , b ⦆ ∈ 𝒱 (pair v w)
  pair-elem v w with 𝒱-val v | 𝒱-val w
  ... | ⟨ a , ⟨ a∈ , a≢ ⟩ ⟩ | ⟨ b , ⟨ b∈ , b≢ ⟩ ⟩ = ⟨ a , ⟨ b , ⟨ a∈ , ⟨ b∈ , ⟨ a≢ , b≢ ⟩ ⟩ ⟩ ⟩ ⟩

  tup-elem : ∀ vs → Σ[ d ∈ Value ] d ∈ 𝒱 (tup vs) × (d ≡ ⟨⟩ ⊎ Σ[ n ∈ ℕ ] Σ[ i ∈ Fin n ] Σ[ d' ∈ Value ] d ≡ tup[ i ] d')
  tup-elem [] = ⟨ ⟨⟩ , ⟨ tt , inj₁ refl ⟩ ⟩
  tup-elem (v ∷ vs) =
    ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-val v)) , ⟨ proj₁ (proj₂ (𝒱-val (tup (v ∷ vs))))
    , inj₂ ⟨ suc (length vs) , ⟨ zero , ⟨ proj₁ (𝒱-val v) , refl ⟩ ⟩ ⟩ ⟩ ⟩

  inl-elem : ∀ v → Σ[ d ∈ Value ] left d ∈ 𝒱 (inl v)
  inl-elem v with 𝒱-val v
  ... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩

  inr-elem : ∀ v → Σ[ d ∈ Value ] right d ∈ 𝒱 (inr v)
  inr-elem v with 𝒱-val v
  ... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩

  {- a value that is not code has a value that is not a function -}
  noncode-wrong : ∀ v → (∀ k → v ≢ code k) → wrong IsFun (𝒱 v)
  noncode-wrong (code k) nc = ⊥-elim (nc k refl)
  noncode-wrong (pair v w) nc with pair-elem v w
  ... | ⟨ a , ⟨ b , ab∈ ⟩ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ab∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noncode-wrong (const B k) nc = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noncode-wrong (tup vs) nc with tup-elem vs
  ... | ⟨ d , ⟨ d∈ , inj₁ refl ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  ... | ⟨ d , ⟨ d∈ , inj₂ ⟨ _ , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noncode-wrong (inl v) nc with inl-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noncode-wrong (inr v) nc with inr-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩

  {- a value that is not a pair has a value that is not a pair -}
  nonpair-wrong : ∀ v → (∀ a b → v ≢ pair a b) → wrong IsPair (𝒱 v)
  nonpair-wrong (code k) np = ⟨ ν , ⟨ table-ν ds k , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nonpair-wrong (pair v w) np = ⊥-elim (np v w refl)
  nonpair-wrong (const B k) np = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nonpair-wrong (tup vs) np with tup-elem vs
  ... | ⟨ d , ⟨ d∈ , inj₁ refl ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  ... | ⟨ d , ⟨ d∈ , inj₂ ⟨ _ , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nonpair-wrong (inl v) np with inl-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nonpair-wrong (inr v) np with inr-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩

  {- a projection fails only on a tuple of another size -}
  proj-length : ∀ {n} (i : Fin n) vs → length vs ≡ n → Σ[ v ∈ Val ] proj i vs ≡ just v
  proj-length {suc n} zero (v ∷ vs) refl rewrite proof.Adequacy.Common.length→has-length n vs refl = ⟨ v , refl ⟩
  proj-length {suc n} (suc i) (v ∷ vs) refl = proj-length i vs refl

  proj-nothing : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → length vs ≢ n
  proj-nothing i vs eq len with proj-length i vs len
  ... | ⟨ v , eq' ⟩ with trans (sym eq) eq'
  ... | ()

  tup-wrong : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → wrong (IsTup n) (𝒱 (tup vs))
  tup-wrong i [] eq = ⟨ ⟨⟩ , ⟨ tt , ⟨ (λ ()) , (λ z → Fin-pos i z) ⟩ ⟩ ⟩
  tup-wrong {n} i (v ∷ vs) eq with 𝒱-val v
  ... | ⟨ d , ⟨ d∈ , _ ⟩ ⟩ =
    ⟨ tup[_]_ {suc (length vs)} zero d
    , ⟨ ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , 𝒱s-val (v ∷ vs) ⟩ , ⟨ (λ ()) , (λ len → proj-nothing i (v ∷ vs) eq len) ⟩ ⟩ ⟩

  {- a value that is not a tuple has a value that is not a tuple -}
  nontup-wrong : ∀ {n} v → (∀ vs → v ≢ tup vs) → wrong (IsTup n) (𝒱 v)
  nontup-wrong (code k) nt = ⟨ ν , ⟨ table-ν ds k , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nontup-wrong (pair v w) nt with pair-elem v w
  ... | ⟨ a , ⟨ b , ab∈ ⟩ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ab∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nontup-wrong (const B k) nt = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nontup-wrong (tup vs) nt = ⊥-elim (nt vs refl)
  nontup-wrong (inl v) nt with inl-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  nontup-wrong (inr v) nt with inr-elem v
  ... | ⟨ d , d∈ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩

  {- a value that is not an injection has a value that is not an injection -}
  noninj-wrong : ∀ v → (∀ w → v ≢ inl w) → (∀ w → v ≢ inr w) → wrong IsInj (𝒱 v)
  noninj-wrong (code k) _ _ = ⟨ ν , ⟨ table-ν ds k , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noninj-wrong (pair v w) _ _ with pair-elem v w
  ... | ⟨ a , ⟨ b , ab∈ ⟩ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ab∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noninj-wrong (const B k) _ _ = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noninj-wrong (tup vs) _ _ with tup-elem vs
  ... | ⟨ d , ⟨ d∈ , inj₁ refl ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  ... | ⟨ d , ⟨ d∈ , inj₂ ⟨ _ , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , ⟨ (λ ()) , (λ ()) ⟩ ⟩ ⟩
  noninj-wrong (inl v) nl _ = ⊥-elim (nl v refl)
  noninj-wrong (inr v) _ nr = ⊥-elim (nr v refl)

  {- calling a value that is not code is an error, once the operands have values -}
  call-wrong : ∀ f e w κ → (∀ k → f ≢ code k) → ω ∈ 𝒦 κ (callᵉ ⟨ 𝒱 f , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩)
  call-wrong f e w κ nc = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ ⟨ noncode-wrong f nc , ⟨ 𝒱-val e , 𝒱-val w ⟩ ⟩ ⟩)

  car-wrong : ∀ v κ → (∀ a b → v ≢ pair a b) → ω ∈ 𝒦 κ (carᵉ ⟨ 𝒱 v , ptt ⟩)
  car-wrong v κ np = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nonpair-wrong v np) ⟩)

  cdr-wrong : ∀ v κ → (∀ a b → v ≢ pair a b) → ω ∈ 𝒦 κ (cdrᵉ ⟨ 𝒱 v , ptt ⟩)
  cdr-wrong v κ np = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nonpair-wrong v np) ⟩)

  get-wrong : ∀ {n} (i : Fin n) v κ → (∀ vs → v ≢ tup vs) → ω ∈ 𝒦 κ (projᵉ i ⟨ 𝒱 v , ptt ⟩)
  get-wrong i v κ nt = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (nontup-wrong v nt) ⟩)

  case-wrong : ∀ v M N γ κ → (∀ w → v ≢ inl w) → (∀ w → v ≢ inr w) → ω ∈ 𝒮 (ret v (caseK M N γ κ))
  case-wrong v M N γ κ nl nr = 𝒦-ω κ (inj₂ (inj₂ ⟨ refl , inj₂ (noninj-wrong v nl nr) ⟩))

  {- Final states ----------------------------------------------------------------}

  {- a state that stops with an error denotes a set that holds ω -}
  final-err : ∀ s → step ds s ≡ stop o-error → ω ∈ 𝒮 s
  final-err (eval (` x) γ κ) eq with γ ‼ x in look
  final-err (eval (` x) γ κ) () | just v
  final-err (eval (` x) γ κ) refl | nothing = 𝒦-ω κ (𝓔-nothing γ x look)
  final-err (eval (fun-ref k ⦅ Nil ⦆) γ κ) ()
  final-err (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) ()
  final-err (eval (lit B k ⦅ Nil ⦆) γ κ) ()
  final-err (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) ()
  final-err (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) ()
  final-err (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) ()
  final-err (eval (tuple n ⦅ args ⦆) γ κ) ()
  final-err (eval (get i ⦅ M ,, Nil ⦆) γ κ) ()
  final-err (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) ()
  final-err (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) ()
  final-err (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
  final-err (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) ()
  final-err (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
  final-err (ret (code k) halt) ()
  final-err (ret (pair v w) halt) ()
  final-err (ret (const B k) halt) ()
  final-err (ret (tup vs) halt) ()
  final-err (ret (inl v) halt) ()
  final-err (ret (inr v) halt) ()
  final-err (ret f (appF M N γ κ)) ()
  final-err (ret e (appE f N γ κ)) ()
  final-err (ret w (appA (code k) e κ)) eq with global ds k in g
  final-err (ret w (appA (code k) e κ)) () | just B
  final-err (ret w (appA (code k) e κ)) refl | nothing =
    𝒦-ω κ (subst (λ L → ω ∈ callᵉ ⟨ L , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩) (sym (global-nothing k g)) (errcode-ω e w))
  final-err (ret w (appA (pair a b) e κ)) refl = call-wrong (pair a b) e w κ (λ _ ())
  final-err (ret w (appA (const B k) e κ)) refl = call-wrong (const B k) e w κ (λ _ ())
  final-err (ret w (appA (tup vs) e κ)) refl = call-wrong (tup vs) e w κ (λ _ ())
  final-err (ret w (appA (inl v) e κ)) refl = call-wrong (inl v) e w κ (λ _ ())
  final-err (ret w (appA (inr v) e κ)) refl = call-wrong (inr v) e w κ (λ _ ())
  final-err (ret v (pairL M γ κ)) ()
  final-err (ret w (pairR v κ)) ()
  final-err (ret (pair v w) (fstK κ)) ()
  final-err (ret (code k) (fstK κ)) refl = car-wrong (code k) κ (λ _ _ ())
  final-err (ret (const B k) (fstK κ)) refl = car-wrong (const B k) κ (λ _ _ ())
  final-err (ret (tup vs) (fstK κ)) refl = car-wrong (tup vs) κ (λ _ _ ())
  final-err (ret (inl v) (fstK κ)) refl = car-wrong (inl v) κ (λ _ _ ())
  final-err (ret (inr v) (fstK κ)) refl = car-wrong (inr v) κ (λ _ _ ())
  final-err (ret (pair v w) (sndK κ)) ()
  final-err (ret (code k) (sndK κ)) refl = cdr-wrong (code k) κ (λ _ _ ())
  final-err (ret (const B k) (sndK κ)) refl = cdr-wrong (const B k) κ (λ _ _ ())
  final-err (ret (tup vs) (sndK κ)) refl = cdr-wrong (tup vs) κ (λ _ _ ())
  final-err (ret (inl v) (sndK κ)) refl = cdr-wrong (inl v) κ (λ _ _ ())
  final-err (ret (inr v) (sndK κ)) refl = cdr-wrong (inr v) κ (λ _ _ ())
  final-err (ret v (tupK vs Ms γ κ)) ()
  final-err (ret (tup vs) (getK i κ)) eq with proj i vs in p
  final-err (ret (tup vs) (getK i κ)) () | just v
  final-err (ret (tup vs) (getK i κ)) refl | nothing = 𝒦-ω κ (inj₂ ⟨ refl , inj₂ (tup-wrong i vs p) ⟩)
  final-err (ret (code k) (getK i κ)) refl = get-wrong i (code k) κ (λ _ ())
  final-err (ret (pair v w) (getK i κ)) refl = get-wrong i (pair v w) κ (λ _ ())
  final-err (ret (const B k) (getK i κ)) refl = get-wrong i (const B k) κ (λ _ ())
  final-err (ret (inl v) (getK i κ)) refl = get-wrong i (inl v) κ (λ _ ())
  final-err (ret (inr v) (getK i κ)) refl = get-wrong i (inr v) κ (λ _ ())
  final-err (ret v (inlK κ)) ()
  final-err (ret v (inrK κ)) ()
  final-err (ret (inl v) (caseK M N γ κ)) ()
  final-err (ret (inr v) (caseK M N γ κ)) ()
  final-err (ret (code k) (caseK M N γ κ)) refl = case-wrong (code k) M N γ κ (λ _ ()) (λ _ ())
  final-err (ret (pair v w) (caseK M N γ κ)) refl = case-wrong (pair v w) M N γ κ (λ _ ()) (λ _ ())
  final-err (ret (const B k) (caseK M N γ κ)) refl = case-wrong (const B k) M N γ κ (λ _ ()) (λ _ ())
  final-err (ret (tup vs) (caseK M N γ κ)) refl = case-wrong (tup vs) M N γ κ (λ _ ()) (λ _ ())
  final-err (ret v (primL p M γ κ)) ()
  final-err (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
  final-err (ret w (primR p v κ)) () | just r
  final-err (ret w (primR p v κ)) refl | nothing = 𝒦-ω κ (prim-ω p v w e)
  final-err (ret v (letK N γ κ)) ()

  private
    error : ∀ {o} → stop {State} o-error ≡ stop o → Answer o → ⊥
    error refl ans = ans refl

  {- a state that stops with an answer returns a value to halt -}
  halts : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ v ∈ Val ] s ≡ ret v halt × o ≡ obs v
  halts (eval (` x) γ κ) eq ans with γ ‼ x
  halts (eval (` x) γ κ) () ans | just v
  halts (eval (` x) γ κ) eq ans | nothing = ⊥-elim (error eq ans)
  halts (eval (fun-ref k ⦅ Nil ⦆) γ κ) () ans
  halts (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) () ans
  halts (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
  halts (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  halts (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (tuple n ⦅ args ⦆) γ κ) () ans
  halts (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  halts (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  halts (ret v halt) refl ans = ⟨ v , ⟨ refl , refl ⟩ ⟩
  halts (ret f (appF M N γ κ)) () ans
  halts (ret e (appE f N γ κ)) () ans
  halts (ret w (appA (code k) e κ)) eq ans with global ds k
  halts (ret w (appA (code k) e κ)) () ans | just B
  halts (ret w (appA (code k) e κ)) eq ans | nothing = ⊥-elim (error eq ans)
  halts (ret w (appA (pair _ _) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (const B k) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (tup vs) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (inl v) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (inr v) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (pairL M γ κ)) () ans
  halts (ret w (pairR v κ)) () ans
  halts (ret (pair v w) (fstK κ)) () ans
  halts (ret (code k) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inl v) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inr v) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (sndK κ)) () ans
  halts (ret (code k) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inl v) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inr v) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (tupK vs Ms γ κ)) () ans
  halts (ret (tup vs) (getK i κ)) eq ans with proj i vs
  halts (ret (tup vs) (getK i κ)) () ans | just v
  halts (ret (tup vs) (getK i κ)) eq ans | nothing = ⊥-elim (error eq ans)
  halts (ret (code k) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inl v) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (inr v) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (inlK κ)) () ans
  halts (ret v (inrK κ)) () ans
  halts (ret (inl v) (caseK M N γ κ)) () ans
  halts (ret (inr v) (caseK M N γ κ)) () ans
  halts (ret (code k) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (letK N γ κ)) () ans
  halts (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  halts (ret v (primL p M γ κ)) () ans
  halts (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
  halts (ret w (primR p v κ)) () ans | just r
  halts (ret w (primR p v κ)) eq ans | nothing = ⊥-elim (error eq ans)

  final-shape : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
  final-shape s fin ans with halts s fin ans
  ... | ⟨ v , ⟨ refl , refl ⟩ ⟩ = 𝒱-shape v

{- Soundness ------------------------------------------------------------------}

{- a well-formed program that terminates with an answer o has an element
   of the shape of o in its denotation -}
soundness : ∀ P → WF P → ∀ {o} → Terminates (sem P) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₚ × ShapeOf o d
soundness (program ds M) ⟨ wfd , _ ⟩ ⟨ s , ⟨ σ , fin ⟩ ⟩ ans
    with final-shape ds wfd s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ ⟦⟧[]-monotone (table ds) M (λ x → id⊆) d (↠-⊆ ds wfd (Common.star→↠ ds σ) d d∈) , sh ⟩ ⟩

{- a well-formed program that stops with an error has ω in its denotation -}
sound-error : ∀ P → WF P → Terminates (sem P) o-error → ω ∈ ⟦ P ⟧ₚ
sound-error (program ds M) ⟨ wfd , _ ⟩ ⟨ s , ⟨ σ , fin ⟩ ⟩ =
  ⟦⟧[]-monotone (table ds) M (λ x → id⊆) ω (↠-⊆ ds wfd (Common.star→↠ ds σ) ω (final-err ds wfd s fin))
