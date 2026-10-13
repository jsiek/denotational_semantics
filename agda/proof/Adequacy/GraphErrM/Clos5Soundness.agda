{-

  Soundness of the Clos5 machine with respect to the monadic graph model
  with errors (Semantics/GraphErrM/Clos5.agda): what the machine computes
  is in the denotation of the (well-formed) program, and when it stops
  with an error, ω is.

  As for ISWIM (proof/Adequacy/GraphErrM/Soundness.agda), each machine
  state denotes a set (𝒮), each step can only shrink it (step-⊆), a
  continuation passes on ω (𝒦-ω: an erring operand errs in its bind),
  and a check of the machine fails on a value of another kind (𝒱-bad:
  the elements of the denotation of a value are of its kind). As for
  Clos5 in the graph model (proof/Adequacy/Clos5Soundness.agda), a code
  pointer code k denotes the entry for k in the table, and calling it is
  β for its two parameters (callᵐ-β), where the definition is
  interpreted with the table of the older ones (stab⊆). A call of a
  reference to no definition denotes ω: errcode is code whose body is
  {ω}.

-}

module proof.Adequacy.GraphErrM.Clos5Soundness where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Out; int; bool; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-env; Con-⌈⌉; Con-⊆; Con⇒≈)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD; ℬ-consis)
open import proof.Framework.GraphModel.Ops using (ΛΛ-β) renaming (pair to pairD)
open import proof.Framework.GraphModel.ErrorMonad renaming (Val to Valᴰ)
open import proof.Framework.GraphModel.ContinuityBase using (mono; consis; Good)
open import Framework.abt.Sig using (■)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import proof.Semantics.GraphErrM.Prim using (primᵐ; primᵐ-good) renaming (out to dout)
open import Language.Clos5
open import Semantics.GraphErrM.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; ⟦_⟧ₚ; table; init) renaming (code to codeD)
open import proof.Semantics.GraphErrM.Clos5
  using (⟦⟧[]-monotone; body-mono; body-continuous; body2-continuous; table-con; Clos5ᵐ-con)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; next; stop)
open import proof.Framework.ListUtil
open import Semantics.CEK.Clos5
import Semantics.CEK.Clos5 as T using (inl; inr)
open import proof.Compiler.GlobalizeTable using (∷-⊑)
open import proof.Adequacy.Common using (ShapeOf; δ?-inv; has-length→length; length→has-length)
open import proof.Adequacy.GraphErrM.Soundness
  using (At; AllNE; 𝒯P; bindL; 𝒯L; _⊆L_; ⊆L-refl; bindL-mono; 𝒯P-mono; Vals; 𝒯L-β; errsL; errsL-ω;
         At-length; At-[]; 𝒯P-kind; Vals⇒AllNE; shape-ω; AllCon; 𝒯P-con; δ?-none)
open import proof.Adequacy.GraphErrM.Clos5WF using (WF; DefsWF)
import proof.Adequacy.GraphErrM.Clos5Common as Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
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

{- ---------------------------------------------------------------------------------}

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

id⊆ : ∀ {D : 𝒫 Value} → D ⊆ D
id⊆ d d∈ = d∈

{- the operators, monotone in their operands -}
call⊆ : ∀ {L L' M M' N N'} → L ⊆ L' → M ⊆ M' → N ⊆ N'
  → callᵐ ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ⊆ callᵐ ⟨ L' , ⟨ M' , ⟨ N' , ptt ⟩ ⟩ ⟩
call⊆ a b c = lower (mono (callᵐ-good {⊤}) _ _ ⟨ lift a , ⟨ lift b , ⟨ lift c , ptt ⟩ ⟩ ⟩)

op2⊆ : ∀ {f} → Good ⊤ (■ ∷ ■ ∷ []) f → ∀ {D D' E E'} → D ⊆ D' → E ⊆ E' → f ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ f ⟨ D' , ⟨ E' , ptt ⟩ ⟩
op2⊆ G a b = lower (mono G _ _ ⟨ lift a , ⟨ lift b , ptt ⟩ ⟩)

op1⊆ : ∀ {f} → Good ⊤ (■ ∷ []) f → ∀ {D D'} → D ⊆ D' → f ⟨ D , ptt ⟩ ⊆ f ⟨ D' , ptt ⟩
op1⊆ G a = lower (mono G _ _ ⟨ lift a , ptt ⟩)

{- the kind of a machine value -}
vkind : Val → Kind
vkind (code k) = fun
vkind (pair v w) = prod
vkind (const B k) = base B
vkind (tup vs) = tup (length vs)
vkind (T.inl v) = inj
vkind (T.inr v) = inj

module _ (ds : List AST) (wf : DefsWF ds) where

  open Common ds

  Tb : Table
  Tb = table ds

  ⟦_⟧ᵀ : AST → VEnv → 𝒫 Value
  ⟦ M ⟧ᵀ ρ = ⟦ M ⟧[ Tb ] ρ

  {- Denotations of values, environments, continuations and states ------------}

  𝒱 : Val → 𝒫 Value
  𝒱s : List Val → List (𝒫 Value)

  𝒱 (code k) = Tb k
  𝒱 (pair v w) = pairᵐ ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  𝒱 (const B k) = ℬ B k ptt
  𝒱 (tup vs) = 𝒯L (𝒱s vs)
  𝒱 (T.inl v) = inlᵐ ⟨ 𝒱 v , ptt ⟩
  𝒱 (T.inr v) = inrᵐ ⟨ 𝒱 v , ptt ⟩

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
  𝒦 (appF M N γ κ) D = 𝒦 κ (callᵐ ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ⟨ ⟦ N ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩ ⟩)
  𝒦 (appE f N γ κ) D = 𝒦 κ (callᵐ ⟨ 𝒱 f , ⟨ D , ⟨ ⟦ N ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩ ⟩)
  𝒦 (appA f e κ) D = 𝒦 κ (callᵐ ⟨ 𝒱 f , ⟨ 𝒱 e , ⟨ D , ptt ⟩ ⟩ ⟩)
  𝒦 (pairL M γ κ) D = 𝒦 κ (pairᵐ ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (pairR v κ) D = 𝒦 κ (pairᵐ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
  𝒦 (fstK κ) D = 𝒦 κ (carᵐ ⟨ D , ptt ⟩)
  𝒦 (sndK κ) D = 𝒦 κ (cdrᵐ ⟨ D , ptt ⟩)
  𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
  𝒦 (getK i κ) D = 𝒦 κ (projᵐ i ⟨ D , ptt ⟩)
  𝒦 (inlK κ) D = 𝒦 κ (inlᵐ ⟨ D , ptt ⟩)
  𝒦 (inrK κ) D = 𝒦 κ (inrᵐ ⟨ D , ptt ⟩)
  𝒦 (caseK M N γ κ) D =
    𝒦 κ (𝒞ᵐ ⟨ D , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
  𝒦 (primL p M γ κ) D = 𝒦 κ (primᵐ p ⟨ D , ⟨ ⟦ M ⟧ᵀ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (primR p v κ) D = 𝒦 κ (primᵐ p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
  𝒦 (letK N γ κ) D = 𝒦 κ (letᵐ ⟨ D , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩)

  𝒮 : State → 𝒫 Value
  𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ᵀ (𝓔 γ))
  𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

  {- Monotonicity of the continuations -----------------------------------------}

  rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
  rev𝒱-mono [] Ds Es s = s
  rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ id⊆ , s ⟩

  𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (appF M N γ κ) D⊆ = 𝒦-mono κ (call⊆ D⊆ id⊆ id⊆)
  𝒦-mono (appE f N γ κ) D⊆ = 𝒦-mono κ (call⊆ id⊆ D⊆ id⊆)
  𝒦-mono (appA f e κ) D⊆ = 𝒦-mono κ (call⊆ id⊆ id⊆ D⊆)
  𝒦-mono (pairL M γ κ) D⊆ = 𝒦-mono κ (op2⊆ pairᵐ-good D⊆ id⊆)
  𝒦-mono (pairR v κ) D⊆ = 𝒦-mono κ (op2⊆ pairᵐ-good id⊆ D⊆)
  𝒦-mono (fstK κ) D⊆ = 𝒦-mono κ (op1⊆ carᵐ-good D⊆)
  𝒦-mono (sndK κ) D⊆ = 𝒦-mono κ (op1⊆ cdrᵐ-good D⊆)
  𝒦-mono (tupK vs Ms γ κ) {D} {E} D⊆ =
    𝒦-mono κ (bindL-mono _ _ (rev𝒱-mono vs (D ∷ _) (E ∷ _) ⟨ D⊆ , ⊆L-refl _ ⟩) 𝒯P-mono)
  𝒦-mono (getK i κ) D⊆ = 𝒦-mono κ (op1⊆ (projᵐ-good i) D⊆)
  𝒦-mono (inlK κ) D⊆ = 𝒦-mono κ (op1⊆ inlᵐ-good D⊆)
  𝒦-mono (inrK κ) D⊆ = 𝒦-mono κ (op1⊆ inrᵐ-good D⊆)
  𝒦-mono (caseK M N γ κ) D⊆ =
    𝒦-mono κ (lower (mono (𝒞ᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ (λ X Y X⊆ → lift (body-mono Tb M (𝓔 γ) X⊆)) ,
                                                           ⟨ (λ X Y X⊆ → lift (body-mono Tb N (𝓔 γ) X⊆)) , ptt ⟩ ⟩ ⟩))
  𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (op2⊆ (primᵐ-good p) D⊆ id⊆)
  𝒦-mono (primR p v κ) D⊆ = 𝒦-mono κ (op2⊆ (primᵐ-good p) id⊆ D⊆)
  𝒦-mono (letK N γ κ) D⊆ =
    𝒦-mono κ (lower (mono (letᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ (λ X Y X⊆ → lift (body-mono Tb N (𝓔 γ) X⊆)) , ptt ⟩ ⟩))

  {- Values denote consistent sets of values of their kind ----------------------}

  length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
  length-𝒱s [] = refl
  length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)

  length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
  length-obs-list [] = refl
  length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

  𝒱-val : ∀ v → Valᴰ (𝒱 v)
  𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
  𝒱s-vals : ∀ vs → Vals (𝒱s vs)
  𝒱-val (code k) = ⟨ table-clean ds k , ⟨ ν , table-ν ds k ⟩ ⟩
  𝒱-val (pair v w) = pairᵐ-val (𝒱-val v) (𝒱-val w)
  𝒱-val (const B k) = ⟨ (λ { .ω () refl }) , ⟨ dconst k , ⟨ refl , refl ⟩ ⟩ ⟩
  𝒱-val (tup vs) = ⟨ (λ { d d∈ refl → shape-ω' (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) d d∈) }) , ⟨ _ , proj₁ (proj₂ (𝒱-shape (tup vs))) ⟩ ⟩
    where shape-ω' : ω ∈ 𝒯P (𝒱s vs) → ⊥
          shape-ω' ()
  𝒱-val (T.inl v) = inlᵐ-val (𝒱-val v)
  𝒱-val (T.inr v) = inrᵐ-val (𝒱-val v)
  𝒱-shape (code k) = ⟨ ν , ⟨ table-ν ds k , tt ⟩ ⟩
  𝒱-shape (pair v w) = ⟨ _ , ⟨ proj₂ (proj₂ (pairᵐ-val (𝒱-val v) (𝒱-val w))) , tt ⟩ ⟩
  𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
  𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
  𝒱-shape (tup (v ∷ vs)) =
    ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-shape v))
    , ⟨ proj₂ (𝒯L-β (𝒱s (v ∷ vs)) vs′) _ ⟨ ⟨ length-𝒱s vs , proj₁ (proj₂ (𝒱-shape v)) ⟩ , Vals⇒AllNE _ vs′ ⟩
      , ⟨ length-obs-list vs , proj₂ (proj₂ (𝒱-shape v)) ⟩ ⟩ ⟩
    where vs′ = ⟨ 𝒱-val v , 𝒱s-vals vs ⟩
  𝒱-shape (T.inl v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ d∈ , d≢ ⟩ ⟩ , sh ⟩ ⟩
    where d≢ = λ { refl → shape-ω (obs v) sh }
  𝒱-shape (T.inr v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ d∈ , d≢ ⟩ ⟩ , sh ⟩ ⟩
    where d≢ = λ { refl → shape-ω (obs v) sh }
  𝒱s-vals [] = tt
  𝒱s-vals (v ∷ vs) = ⟨ 𝒱-val v , 𝒱s-vals vs ⟩

  𝒱-conv : ∀ v → Conv (𝒱 v)
  𝒱-conv v = Val⇒Conv (𝒱-val v)

  𝒱-kind : ∀ v d → d ∈ ⌊ 𝒱 v ⌋ → kind d ≡ vkind v
  𝒱-kind (code k) d ⟨ d∈ , _ ⟩ = table-fun ds k d d∈
  𝒱-kind (pair v w) d ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  𝒱-kind (pair v w) d ⟨ inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  𝒱-kind (pair v w) ⦅ a , b ⦆ ⟨ inj₂ ⟨ _ , inj₂ _ ⟩ , _ ⟩ = refl
  𝒱-kind (const B k) (dconst k') ⟨ ⟨ refl , _ ⟩ , _ ⟩ = refl
  𝒱-kind (tup vs) d ⟨ d∈ , _ ⟩ =
    trans (𝒯P-kind (𝒱s vs) d (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) d d∈)) (cong tup (length-𝒱s vs))
  𝒱-kind (T.inl v) d ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  𝒱-kind (T.inl v) (left d) ⟨ inj₂ _ , _ ⟩ = refl
  𝒱-kind (T.inr v) d ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  𝒱-kind (T.inr v) (right d) ⟨ inj₂ _ , _ ⟩ = refl

  {- the check of a kind fails on a value of another kind -}
  𝒱-bad : ∀ v {k} → vkind v ≢ k → Bad k ⌊ 𝒱 v ⌋
  𝒱-bad v ne with 𝒱-conv v
  ... | ⟨ d , d∈ ⟩ = ⟨ d , ⟨ d∈ , (λ eq → ne (trans (sym (𝒱-kind v d d∈)) eq)) ⟩ ⟩

  𝒱-con : ∀ v → Con (𝒱 v)
  𝒱s-con : ∀ vs → AllCon (𝒱s vs)
  𝒱-con (code k) = table-con ds k
  𝒱-con (pair v w) = lower (consis (pairᵐ-good {⊤}) tt _ _ ⟨ lift (𝒱-con v) , ⟨ lift (𝒱-con w) , ptt ⟩ ⟩)
  𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
  𝒱-con (tup vs) = Con-⊆ (𝒯P-con (𝒱s vs) (𝒱s-con vs)) (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)))
  𝒱-con (T.inl v) = lower (consis (inlᵐ-good {⊤}) tt _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱-con (T.inr v) = lower (consis (inrᵐ-good {⊤}) tt _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱s-con [] = tt
  𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩

  {- Environments -----------------------------------------------------------------}

  𝓔-nonempty : ∀ γ → proof.Framework.GraphModel.Env.nonempty-env (𝓔 γ)
  𝓔-nonempty [] x = ⟨ ω , refl ⟩
  𝓔-nonempty (v ∷ γ) zero = proj₂ (𝒱-val v)
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

  {- Calls ---------------------------------------------------------------------------}

  {- β for the two parameters of code: calling code k, found in the table
     as B, on the environment e and the argument w -}
  call-⊆ : ∀ k {B} w e → global ds k ≡ just B
    → ⟦ B ⟧ᵀ (𝓔 (w ∷ e ∷ [])) ⊆ callᵐ ⟨ Tb k , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩
  call-⊆ k {B} w e g d d∈ with global-split k g
  ... | ⟨ Ns , ⟨ p , refl ⟩ ⟩ =
    call⊆ (≡→⊆ (sym (table-at p))) id⊆ id⊆ d
      (callᵐ-β {λ X Y → ⟦ B ⟧[ table Ns ] (Y • X • (λ _ → init))} (𝒱-con e) (𝒱-con w) (𝒱-val e) (𝒱-val w)
         (body2-continuous (table Ns) B (λ _ → init) (λ _ → ⟨ ω , refl ⟩) (proj₂ (𝒱-val e)) (proj₂ (𝒱-val w))) d
         (⟦⟧[]-monotone (table Ns) B env⊆ d
            (stab⊆ (length Ns) Tb (table Ns) B ag (proj₁ (DefsWF-⊑ p wf)) (λ x → id⊆) d d∈)))
    where
    ≡→⊆ : ∀ {D E : 𝒫 Value} → D ≡ E → D ⊆ E
    ≡→⊆ refl = id⊆
    ag : Agree⊆ (length Ns) Tb (table Ns)
    ag j j< = ≡→⊆ (table-agree (∷-⊑ p) j j<)
    env⊆ : ∀ x → 𝓔 (w ∷ e ∷ []) x ⊆ (𝒱 w • 𝒱 e • (λ _ → init)) x
    env⊆ zero = id⊆
    env⊆ (suc zero) = id⊆
    env⊆ (suc (suc x)) = id⊆

  {- a call of errcode is an error, once its operands have values -}
  errcode-ω : ∀ e w → ω ∈ callᵐ ⟨ errcode , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩
  errcode-ω e w with 𝒱-val e | 𝒱-val w
  ... | ⟨ _ , ⟨ a , a∈ ⟩ ⟩ | ⟨ _ , ⟨ b , b∈ ⟩ ⟩ =
    callᵐ-β {λ _ _ → ⌈ ω ⌉} (𝒱-con e) (𝒱-con w) (𝒱-val e) (𝒱-val w)
      (λ u u∈ → ⟨ a ∷ [] , ⟨ b ∷ [] , ⟨ (λ ()) , ⟨ (λ ()) , ⟨ (λ { _ (here refl) → a∈ }) , ⟨ (λ { _ (here refl) → b∈ }) , u∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
      ω refl

  {- Tuples ------------------------------------------------------------------------}

  𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
  𝒱s-reverseAcc acc [] = refl
  𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

  tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
  tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
  tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

  {- the tuple of a list of operands is the tuple of the operands -}
  𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯ᵐ n (⟦ args ⟧₊[ Tb ] ρ)
  𝒯L-args {n} args ρ = go args (tup⊆ n)
    where
    open import proof.Framework.GraphModel.Ops using (𝒯)
    Rel : ∀ m → List (𝒫 Value) → Results (𝒫 Value) (replicate m ■) → Set
    Rel zero [] _ = ⊤
    Rel (suc m) (X ∷ Xs) ⟨ Y , Ys ⟩ = X ⊆ Y × Rel m Xs Ys
    Rel _ _ _ = ⊥
    Rel-len : ∀ {m Xs Ys} → Rel m Xs Ys → length Xs ≡ m
    Rel-len {zero} {[]} _ = refl
    Rel-len {suc m} {X ∷ Xs} ⟨ _ , r ⟩ = cong suc (Rel-len r)
    Rel-At : ∀ {m Xs Ys} (i : Fin m) {d} → Rel m Xs Ys → At i Xs d → d ∈ nthD Ys i
    Rel-At {suc m} {X ∷ Xs} zero ⟨ X⊆ , _ ⟩ ⟨ _ , d∈ ⟩ = X⊆ _ d∈
    Rel-At {suc m} {X ∷ Xs} (suc i) ⟨ _ , r ⟩ a = Rel-At i r a
    Rel-ne : ∀ {m Xs Ys} → Rel m Xs Ys → AllNE Xs → ∀ j → nonempty (nthD Ys j)
    Rel-ne {suc m} {X ∷ Xs} ⟨ X⊆ , _ ⟩ ⟨ ⟨ d , d∈ ⟩ , _ ⟩ zero = ⟨ d , X⊆ d d∈ ⟩
    Rel-ne {suc m} {X ∷ Xs} ⟨ _ , r ⟩ ⟨ _ , ne ⟩ (suc j) = Rel-ne r ne j
    tup⊆ : ∀ m {Xs Ys} → Rel m Xs Ys → 𝒯P Xs ⊆ 𝒯 m Ys
    tup⊆ zero {[]} _ ⟨⟩ _ = tt
    tup⊆ zero {[]} _ (tup[ i ] d) ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
    tup⊆ (suc m) {X ∷ Xs} _ ⟨⟩ ()
    tup⊆ (suc m) {Xs} r (tup[ i ] d) ⟨ a , ne ⟩ with trans (sym (At-length i Xs d a)) (Rel-len r)
    ... | refl = ⟨ refl , ⟨ Rel-At i r a , Rel-ne r ne ⟩ ⟩
    go : ∀ {m} (as : Args (replicate m ■)) {K K'} → (∀ {Xs Ys} → Rel m Xs Ys → K Xs ⊆ K' Ys)
      → bindL (⟦ args→list as ⟧* ρ) K ⊆ binds m (⟦ as ⟧₊[ Tb ] ρ) K'
    go {zero} Nil h = h tt
    go {suc m} (M ,, as) h = ≫=-mono (λ d z → z) (λ X⊆ → go as (λ r → h ⟨ X⊆ , r ⟩))

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

  proj-nothing : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → length vs ≢ n
  proj-nothing i vs eq len with proj-length i vs len
  ... | ⟨ v , eq' ⟩ with trans (sym eq) eq'
  ... | ()

  {- Primitives -------------------------------------------------------------------}

  int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ ⌊ 𝒱 v ⌋
  int-in (const B k) refl = ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩

  𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
  𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
  𝒱-out (bool true) d (inj₁ ⟨ refl , () ⟩)
  𝒱-out (bool true) (left ⟨⟩) (inj₂ _) = refl
  𝒱-out (bool true) (left (tup[ i ] d)) (inj₂ ⟨ _ , ⟨ ⟨ a , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (At-[] i a)
  𝒱-out (bool false) d (inj₁ ⟨ refl , () ⟩)
  𝒱-out (bool false) (right ⟨⟩) (inj₂ _) = refl
  𝒱-out (bool false) (right (tup[ i ] d)) (inj₂ ⟨ _ , ⟨ ⟨ a , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (At-[] i a)

  prim-⊆ : ∀ p v w r → δ? p (obs v) (obs w) ≡ just r → 𝒱 (out r) ⊆ primᵐ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  prim-⊆ p v w r e d d∈ with δ?-inv p (obs v) (obs w) e
  ... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ =
    inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , 𝒱-out (δ p n m) d d∈ ⟩ ⟩ ⟩ ⟩) ⟩ ⟩

  {- a value whose observation is not an integer is not of the kind of one -}
  notint-kind : ∀ v → (∀ n → obs v ≢ o-const Int n) → vkind v ≢ base Int
  notint-kind (const .Int k) f refl = f k refl

  prim-ω : ∀ p v w → δ? p (obs v) (obs w) ≡ nothing → ω ∈ primᵐ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  prim-ω p v w e with δ?-none p (obs v) (obs w) e
  ... | inj₁ ni = inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₁ ⟨ refl , 𝒱-bad v (notint-kind v ni) ⟩ ⟩ ⟩
  ... | inj₂ ni = inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₂ (inj₁ ⟨ refl , 𝒱-bad w (notint-kind w ni) ⟩) ⟩ ⟩

  {- Steps shrink the denotation of the state --------------------------------}

  {- β for one parameter: the body of a let or a case, run on a value -}
  let-β : ∀ N γ w → ⟦ N ⟧ᵀ (𝓔 (w ∷ γ)) ⊆ letᵐ ⟨ 𝒱 w , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩
  let-β N γ w d d∈ =
    proj₂ (letᵐ-β (body-mono Tb N (𝓔 γ)) (body-continuous Tb N (𝓔 γ) (𝓔-nonempty γ) (𝒱 w) (proj₂ (𝒱-val w)))
                  (𝒱-con w) (𝒱-val w)) d (⟦⟧[]-monotone Tb N (𝓔-ext w γ) d d∈)

  case-inl-β : ∀ M N γ v → ⟦ M ⟧ᵀ (𝓔 (v ∷ γ))
    ⊆ 𝒞ᵐ ⟨ inlᵐ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  case-inl-β M N γ v d d∈ =
    proj₂ (𝒞ᵐ-inl-β {G = λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)} (body-mono Tb M (𝓔 γ))
             (body-continuous Tb M (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (proj₂ (𝒱-val v))) (𝒱-con v) (𝒱-val v))
          d (⟦⟧[]-monotone Tb M (𝓔-ext v γ) d d∈)

  case-inr-β : ∀ M N γ v → ⟦ N ⟧ᵀ (𝓔 (v ∷ γ))
    ⊆ 𝒞ᵐ ⟨ inrᵐ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ᵀ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  case-inr-β M N γ v d d∈ =
    proj₂ (𝒞ᵐ-inr-β {F = λ X → ⟦ M ⟧ᵀ (X • 𝓔 γ)} (body-mono Tb N (𝓔 γ))
             (body-continuous Tb N (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (proj₂ (𝒱-val v))) (𝒱-con v) (𝒱-val v))
          d (⟦⟧[]-monotone Tb N (𝓔-ext v γ) d d∈)

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
  step-⊆ (ret v (pairL M γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (pairR v κ)) refl d d∈ = d∈
  step-⊆ (ret (pair v w) (fstK κ)) refl = 𝒦-mono κ (carᵐ-pair (𝒱-val v) (𝒱-val w))
  step-⊆ (ret (pair v w) (sndK κ)) refl = 𝒦-mono κ (cdrᵐ-pair (𝒱-val v) (𝒱-val w))
  step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
  step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
  step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
    𝒦-mono κ λ d d∈ → inj₂ ⟨ 𝒱-conv (tup vs) , inj₂ ⟨ proj₂ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) _
                        ⟨ proj-𝒱s i vs p d d∈ , Vals⇒AllNE _ (𝒱s-vals vs) ⟩ , (λ ()) ⟩ ⟩
  step-⊆ (ret (tup vs) (getK i κ)) () | nothing
  step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
  step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
  step-⊆ (ret (T.inl v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inl-β M N γ v)
  step-⊆ (ret (T.inr v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inr-β M N γ v)
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
  errsL-rev (v ∷ vs) Ds e = errsL-rev vs (𝒱 v ∷ Ds) (inj₂ ⟨ 𝒱-conv v , e ⟩)

  𝒦-ω : ∀ κ {D} → ω ∈ D → ω ∈ 𝒦 κ D
  𝒦-ω halt ω∈ = ω∈
  𝒦-ω (appF M N γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (appE f N γ κ) ω∈ = 𝒦-ω κ (callᵐ-ω (inj₂ (𝒱-conv f)) (inj₁ ω∈))
  𝒦-ω (appA f e κ) ω∈ = 𝒦-ω κ (callᵐ-ω (inj₂ (𝒱-conv f)) (inj₂ ⟨ 𝒱-conv e , ω∈ ⟩))
  𝒦-ω (pairL M γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (pairR v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv v , inj₁ ⟨ refl , ω∈ ⟩ ⟩)
  𝒦-ω (fstK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (sndK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (tupK vs Ms γ κ) {D} ω∈ = 𝒦-ω κ (errsL-ω _ (errsL-rev vs (D ∷ _) (inj₁ ω∈)))
  𝒦-ω (getK i κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (inlK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (inrK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (caseK M N γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (primL p M γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
  𝒦-ω (primR p v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv v , inj₁ ⟨ refl , ω∈ ⟩ ⟩)
  𝒦-ω (letK N γ κ) {D} ω∈ = 𝒦-ω κ (proj₂ (letᵐ-unfold {D}) ω (inj₁ ⟨ refl , ω∈ ⟩))

  {- the checks of the machine, on a value of another kind -}
  call-bad : ∀ f e w κ → vkind f ≢ fun → ω ∈ 𝒦 κ (callᵐ ⟨ 𝒱 f , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩)
  call-bad f e w κ nf = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv f , inj₂ ⟨ 𝒱-conv e , inj₂ ⟨ 𝒱-conv w , inj₁ ⟨ refl , 𝒱-bad f nf ⟩ ⟩ ⟩ ⟩)

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
  final-err (ret (T.inl v) halt) ()
  final-err (ret (T.inr v) halt) ()
  final-err (ret w (appA (code k) e κ)) eq with global ds k in g
  final-err (ret w (appA (code k) e κ)) () | just B
  final-err (ret w (appA (code k) e κ)) refl | nothing =
    𝒦-ω κ (subst (λ L → ω ∈ callᵐ ⟨ L , ⟨ 𝒱 e , ⟨ 𝒱 w , ptt ⟩ ⟩ ⟩) (sym (global-nothing k g)) (errcode-ω e w))
  final-err (ret w (appA (pair a b) e κ)) refl = call-bad (pair a b) e w κ (λ ())
  final-err (ret w (appA (const B k) e κ)) refl = call-bad (const B k) e w κ (λ ())
  final-err (ret w (appA (tup vs) e κ)) refl = call-bad (tup vs) e w κ (λ ())
  final-err (ret w (appA (T.inl v) e κ)) refl = call-bad (T.inl v) e w κ (λ ())
  final-err (ret w (appA (T.inr v) e κ)) refl = call-bad (T.inr v) e w κ (λ ())
  final-err (ret (code k) (fstK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (code k) , inj₁ ⟨ refl , 𝒱-bad (code k) (λ ()) ⟩ ⟩)
  final-err (ret (const B k) (fstK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
  final-err (ret (tup vs) (fstK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
  final-err (ret (T.inl v) (fstK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
  final-err (ret (T.inr v) (fstK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
  final-err (ret (code k) (sndK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (code k) , inj₁ ⟨ refl , 𝒱-bad (code k) (λ ()) ⟩ ⟩)
  final-err (ret (const B k) (sndK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
  final-err (ret (tup vs) (sndK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
  final-err (ret (T.inl v) (sndK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
  final-err (ret (T.inr v) (sndK κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
  final-err (ret (tup vs) (getK i κ)) eq with proj i vs in p
  final-err (ret (tup vs) (getK i κ)) () | just v
  final-err (ret (tup vs) (getK i κ)) refl | nothing =
    𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ { refl → proj-nothing i vs p refl }) ⟩ ⟩)
  final-err (ret (code k) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (code k) , inj₁ ⟨ refl , 𝒱-bad (code k) (λ ()) ⟩ ⟩)
  final-err (ret (pair v w) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (pair v w) , inj₁ ⟨ refl , 𝒱-bad (pair v w) (λ ()) ⟩ ⟩)
  final-err (ret (const B k) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
  final-err (ret (T.inl v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
  final-err (ret (T.inr v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
  final-err (ret (code k) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (code k) , inj₁ ⟨ refl , 𝒱-bad (code k) (λ ()) ⟩ ⟩)
  final-err (ret (pair v w) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (pair v w) , inj₁ ⟨ refl , 𝒱-bad (pair v w) (λ ()) ⟩ ⟩)
  final-err (ret (const B k) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
  final-err (ret (tup vs) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
  final-err (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
  final-err (ret w (primR p v κ)) () | just r
  final-err (ret w (primR p v κ)) refl | nothing = 𝒦-ω κ (prim-ω p v w e)

  {- a state that stops with an answer returns a value to halt -}
  final-shape : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
  final-shape (ret v halt) refl ans = 𝒱-shape v
  final-shape (eval (` x) γ κ) eq ans with γ ‼ x
  final-shape (eval (` x) γ κ) () ans | just v
  final-shape (eval (` x) γ κ) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (eval (fun-ref k ⦅ Nil ⦆) γ κ) () ans
  final-shape (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) () ans
  final-shape (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
  final-shape (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (tuple n ⦅ args ⦆) γ κ) () ans
  final-shape (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  final-shape (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  final-shape (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  final-shape (ret w (appA (code k) e κ)) eq ans with global ds k
  final-shape (ret w (appA (code k) e κ)) () ans | just B
  final-shape (ret w (appA (code k) e κ)) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (ret w (appA (pair _ _) e κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret w (appA (const B k) e κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret w (appA (tup vs) e κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret w (appA (T.inl v) e κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret w (appA (T.inr v) e κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (code k) (fstK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (const B k) (fstK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (tup vs) (fstK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inl v) (fstK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inr v) (fstK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (code k) (sndK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (const B k) (sndK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (tup vs) (sndK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inl v) (sndK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inr v) (sndK κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (tup vs) (getK i κ)) eq ans with proj i vs
  final-shape (ret (tup vs) (getK i κ)) () ans | just v
  final-shape (ret (tup vs) (getK i κ)) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (ret (code k) (getK i κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (pair v w) (getK i κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (const B k) (getK i κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inl v) (getK i κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (T.inr v) (getK i κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (code k) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (pair v w) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (const B k) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret (tup vs) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
  final-shape (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
  final-shape (ret w (primR p v κ)) () ans | just r
  final-shape (ret w (primR p v κ)) refl ans | nothing = ⊥-elim (ans refl)

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
