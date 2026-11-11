{-

  The table of the X86μ program that the compiler produces satisfies the
  premise of soundness in Scott domains (X86Soundness.agda): each entry
  is the code of its definition interpreted with the whole table, not
  only with the table of the older ones, as the semantics interprets it.
  As in the graph model (FPC/proof/Adequacy/X86Compiled.agda):

  * the GlobalFunμ program that hoist produces refers, in each
    definition, only to older ones (FPC/proof/Compiler/HoistOlder.agda);
    definition f means its code with the table of the older ones
    (table-at), the older definitions mean the same in the table of all
    of them (agree), and a term means the same in two tables that agree
    on the references it makes (tbl-cong);
  * this passes to X86μ through the lemmas of the Scott-domain proofs of
    remove complex operands, lift locals, explicate control and select
    instructions: the tables of the two programs agree, and so does the
    code of each definition, interpreted with tables that agree.

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Framework.abt.GSubst using (_•_)
open import FPC.Language.Type using (Type; _∋_; Z; S; idx; lvl)
open import FPC.Language.GlobalFun using (DSig; Code; Tm; `_; fun-ref; pair; callc; lit; tuple; get; inl; inr; case; prim;
                                         let′; fold; unfold)
import FPC.Language.GlobalFun as GlobalFun
open import FPC.Language.X86 using (Program)
open import FPC.Language.FPC using () renaming (Tm to FPC-Tm)
open import FPC.Language.Mon using (⌜_⌝)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; pos) renaming (map to All-map)
open import FPC.proof.Framework.AllProp using (lookup-map)
open import FPC.Compiler.Pipeline using (compile-to-GlobalFun; compile-to-PairClos; compile)
open import FPC.Compiler.RCO using (rco)
open import FPC.Compiler.LiftLocals using () renaming (lift to liftₗ)
open import FPC.Compiler.Explicate using (explicate-body)
open import FPC.Compiler.Select using (def-body)
open import FPC.proof.Compiler.HoistOlder using (Older; Olders; OlderDefs; hoist-older)
open import proof.Framework.Lookup using (lvl-<)

open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (zero; suc)
import Data.Product as P
open import Data.Nat using (_<_; _≟_)
open import Data.Nat.Properties using (<-irrefl; <-trans)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; subst to ≡-subst; cong to ≡-cong)

module FPC.proof.Adequacy.ScottDomains.X86Compiled
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe hiding (Val; case)
  renaming (Env to Envᵈ; app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe using (env₂; caseᶜ-cong; letᶜ-cong)
open import Semantics.Scott.Prim pt fe pe using (primD)
open import FPC.Semantics.ScottDomains.Ops pt fe pe using (Table; tables; tables-yes; tables-no)
open import FPC.Semantics.ScottDomains.GlobalFun pt fe pe using (⟦_⟧[_]; ⟦_⟧s[_]; code′)
import FPC.Semantics.ScottDomains.Imp pt fe pe as I
import FPC.Semantics.ScottDomains.CFG pt fe pe as C
open import FPC.Semantics.ScottDomains.X86 pt fe pe using (codeₜ)
open import FPC.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using (codeᶜ-cong)
open import FPC.proof.Correctness.ScottDomains.RCOCorrect pt fe pe using (code-rco; table-rco)
open import FPC.proof.Correctness.ScottDomains.LiftLocalsCorrect pt fe pe using (code-lift; table-lift)
open import FPC.proof.Correctness.ScottDomains.ExplicateCorrect pt fe pe using (body-＝; table-explicate)
open import FPC.proof.Correctness.ScottDomains.SelectCorrect pt fe pe using (db; code-＝; table-＝; map-db)

private
 ≡→＝ : ∀ {X : Set} {x y : X}
   → x ≡ y
   → x ＝ y
 ≡→＝ ≡-refl = refl

{- The older definitions --------------------------------------------------------------}

older : ∀ {ss : List DSig} {s} → ss ∋ s → List DSig
older {_ ∷ ss} Z = ss
older (S f) = older f

dropᵗ : ∀ {P : DSig → Set} {ss s} (f : ss ∋ s) → All P ss → All P (older f)
dropᵗ Z (_ ∷ ps) = ps
dropᵗ (S f) (_ ∷ ps) = dropᵗ f ps

older-lvl : ∀ {ss : List DSig} {s} (f : ss ∋ s) → length (older f) ≡ lvl f
older-lvl Z = ≡-refl
older-lvl (S f) = older-lvl f

olderAt : ∀ {Σ ss s} {ps : All (Code Σ) ss}
  → OlderDefs ps
  → (f : ss ∋ s)
  → Older (length (older f)) (lookup ps f)
olderAt {ps = p ∷ ps} (o P., _) Z = o
olderAt {ps = p ∷ ps} (_ P., os) (S f) = olderAt os f

module _ {Σ : List DSig} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) where

  {- definition g of a part ps of the table, reached through r -}
  table-at′ : ∀ {ss} (ps : All D ss) (r : ∀ {s} → ss ∋ s → Σ ∋ s)
    → (∀ {s} (g : ss ∋ s) → lvl (r g) ≡ lvl g)
    → ∀ {s} (g : ss ∋ s)
    → tables cd ps (r g) ＝ cd (tables cd (dropᵗ g ps)) (lookup ps g)
  table-at′ (p ∷ ps) r rl Z = tables-yes cd p ps (r Z) (rl Z)
  table-at′ (p ∷ ps) r rl (S g) =
    tables-no cd p ps (r (S g)) (λ e → <-irrefl (≡-trans (≡-sym (rl (S g))) e) (lvl-< g))
    ∙ table-at′ ps (λ x → r (S x)) (λ x → rl (S x)) g

  table-at : (ps : All D Σ) → ∀ {s} (f : Σ ∋ s) → tables cd ps f ＝ cd (tables cd (dropᵗ f ps)) (lookup ps f)
  table-at ps = table-at′ ps (λ x → x) (λ _ → ≡-refl)

  {- the definitions older than f mean the same without the newer ones -}
  agree : ∀ {ss s} (ps : All D ss) (f : ss ∋ s) {s'} (g : Σ ∋ s')
    → lvl g < length (older f)
    → tables cd ps g ＝ tables cd (dropᵗ f ps) g
  agree (p ∷ ps) Z g g< = tables-no cd p ps g (λ e → <-irrefl e g<)
  agree {_ ∷ ss} (p ∷ ps) (S f) g g< =
    tables-no cd p ps g (λ e → <-irrefl e (<-trans g< (≡-subst (_< length ss) (≡-sym (older-lvl f)) (lvl-< f))))
    ∙ agree ps f g g<

{- A term means the same in tables that agree on the references it makes -----------}

module _ {Σ : List DSig} {T T' : Table Σ} {k} (h : ∀ {s} (g : Σ ∋ s) → lvl g < k → T g ＝ T' g) where

  tbl-cong : ∀ {Γ A} (M : Tm Σ Γ A)
    → Older k M
    → (ρ : ⟨ Envᵈ ⟩)
    → ⟦ M ⟧[ T ] · ρ ＝ ⟦ M ⟧[ T' ] · ρ
  tbl-congs : ∀ {Γ Δ} (Ms : All (Tm Σ Γ) Δ)
    → Olders k Ms
    → (ρ : ⟨ Envᵈ ⟩)
    → ⟦ Ms ⟧s[ T ] · ρ ＝ ⟦ Ms ⟧s[ T' ] · ρ
  tbl-cong (` x) o ρ = refl
  tbl-cong (fun-ref f) o ρ = h f o
  tbl-cong (pair L M) (o₁ P., o₂) ρ = ap₂ (λ a b → pairᵈ · a · b) (tbl-cong L o₁ ρ) (tbl-cong M o₂ ρ)
  tbl-cong (callc L M) (o₁ P., o₂) ρ =
    ap₂ (λ a b → appᵈ · (appᵈ · (car · a) · (cdr · a)) · b) (tbl-cong L o₁ ρ) (tbl-cong M o₂ ρ)
  tbl-cong (lit B c) o ρ = refl
  tbl-cong (tuple {Δ} Ms) o ρ = ap (tupleᵈ (length Δ) ·_) (tbl-congs Ms o ρ)
  tbl-cong (get i M) o ρ = ap (proj (pos i) ·_) (tbl-cong M o ρ)
  tbl-cong (inl M) o ρ = ap (inlᵈ ·_) (tbl-cong M o ρ)
  tbl-cong (inr M) o ρ = ap (inrᵈ ·_) (tbl-cong M o ρ)
  tbl-cong (case L M N) (o₁ P., o₂ P., o₃) ρ =
    caseᶜ-cong ⟦ L ⟧[ T ] ⟦ L ⟧[ T' ] ⟦ M ⟧[ T ] ⟦ M ⟧[ T' ] ⟦ N ⟧[ T ] ⟦ N ⟧[ T' ] ρ ρ
      (tbl-cong L o₁ ρ) (λ d _ → tbl-cong M o₂ (d • ρ)) (λ d _ → tbl-cong N o₃ (d • ρ))
  tbl-cong (prim p L M) (o₁ P., o₂) ρ = ap₂ (λ a b → primD p · a · b) (tbl-cong L o₁ ρ) (tbl-cong M o₂ ρ)
  tbl-cong (let′ M N) (o₁ P., o₂) ρ =
    letᶜ-cong ⟦ M ⟧[ T ] ⟦ M ⟧[ T' ] ⟦ N ⟧[ T ] ⟦ N ⟧[ T' ] ρ ρ (tbl-cong M o₁ ρ) (λ d _ → tbl-cong N o₂ (d • ρ))
  tbl-cong (fold M) o ρ = tbl-cong M o ρ
  tbl-cong (unfold M) o ρ = tbl-cong M o ρ
  tbl-congs [] o ρ = refl
  tbl-congs (M ∷ Ms) (o P., os) ρ = dfunext fe λ { zero → tbl-cong M o ρ ; (suc i) → happly (tbl-congs Ms os ρ) i }

{- each definition of a program that hoist produces is its code with the whole table -}
clos5-closed : ∀ {Σ} (ds : All (Code Σ) Σ)
  → OlderDefs ds
  → ∀ {s} (f : Σ ∋ s)
  → tables code′ ds f ＝ code′ (tables code′ ds) (lookup ds f)
clos5-closed ds od f =
  table-at code′ ds f
  ∙ codeᶜ-cong ⟦ lookup ds f ⟧[ tables code′ (dropᵗ f ds) ] ⟦ lookup ds f ⟧[ tables code′ ds ]
      (λ X Y _ _ → tbl-cong (λ g g< → agree code′ ds f g g< ⁻¹) (lookup ds f) (olderAt od f) (env₂ X Y))

{- The X86μ program that the compiler produces, from its GlobalFunμ one ----------------}

compiled : ∀ {A} (M : FPC-Tm [] A) → let ds = Program.defs (compile M) in
  ∀ {s} (f : _ ∋ s) → tables codeₜ ds f ＝ codeₜ (tables codeₜ ds) (lookup ds f)
compiled M f = TT f ⁻¹ ∙ clos5-closed ds₅ (hoist-older (compile-to-PairClos M)) f ∙ code-chain
 where
  ds₅ = GlobalFun.Program.defs (compile-to-GlobalFun M)
  dsₘ = All-map (λ D → rco D (λ x → x)) ds₅
  dsᵢ = All-map liftₗ dsₘ
  ds꜀ = All-map explicate-body dsᵢ
  dsₓ = All-map def-body ds꜀
  T₅ = tables code′ ds₅
  T꜀ = tables C.code′ ds꜀
  Tₓ = tables codeₜ dsₓ
  TT₄ : ∀ {s} (g : _ ∋ s) → T꜀ g ＝ Tₓ g
  TT₄ g = table-＝ ds꜀ g ∙ ap (λ ds' → tables codeₜ ds' g) (≡→＝ (map-db ds꜀))
  TT : ∀ {s} (g : _ ∋ s) → T₅ g ＝ Tₓ g
  TT g = table-rco ds₅ g ∙ table-lift dsₘ g ∙ table-explicate dsᵢ g ∙ TT₄ g
  dₘ = rco (lookup ds₅ f) (λ x → x)
  {- the definition, in CFGμ and X86μ -}
  eq꜀ : lookup ds꜀ f ≡ explicate-body (liftₗ dₘ)
  eq꜀ = ≡-trans (lookup-map explicate-body dsᵢ f)
          (≡-cong explicate-body (≡-trans (lookup-map liftₗ dsₘ f) (≡-cong liftₗ (lookup-map (λ D → rco D (λ x → x)) ds₅ f))))
  eqₓ : db (lookup ds꜀ f) ≡ lookup dsₓ f
  eqₓ = ≡-trans (≡-sym (lookup-map db ds꜀ f)) (≡-cong (λ l → lookup l f) (map-db ds꜀))
  code-chain : code′ T₅ (lookup ds₅ f) ＝ codeₜ Tₓ (lookup dsₓ f)
  code-chain =
    code-rco (table-rco ds₅) (lookup ds₅ f)
    ∙ code-lift (table-lift dsₘ) dₘ
    ∙ codeᶜ-cong (∘₁ Envᵈ (I.K ⟹₁ 𝔻) 𝔻 (I.⟦ liftₗ dₘ ⟧ᴷ (tables I.code′ dsᵢ)) (at-point₁ I.K 𝔻 I.idK))
        (C.run (explicate-body (liftₗ dₘ)) T꜀)
        (λ X Y _ _ → body-＝ (table-explicate dsᵢ) (liftₗ dₘ) (env₂ X Y))
    ∙ ap (C.code′ T꜀) (≡→＝ eq꜀) ⁻¹
    ∙ code-＝ TT₄ (lookup ds꜀ f)
    ∙ ap (codeₜ Tₓ) (≡→＝ eqₓ)
