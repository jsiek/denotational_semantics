{-

  Correctness of globalize (Clos4μ → Clos5μ, Mu/Compiler/Globalize.agda)
  by a forward simulation between the machines, as for typed globalize
  (proof/Correctness/CEK/GlobalizeSim.agda).

  The machines run in lock step. A Clos4μ term is related to a Clos5μ
  term over the final table (Top ⊢ M ⇝ M') when they agree, except that
  code N is related to fun-ref g when N is related to definition g
  (Top g N). Values are related in the same way (code N to code g),
  environments pointwise, continuations frame by frame.

  The pass makes each term over the table made so far, and later weakens
  it; so the relation is taken relative to an interpretation I of the
  references of a smaller table (I ⊢ M ⇝ M'), and weakening a term
  changes the interpretation (⊢-wk). The definitions made before a term
  are those of the final table at the same positions, each the
  weakening of what was made (Faithful): glob makes only more
  definitions (glob-grows, MExt), and close weakens each to the whole
  table (close-faithful). So the whole program is related to the main
  term of globalize (glob-⇝).

-}

module Mu.proof.Correctness.CEK.GlobalizeSim where

open import Mu.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Mu.Language.Clos4 as S
open import Mu.Language.Clos5
open import Mu.Compiler.Globalize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; All₂; lookup₂; _<><₂_)
open import proof.Framework.Lookup using (⊑-irr; ⊑-∋-trans)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.CEK.Clos4 as Sₘ
import Mu.Semantics.CEK.Clos5 as Tₘ

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry′)
open import Data.Unit using (⊤; tt)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- Terms, relative to an interpretation of the references ---------------------}

{- what the code of each definition of a table may be -}
Interp : List DSig → Set₁
Interp Σ = ∀ {s} → Σ ∋ s → S.Tm (Args s) (DSig.cod s) → Set

infix 4 _⊢_⇝_
data _⊢_⇝_ {Σ} (I : Interp Σ) {Γ} : ∀ {A} → S.Tm Γ A → Tm Σ Γ A → Set where
  var : ∀ {A} {x : Γ ∋ A} → I ⊢ S.` x ⇝ ` x
  code : ∀ {Δ A B} {g : Σ ∋ sig Δ A B} {N} → I g N → I ⊢ S.code N ⇝ fun-ref g
  pack : ∀ {Δ A B} {L : S.Tm Γ (code Δ A B)} {L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.pack L M ⇝ pack L' M'
  callc : ∀ {A B} {L : S.Tm Γ (A ⇒ B)} {L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.callc L M ⇝ callc L' M'
  lit : ∀ {B c} → I ⊢ S.lit B c ⇝ lit B c
  tuple : ∀ {Δ} {Ms : All _ Δ} {Ms'} → All₂ (I ⊢_⇝_) Ms Ms' → I ⊢ S.tuple Ms ⇝ tuple Ms'
  get : ∀ {Δ A} {i : Δ ∋ A} {M M'} → I ⊢ M ⇝ M' → I ⊢ S.get i M ⇝ get i M'
  inl : ∀ {A B} {M : S.Tm Γ A} {M'} → I ⊢ M ⇝ M' → I ⊢ S.inl {B = B} M ⇝ inl M'
  inr : ∀ {A B} {M : S.Tm Γ B} {M'} → I ⊢ M ⇝ M' → I ⊢ S.inr {A = A} M ⇝ inr M'
  case : ∀ {A B C} {L : S.Tm Γ (A ⊹ B)} {L'} {M : S.Tm (A ∷ Γ) C} {M' N N'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ N ⇝ N'
    → I ⊢ S.case L M N ⇝ case L' M' N'
  prim : ∀ {p L L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.prim p L M ⇝ prim p L' M'
  let′ : ∀ {A B} {M : S.Tm Γ A} {M'} {N : S.Tm (A ∷ Γ) B} {N'} → I ⊢ M ⇝ M' → I ⊢ N ⇝ N' → I ⊢ S.let′ M N ⇝ let′ M' N'
  fold : ∀ {A M M'} → I ⊢ M ⇝ M' → I ⊢ S.fold {A = A} M ⇝ fold M'
  unfold : ∀ {A M M'} → I ⊢ M ⇝ M' → I ⊢ S.unfold {A = A} M ⇝ unfold M'

{- weakening a term -}
⊢-wk : ∀ {Σ₁ Σ₂} {I : Interp Σ₁} {J : Interp Σ₂} {σ : ∀ {s} → Σ₁ ∋ s → Σ₂ ∋ s}
  → (∀ {s} {g : Σ₁ ∋ s} {N} → I g N → J (σ g) N) → ∀ {Γ A} {M : S.Tm Γ A} {M'} → I ⊢ M ⇝ M' → J ⊢ M ⇝ wk σ M'
⊢-wks : ∀ {Σ₁ Σ₂} {I : Interp Σ₁} {J : Interp Σ₂} {σ : ∀ {s} → Σ₁ ∋ s → Σ₂ ∋ s}
  → (∀ {s} {g : Σ₁ ∋ s} {N} → I g N → J (σ g) N) → ∀ {Γ Δ} {Ms : All (S.Tm Γ) Δ} {Ms'}
  → All₂ (I ⊢_⇝_) Ms Ms' → All₂ (J ⊢_⇝_) Ms (wks σ Ms')
⊢-wk h var = var
⊢-wk h (code r) = code (h r)
⊢-wk h (pack r r') = pack (⊢-wk h r) (⊢-wk h r')
⊢-wk h (callc r r') = callc (⊢-wk h r) (⊢-wk h r')
⊢-wk h lit = lit
⊢-wk h (tuple rs) = tuple (⊢-wks h rs)
⊢-wk h (get r) = get (⊢-wk h r)
⊢-wk h (inl r) = inl (⊢-wk h r)
⊢-wk h (inr r) = inr (⊢-wk h r)
⊢-wk h (case r r' r'') = case (⊢-wk h r) (⊢-wk h r') (⊢-wk h r'')
⊢-wk h (prim r r') = prim (⊢-wk h r) (⊢-wk h r')
⊢-wk h (let′ r r') = let′ (⊢-wk h r) (⊢-wk h r')
⊢-wk h (fold r) = fold (⊢-wk h r)
⊢-wk h (unfold r) = unfold (⊢-wk h r)
⊢-wks h [] = []
⊢-wks h (r ∷ rs) = ⊢-wk h r ∷ ⊢-wks h rs

{- the definitions made before grow into those made after -}
data MExt : ∀ {Σ₁ Σ₂} → Σ₁ ⊑ Σ₂ → Made Σ₁ → Made Σ₂ → Set where
  here : ∀ {Σ} {D : Made Σ} → MExt here⊑ D D
  there : ∀ {Σ₁ Σ₂ s g} {D : Made Σ₁} {D' : Made Σ₂} {N : Code Σ₂ s} → MExt g D D' → MExt (there⊑ g) D (D' ▷ N)

mext-trans : ∀ {Σ₁ Σ₂ Σ₃} {g : Σ₁ ⊑ Σ₂} {g' : Σ₂ ⊑ Σ₃} {D₁ D₂ D₃} → MExt g D₁ D₂ → MExt g' D₂ D₃ → MExt (⊑-trans g g') D₁ D₃
mext-trans x here = x
mext-trans x (there y) = there (mext-trans x y)

glob-grows : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → MExt (Out.grows (glob M D)) D (Out.made (glob M D))
globs-grows : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → MExt (Out.grows (globs Ms D)) D (Out.made (globs Ms D))
glob-grows (S.` x) D = here
glob-grows (S.code N) D = there (glob-grows N D)
glob-grows (S.pack L M) D = mext-trans (glob-grows L D) (glob-grows M _)
glob-grows (S.callc L M) D = mext-trans (glob-grows L D) (glob-grows M _)
glob-grows (S.lit B c) D = here
glob-grows (S.tuple Ms) D = globs-grows Ms D
glob-grows (S.get i M) D = glob-grows M D
glob-grows (S.inl M) D = glob-grows M D
glob-grows (S.inr M) D = glob-grows M D
glob-grows (S.case L M N) D = mext-trans (glob-grows L D) (mext-trans (glob-grows M _) (glob-grows N _))
glob-grows (S.prim p L M) D = mext-trans (glob-grows L D) (glob-grows M _)
glob-grows (S.let′ M N) D = mext-trans (glob-grows M D) (glob-grows N _)
glob-grows (S.fold M) D = glob-grows M D
glob-grows (S.unfold M) D = glob-grows M D
globs-grows [] D = here
globs-grows (M ∷ Ms) D = mext-trans (glob-grows M D) (globs-grows Ms _)

{- The definitions of the final table ------------------------------------------}

module Table {Σ : List DSig} (defs : All (Code Σ) Σ) where

  {- the code of definition g is related to it -}
  data Top {s} (g : Σ ∋ s) (N : S.Tm (Args s) (DSig.cod s)) : Set where
    top : (λ {m} → Top {m}) ⊢ N ⇝ lookup defs g → Top g N

  {- the references of a smaller table, at their positions in Σ -}
  I[_] : ∀ {Σ₀} → Σ₀ ⊑ Σ → Interp Σ₀
  I[ s ] g N = Top (⊑-∋ s g) N

  {- the definitions made, each related to the definition at its position -}
  Faithful : ∀ {Σ₀} → Made Σ₀ → Σ₀ ⊑ Σ → Set
  Faithful [] s = ⊤
  Faithful (D ▷ N') s = (∀ N → I[ ⊑-trans (there⊑ here⊑) s ] ⊢ N ⇝ N' → Top (⊑-∋ s Z) N) × Faithful D (⊑-trans (there⊑ here⊑) s)

  faithful-ext : ∀ {Σ₁ Σ₂} {t : Σ₁ ⊑ Σ₂} {s : Σ₂ ⊑ Σ} {D₁ D₂} → MExt t D₁ D₂ → Faithful D₂ s → Faithful D₁ (⊑-trans t s)
  faithful-ext {s = s} {D₁ = D₁} here F = subst (Faithful D₁) (⊑-irr _ _) F
  faithful-ext {t = there⊑ t} {s} {D₁ = D₁} (there x) (_ , F) = subst (Faithful D₁) (⊑-irr _ _) (faithful-ext x F)

  {- weakening a term made earlier -}
  lift : ∀ {Σ₁ Σ₂} {t : Σ₁ ⊑ Σ₂} {s : Σ₂ ⊑ Σ} {Γ A} {M : S.Tm Γ A} {M'}
    → I[ ⊑-trans t s ] ⊢ M ⇝ M' → I[ s ] ⊢ M ⇝ wk (⊑-∋ t) M'
  lift {t = t} {s} = ⊢-wk λ {_} {g} r → subst (λ h → Top h _) (⊑-∋-trans t s g) r

  glob-⇝ : ∀ {Σ₀ Γ A} (M : S.Tm Γ A) (D : Made Σ₀) {s} → Faithful (Out.made (glob M D)) s → I[ s ] ⊢ M ⇝ Out.res (glob M D)
  globs-⇝ : ∀ {Σ₀ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ₀) {s} → Faithful (Out.made (globs Ms D)) s
    → All₂ (I[ s ] ⊢_⇝_) Ms (Out.res (globs Ms D))
  two : ∀ {Σ₀ Γ₁ Γ₂ A B} (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B) (D : Made Σ₀) {s}
    → Faithful (Out.made (glob M (Out.made (glob L D)))) s
    → I[ s ] ⊢ L ⇝ wk (⊑-∋ (Out.grows (glob M (Out.made (glob L D))))) (Out.res (glob L D))
      × I[ s ] ⊢ M ⇝ Out.res (glob M (Out.made (glob L D)))
  two L M D F = lift (glob-⇝ L D (faithful-ext (glob-grows M _) F)) , glob-⇝ M _ F

  glob-⇝ (S.` x) D F = var
  glob-⇝ (S.code N) D (h , F) = code (h N (glob-⇝ N D F))
  glob-⇝ (S.pack L M) D F = uncurry′ pack (two L M D F)
  glob-⇝ (S.callc L M) D F = uncurry′ callc (two L M D F)
  glob-⇝ (S.lit B c) D F = lit
  glob-⇝ (S.tuple Ms) D F = tuple (globs-⇝ Ms D F)
  glob-⇝ (S.get i M) D F = get (glob-⇝ M D F)
  glob-⇝ (S.inl M) D F = inl (glob-⇝ M D F)
  glob-⇝ (S.inr M) D F = inr (glob-⇝ M D F)
  glob-⇝ (S.case L M N) D F =
    case (lift (glob-⇝ L D (faithful-ext (mext-trans (glob-grows M _) (glob-grows N _)) F)))
         (lift (glob-⇝ M _ (faithful-ext (glob-grows N _) F))) (glob-⇝ N _ F)
  glob-⇝ (S.prim p L M) D F = uncurry′ prim (two L M D F)
  glob-⇝ (S.let′ M N) D F = uncurry′ let′ (two M N D F)
  glob-⇝ (S.fold M) D F = fold (glob-⇝ M D F)
  glob-⇝ (S.unfold M) D F = unfold (glob-⇝ M D F)
  globs-⇝ [] D F = []
  globs-⇝ (M ∷ Ms) D F = proj₁ (two M (S.tuple Ms) D F) ∷ globs-⇝ Ms _ F

  {- close puts the definitions made before at their positions -}
  suffix : ∀ {Σ₀ Σ₁} {s : Σ₀ ⊑ Σ₁} {D : Made Σ₀} {D₁ : Made Σ₁} → MExt s D D₁ → ∀ (q : Σ₁ ⊑ Σ) {t} (x : Σ₀ ∋ t)
    → lookup (close D₁ q) (⊑-∋ s x) ≡ lookup (close D (⊑-trans s q)) x
  suffix {D = D} here q x = cong (λ r → lookup (close D r) x) (⊑-irr _ _)
  suffix {D = D} (there e) q x = trans (suffix e (⊑-trans (there⊑ here⊑) q) x) (cong (λ r → lookup (close D r) x) (⊑-irr _ _))

  close-faithful : ∀ {D_f : Made Σ} → defs ≡ close D_f here⊑ → ∀ {Σ₀} {s : Σ₀ ⊑ Σ} {D : Made Σ₀} → MExt s D D_f → Faithful D s
  close-faithful e {D = []} x = tt
  close-faithful e {s = s} {D = D ▷ N'} x =
    (λ N r → top (subst ((λ {m} → Top {m}) ⊢ N ⇝_) (sym (trans (cong (λ ds → lookup ds (⊑-∋ s Z)) e) (suffix x here⊑ Z)))
                        (⊢-wk (λ r → r) r)))
    , close-faithful e (mext-trans (there here) x)

  {- The simulation relation ----------------------------------------------------}

  infix 4 _⇝_ _≈_ _≈k_ _~_
  _⇝_ : ∀ {Γ A} → S.Tm Γ A → Tm Σ Γ A → Set
  M ⇝ M' = (λ {m} → Top {m}) ⊢ M ⇝ M'

  data _≈_ : ∀ {A} → Sₘ.Val A → Tₘ.Val Σ A → Set where
    code≈ : ∀ {Δ A B N} {g : Σ ∋ sig Δ A B} → Top g N → Sₘ.code N ≈ Tₘ.code g
    pack≈ : ∀ {Δ A B} {c : Sₘ.Val (code Δ A B)} {c' e e'} → c ≈ c' → e ≈ e' → Sₘ.pack c e ≈ Tₘ.pack c' e'
    const≈ : ∀ {B c} → Sₘ.const {B} c ≈ Tₘ.const c
    tup≈ : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → Sₘ.tup vs ≈ Tₘ.tup ws
    inl≈ : ∀ {A B v w} → v ≈ w → Sₘ.inl {A} {B} v ≈ Tₘ.inl w
    inr≈ : ∀ {A B v w} → v ≈ w → Sₘ.inr {A} {B} v ≈ Tₘ.inr w
    fold≈ : ∀ {A v w} → v ≈ w → Sₘ.fold {A} v ≈ Tₘ.fold w

  EnvRel : ∀ {Γ} → Sₘ.Env Γ → Tₘ.Env Σ Γ → Set
  EnvRel = All₂ _≈_

  data _≈k_ : ∀ {A} → Sₘ.Cont A → Tₘ.Cont Σ A → Set where
    halt : ∀ {A} → Sₘ.halt {A} ≈k Tₘ.halt
    callL : ∀ {Γ A B} {M : S.Tm Γ A} {M' ρ₁ ρ₂} {κ₁ : Sₘ.Cont B} {κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.callL M ρ₁ κ₁ ≈k Tₘ.callL M' ρ₂ κ₂
    callR : ∀ {A B v w} {κ₁ : Sₘ.Cont B} {κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.callR {A} v κ₁ ≈k Tₘ.callR w κ₂
    packL : ∀ {Γ Δ A B} {M : S.Tm Γ (tup Δ)} {M' ρ₁ ρ₂} {κ₁ : Sₘ.Cont (A ⇒ B)} {κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.packL M ρ₁ κ₁ ≈k Tₘ.packL M' ρ₂ κ₂
    packR : ∀ {Δ A B} {v : Sₘ.Val (code Δ A B)} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.packR v κ₁ ≈k Tₘ.packR w κ₂
    tupK : ∀ {Γ Δ' A Δ} {vs : All _ Δ'} {ws} {Ms : All (S.Tm Γ) Δ} {Ms'} {ρ₁ ρ₂} {κ₁ : Sₘ.Cont (tup (Δ' <>< (A ∷ Δ)))} {κ₂}
      → All₂ _≈_ vs ws → All₂ _⇝_ Ms Ms' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.tupK vs Ms ρ₁ κ₁ ≈k Tₘ.tupK ws Ms' ρ₂ κ₂
    getK : ∀ {Δ A i κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.getK {Δ} {A} i κ₁ ≈k Tₘ.getK i κ₂
    inlK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.inlK {A} {B} κ₁ ≈k Tₘ.inlK κ₂
    inrK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.inrK {A} {B} κ₁ ≈k Tₘ.inrK κ₂
    caseK : ∀ {Γ A B C} {M : S.Tm (A ∷ Γ) C} {M'} {N : S.Tm (B ∷ Γ) C} {N' ρ₁ ρ₂ κ₁ κ₂} → M ⇝ M' → N ⇝ N' → EnvRel ρ₁ ρ₂
      → κ₁ ≈k κ₂ → Sₘ.caseK M N ρ₁ κ₁ ≈k Tₘ.caseK M' N' ρ₂ κ₂
    primL : ∀ {Γ p} {M : S.Tm Γ _} {M' ρ₁ ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.primL p M ρ₁ κ₁ ≈k Tₘ.primL p M' ρ₂ κ₂
    primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.primR p n κ₁ ≈k Tₘ.primR p n κ₂
    letK : ∀ {Γ A B} {N : S.Tm (A ∷ Γ) B} {N' ρ₁ ρ₂ κ₁ κ₂} → N ⇝ N' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.letK N ρ₁ κ₁ ≈k Tₘ.letK N' ρ₂ κ₂
    foldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.foldK {A} κ₁ ≈k Tₘ.foldK κ₂
    unfoldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.unfoldK {A} κ₁ ≈k Tₘ.unfoldK κ₂

  data _~_ : Sₘ.State → Tₘ.State Σ → Set where
    eval~ : ∀ {Γ A} {M : S.Tm Γ A} {M' ρ₁ ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.eval M ρ₁ κ₁ ~ Tₘ.eval M' ρ₂ κ₂
    ret~ : ∀ {A} {v : Sₘ.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.ret v κ₁ ~ Tₘ.ret w κ₂

  obs≈ : ∀ {A} {v : Sₘ.Val A} {w} → v ≈ w → Sₘ.obs v ≡ Tₘ.obs w
  obs≈* : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → Sₘ.obs-all vs ≡ Tₘ.obs-all ws
  obs≈ (code≈ _) = refl
  obs≈ (pack≈ _ _) = refl
  obs≈ const≈ = refl
  obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (fold≈ r) = obs≈ r
  obs≈* [] = refl
  obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

  δ≈ : ∀ p n m → Sₘ.δᵀ p n m ≈ Tₘ.δᵀ {Σ} p n m
  δ≈ sub n m = const≈
  δ≈ eq n m with does (n ≟ m)
  ... | true = inl≈ (tup≈ [])
  ... | false = inr≈ (tup≈ [])

  module _ {T : Type} (M₀ : Tm Σ [] T) where

    L₂ = Tₘ.sem (program defs M₀)

    tuple-next~ : ∀ {Γ Δ' Δ} {vs : All _ Δ'} {ws} {Ms : All (S.Tm Γ) Δ} {Ms'} {ρ₁ ρ₂} {κ₁ : Sₘ.Cont (tup (Δ' <>< Δ))} {κ₂}
      → All₂ _≈_ vs ws → All₂ _⇝_ Ms Ms' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.tuple-next vs Ms ρ₁ κ₁ ~ Tₘ.tuple-next ws Ms' ρ₂ κ₂
    tuple-next~ rs [] er k = ret~ (tup≈ (rs <><₂ [])) k
    tuple-next~ rs (m ∷ ms) er k = eval~ m er (tupK rs ms er k)

    sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Sₘ.step s₁) s₂
    sim (eval~ (var {x = x}) er k) = steps₁ refl (ret~ (lookup₂ er x) k)
    sim (eval~ (code h) er k) = steps₁ refl (ret~ (code≈ h) k)
    sim (eval~ (pack m m') er k) = steps₁ refl (eval~ m er (packL m' er k))
    sim (eval~ (callc m m') er k) = steps₁ refl (eval~ m er (callL m' er k))
    sim (eval~ lit er k) = steps₁ refl (ret~ const≈ k)
    sim (eval~ (tuple ms) er k) = steps₁ refl (tuple-next~ [] ms er k)
    sim (eval~ (get m) er k) = steps₁ refl (eval~ m er (getK k))
    sim (eval~ (inl m) er k) = steps₁ refl (eval~ m er (inlK k))
    sim (eval~ (inr m) er k) = steps₁ refl (eval~ m er (inrK k))
    sim (eval~ (case m m' m'') er k) = steps₁ refl (eval~ m er (caseK m' m'' er k))
    sim (eval~ (prim m m') er k) = steps₁ refl (eval~ m er (primL m' er k))
    sim (eval~ (let′ m m') er k) = steps₁ refl (eval~ m er (letK m' er k))
    sim (eval~ (fold m) er k) = steps₁ refl (eval~ m er (foldK k))
    sim (eval~ (unfold m) er k) = steps₁ refl (eval~ m er (unfoldK k))
    sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
    sim (ret~ r (callL m er k)) = steps₁ refl (eval~ m er (callR r k))
    sim (ret~ r (callR (pack≈ (code≈ (top h)) re) k)) = steps₁ refl (eval~ h (r ∷ re ∷ []) k)
    sim (ret~ r (packL m er k)) = steps₁ refl (eval~ m er (packR r k))
    sim (ret~ r (packR r' k)) = steps₁ refl (ret~ (pack≈ r' r) k)
    sim (ret~ r (tupK rs ms er k)) = steps₁ refl (tuple-next~ (r ∷ rs) ms er k)
    sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (lookup₂ rs i) k)
    sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
    sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
    sim (ret~ (inl≈ r) (caseK m m' er k)) = steps₁ refl (eval~ m (r ∷ er) k)
    sim (ret~ (inr≈ r) (caseK m m' er k)) = steps₁ refl (eval~ m' (r ∷ er) k)
    sim (ret~ const≈ (primL m er k)) = steps₁ refl (eval~ m er (primR k))
    sim (ret~ (const≈ {c = c}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n c) k)
    sim (ret~ r (letK m er k)) = steps₁ refl (eval~ m (r ∷ er) k)
    sim (ret~ r (foldK k)) = steps₁ refl (ret~ (fold≈ r) k)
    sim (ret~ (fold≈ r) (unfoldK k)) = steps₁ refl (ret~ r k)

{- The end theorem: for every Clos4μ program ----------------------------------}

globalize-correct : ∀ {A} (M : S.Tm [] A) → Equivalent (Sₘ.sem M) (Tₘ.sem (globalize M))
globalize-correct M =
  equivalent (plus-simulation _~_ (eval~ (glob-⇝ M [] (close-faithful refl here)) [] halt) (sim (Out.res (glob M []))))
  where open Table (close (Out.made (glob M [])) here⊑)
