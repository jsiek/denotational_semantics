{-

  Correctness of typed globalize (Clos4ᵀ → Clos5ᵀ,
  Compiler/Typed/Globalize.agda) by a forward simulation between the
  typed machines (see the design note in Semantics/CEK/Smallstep.agda).

  The machines run in lock step. A Clos4ᵀ term is related to a Clos5ᵀ
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

module proof.Correctness.Typed.CEK.GlobalizeSim where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Framework.Lookup using (_!_)
import Language.Typed.Clos4 as S
open import Language.Typed.Clos5
open import Compiler.Typed.Globalize
open import proof.Framework.Membership using (⊑-irr; ⊑-∋-trans)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Correctness.Typed.CEK.Common using (collected≈; Lock; same-stop; same-next; lock)
import Semantics.CEK.Typed.Clos4 as Sₘ
import Semantics.CEK.Typed.Clos5 as Tₘ

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Pointwise as L
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; does)

{- Terms, relative to an interpretation of the references ---------------------}

{- what the code of each definition of a table may be -}
Interp : List ℕ → Set₁
Interp Σ = ∀ {n} → Σ ∋ n → S.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Set

infix 4 _⊢_⇝_
data _⊢_⇝_ {Σ} (I : Interp Σ) {Γ} : ∀ {A} → S.Tm Γ A → Tm Σ Γ A → Set where
  var : ∀ {A} {x : Γ ∋ A} → I ⊢ S.` x ⇝ ` x
  code : ∀ {n} {g : Σ ∋ n} {N} → I g N → I ⊢ S.code N ⇝ fun-ref g
  pack : ∀ {n L L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.pack {n = n} L M ⇝ pack L' M'
  callc : ∀ {L L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.callc L M ⇝ callc L' M'
  lit : ∀ {B c} → I ⊢ S.lit B c ⇝ lit B c
  tuple : ∀ {n} {Ms : Vec _ n} {Ms'} → V.Pointwise (I ⊢_⇝_) Ms Ms' → I ⊢ S.tuple Ms ⇝ tuple Ms'
  get : ∀ {n i M M'} → I ⊢ M ⇝ M' → I ⊢ S.get {n = n} i M ⇝ get i M'
  inl : ∀ {M M'} → I ⊢ M ⇝ M' → I ⊢ S.inl M ⇝ inl M'
  inr : ∀ {M M'} → I ⊢ M ⇝ M' → I ⊢ S.inr M ⇝ inr M'
  case : ∀ {L L' M M' N N'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ N ⇝ N' → I ⊢ S.case L M N ⇝ case L' M' N'
  prim : ∀ {p L L' M M'} → I ⊢ L ⇝ L' → I ⊢ M ⇝ M' → I ⊢ S.prim p L M ⇝ prim p L' M'
  let′ : ∀ {M M' N N'} → I ⊢ M ⇝ M' → I ⊢ N ⇝ N' → I ⊢ S.let′ M N ⇝ let′ M' N'
  inject : ∀ {G M M'} → I ⊢ M ⇝ M' → I ⊢ S.inject G M ⇝ inject G M'
  project : ∀ {t M M'} → I ⊢ M ⇝ M' → I ⊢ S.project t M ⇝ project t M'

{- weakening a term -}
⊢-wk : ∀ {Σ₁ Σ₂} {I : Interp Σ₁} {J : Interp Σ₂} {σ : ∀ {n} → Σ₁ ∋ n → Σ₂ ∋ n}
  → (∀ {n} {g : Σ₁ ∋ n} {N} → I g N → J (σ g) N) → ∀ {Γ A} {M : S.Tm Γ A} {M'} → I ⊢ M ⇝ M' → J ⊢ M ⇝ wk σ M'
⊢-wks : ∀ {Σ₁ Σ₂} {I : Interp Σ₁} {J : Interp Σ₂} {σ : ∀ {n} → Σ₁ ∋ n → Σ₂ ∋ n}
  → (∀ {n} {g : Σ₁ ∋ n} {N} → I g N → J (σ g) N) → ∀ {Γ k} {Ms : Vec (S.Tm Γ Any) k} {Ms'}
  → V.Pointwise (I ⊢_⇝_) Ms Ms' → V.Pointwise (J ⊢_⇝_) Ms (wks σ Ms')
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
⊢-wk h (inject r) = inject (⊢-wk h r)
⊢-wk h (project r) = project (⊢-wk h r)
⊢-wks h [] = []
⊢-wks h (r ∷ rs) = ⊢-wk h r ∷ ⊢-wks h rs

{- the definitions made before grow into those made after -}
data MExt : ∀ {Σ₁ Σ₂} → Σ₁ ⊑ Σ₂ → Made Σ₁ → Made Σ₂ → Set where
  here : ∀ {Σ} {D : Made Σ} → MExt here⊑ D D
  there : ∀ {Σ₁ Σ₂ n g} {D : Made Σ₁} {D' : Made Σ₂} {N : Code Σ₂ n} → MExt g D D' → MExt (there⊑ g) D (D' ▷ N)

mext-trans : ∀ {Σ₁ Σ₂ Σ₃} {g : Σ₁ ⊑ Σ₂} {g' : Σ₂ ⊑ Σ₃} {D₁ D₂ D₃} → MExt g D₁ D₂ → MExt g' D₂ D₃ → MExt (⊑-trans g g') D₁ D₃
mext-trans x here = x
mext-trans x (there y) = there (mext-trans x y)

glob-grows : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → MExt (Out.grows (glob M D)) D (Out.made (glob M D))
globs-grows : ∀ {Σ Γ n} (Ms : Vec (S.Tm Γ Any) n) (D : Made Σ) → MExt (Out.grows (globs Ms D)) D (Out.made (globs Ms D))
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
glob-grows (S.inject G M) D = glob-grows M D
glob-grows (S.project t M) D = glob-grows M D
globs-grows [] D = here
globs-grows (M ∷ Ms) D = mext-trans (glob-grows M D) (globs-grows Ms _)

{- The definitions of the final table ------------------------------------------}

module Table {Σ : List ℕ} (defs : All (Code Σ) Σ) where

  {- the code of definition g is related to it -}
  data Top {n} (g : Σ ∋ n) (N : S.Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any) : Set where
    top : (λ {m} → Top {m}) ⊢ N ⇝ defs ! g → Top g N

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
  globs-⇝ : ∀ {Σ₀ Γ k} (Ms : Vec (S.Tm Γ Any) k) (D : Made Σ₀) {s} → Faithful (Out.made (globs Ms D)) s
    → V.Pointwise (I[ s ] ⊢_⇝_) Ms (Out.res (globs Ms D))
  two : ∀ {Σ₀ Γ₁ Γ₂ A B} (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B) (D : Made Σ₀) {s}
    → Faithful (Out.made (glob M (Out.made (glob L D)))) s
    → I[ s ] ⊢ L ⇝ wk (⊑-∋ (Out.grows (glob M (Out.made (glob L D))))) (Out.res (glob L D))
      × I[ s ] ⊢ M ⇝ Out.res (glob M (Out.made (glob L D)))
  two L M D F = lift (glob-⇝ L D (faithful-ext (glob-grows M _) F)) , glob-⇝ M _ F

  glob-⇝ (S.` x) D F = var
  glob-⇝ (S.code N) D (h , F) = code (h N (glob-⇝ N D F))
  glob-⇝ (S.pack L M) D F = pack (proj₁ (two L M D F)) (proj₂ (two L M D F))
  glob-⇝ (S.callc L M) D F = callc (proj₁ (two L M D F)) (proj₂ (two L M D F))
  glob-⇝ (S.lit B c) D F = lit
  glob-⇝ (S.tuple Ms) D F = tuple (globs-⇝ Ms D F)
  glob-⇝ (S.get i M) D F = get (glob-⇝ M D F)
  glob-⇝ (S.inl M) D F = inl (glob-⇝ M D F)
  glob-⇝ (S.inr M) D F = inr (glob-⇝ M D F)
  glob-⇝ (S.case L M N) D F =
    case (lift (glob-⇝ L D (faithful-ext (mext-trans (glob-grows M _) (glob-grows N _)) F)))
         (lift (glob-⇝ M _ (faithful-ext (glob-grows N _) F))) (glob-⇝ N _ F)
  glob-⇝ (S.prim p L M) D F = prim (proj₁ (two L M D F)) (proj₂ (two L M D F))
  glob-⇝ (S.let′ M N) D F = let′ (proj₁ (two M N D F)) (proj₂ (two M N D F))
  glob-⇝ (S.inject G M) D F = inject (glob-⇝ M D F)
  glob-⇝ (S.project t M) D F = project (glob-⇝ M D F)
  globs-⇝ [] D F = []
  globs-⇝ (M ∷ Ms) D F = proj₁ (two M (S.tuple Ms) D F) ∷ globs-⇝ Ms _ F

  {- close puts the definitions made before at their positions -}
  suffix : ∀ {Σ₀ Σ₁} {s : Σ₀ ⊑ Σ₁} {D : Made Σ₀} {D₁ : Made Σ₁} → MExt s D D₁ → ∀ (q : Σ₁ ⊑ Σ) {n} (x : Σ₀ ∋ n)
    → close D₁ q ! ⊑-∋ s x ≡ close D (⊑-trans s q) ! x
  suffix {D = D} here q x = cong (λ r → close D r ! x) (⊑-irr _ _)
  suffix {D = D} (there e) q x = trans (suffix e (⊑-trans (there⊑ here⊑) q) x) (cong (λ r → close D r ! x) (⊑-irr _ _))

  close-faithful : ∀ {D_f : Made Σ} → defs ≡ close D_f here⊑ → ∀ {Σ₀} {s : Σ₀ ⊑ Σ} {D : Made Σ₀} → MExt s D D_f → Faithful D s
  close-faithful e {D = []} x = tt
  close-faithful e {s = s} {D = D ▷ N'} x =
    (λ N r → top (subst ((λ {m} → Top {m}) ⊢ N ⇝_) (sym (trans (cong (_! ⊑-∋ s Z) e) (suffix x here⊑ Z))) (⊢-wk (λ r → r) r)))
    , close-faithful e (mext-trans (there here) x)

  {- The simulation relation ----------------------------------------------------}

  infix 4 _⇝_ _≈_ _≈k_ _~_
  _⇝_ : ∀ {Γ A} → S.Tm Γ A → Tm Σ Γ A → Set
  M ⇝ M' = (λ {m} → Top {m}) ⊢ M ⇝ M'

  data _≈_ : ∀ {A} → Sₘ.Val A → Tₘ.Val Σ A → Set where
    code≈ : ∀ {n N} {g : Σ ∋ n} → Top g N → Sₘ.code N ≈ Tₘ.code g
    pack≈ : ∀ {n} {c : Sₘ.Val (code n)} {c' e e'} → c ≈ c' → e ≈ e' → Sₘ.pack c e ≈ Tₘ.pack c' e'
    const≈ : ∀ {B c} → Sₘ.const {B} c ≈ Tₘ.const c
    tup≈ : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Sₘ.tup vs ≈ Tₘ.tup ws
    inl≈ : ∀ {v w} → v ≈ w → Sₘ.inl v ≈ Tₘ.inl w
    inr≈ : ∀ {v w} → v ≈ w → Sₘ.inr v ≈ Tₘ.inr w
    dyn≈ : ∀ {G v w} → v ≈ w → Sₘ.dyn G v ≈ Tₘ.dyn G w

  record EnvRel {Γ} (ρ₁ : Sₘ.Env Γ) (ρ₂ : Tₘ.Env Σ Γ) : Set where
    constructor env
    field at : ∀ {A} (x : Γ ∋ A) → ρ₁ Sₘ.! x ≈ ρ₂ ! x
  open EnvRel

  data _≈k_ : ∀ {A} → Sₘ.Cont A → Tₘ.Cont Σ A → Set where
    halt : Sₘ.halt ≈k Tₘ.halt
    callL : ∀ {Γ M M'} {ρ₁ : Sₘ.Env Γ} {ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂ → Sₘ.callL M ρ₁ κ₁ ≈k Tₘ.callL M' ρ₂ κ₂
    callR : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.callR v κ₁ ≈k Tₘ.callR w κ₂
    packL : ∀ {Γ n} {M : S.Tm Γ ⟪ tup n ⟫} {M' ρ₁ ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.packL M ρ₁ κ₁ ≈k Tₘ.packL M' ρ₂ κ₂
    packR : ∀ {n} {v : Sₘ.Val (code n)} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.packR v κ₁ ≈k Tₘ.packR w κ₂
    tupK : ∀ {Γ n j vs ws} {Ms : Vec _ j} {Ms' : Vec (Tm Σ Γ Any) j} {ρ₁ : Sₘ.Env Γ} {ρ₂} {e : _ ≡ n} {e' κ₁ κ₂}
      → L.Pointwise _≈_ vs ws → V.Pointwise _⇝_ Ms Ms' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.tupK vs Ms ρ₁ e κ₁ ≈k Tₘ.tupK ws Ms' ρ₂ e' κ₂
    getK : ∀ {n i κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.getK {n} i κ₁ ≈k Tₘ.getK i κ₂
    inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.inlK κ₁ ≈k Tₘ.inlK κ₂
    inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.inrK κ₁ ≈k Tₘ.inrK κ₂
    caseK : ∀ {Γ M M' N N'} {ρ₁ : Sₘ.Env Γ} {ρ₂ κ₁ κ₂} → M ⇝ M' → N ⇝ N' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.caseK M N ρ₁ κ₁ ≈k Tₘ.caseK M' N' ρ₂ κ₂
    primL : ∀ {Γ p M M'} {ρ₁ : Sₘ.Env Γ} {ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.primL p M ρ₁ κ₁ ≈k Tₘ.primL p M' ρ₂ κ₂
    primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.primR p n κ₁ ≈k Tₘ.primR p n κ₂
    letK : ∀ {Γ N N'} {ρ₁ : Sₘ.Env Γ} {ρ₂ κ₁ κ₂} → N ⇝ N' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.letK N ρ₁ κ₁ ≈k Tₘ.letK N' ρ₂ κ₂
    injK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.injK G κ₁ ≈k Tₘ.injK G κ₂
    projK : ∀ {t κ₁ κ₂} → κ₁ ≈k κ₂ → Sₘ.projK t κ₁ ≈k Tₘ.projK t κ₂

  data _~_ : Sₘ.State → Tₘ.State Σ → Set where
    eval~ : ∀ {Γ A} {M : S.Tm Γ A} {M' ρ₁ ρ₂ κ₁ κ₂} → M ⇝ M' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.eval M ρ₁ κ₁ ~ Tₘ.eval M' ρ₂ κ₂
    ret~ : ∀ {A} {v : Sₘ.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Sₘ.ret v κ₁ ~ Tₘ.ret w κ₂

  obs≈ : ∀ {A} {v : Sₘ.Val A} {w} → v ≈ w → Sₘ.obs v ≡ Tₘ.obs w
  obs≈* : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Sₘ.obs-vec vs ≡ Tₘ.obs-vec ws
  obs≈ (code≈ _) = refl
  obs≈ (pack≈ _ _) = refl
  obs≈ const≈ = refl
  obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (dyn≈ r) = obs≈ r
  obs≈* [] = refl
  obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

  δ≈ : ∀ p n m → Sₘ.δᵀ p n m ≈ Tₘ.δᵀ {Σ} p n m
  δ≈ sub n m = const≈
  δ≈ eq n m with does (n ≟ m)
  ... | true = inl≈ (dyn≈ (tup≈ []))
  ... | false = inr≈ (dyn≈ (tup≈ []))

  env-ext : ∀ {Γ B} {ρ₁ : Sₘ.Env Γ} {ρ₂} {v : Sₘ.Val B} {w} → v ≈ w → EnvRel ρ₁ ρ₂ → EnvRel (v ∷ ρ₁) (w ∷ ρ₂)
  env-ext r er = env λ { Z → r ; (S x) → at er x }

  {- the only error: both machines project, and fail, at the same time -}
  proj~ : ∀ {H t v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
    → Lock _~_ (Sₘ.step (Sₘ.ret (Sₘ.dyn H v) (Sₘ.projK t κ₁))) (Tₘ.step defs (Tₘ.ret (Tₘ.dyn H w) (Tₘ.projK t κ₂)))
  proj~ {H} {t} r k with H ≟F flat t
  ... | yes refl = same-next (ret~ r k)
  ... | no _ = same-stop

  module _ (M₀ : Tm Σ [] Any) where

    L₂ = Tₘ.sem (program defs M₀)

    tuple-next~ : ∀ {Γ n j vs ws} {Ms : Vec _ j} {Ms' : Vec (Tm Σ Γ Any) j} {ρ₁ : Sₘ.Env Γ} {ρ₂} {e : _ ≡ n} {e' κ₁ κ₂}
      → L.Pointwise _≈_ vs ws → V.Pointwise _⇝_ Ms Ms' → EnvRel ρ₁ ρ₂ → κ₁ ≈k κ₂
      → Sₘ.tuple-next vs Ms ρ₁ e κ₁ ~ Tₘ.tuple-next ws Ms' ρ₂ e' κ₂
    tuple-next~ {e = e} {e'} rs [] er k = ret~ (tup≈ (collected≈ rs e e')) k
    tuple-next~ rs (m ∷ ms) er k = eval~ m er (tupK rs ms er k)

    sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Sₘ.step s₁) s₂
    sim (eval~ (var {x = x}) er k) = steps₁ refl (ret~ (at er x) k)
    sim (eval~ (code h) er k) = steps₁ refl (ret~ (code≈ h) k)
    sim (eval~ (pack m m') er k) = steps₁ refl (eval~ m er (packL m' er k))
    sim (eval~ (callc m m') er k) = steps₁ refl (eval~ m er (callL m' er k))
    sim (eval~ lit er k) = steps₁ refl (ret~ const≈ k)
    sim (eval~ (tuple ms) er k) = steps₁ refl (tuple-next~ L.[] ms er k)
    sim (eval~ (get m) er k) = steps₁ refl (eval~ m er (getK k))
    sim (eval~ (inl m) er k) = steps₁ refl (eval~ m er (inlK k))
    sim (eval~ (inr m) er k) = steps₁ refl (eval~ m er (inrK k))
    sim (eval~ (case m m' m'') er k) = steps₁ refl (eval~ m er (caseK m' m'' er k))
    sim (eval~ (prim m m') er k) = steps₁ refl (eval~ m er (primL m' er k))
    sim (eval~ (let′ m m') er k) = steps₁ refl (eval~ m er (letK m' er k))
    sim (eval~ (inject m) er k) = steps₁ refl (eval~ m er (injK k))
    sim (eval~ (project m) er k) = steps₁ refl (eval~ m er (projK k))
    sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
    sim (ret~ r (callL m er k)) = steps₁ refl (eval~ m er (callR r k))
    sim (ret~ r (callR (pack≈ (code≈ (top h)) re) k)) = steps₁ refl (eval~ h (env λ { Z → r ; (S Z) → re }) k)
    sim (ret~ r (packL m er k)) = steps₁ refl (eval~ m er (packR r k))
    sim (ret~ r (packR r' k)) = steps₁ refl (ret~ (pack≈ r' r) k)
    sim (ret~ r (tupK rs ms er k)) = steps₁ refl (tuple-next~ (r L.∷ rs) ms er k)
    sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (V.lookup rs i) k)
    sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
    sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
    sim (ret~ (inl≈ r) (caseK m m' er k)) = steps₁ refl (eval~ m (env-ext r er) k)
    sim (ret~ (inr≈ r) (caseK m m' er k)) = steps₁ refl (eval~ m' (env-ext r er) k)
    sim (ret~ const≈ (primL m er k)) = steps₁ refl (eval~ m er (primR k))
    sim (ret~ (const≈ {c = c}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n c) k)
    sim (ret~ r (letK m er k)) = steps₁ refl (eval~ m (env-ext r er) k)
    sim (ret~ r (injK k)) = steps₁ refl (ret~ (dyn≈ r) k)
    sim (ret~ (dyn≈ r) (projK k)) = lock (proj~ r k)

{- The end theorem: for every Clos4ᵀ program ----------------------------------}

globalize-correct : ∀ (M : S.Tm [] Any) → Equivalent (Sₘ.sem M) (Tₘ.sem (globalize M))
globalize-correct M =
  equivalent (plus-simulation _~_ (eval~ (glob-⇝ M [] (close-faithful refl here)) (env λ ()) halt) (sim (Out.res (glob M []))))
  where open Table (close (Out.made (glob M [])) here⊑)
