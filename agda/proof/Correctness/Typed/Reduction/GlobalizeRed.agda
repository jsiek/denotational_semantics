{-

  Correctness of typed globalize (Clos4ᵀ → Clos5ᵀ) by a forward
  simulation between their reduction semantics, in lock step.

  The Clos5ᵀ program runs with the definitions ds that the pass made for
  the whole program, and the relation is for ds: a congruence, closed
  under substitution (≈-trav), except that code N is related to a
  reference f when N is related to the definition ds ! f. The pass
  threads the definitions made so far (Made) through the term, each over
  the table before it, and weakens: a subterm is related to its output,
  weakened to the whole table along s, when the definitions made agree
  with ds along s (Agree).

-}

module proof.Correctness.Typed.Reduction.GlobalizeRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import proof.Framework.Lookup using (⊑-irr; ⊑-∋-trans)
open import Framework.Lookup using (_!_)
open import Language.Typed.Clos4
import Language.Typed.Clos5 as C
open import Compiler.Typed.Globalize
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷; cong₃)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.Clos4 as S
import proof.Semantics.Reduction.Typed.Clos5 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using () renaming (All to Allᵥ; [] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)

{- weakening the table twice -}
wk-wk : ∀ {Σ Σ' Σ'' Γ A} {e : ∀ {n} → Σ' ∋ n → Σ'' ∋ n} {e' : ∀ {n} → Σ ∋ n → Σ' ∋ n} {e'' : ∀ {n} → Σ ∋ n → Σ'' ∋ n}
  → (∀ {n} (x : Σ ∋ n) → e (e' x) ≡ e'' x) → (M : C.Tm Σ Γ A) → C.wk e (C.wk e' M) ≡ C.wk e'' M
wks-wk : ∀ {Σ Σ' Σ'' Γ n} {e : ∀ {n} → Σ' ∋ n → Σ'' ∋ n} {e' : ∀ {n} → Σ ∋ n → Σ' ∋ n} {e'' : ∀ {n} → Σ ∋ n → Σ'' ∋ n}
  → (∀ {n} (x : Σ ∋ n) → e (e' x) ≡ e'' x) → (Ms : Vec (C.Tm Σ Γ Any) n) → C.wks e (C.wks e' Ms) ≡ C.wks e'' Ms
wk-wk h (C.` x) = refl
wk-wk h (C.fun-ref f) = cong C.fun-ref (h f)
wk-wk h (C.pack L M) = cong₂ C.pack (wk-wk h L) (wk-wk h M)
wk-wk h (C.callc L M) = cong₂ C.callc (wk-wk h L) (wk-wk h M)
wk-wk h (C.lit B c) = refl
wk-wk h (C.tuple Ms) = cong C.tuple (wks-wk h Ms)
wk-wk h (C.get i M) = cong (C.get i) (wk-wk h M)
wk-wk h (C.inl M) = cong C.inl (wk-wk h M)
wk-wk h (C.inr M) = cong C.inr (wk-wk h M)
wk-wk h (C.case L M N) = cong₃ C.case (wk-wk h L) (wk-wk h M) (wk-wk h N)
wk-wk h (C.prim p L M) = cong₂ (C.prim p) (wk-wk h L) (wk-wk h M)
wk-wk h (C.let′ M N) = cong₂ C.let′ (wk-wk h M) (wk-wk h N)
wk-wk h (C.inject G M) = cong (C.inject G) (wk-wk h M)
wk-wk h (C.project t M) = cong (C.project t) (wk-wk h M)
wks-wk h [] = refl
wks-wk h (M ∷ Ms) = cong₂ _∷_ (wk-wk h M) (wks-wk h Ms)

module _ {Σf : List ℕ} (ds : All (C.Code Σf) Σf) where

  {- The relation ---------------------------------------------------------------}

  infix 4 _≈_
  data _≈_ : ∀ {Γ A} → Tm Γ A → C.Tm Σf Γ A → Set where
    var≈ : ∀ {Γ A} {x : Γ ∋ A} → ` x ≈ C.` x
    code≈ : ∀ {Γ n N} {f : Σf ∋ n} → N ≈ ds ! f → code {Γ} N ≈ C.fun-ref f
    pack≈ : ∀ {Γ n} {L : Tm Γ (code n)} {L' M M'} → L ≈ L' → M ≈ M' → pack L M ≈ C.pack L' M'
    callc≈ : ∀ {Γ} {L : Tm Γ _} {L' M M'} → L ≈ L' → M ≈ M' → callc L M ≈ C.callc L' M'
    lit≈ : ∀ {Γ B c} → lit {Γ} B c ≈ C.lit B c
    tuple≈ : ∀ {Γ n} {Ms : Vec (Tm Γ Any) n} {Ms'} → Pointwise _≈_ Ms Ms' → tuple Ms ≈ C.tuple Ms'
    get≈ : ∀ {Γ n i} {M : Tm Γ ⟪ tup n ⟫} {M'} → M ≈ M' → get i M ≈ C.get i M'
    inl≈ : ∀ {Γ} {M : Tm Γ Any} {M'} → M ≈ M' → inl M ≈ C.inl M'
    inr≈ : ∀ {Γ} {M : Tm Γ Any} {M'} → M ≈ M' → inr M ≈ C.inr M'
    case≈ : ∀ {Γ} {L : Tm Γ _} {L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N' → case L M N ≈ C.case L' M' N'
    prim≈ : ∀ {Γ p} {L : Tm Γ _} {L' M M'} → L ≈ L' → M ≈ M' → prim p L M ≈ C.prim p L' M'
    let≈ : ∀ {Γ} {M : Tm Γ _} {M' N N'} → M ≈ M' → N ≈ N' → let′ M N ≈ C.let′ M' N'
    inject≈ : ∀ {Γ G} {M : Tm Γ ⟪ G ⟫} {M'} → M ≈ M' → inject G M ≈ C.inject G M'
    project≈ : ∀ {Γ t} {M : Tm Γ Any} {M'} → M ≈ M' → project t M ≈ C.project t M'

  {- The fundamental lemma ----------------------------------------------------------}

  {- the definitions made agree with ds, weakened along s -}
  Agree : ∀ {Σ} → Made Σ → Σ ⊑ Σf → Set
  Agree [] s = ⊤
  Agree (D ▷ N) s = ds ! ⊑-∋ s Z ≡ C.wk (⊑-∋ (⊑-trans (there⊑ here⊑) s)) N × Agree D (⊑-trans (there⊑ here⊑) s)

  agree-irr : ∀ {Σ} {D : Made Σ} {s s'} → Agree D s → Agree D s'
  agree-irr {s = s} {s'} a rewrite ⊑-irr s s' = a

  {- the source is related to the output, weakened, and the definitions made before agree too -}
  Glob : ∀ {Σ Γ A} → Tm Γ A → Made Σ → Out Σ (λ Σ' → C.Tm Σ' Γ A) → Set
  Glob M D (out g D' M') = ∀ s → Agree D' s → M ≈ C.wk (⊑-∋ s) M' × Agree D (⊑-trans g s)

  Globs : ∀ {Σ Γ n} → Vec (Tm Γ Any) n → Made Σ → Out Σ (λ Σ' → Vec (C.Tm Σ' Γ Any) n) → Set
  Globs Ms D (out g D' Ms') = ∀ s → Agree D' s → Pointwise _≈_ Ms (C.wks (⊑-∋ s) Ms') × Agree D (⊑-trans g s)

  {- one operand, and then another, under the weakening of the first -}
  wk≈ : ∀ {Σ Σ' Γ A} {M : Tm Γ A} {M' : C.Tm Σ Γ A} {g : Σ ⊑ Σ'} {s : Σ' ⊑ Σf}
    → M ≈ C.wk (⊑-∋ (⊑-trans g s)) M' → M ≈ C.wk (⊑-∋ s) (C.wk (⊑-∋ g) M')
  wk≈ {M' = M'} {g} {s} r = subst (_ ≈_) (sym (wk-wk (λ x → sym (⊑-∋-trans g s x)) M')) r

  glob≈ : ∀ {Σ Γ A} (M : Tm Γ A) (D : Made Σ) → Glob M D (glob M D)
  globs≈ : ∀ {Σ Γ n} (Ms : Vec (Tm Γ Any) n) (D : Made Σ) → Globs Ms D (globs Ms D)
  glob₁≈ : ∀ {Σ Γ Γ₁ A B} {f : ∀ {Σ'} → C.Tm Σ' Γ₁ A → C.Tm Σ' Γ B} {h : Tm Γ₁ A → Tm Γ B}
    → (∀ {Σ'} {e : ∀ {n} → Σ' ∋ n → Σf ∋ n} {X X'} → X ≈ C.wk e X' → h X ≈ C.wk e (f X'))
    → (M : Tm Γ₁ A) (D : Made Σ) → Glob (h M) D (glob₁ f M D)
  glob₂≈ : ∀ {Σ Γ Γ₁ Γ₂ A B Cc} {f : ∀ {Σ'} → C.Tm Σ' Γ₁ A → C.Tm Σ' Γ₂ B → C.Tm Σ' Γ Cc} {h : Tm Γ₁ A → Tm Γ₂ B → Tm Γ Cc}
    → (∀ {Σ'} {e : ∀ {n} → Σ' ∋ n → Σf ∋ n} {X X' Y Y'} → X ≈ C.wk e X' → Y ≈ C.wk e Y' → h X Y ≈ C.wk e (f X' Y'))
    → (L : Tm Γ₁ A) (M : Tm Γ₂ B) (D : Made Σ) → Glob (h L M) D (glob₂ f L M D)

  glob≈ (` x) D s a = var≈ , agree-irr a
  glob≈ (code N) D with glob N D | glob≈ N D
  ... | out g D' N' | ih = λ { s (e , a) → let (r , a') = ih _ a in
          code≈ (subst (_ ≈_) (sym e) r) , agree-irr a' }
  glob≈ (pack L M) D = glob₂≈ pack≈ L M D
  glob≈ (callc L M) D = glob₂≈ callc≈ L M D
  glob≈ (lit B c) D s a = lit≈ , agree-irr a
  glob≈ (tuple Ms) D with globs Ms D | globs≈ Ms D
  ... | out g D' Ms' | ih = λ s a → let (rs , a') = ih s a in tuple≈ rs , a'
  glob≈ (get i M) D = glob₁≈ get≈ M D
  glob≈ (inl M) D = glob₁≈ inl≈ M D
  glob≈ (inr M) D = glob₁≈ inr≈ M D
  glob≈ (case L M N) D with glob L D | glob≈ L D
  ... | out g₁ D₁ L' | ih₁ with glob M D₁ | glob≈ M D₁
  ...   | out g₂ D₂ M' | ih₂ with glob N D₂ | glob≈ N D₂
  ...     | out g₃ D₃ N' | ih₃ = λ s a →
    let (r₃ , a₂) = ih₃ s a ; (r₂ , a₁) = ih₂ _ a₂ ; (r₁ , a₀) = ih₁ _ a₁ in
    case≈ (wk≈ (subst (_ ≈_) (cong (λ q → C.wk (⊑-∋ q) L') (⊑-irr _ _)) r₁)) (wk≈ r₂) r₃ , agree-irr a₀
  glob≈ (prim p L M) D = glob₂≈ prim≈ L M D
  glob≈ (let′ M N) D = glob₂≈ let≈ M N D
  glob≈ (inject G M) D = glob₁≈ inject≈ M D
  glob≈ (project t M) D = glob₁≈ project≈ M D

  globs≈ [] D s a = [] , agree-irr a
  globs≈ (M ∷ Ms) D with glob M D | glob≈ M D
  ... | out g₁ D₁ M' | ih₁ with globs Ms D₁ | globs≈ Ms D₁
  ...   | out g₂ D₂ Ms' | ih₂ = λ s a →
    let (rs , a₁) = ih₂ s a ; (r , a₀) = ih₁ _ a₁ in wk≈ r ∷ rs , agree-irr a₀

  glob₁≈ c M D with glob M D | glob≈ M D
  ... | out g D' M' | ih = λ s a → let (r , a') = ih s a in c r , a'

  glob₂≈ c L M D with glob L D | glob≈ L D
  ... | out g₁ D₁ L' | ih₁ with glob M D₁ | glob≈ M D₁
  ...   | out g₂ D₂ M' | ih₂ = λ s a →
    let (r₂ , a₁) = ih₂ s a ; (r₁ , a₀) = ih₁ _ a₁ in c (wk≈ r₁) r₂ , agree-irr a₀

  {- the definitions of the whole program agree with ds -}
  agree-close : ∀ {Σ} (D : Made Σ) (s : Σ ⊑ Σf) → (∀ {n} (f : Σ ∋ n) → ds ! ⊑-∋ s f ≡ close D s ! f) → Agree D s
  agree-close [] s h = tt
  agree-close (D ▷ N) s h =
    h Z , agree-close D _ λ f → trans (cong (ds !_) (⊑-∋-trans (there⊑ here⊑) s f)) (h (S f))

  {- Closure under substitution -----------------------------------------------------}

  record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit {Σf}) : Set where
    field
      rel-vr : ∀ {Γ B} → S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ (Z {Γ = Γ} {a = B})) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z)
      rel-wk : ∀ {Γ A B} {a : S.Kit.K 𝒦₁ Γ A} {b} → S.Kit.tm 𝒦₁ a ≈ T.Kit.tm 𝒦₂ b
        → S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ {B = B} a) ≈ T.Kit.tm 𝒦₂ (T.Kit.wk 𝒦₂ b)

  module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
    open KR K

    OK : ∀ {Γ Δ} → S.Sub 𝒦₁ Γ Δ → T.Sub 𝒦₂ Γ Δ → Set
    OK σ τ = ∀ {A} (x : _ ∋ A) → S.Kit.tm 𝒦₁ (σ x) ≈ T.Kit.tm 𝒦₂ (τ x)

    ok-ext : ∀ {Γ Δ B} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} → OK σ τ → OK (S.exts 𝒦₁ {B = B} σ) (T.exts 𝒦₂ τ)
    ok-ext ok Z = rel-vr
    ok-ext ok (S x) = rel-wk (ok x)

    ≈-trav : ∀ {Γ Δ A} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {M : Tm Γ A} {M'} → M ≈ M' → OK σ τ
      → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
    ≈-travs : ∀ {Γ Δ n} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {Ms : Vec (Tm Γ Any) n} {Ms' : Vec (C.Tm Σf Γ Any) n}
      → Pointwise _≈_ Ms Ms' → OK σ τ → Pointwise _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
    ≈-trav var≈ ok = ok _
    ≈-trav (code≈ r) ok = code≈ r
    ≈-trav (pack≈ r s) ok = pack≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav (callc≈ r s) ok = callc≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav lit≈ ok = lit≈
    ≈-trav (tuple≈ rs) ok = tuple≈ (≈-travs rs ok)
    ≈-trav (get≈ r) ok = get≈ (≈-trav r ok)
    ≈-trav (inl≈ r) ok = inl≈ (≈-trav r ok)
    ≈-trav (inr≈ r) ok = inr≈ (≈-trav r ok)
    ≈-trav (case≈ r s t) ok = case≈ (≈-trav r ok) (≈-trav s (ok-ext ok)) (≈-trav t (ok-ext ok))
    ≈-trav (prim≈ r s) ok = prim≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav (let≈ r s) ok = let≈ (≈-trav r ok) (≈-trav s (ok-ext ok))
    ≈-trav (inject≈ r) ok = inject≈ (≈-trav r ok)
    ≈-trav (project≈ r) ok = project≈ (≈-trav r ok)
    ≈-travs [] ok = []
    ≈-travs (r ∷ rs) ok = ≈-trav r ok ∷ ≈-travs rs ok

  varKR : KR S.varK T.varK
  varKR = record { rel-vr = var≈ ; rel-wk = λ { var≈ → var≈ } }

  tmKR : KR S.tmK T.tmK
  tmKR = record { rel-vr = var≈ ; rel-wk = λ r → Trav.≈-trav varKR r λ _ → var≈ }

  {- The simulation ----------------------------------------------------------------------}

  Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm Σf [] A → Set
  Ans′ = Ans (T.red ds) Value _≈_

  obs≈ : ∀ {A} {V : Tm [] A} {V'} → V ≈ V' → S.obs V ≡ T.obs V'
  obss≈ : ∀ {n} {Vs : Vec (Tm [] Any) n} {Vs'} → Pointwise _≈_ Vs Vs' → S.obss Vs ≡ T.obss Vs'
  obs≈ (var≈ {x = ()})
  obs≈ (code≈ _) = refl
  obs≈ (pack≈ _ _) = refl
  obs≈ (callc≈ _ _) = refl
  obs≈ lit≈ = refl
  obs≈ (tuple≈ rs) = cong o-tuple (obss≈ rs)
  obs≈ (get≈ _) = refl
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (case≈ _ _ _) = refl
  obs≈ (prim≈ _ _) = refl
  obs≈ (let≈ _ _) = refl
  obs≈ (inject≈ r) = obs≈ r
  obs≈ (project≈ _) = refl
  obss≈ [] = refl
  obss≈ (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obss≈ rs)

  out≈ : ∀ p n m → S.out {[]} p n m ≈ T.out p n m
  out≈ P.sub n m = lit≈
  out≈ P.eq n m with does (n Z.≟ m)
  ... | true = inl≈ (inject≈ (tuple≈ []))
  ... | false = inr≈ (inject≈ (tuple≈ []))

  ≈-[] : ∀ {A} {N : Tm (Any ∷ []) A} {N' V V'} → N ≈ N' → V ≈ V' → (N S.[ V ]) ≈ (N' T.[ V' ])
  ≈-[] n m = Trav.≈-trav tmKR n λ { Z → m ; (S ()) }

  sim : ∀ {A} {M : Tm [] A} {M'} → M ≈ M' → Ans′ M (S.red M) M'
  sims : ∀ {n} {Ms : Vec (Tm [] Any) n} {Ms'} → Pointwise _≈_ Ms Ms' → Ans (T.reds ds) (Allᵥ Value) (Pointwise _≈_) Ms (S.reds Ms) Ms'
  sim (var≈ {x = ()})
  sim (code≈ r) = val ε T.fun-ref (code≈ r)
  sim (pack≈ r s) =
    ans-in (frame _ λ _ → refl) (λ m → pack≈ m s) (sim r)
      λ v m → ans-in (frame {g = C.pack _} _ λ _ → val-in (value-red v)) (pack≈ m) (sim s) λ w m' → val ε (T.pack v w) (pack≈ m m')
  sim (callc≈ r s) =
    ans-in (frame _ λ _ → refl) (λ m → callc≈ m s) (sim r)
      λ v m → ans-in (frame {g = C.callc _} _ λ _ → val-in (value-red v)) (callc≈ m) (sim s) λ w m' → call-sim v m w m'
    where
    call-sim : ∀ {V V' W W'} → Value V' → V ≈ V' → Value W' → W ≈ W' → Ans′ (callc V W) (S.call V W) (C.callc V' W')
    call-sim (T.pack T.fun-ref e) (pack≈ (code≈ n) m) w m' =
      to (one (trans (val-in (value-red (T.pack T.fun-ref e))) (val-in (value-red w))))
         (Trav.≈-trav tmKR n λ { Z → m' ; (S Z) → m })
  sim lit≈ = val ε T.lit lit≈
  sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
  sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
    λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (PW.lookup ms i) }
  sim (inl≈ r) = ans-in (frame _ λ _ → refl) inl≈ (sim r) λ v m → val ε (T.inl v) (inl≈ m)
  sim (inr≈ r) = ans-in (frame _ λ _ → refl) inr≈ (sim r) λ v m → val ε (T.inr v) (inr≈ m)
  sim (case≈ r s t) = ans-in (frame _ λ _ → refl) (λ m → case≈ m s t) (sim r)
    λ { (T.inl v) (inl≈ m) → to (one (val-in (value-red (T.inl v)))) (≈-[] s m)
      ; (T.inr v) (inr≈ m) → to (one (val-in (value-red (T.inr v)))) (≈-[] t m) }
  sim (prim≈ {p = p} r s) = ans-in (frame _ λ _ → refl) (λ m → prim≈ m s) (sim r)
    λ { T.lit lit≈ → ans-in (frame {g = C.prim p _} _ λ _ → refl) (prim≈ lit≈) (sim s)
      λ { T.lit lit≈ → to (one refl) (out≈ p _ _) } }
  sim (let≈ r s) = ans-in (frame _ λ _ → refl) (λ m → let≈ m s) (sim r)
    λ v m → to (one (val-in (value-red v))) (≈-[] s m)
  sim (inject≈ r) = ans-in (frame _ λ _ → refl) inject≈ (sim r) λ v m → val ε (T.inject v) (inject≈ m)
  sim (project≈ {t = t} r) = ans-in (frame _ λ _ → refl) project≈ (sim r) λ { (T.inject v) (inject≈ m) → proj-sim v m }
    where
    proj-sim : ∀ {G V V'} → Value V' → V ≈ V' → Ans′ (project t (inject G V)) (S.project? t (inject G V)) (C.project t (C.inject G V'))
    proj-sim {G} {V} {V'} v m = pd (G ≟F flat t) (val-in (value-red (T.inject v)))
      where pd : ∀ {H} (d : Dec (G ≡ H)) {X Y} → T.red ds X ≡ T.proj-dec d V' → Ans′ Y (S.proj-dec d V) X
            pd (yes refl) e = to (one e) m
            pd (no _) e = error ε e
  sims [] = val ε []ᵥ []
  sims (r ∷ rs) = ans-∷ (T.reds ds) (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- weakening along the identity -}
wk-id : ∀ {Σ Γ A} {e : ∀ {n} → Σ ∋ n → Σ ∋ n} → (∀ {n} (x : Σ ∋ n) → e x ≡ x) → (M : C.Tm Σ Γ A) → C.wk e M ≡ M
wks-id : ∀ {Σ Γ n} {e : ∀ {n} → Σ ∋ n → Σ ∋ n} → (∀ {n} (x : Σ ∋ n) → e x ≡ x) → (Ms : Vec (C.Tm Σ Γ Any) n) → C.wks e Ms ≡ Ms
wk-id h (C.` x) = refl
wk-id h (C.fun-ref f) = cong C.fun-ref (h f)
wk-id h (C.pack L M) = cong₂ C.pack (wk-id h L) (wk-id h M)
wk-id h (C.callc L M) = cong₂ C.callc (wk-id h L) (wk-id h M)
wk-id h (C.lit B c) = refl
wk-id h (C.tuple Ms) = cong C.tuple (wks-id h Ms)
wk-id h (C.get i M) = cong (C.get i) (wk-id h M)
wk-id h (C.inl M) = cong C.inl (wk-id h M)
wk-id h (C.inr M) = cong C.inr (wk-id h M)
wk-id h (C.case L M N) = cong₃ C.case (wk-id h L) (wk-id h M) (wk-id h N)
wk-id h (C.prim p L M) = cong₂ (C.prim p) (wk-id h L) (wk-id h M)
wk-id h (C.let′ M N) = cong₂ C.let′ (wk-id h M) (wk-id h N)
wk-id h (C.inject G M) = cong (C.inject G) (wk-id h M)
wk-id h (C.project t M) = cong (C.project t) (wk-id h M)
wks-id h [] = refl
wks-id h (M ∷ Ms) = cong₂ _∷_ (wk-id h M) (wks-id h Ms)

{- The end theorem ---------------------------------------------------------------------}

globalize-correct : ∀ (M : Tm [] Any) → Equivalent (S.sem M) (T.sem (globalize M))
globalize-correct M with glob M [] | (λ {Σf} (ds : All (C.Code Σf) Σf) → glob≈ ds M [])
... | out g D M' | ih =
  red-equivalent value-red (_≈_ (close D here⊑)) (sim (close D here⊑)) (λ m _ _ → obs≈ (close D here⊑) m)
    (subst (λ X → _≈_ (close D here⊑) M X) (wk-id (λ _ → refl) M') (proj₁ (ih (close D here⊑) here⊑ (agree-close (close D here⊑) D here⊑ λ _ → refl))))
