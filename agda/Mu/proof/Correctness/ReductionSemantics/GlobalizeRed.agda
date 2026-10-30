{-

  Correctness of globalize (PairClosμ → GlobalFunμ) by a forward simulation
  between their reduction semantics, in lock step, as for typed
  globalize (proof/Correctness/Reduction/GlobalizeRed.agda).

  The GlobalFunμ program runs with the definitions ds that the pass made for
  the whole program, and the relation is for ds: a congruence, closed
  under substitution (≈-trav), except that code N is related to a
  reference f when N is related to the definition lookup ds f. The pass
  threads the definitions made so far (Made) through the term, each over
  the table before it, and weakens. So the relation is along an
  embedding e of the target's table into that of the whole program
  (e ⊢ M ≈ M', and M ≈ M' along the identity), and weakening the target
  is a change of embedding (≈-wk): a subterm is related to its output
  along s, when the definitions made agree with ds along s (Agree).

-}

module Mu.proof.Correctness.ReductionSemantics.GlobalizeRed where

open import Mu.Language.Type hiding (_[_])
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import proof.Framework.Lookup using (⊑-irr; ⊑-∋-trans)
open import Mu.Language.PairClos
import Mu.Language.GlobalFun as C
open C using (DSig; sig)
open import Mu.Compiler.Globalize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.ReductionSemantics.PairClos as S
import Mu.proof.Semantics.ReductionSemantics.GlobalFun as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

module _ {Σf : List DSig} (ds : All (C.Code Σf) Σf) where

  {- The relation ---------------------------------------------------------------}

  {- for a table Σ that e embeds into Σf -}
  Emb : List DSig → Set
  Emb Σ = ∀ {n} → Σ ∋ n → Σf ∋ n

  infix 4 _⊢_≈_ _≈_
  data _⊢_≈_ {Σ} (e : Emb Σ) : ∀ {Γ A} → Tm Γ A → C.Tm Σ Γ A → Set where
    var≈ : ∀ {Γ A} {x : Γ ∋ A} → e ⊢ ` x ≈ C.` x
    code≈ : ∀ {Γ Δ A B N} {f : Σ ∋ sig Δ A B} → (λ x → x) ⊢ N ≈ lookup ds (e f) → e ⊢ code {Γ} N ≈ C.fun-ref f
    pair≈ : ∀ {Γ Δ A B} {L : Tm Γ (code Δ A B)} {L' M M'} → e ⊢ L ≈ L' → e ⊢ M ≈ M' → e ⊢ pair L M ≈ C.pair L' M'
    callc≈ : ∀ {Γ A B} {L : Tm Γ (A ⇒ B)} {L' M M'} → e ⊢ L ≈ L' → e ⊢ M ≈ M' → e ⊢ callc L M ≈ C.callc L' M'
    lit≈ : ∀ {Γ B c} → e ⊢ lit {Γ} B c ≈ C.lit B c
    tuple≈ : ∀ {Γ Δ} {Ms : All (Tm Γ) Δ} {Ms'} → All₂ (e ⊢_≈_) Ms Ms' → e ⊢ tuple Ms ≈ C.tuple Ms'
    get≈ : ∀ {Γ Δ A} {i : Δ ∋ A} {M : Tm Γ (tup Δ)} {M'} → e ⊢ M ≈ M' → e ⊢ get i M ≈ C.get i M'
    inl≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} → e ⊢ M ≈ M' → e ⊢ inl {B = B} M ≈ C.inl M'
    inr≈ : ∀ {Γ A B} {M : Tm Γ B} {M'} → e ⊢ M ≈ M' → e ⊢ inr {A = A} M ≈ C.inr M'
    case≈ : ∀ {Γ A B C} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → e ⊢ L ≈ L' → e ⊢ M ≈ M' → e ⊢ N ≈ N'
      → e ⊢ case L M N ≈ C.case L' M' N'
    prim≈ : ∀ {Γ p} {L : Tm Γ _} {L' M M'} → e ⊢ L ≈ L' → e ⊢ M ≈ M' → e ⊢ prim p L M ≈ C.prim p L' M'
    let≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → e ⊢ M ≈ M' → e ⊢ N ≈ N' → e ⊢ let′ M N ≈ C.let′ M' N'
    fold≈ : ∀ {Γ A} {M : Tm Γ (unroll A)} {M'} → e ⊢ M ≈ M' → e ⊢ fold {A = A} M ≈ C.fold M'
    unfold≈ : ∀ {Γ A} {M : Tm Γ (μ A)} {M'} → e ⊢ M ≈ M' → e ⊢ unfold M ≈ C.unfold M'

  {- the relation for the terms of the whole program -}
  _≈_ : ∀ {Γ A} → Tm Γ A → C.Tm Σf Γ A → Set
  _≈_ = (λ x → x) ⊢_≈_

  {- weakening the target's table -}
  ≈-wk : ∀ {Σ Σ' Γ A} {e : Emb Σ} {e' : Emb Σ'} {g : ∀ {n} → Σ ∋ n → Σ' ∋ n} {M : Tm Γ A} {M'}
    → (∀ {n} (f : Σ ∋ n) → e' (g f) ≡ e f) → e ⊢ M ≈ M' → e' ⊢ M ≈ C.wk g M'
  ≈-wks : ∀ {Σ Σ' Γ Δ} {e : Emb Σ} {e' : Emb Σ'} {g : ∀ {n} → Σ ∋ n → Σ' ∋ n} {Ms : All (Tm Γ) Δ} {Ms'}
    → (∀ {n} (f : Σ ∋ n) → e' (g f) ≡ e f) → All₂ (e ⊢_≈_) Ms Ms' → All₂ (e' ⊢_≈_) Ms (C.wks g Ms')
  ≈-wk h var≈ = var≈
  ≈-wk {M = code N} h (code≈ {f = f} r) = code≈ (subst (λ f' → N ≈ lookup ds f') (sym (h f)) r)
  ≈-wk h (pair≈ r s) = pair≈ (≈-wk h r) (≈-wk h s)
  ≈-wk h (callc≈ r s) = callc≈ (≈-wk h r) (≈-wk h s)
  ≈-wk h lit≈ = lit≈
  ≈-wk h (tuple≈ rs) = tuple≈ (≈-wks h rs)
  ≈-wk h (get≈ r) = get≈ (≈-wk h r)
  ≈-wk h (inl≈ r) = inl≈ (≈-wk h r)
  ≈-wk h (inr≈ r) = inr≈ (≈-wk h r)
  ≈-wk h (case≈ r s t) = case≈ (≈-wk h r) (≈-wk h s) (≈-wk h t)
  ≈-wk h (prim≈ r s) = prim≈ (≈-wk h r) (≈-wk h s)
  ≈-wk h (let≈ r s) = let≈ (≈-wk h r) (≈-wk h s)
  ≈-wk h (fold≈ r) = fold≈ (≈-wk h r)
  ≈-wk h (unfold≈ r) = unfold≈ (≈-wk h r)
  ≈-wks h [] = []
  ≈-wks h (r ∷ rs) = ≈-wk h r ∷ ≈-wks h rs

  {- The fundamental lemma ----------------------------------------------------------}

  {- the definitions made agree with ds, weakened along s -}
  Agree : ∀ {Σ} → Made Σ → Σ ⊑ Σf → Set
  Agree [] s = ⊤
  Agree (D ▷ N) s = lookup ds (⊑-∋ s Z) ≡ C.wk (⊑-∋ (⊑-trans (there⊑ here⊑) s)) N × Agree D (⊑-trans (there⊑ here⊑) s)

  agree-irr : ∀ {Σ} {D : Made Σ} {s s'} → Agree D s → Agree D s'
  agree-irr {s = s} {s'} a rewrite ⊑-irr s s' = a

  {- the source is related to the output along s, and the definitions made before agree too -}
  Glob : ∀ {Σ Γ A} → Tm Γ A → Made Σ → Out Σ (λ Σ' → C.Tm Σ' Γ A) → Set
  Glob M D (out g D' M') = ∀ s → Agree D' s → ⊑-∋ s ⊢ M ≈ M' × Agree D (⊑-trans g s)

  Globs : ∀ {Σ Γ Δ} → All (Tm Γ) Δ → Made Σ → Out Σ (λ Σ' → All (C.Tm Σ' Γ) Δ) → Set
  Globs Ms D (out g D' Ms') = ∀ s → Agree D' s → All₂ (⊑-∋ s ⊢_≈_) Ms Ms' × Agree D (⊑-trans g s)

  {- one operand, and then another, under the weakening of the first -}
  wk≈ : ∀ {Σ Σ' Γ A} {M : Tm Γ A} {M' : C.Tm Σ Γ A} {g : Σ ⊑ Σ'} {s : Σ' ⊑ Σf}
    → ⊑-∋ (⊑-trans g s) ⊢ M ≈ M' → ⊑-∋ s ⊢ M ≈ C.wk (⊑-∋ g) M'
  wk≈ {g = g} {s} = ≈-wk λ x → sym (⊑-∋-trans g s x)

  glob≈ : ∀ {Σ Γ A} (M : Tm Γ A) (D : Made Σ) → Glob M D (glob M D)
  globs≈ : ∀ {Σ Γ Δ} (Ms : All (Tm Γ) Δ) (D : Made Σ) → Globs Ms D (globs Ms D)
  glob₁≈ : ∀ {Σ Γ Γ₁ A B} {f : ∀ {Σ'} → C.Tm Σ' Γ₁ A → C.Tm Σ' Γ B} {h : Tm Γ₁ A → Tm Γ B}
    → (∀ {Σ'} {e : Emb Σ'} {X X'} → e ⊢ X ≈ X' → e ⊢ h X ≈ f X')
    → (M : Tm Γ₁ A) (D : Made Σ) → Glob (h M) D (glob₁ f M D)
  glob₂≈ : ∀ {Σ Γ Γ₁ Γ₂ A B Cc} {f : ∀ {Σ'} → C.Tm Σ' Γ₁ A → C.Tm Σ' Γ₂ B → C.Tm Σ' Γ Cc} {h : Tm Γ₁ A → Tm Γ₂ B → Tm Γ Cc}
    → (∀ {Σ'} {e : Emb Σ'} {X X' Y Y'} → e ⊢ X ≈ X' → e ⊢ Y ≈ Y' → e ⊢ h X Y ≈ f X' Y')
    → (L : Tm Γ₁ A) (M : Tm Γ₂ B) (D : Made Σ) → Glob (h L M) D (glob₂ f L M D)

  glob≈ (` x) D s a = var≈ , agree-irr a
  glob≈ (code N) D with glob N D | glob≈ N D
  ... | out g D' N' | ih = λ { s (e , a) → let (r , a') = ih _ a in
          code≈ (subst (_ ≈_) (sym e) (≈-wk (λ _ → refl) r)) , agree-irr a' }
  glob≈ (pair L M) D = glob₂≈ pair≈ L M D
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
    case≈ (wk≈ (subst (λ q → ⊑-∋ q ⊢ L ≈ L') (⊑-irr _ _) r₁)) (wk≈ r₂) r₃ , agree-irr a₀
  glob≈ (prim p L M) D = glob₂≈ prim≈ L M D
  glob≈ (let′ M N) D = glob₂≈ let≈ M N D
  glob≈ (fold M) D = glob₁≈ fold≈ M D
  glob≈ (unfold M) D = glob₁≈ unfold≈ M D

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
  agree-close : ∀ {Σ} (D : Made Σ) (s : Σ ⊑ Σf) → (∀ {n} (f : Σ ∋ n) → lookup ds (⊑-∋ s f) ≡ lookup (close D s) f) → Agree D s
  agree-close [] s h = tt
  agree-close (D ▷ N) s h =
    h Z , agree-close D _ λ f → trans (cong (lookup ds) (⊑-∋-trans (there⊑ here⊑) s f)) (h (S f))

  {- Closure under substitution -----------------------------------------------------}

  {- for a kit of each language, which agree on variable 0 and on weakening -}
  module Trav {𝒦₁ : S.Kit} {𝒦₂ : T.Kit {Σf}}
    (rel-vr : ∀ {Γ B} → S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ (Z {Γ = Γ} {a = B})) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z))
    (rel-wk : ∀ {Γ A B} {a : S.Kit.K 𝒦₁ Γ A} {b} → S.Kit.tm 𝒦₁ a ≈ T.Kit.tm 𝒦₂ b
      → S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ {B = B} a) ≈ T.Kit.tm 𝒦₂ (T.Kit.wk 𝒦₂ b)) where

    OK : ∀ {Γ Δ} → S.Sub 𝒦₁ Γ Δ → T.Sub 𝒦₂ Γ Δ → Set
    OK σ τ = ∀ {A} (x : _ ∋ A) → S.Kit.tm 𝒦₁ (σ x) ≈ T.Kit.tm 𝒦₂ (τ x)

    ok-ext : ∀ {Γ Δ B} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} → OK σ τ → OK (S.exts 𝒦₁ {B = B} σ) (T.exts 𝒦₂ τ)
    ok-ext ok Z = rel-vr
    ok-ext ok (S x) = rel-wk (ok x)

    ≈-trav : ∀ {Γ Δ A} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {M : Tm Γ A} {M'} → M ≈ M' → OK σ τ
      → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
    ≈-travs : ∀ {Γ Δ Θ} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {Ms : All (Tm Γ) Θ} {Ms' : All (C.Tm Σf Γ) Θ}
      → All₂ _≈_ Ms Ms' → OK σ τ → All₂ _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
    ≈-trav var≈ ok = ok _
    ≈-trav (code≈ r) ok = code≈ r
    ≈-trav (pair≈ r s) ok = pair≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav (callc≈ r s) ok = callc≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav lit≈ ok = lit≈
    ≈-trav (tuple≈ rs) ok = tuple≈ (≈-travs rs ok)
    ≈-trav (get≈ r) ok = get≈ (≈-trav r ok)
    ≈-trav (inl≈ r) ok = inl≈ (≈-trav r ok)
    ≈-trav (inr≈ r) ok = inr≈ (≈-trav r ok)
    ≈-trav (case≈ r s t) ok = case≈ (≈-trav r ok) (≈-trav s (ok-ext ok)) (≈-trav t (ok-ext ok))
    ≈-trav (prim≈ r s) ok = prim≈ (≈-trav r ok) (≈-trav s ok)
    ≈-trav (let≈ r s) ok = let≈ (≈-trav r ok) (≈-trav s (ok-ext ok))
    ≈-trav (fold≈ r) ok = fold≈ (≈-trav r ok)
    ≈-trav (unfold≈ r) ok = unfold≈ (≈-trav r ok)
    ≈-travs [] ok = []
    ≈-travs (r ∷ rs) ok = ≈-trav r ok ∷ ≈-travs rs ok

  module RenT = Trav {S.varK} {T.varK} var≈ (λ { var≈ → var≈ })
  module SubT = Trav {S.tmK} {T.tmK} var≈ (λ r → RenT.≈-trav r λ _ → var≈)

  {- The simulation ----------------------------------------------------------------------}

  Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm Σf [] A → Set
  Ans′ = Ans (T.red ds) Value _≈_

  obs≈ : ∀ {A} {V : Tm [] A} {V'} → V ≈ V' → Value V' → S.obs V ≡ T.obs V'
  obss≈ : ∀ {Δ} {Vs : All (Tm []) Δ} {Vs'} → All₂ _≈_ Vs Vs' → Each Value Vs' → S.obss Vs ≡ T.obss Vs'
  obs≈ (code≈ _) _ = refl
  obs≈ (pair≈ _ _) _ = refl
  obs≈ lit≈ _ = refl
  obs≈ (tuple≈ rs) (T.tuple vs) = cong o-tuple (obss≈ rs vs)
  obs≈ (inl≈ r) (T.inl v) = cong o-inl (obs≈ r v)
  obs≈ (inr≈ r) (T.inr v) = cong o-inr (obs≈ r v)
  obs≈ (fold≈ r) (T.fold v) = obs≈ r v
  obss≈ [] [] = refl
  obss≈ (r ∷ rs) (v ∷ vs) = cong₂ _∷_ (obs≈ r v) (obss≈ rs vs)

  out≈ : ∀ p n m → S.out {[]} p n m ≈ T.out p n m
  out≈ P.sub n m = lit≈
  out≈ P.eq n m with does (n Z.≟ m)
  ... | true = inl≈ (tuple≈ [])
  ... | false = inr≈ (tuple≈ [])

  ≈-[] : ∀ {A B} {N : Tm (A ∷ []) B} {N' V V'} → N ≈ N' → V ≈ V' → (N S.[ V ]) ≈ (N' T.[ V' ])
  ≈-[] n m = SubT.≈-trav n λ { Z → m }

  sim : ∀ {A} {M : Tm [] A} {M'} → M ≈ M' → Ans′ M (S.red M) M'
  sims : ∀ {Δ} {Ms : All (Tm []) Δ} {Ms'} → All₂ _≈_ Ms Ms' → Ans (T.reds ds) (Each Value) (All₂ _≈_) Ms (S.reds Ms) Ms'
  sim (code≈ r) = val ε T.fun-ref (code≈ r)
  sim (pair≈ r s) =
    ans-in (frame _ λ _ → refl) (λ m → pair≈ m s) (sim r)
      λ v m → ans-in (frame {g = C.pair _} _ λ _ → val-in (value-red v)) (pair≈ m) (sim s) λ w m' → val ε (T.pair v w) (pair≈ m m')
  sim (callc≈ r s) =
    ans-in (frame _ λ _ → refl) (λ m → callc≈ m s) (sim r)
      λ v m → ans-in (frame {g = C.callc _} _ λ _ → val-in (value-red v)) (callc≈ m) (sim s) λ w m' → call-sim v m w m'
    where
    call-sim : ∀ {A B} {V : Tm [] (A ⇒ B)} {V' W W'} → Value V' → V ≈ V' → Value W' → W ≈ W'
      → Ans′ (callc V W) (S.call V refl W) (C.callc V' W')
    call-sim (T.pair T.fun-ref e) (pair≈ (code≈ n) m) w m' =
      to (one (trans (val-in (value-red (T.pair T.fun-ref e))) (val-in (value-red w))))
         (SubT.≈-trav n λ { Z → m' ; (S Z) → m })
  sim lit≈ = val ε T.lit lit≈
  sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
  sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
    λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (lookup₂ ms i) }
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
  sim (fold≈ r) = ans-in (frame _ λ _ → refl) fold≈ (sim r) λ v m → val ε (T.fold v) (fold≈ m)
  sim (unfold≈ r) = ans-in (frame _ λ _ → refl) unfold≈ (sim r)
    λ { (T.fold v) (fold≈ m) → to (one (val-in (value-red (T.fold v)))) m }
  sims [] = val ε [] []
  sims (r ∷ rs) = ans-∷ (T.reds ds) (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- The end theorem ---------------------------------------------------------------------}

globalize-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (globalize M))
globalize-correct M with glob M [] | (λ {Σf} (ds : All (C.Code Σf) Σf) → glob≈ ds M [])
... | out g D M' | ih =
  red-equivalent value-red (_≈_ (close D here⊑)) (sim (close D here⊑)) (λ m _ → obs≈ (close D here⊑) m)
    (proj₁ (ih (close D here⊑) here⊑ (agree-close (close D here⊑) D here⊑ λ _ → refl)))
