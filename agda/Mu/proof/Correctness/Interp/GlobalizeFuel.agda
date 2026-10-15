{-

  Correctness of globalize (Clos4μ → Clos5μ), clock for clock, as for
  typed globalize (proof/Correctness/Interp/GlobalizeFuel.agda):
  globalize maps each callc to one callc, so the interpreters call in
  lock step.

  The Clos5μ interpreter runs with the table dsf that the pass made for
  the whole program. A subterm M, globalized after the definitions D,
  gives a term over the table of the definitions made by then, which is
  weakened by r into the final table; the definitions made by then are
  found in dsf through r (Contains). Every definition made from D
  stays (Ext), so a term made earlier finds its definitions as well.
  Code N is related to a reference f when definition f is the
  globalized N, weakened (GCode); environments are related pointwise.

-}

module Mu.proof.Correctness.Interp.GlobalizeFuel where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Mu.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Mu.Language.Clos4 as S
open import Mu.Language.Clos5
open import Mu.Compiler.Globalize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂)
open import proof.Semantics.Interp.Clock
import Mu.Semantics.Interp.Clos4 as S4
import Mu.Semantics.Interp.Clos5 as T
open import proof.Framework.Lookup using (⊑-∋-trans)

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

Ren : List Sig → List Sig → Set
Ren Σ Σ' = ∀ {n} → Σ ∋ n → Σ' ∋ n

{- Weakening of tables -----------------------------------------------------------}

wk-wk : ∀ {Σ₁ Σ₂ Σ₃ Γ A} (r : Ren Σ₂ Σ₃) (r' : Ren Σ₁ Σ₂) (M : Tm Σ₁ Γ A) → wk r (wk r' M) ≡ wk (λ x → r (r' x)) M
wks-wk : ∀ {Σ₁ Σ₂ Σ₃ Γ Δ} (r : Ren Σ₂ Σ₃) (r' : Ren Σ₁ Σ₂) (Ms : All (Tm Σ₁ Γ) Δ)
  → wks r (wks r' Ms) ≡ wks (λ x → r (r' x)) Ms
wk-wk r r' (` x) = refl
wk-wk r r' (fun-ref f) = refl
wk-wk r r' (pack L M) = cong₂ pack (wk-wk r r' L) (wk-wk r r' M)
wk-wk r r' (callc L M) = cong₂ callc (wk-wk r r' L) (wk-wk r r' M)
wk-wk r r' (lit B c) = refl
wk-wk r r' (tuple Ms) = cong tuple (wks-wk r r' Ms)
wk-wk r r' (get i M) = cong (get i) (wk-wk r r' M)
wk-wk r r' (inl M) = cong inl (wk-wk r r' M)
wk-wk r r' (inr M) = cong inr (wk-wk r r' M)
wk-wk r r' (case L M N) rewrite wk-wk r r' L | wk-wk r r' M | wk-wk r r' N = refl
wk-wk r r' (prim p L M) = cong₂ (prim p) (wk-wk r r' L) (wk-wk r r' M)
wk-wk r r' (let′ M N) = cong₂ let′ (wk-wk r r' M) (wk-wk r r' N)
wk-wk r r' (fold M) = cong fold (wk-wk r r' M)
wk-wk r r' (unfold M) = cong unfold (wk-wk r r' M)
wks-wk r r' [] = refl
wks-wk r r' (M ∷ Ms) = cong₂ _∷_ (wk-wk r r' M) (wks-wk r r' Ms)

wk-id : ∀ {Σ Γ A} (M : Tm Σ Γ A) → wk (λ x → x) M ≡ M
wks-id : ∀ {Σ Γ Δ} (Ms : All (Tm Σ Γ) Δ) → wks (λ x → x) Ms ≡ Ms
wk-id (` x) = refl
wk-id (fun-ref f) = refl
wk-id (pack L M) = cong₂ pack (wk-id L) (wk-id M)
wk-id (callc L M) = cong₂ callc (wk-id L) (wk-id M)
wk-id (lit B c) = refl
wk-id (tuple Ms) = cong tuple (wks-id Ms)
wk-id (get i M) = cong (get i) (wk-id M)
wk-id (inl M) = cong inl (wk-id M)
wk-id (inr M) = cong inr (wk-id M)
wk-id (case L M N) rewrite wk-id L | wk-id M | wk-id N = refl
wk-id (prim p L M) = cong₂ (prim p) (wk-id L) (wk-id M)
wk-id (let′ M N) = cong₂ let′ (wk-id M) (wk-id N)
wk-id (fold M) = cong fold (wk-id M)
wk-id (unfold M) = cong unfold (wk-id M)
wks-id [] = refl
wks-id (M ∷ Ms) = cong₂ _∷_ (wk-id M) (wks-id Ms)

{- the definitions D' are D and more -}
data Ext : ∀ {Σ Σ'} → Made Σ → Σ ⊑ Σ' → Made Σ' → Set where
  same : ∀ {Σ} {D : Made Σ} → Ext D here⊑ D
  more : ∀ {Σ Σ' s₀} {D : Made Σ} {s} {D' : Made Σ'} {N : Code Σ' s₀} → Ext D s D' → Ext D (there⊑ s) (D' ▷ N)

ext-trans : ∀ {Σ₀ Σ₁ Σ₂} {D₀ : Made Σ₀} {D₁ : Made Σ₁} {D₂ : Made Σ₂} {s₁ s₂}
  → Ext D₀ s₁ D₁ → Ext D₁ s₂ D₂ → Ext D₀ (⊑-trans s₁ s₂) D₂
ext-trans e₁ same = e₁
ext-trans e₁ (more e₂) = more (ext-trans e₁ e₂)

glob-ext : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → Ext D (Out.grows (glob M D)) (Out.made (glob M D))
globs-ext : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → Ext D (Out.grows (globs Ms D)) (Out.made (globs Ms D))
glob₁-ext : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (D : Made Σ)
  → Ext D (Out.grows (glob₁ f M D)) (Out.made (glob₁ f M D))
glob₂-ext : ∀ {Σ Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) L M (D : Made Σ)
  → Ext D (Out.grows (glob₂ f L M D)) (Out.made (glob₂ f L M D))
glob-ext (S.` x) D = same
glob-ext (S.code N) D with glob N D | glob-ext N D
... | out s D' N' | e = more e
glob-ext (S.pack L M) D = glob₂-ext pack L M D
glob-ext (S.callc L M) D = glob₂-ext callc L M D
glob-ext (S.lit B c) D = same
glob-ext (S.tuple Ms) D with globs Ms D | globs-ext Ms D
... | out s D' Ms' | e = e
glob-ext (S.get i M) D = glob₁-ext (get i) M D
glob-ext (S.inl {B = B} M) D = glob₁-ext (inl {B = B}) M D
glob-ext (S.inr {A = A} M) D = glob₁-ext (inr {A = A}) M D
glob-ext (S.case L M N) D with glob L D | glob-ext L D
... | out s₁ D₁ L' | e₁ with glob M D₁ | glob-ext M D₁
...   | out s₂ D₂ M' | e₂ with glob N D₂ | glob-ext N D₂
...     | out s₃ D₃ N' | e₃ = ext-trans e₁ (ext-trans e₂ e₃)
glob-ext (S.prim p L M) D = glob₂-ext (prim p) L M D
glob-ext (S.let′ M N) D = glob₂-ext let′ M N D
glob-ext (S.fold {A} {c} M) D = glob₁-ext (fold {A = A} {c}) M D
glob-ext (S.unfold {A} {c} M) D = glob₁-ext (unfold {A = A} {c}) M D
globs-ext [] D = same
globs-ext (M ∷ Ms) D with glob M D | glob-ext M D
... | out s₁ D₁ M' | e₁ with globs Ms D₁ | globs-ext Ms D₁
...   | out s₂ D₂ Ms' | e₂ = ext-trans e₁ e₂
glob₁-ext f M D with glob M D | glob-ext M D
... | out s D' M' | e = e
glob₂-ext f L M D with glob L D | glob-ext L D
... | out s₁ D₁ L' | e₁ with glob M D₁ | glob-ext M D₁
...   | out s₂ D₂ M' | e₂ = ext-trans e₁ e₂

{- For the final table dsf ------------------------------------------------------}

module G {Σf : List Sig} (dsf : All (Code Σf) Σf) where
  open T.Vals Σf renaming (Val to TVal; Env to TEnv)

  {- the definitions D are found in dsf through r -}
  Contains : ∀ {Σ} → Made Σ → Ren Σ Σf → Set
  Contains [] r = ⊤
  Contains (D ▷ N) r = Σ[ r' ∈ Ren _ Σf ] (∀ {m} (x : _ ∋ m) → r (S x) ≡ r' x) × lookup dsf (r Z) ≡ wk r' N
    × Contains D (λ x → r (S x))

  contains-cong : ∀ {Σ} (D : Made Σ) {r r' : Ren Σ Σf} → (∀ {m} (x : Σ ∋ m) → r x ≡ r' x) → Contains D r → Contains D r'
  contains-cong [] h c = tt
  contains-cong (D ▷ N) h (r'' , h' , e , c) =
    r'' , (λ x → trans (sym (h (S x))) (h' x)) , subst (λ f → lookup dsf f ≡ _) (h Z) e , contains-cong D (λ x → h (S x)) c

  contains-ext : ∀ {Σ Σ'} {D : Made Σ} {s} {D' : Made Σ'} {r : Ren Σ' Σf} → Ext D s D' → Contains D' r → Contains D (λ x → r (⊑-∋ s x))
  contains-ext same c = c
  contains-ext (more e) (_ , _ , _ , c) = contains-ext e c

  record GCode {Δ A B} (N : S.Tm (A ∷ tup Δ ∷ []) B) (f : Σf ∋ sig Δ A B) : Set where
    constructor gcode
    field
      {Σ₀} : List Sig
      D : Made Σ₀
      o : Out Σ₀ (λ Σ' → Tm Σ' (A ∷ tup Δ ∷ []) B)
      is-glob : glob N D ≡ o
      r : Ren (Out.Σ' o) Σf
      contains : Contains (Out.made o) r
      is-def : lookup dsf f ≡ wk r (Out.res o)

  open import Mu.proof.Semantics.Interp.Rel {λ Δ A B → S.Tm (A ∷ tup Δ ∷ []) B} {λ Δ A B → Σf ∋ sig Δ A B}
  open Rel GCode (Same GCode) public

  Env≈ : ∀ {Γ} → S4.Env Γ → TEnv Γ → Set
  Env≈ ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → lookup ρ₁ x ≈ lookup ρ₂ x

  env-ext : ∀ {Γ B ρ₁ ρ₂ v w} → v ≈ w → Env≈ {Γ} ρ₁ ρ₂ → Env≈ {B ∷ Γ} (v ∷ ρ₁) (w ∷ ρ₂)
  env-ext v E Z = v
  env-ext v E (S x) = E x

  pack≈' : ∀ {Δ A B} {c : S4.Val (code Δ A B)} {c' e e'} → c ≈ c' → e ≈ e' → S4.pack c e ≈ T.Vals.pack c' e'
  pack≈' (code≈ g) (tup≈ rs) = pack≈ rs (same g)

  run≈ : ∀ ck {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) {r : Ren (Out.Σ' (glob M D)) Σf} {ρ₁ ρ₂}
    → Contains (Out.made (glob M D)) r → Env≈ ρ₁ ρ₂
    → RelResult _≈_ (S4.eval ck ρ₁ M) (T.eval dsf ck ρ₂ (wk r (Out.res (glob M D))))
  runs≈ : ∀ ck {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) {r : Ren (Out.Σ' (globs Ms D)) Σf} {ρ₁ ρ₂}
    → Contains (Out.made (globs Ms D)) r → Env≈ ρ₁ ρ₂
    → RelResult (All₂ _≈_) (S4.evals ck ρ₁ Ms) (T.evals dsf ck ρ₂ (wks r (Out.res (globs Ms D))))
  call≈ : ∀ ck {A B} {f : S4.Val (A ⇒ B)} {g v w} → f ≈ g → v ≈ w → RelResult _≈_ (S4.call ck f v) (T.call dsf ck g w)

  run≈ ck (S.` x) D c E = ret (E x)
  run≈ ck (S.code N) D {r} c E with glob N D in eq
  ... | out s D' N' with c
  ...   | r' , h , d , c' = ret (code≈ (gcode D _ eq r' (contains-cong D' h c') d))
  run≈ ck (S.pack L M) D {r} c E with glob L D | run≈ ck L D
  ... | out s₁ D₁ L' | ihL with glob M D₁ | glob-ext M D₁ | run≈ ck M D₁
  ...   | out s₂ D₂ M' | e₂ | ihM rewrite wk-wk r (⊑-∋ s₂) L' =
    bind-rel (ihL (contains-ext e₂ c) E) λ v → bind-rel (ihM c E) λ w → ret (pack≈' v w)
  run≈ ck (S.callc L M) D {r} c E with glob L D | run≈ ck L D
  ... | out s₁ D₁ L' | ihL with glob M D₁ | glob-ext M D₁ | run≈ ck M D₁
  ...   | out s₂ D₂ M' | e₂ | ihM rewrite wk-wk r (⊑-∋ s₂) L' =
    bind-rel (ihL (contains-ext e₂ c) E) λ v → bind-rel (ihM c E) λ w → call≈ ck v w
  run≈ ck (S.lit B k) D c E = ret const≈
  run≈ ck (S.tuple Ms) D c E with globs Ms D | runs≈ ck Ms D
  ... | out s D' Ms' | ih = bind-rel (ih c E) λ vs → ret (tup≈ vs)
  run≈ ck (S.get i M) D c E with glob M D | run≈ ck M D
  ... | out s D' M' | ih = bind-rel (ih c E) λ v → ret (nth≈ i v)
  run≈ ck (S.inl M) D c E with glob M D | run≈ ck M D
  ... | out s D' M' | ih = bind-rel (ih c E) λ v → ret (inl≈ v)
  run≈ ck (S.inr M) D c E with glob M D | run≈ ck M D
  ... | out s D' M' | ih = bind-rel (ih c E) λ v → ret (inr≈ v)
  run≈ ck (S.case L M N) D {r} c E with glob L D | run≈ ck L D
  ... | out s₁ D₁ L' | ihL with glob M D₁ | glob-ext M D₁ | run≈ ck M D₁
  ...   | out s₂ D₂ M' | e₂ | ihM with glob N D₂ | glob-ext N D₂ | run≈ ck N D₂
  ...     | out s₃ D₃ N' | e₃ | ihN rewrite wk-wk r (⊑-∋ (⊑-trans s₂ s₃)) L' | wk-wk r (⊑-∋ s₃) M' =
    bind-rel (ihL (contains-ext (ext-trans e₂ e₃) c) E) λ u → either≈ u
      (λ v → ihM (contains-ext e₃ c) (env-ext v E)) (λ v → ihN c (env-ext v E))
  run≈ ck (S.prim p L M) D {r} c E with glob L D | run≈ ck L D
  ... | out s₁ D₁ L' | ihL with glob M D₁ | glob-ext M D₁ | run≈ ck M D₁
  ...   | out s₂ D₂ M' | e₂ | ihM rewrite wk-wk r (⊑-∋ s₂) L' =
    bind-rel (ihL (contains-ext e₂ c) E) λ v → bind-rel (ihM c E) λ w → ret (δ≈ p v w)
  run≈ ck (S.let′ M N) D {r} c E with glob M D | run≈ ck M D
  ... | out s₁ D₁ M' | ihM with glob N D₁ | glob-ext N D₁ | run≈ ck N D₁
  ...   | out s₂ D₂ N' | e₂ | ihN rewrite wk-wk r (⊑-∋ s₂) M' =
    bind-rel (ihM (contains-ext e₂ c) E) λ v → ihN c (env-ext v E)
  run≈ ck (S.fold M) D c E with glob M D | run≈ ck M D
  ... | out s D' M' | ih = bind-rel (ih c E) λ v → ret (fold≈ v)
  run≈ ck (S.unfold M) D c E with glob M D | run≈ ck M D
  ... | out s D' M' | ih = bind-rel (ih c E) λ v → ret (unfold≈ v)

  runs≈ ck [] D c E = ret []
  runs≈ ck (M ∷ Ms) D {r} c E with glob M D | run≈ ck M D
  ... | out s₁ D₁ M' | ihM with globs Ms D₁ | globs-ext Ms D₁ | runs≈ ck Ms D₁
  ...   | out s₂ D₂ Ms' | e₂ | ihMs rewrite wk-wk r (⊑-∋ s₂) M' =
    bind-rel (ihM (contains-ext e₂ c) E) λ v → bind-rel (ihMs c E) λ vs → ret (v ∷ vs)

  call≈ zero f w = timeout
  call≈ (suc ck) (pack≈ {c = N} rs (same (gcode D _ refl r c d))) w rewrite d =
    run≈ ck N D c λ { Z → w ; (S Z) → tup≈ rs }

{- the definitions made, closed over the whole table, are found there -}
close-ok : ∀ {Σ Σf} (dsf : All (Code Σf) Σf) (D : Made Σ) (s : Σ ⊑ Σf)
  → (∀ {n} (x : Σ ∋ n) → lookup dsf (⊑-∋ s x) ≡ lookup (close D s) x) → G.Contains dsf D (⊑-∋ s)
close-ok dsf [] s h = tt
close-ok dsf (D ▷ N) s h =
  ⊑-∋ s' , (λ x → sym (⊑-∋-trans (there⊑ here⊑) s x)) , h Z
  , G.contains-cong dsf D (⊑-∋-trans (there⊑ here⊑) s) (close-ok dsf D s' λ x → trans (cong (lookup dsf) (⊑-∋-trans (there⊑ here⊑) s x)) (h (S x)))
  where s' = ⊑-trans (there⊑ here⊑) s

globalize-correct : ∀ {A} (M : S.Tm [] A) → Equivalent (S4.sem M) (T.sem (globalize M))
globalize-correct M with glob M [] in eq
... | out s D M' = clocked _≈_ obs≈ λ ck → subst (λ N → RelResult _≈_ (S4.eval ck [] M) (T.eval dsf ck [] N)) (wk-id M')
    (run-out ck eq (close-ok dsf D here⊑ λ x → refl) λ ())
  where
  dsf = close D here⊑
  open G dsf
  run-out : ∀ ck {o} → glob M [] ≡ o → {r : Ren (Out.Σ' o) _} → Contains (Out.made o) r → Env≈ [] []
    → RelResult _≈_ (S4.eval ck [] M) (T.eval dsf ck [] (wk r (Out.res o)))
  run-out ck refl = run≈ ck M []
