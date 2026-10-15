{-

  Correctness of typed remove complex operands (Clos5ᵀ → Monᵀ,
  Compiler/RCO.agda) in the graph model with errors: a Monᵀ
  program means its embedding into Clos5ᵀ, which means what the source
  means, for every program.

  Every typed operator is a kernel under binds of its operands (binds),
  with no check. So binding a complex operand to a variable first is
  the bind the operator does anyway; on an atom, a set of values, the
  operator's binds are their left unit (βₙ). By induction on the term,
  for environments that agree up to the renaming of the pass, with
  values for the variables in scope (R); atomize N k means the bind of
  N into what k means, for any continuation k that means H on an atom
  that means X (Kripke-style, under the lets that later operands add).

-}

module proof.Correctness.GraphErr.RCOCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.OpsBase using (nthD; ℬ)
open import proof.Framework.GraphModel.Ops using (pair; proj; inl; inr; 𝒯; 𝒞)
open import proof.Framework.GraphModel.Continuity using (pair-good; proj-good; inl-good; inr-good; 𝒯-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Framework.GraphModel.TypedBinders using (binds-val-≃; callcᵈ; callc-good)
open import proof.Framework.GraphModel.TypedOk using (check-kind-good)
open import proof.Semantics.Graph.Prim using (primD-good)
open import Semantics.Graph.Prim using (primD)
open import Semantics.GraphErr.Typed.Ops using (caseᵗ; checkedᵠ; keep; hit; kindᶠ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import proof.Semantics.GraphErr.Typed.Clos2 using (⌊⌋-≃; hit-mono; hit-fin)
open import proof.Semantics.GraphErr.Typed.Clos5
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5
import Language.Typed.Mon as M
open M using (Atm; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Compiler.RCO

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Function using (_$_)

{- binds on sets of values equal to Ys are the kernel on Ys -}
≃s⇒RRs : ∀ n {Ds Es : Results (𝒫 Value) (replicate n ■)} → (∀ i → nthD Ds i ≃ nthD Es i) → RRs (replicate n ■) Ds Es
≃s⇒RRs zero _ = ptt
≃s⇒RRs (suc n) e = ⟨ lift (e zero) , ≃s⇒RRs n (λ i → e (suc i)) ⟩

βₙ : ∀ n {K Ds Ys} → Good ⊤ (replicate n ■) K → AllVal n Ds → (∀ i → nthD Ys i ≃ nthD Ds i) → K Ys ≃ binds n Ds K
βₙ n G vs e = ≃-sym (binds-val-≃ n vs λ Xs≃ → mono-≃ (mono G) (≃s⇒RRs n λ i → ≃-trans (Xs≃ i) (≃-sym (e i))))

ℬ-val : ∀ {B c} → Val (ℬ B c ptt)
ℬ-val {c = c} = ⟨ (λ { _ d∈ refl → ⊥-elim d∈ }) , ⟨ const c , ⟨ refl , refl ⟩ ⟩ ⟩

{- a case on a set of values equal to A -}
case-val : ∀ {A X F F' G G'} → Val X → X ≃ A → BodyEq F F' → BodyEq G G'
  → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ caseᵗ A F' G'
case-val {A} {X} {F} {F'} {G} {G'} v e eF eG =
  ≃-trans ⟨ 𝒞⇂-⊆ {X} {⌊ A ⌋} {F} {F'} {G} {G'} (λ d d∈ → ⟨ proj₁ e d d∈ , proj₁ v d d∈ ⟩) (λ V a b c → proj₁ (eF V a b c)) (λ V a b c → proj₁ (eG V a b c))
    , 𝒞⇂-⊆ {⌊ A ⌋} {X} {F'} {F} {G'} {G} (λ d d∈ → proj₂ e d (proj₁ d∈)) (λ V a b c → proj₂ (eF V a b c)) (λ V a b c → proj₂ (eG V a b c)) ⟩
    (≃-sym (≫=-val-β {A} {λ Y → 𝒞 ⟨ Y ⇂ ValPayload , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩} (Val-≃ e v)))

{- the kernels of the operators -}
pk : ∀ t → Good ⊤ (■ ∷ []) (λ Ds → checkedᵠ kind₄ (kindᶠ (flat t)) (proj₁ Ds) (keep kind₄ t (proj₁ Ds)))
pk t = check-kind-good (hit t) (hit-mono t) (hit-fin t) kind₄ (kindᶠ (flat t))

{- Environments --------------------------------------------------------------------}

{- source and target environments agree up to r, on values -}
record R {Γ Δ} (r : Ren Γ Δ) (ρ ρ' : Env Value) : Set where
  constructor mkR
  field at : ∀ {A} (x : Γ ∋ A) → ρ (idx x) ≃ ρ' (idx (r x)) × Val (ρ' (idx (r x)))

{- a target environment under more lets -}
record R' {Δ Δ'} (r : Ren Δ Δ') (ρ' ρ'' : Env Value) : Set where
  constructor mkR'
  field at : ∀ {A} (x : Δ ∋ A) → ρ' (idx x) ≃ ρ'' (idx (r x))

R-∘ : ∀ {Γ Δ Δ'} {r : Ren Γ Δ} {r' : Ren Δ Δ'} {ρ ρ' ρ''} → R r ρ ρ' → R' r' ρ' ρ'' → R (λ x → r' (r x)) ρ ρ''
R-∘ h h' = mkR λ x → ⟨ ≃-trans (proj₁ (R.at h x)) (R'.at h' _) , Val-≃ (R'.at h' _) (proj₂ (R.at h x)) ⟩

R-ext : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ ρ' X X'} → R r ρ ρ' → X ≃ X' → Val X' → R (ext {B = B} r) (X • ρ) (X' • ρ')
R-ext h e v = mkR λ { Z → ⟨ e , v ⟩ ; (S x) → R.at h x }

R'-id : ∀ {Δ} {ρ' : Env Value} → R' {Δ} (λ y → y) ρ' ρ'
R'-id = mkR' λ x → ≃-refl

R'-S : ∀ {Δ B} {ρ' : Env Value} {X} → R' {Δ} (S {b = B}) ρ' (X • ρ')
R'-S = mkR' λ x → ≃-refl

{- The pass ------------------------------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TV : ∀ k → Val (T k)) where

  𝒜 : ∀ {Σ Δ A} → Atm Σ Δ A → Env Value → 𝒫 Value
  𝒜 a = ⟦ ⌜ a ⌝ᵃ ⟧[ T' ]

  ren-𝒜 : ∀ {Σ Δ Δ' A} {r : Ren Δ Δ'} {ρ' ρ''} → R' r ρ' ρ'' → (a : Atm Σ Δ A) → 𝒜 a ρ' ≃ 𝒜 (ren r a) ρ''
  ren-𝒜 h (var x) = R'.at h x
  ren-𝒜 h (lit B c) = ≃-refl
  ren-𝒜 h (ref f) = ≃-refl

  {- H on X is what k means on an atom that means X -}
  Kont : ∀ {Σ Δ A B} → (𝒫 Value → 𝒫 Value) → K Σ Δ A B → Env Value → Set₁
  Kont {Σ} {Δ} {A} H k ρ' = ∀ {Δ'} (r' : Ren Δ Δ') {ρ''} → R' r' ρ' ρ'' → (a : Atm Σ Δ' A) → ∀ {X} → Val X → X ≃ 𝒜 a ρ''
    → H X ≃ ⟦ ⌜ k r' a ⌝ ⟧[ T' ] ρ''

  rco-sem : ∀ {Σ Γ Δ A} (M : Tm Σ Γ A) (r : Ren Γ Δ) {ρ ρ'} → R r ρ ρ' → ⟦ M ⟧[ T ] ρ ≃ ⟦ ⌜ rco M r ⌝ ⟧[ T' ] ρ'
  atomize-sem : ∀ {Σ Γ Δ A B} (N : Tm Σ Γ A) (r : Ren Γ Δ) (k : K Σ Δ A B) {ρ ρ' H} → R r ρ ρ' → Kont H k ρ'
    → (⟦ N ⟧[ T ] ρ ≫= H) ≃ ⟦ ⌜ atomize N r k ⌝ ⟧[ T' ] ρ'

  {- a complex operand: a let -}
  cx : ∀ {Σ Γ Δ A B} (N : Tm Σ Γ A) (r : Ren Γ Δ) (k : K Σ Δ A B) {ρ ρ' H} → R r ρ ρ' → Kont H k ρ'
    → (⟦ N ⟧[ T ] ρ ≫= H) ≃ ⟦ ⌜ M.let′ (rco N r) (k S (var Z)) ⌝ ⟧[ T' ] ρ'
  cx N r k {ρ} {ρ'} {H} h hk = ≫=-≃ {F = H} {λ X → ⟦ ⌜ k S (var Z) ⌝ ⟧[ T' ] (X • ρ')} (rco-sem N r h)
    λ c _ → hk S R'-S (var Z) (⌊⌋-val c) (⌊⌋-≃ (rco-sem N r h))

  {- an atom: a set of values -}
  at : ∀ {Σ Δ A B} {k : K Σ Δ A B} {ρ' H} (a : Atm Σ Δ A) {D} → Kont H k ρ' → Val D → D ≃ 𝒜 a ρ'
    → (D ≫= H) ≃ ⟦ ⌜ k (λ y → y) a ⌝ ⟧[ T' ] ρ'
  at {H = H} a {D} hk v e = ≃-trans (≫=-val-β {D} {H} v)
                        (hk (λ y → y) R'-id a (⌊⌋-val (Val⇒Conv v)) (≃-trans (⌊⌋-≃′ v) e))
    where ⌊⌋-≃′ : ∀ {D} → Val D → ⌊ D ⌋ ≃ D
          ⌊⌋-≃′ v = ⟨ ⌊⌋-⊆ , ⌊⌋-clean (proj₁ v) ⟩

  atomize-sem (` x) r k h hk = at {k = k} (var (r x)) hk (Val-≃ (≃-sym (proj₁ (R.at h x))) (proj₂ (R.at h x))) (proj₁ (R.at h x))
  atomize-sem (fun-ref f) r k h hk = at {k = k} (ref f) hk (TV _) (TT _)
  atomize-sem (lit B c) r k h hk = at {k = k} (lit B c) hk ℬ-val ≃-refl
  atomize-sem N@(pack _ _) r k h hk = cx N r k h hk
  atomize-sem N@(callc _ _) r k h hk = cx N r k h hk
  atomize-sem N@(tuple _) r k h hk = cx N r k h hk
  atomize-sem N@(get _ _) r k h hk = cx N r k h hk
  atomize-sem N@(inl _) r k h hk = cx N r k h hk
  atomize-sem N@(inr _) r k h hk = cx N r k h hk
  atomize-sem N@(case _ _ _) r k h hk = cx N r k h hk
  atomize-sem N@(prim _ _ _) r k h hk = cx N r k h hk
  atomize-sem N@(let′ _ _) r k h hk = cx N r k h hk
  atomize-sem N@(inject _ _) r k h hk = cx N r k h hk
  atomize-sem N@(project _ _) r k h hk = cx N r k h hk

  {- one operand, into a kernel κ -}
  op₁ : ∀ {Σ Γ Δ A B} (N : Tm Σ Γ A) (r : Ren Γ Δ) (f : ∀ {Δ'} → Atm Σ Δ' A → M.Exp Σ Δ' B) {κ} → Good ⊤ (■ ∷ []) κ
    → (∀ {Δ'} (a : Atm Σ Δ' A) {ρ''} → binds 1 ⟨ 𝒜 a ρ'' , ptt ⟩ κ ≡ ⟦ ⌜ f a ⌝ ⟧[ T' ] ρ'')
    → ∀ {ρ ρ'} → R r ρ ρ' → binds 1 ⟨ ⟦ N ⟧[ T ] ρ , ptt ⟩ κ ≃ ⟦ ⌜ atomize N r (λ _ a → f a) ⌝ ⟧[ T' ] ρ'
  op₁ N r f G hf h = atomize-sem N r (λ _ a → f a) h λ r' h' a {X} v e →
    ≃-trans (βₙ 1 G (λ { zero → Val-≃ e v }) λ { zero → e }) (≃-reflexive (hf a))

  {- two operands, into a kernel κ -}
  op₂ : ∀ {Σ Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) (r : Ren Γ Δ)
    (f : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → M.Exp Σ Δ' B) {κ} → Good ⊤ (■ ∷ ■ ∷ []) κ
    → (∀ {Δ'} (a : Atm Σ Δ' A₁) b {ρ''} → binds 2 ⟨ 𝒜 a ρ'' , ⟨ 𝒜 b ρ'' , ptt ⟩ ⟩ κ ≡ ⟦ ⌜ f a b ⌝ ⟧[ T' ] ρ'')
    → ∀ {ρ ρ'} → R r ρ ρ' → binds 2 ⟨ ⟦ L ⟧[ T ] ρ , ⟨ ⟦ N ⟧[ T ] ρ , ptt ⟩ ⟩ κ ≃ ⟦ ⌜ atomize₂ L N r f ⌝ ⟧[ T' ] ρ'
  op₂ L N r f G hf h = atomize-sem L r _ h λ r' h' a {X} v e →
    atomize-sem N (λ x → r' (r x)) _ (R-∘ h h') λ r'' h'' b {Y} w e' →
      ≃-trans (βₙ 2 G (λ { zero → Val-≃ (≃-trans e (ren-𝒜 h'' a)) v ; (suc zero) → Val-≃ e' w })
                      λ { zero → ≃-trans e (ren-𝒜 h'' a) ; (suc zero) → e' })
        (≃-reflexive (hf (ren r'' a) b))

  {- n operands, into a kernel K -}
  atomizes-sem : ∀ {Σ Γ Δ n B} (Ns : Vec (Tm Σ Γ Any) n) (r : Ren Γ Δ)
    (k : ∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) n → M.Exp Σ Δ' B) {ρ ρ'} {H : Results (𝒫 Value) (replicate n ■) → 𝒫 Value}
    → R r ρ ρ'
    → (∀ {Δ'} (r' : Ren Δ Δ') {ρ''} → R' r' ρ' ρ'' → (as : Vec (Atm Σ Δ' Any) n) → ∀ {Xs} → AllVal n Xs
         → (∀ i → nthD Xs i ≃ nthD (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] ρ'') i) → H Xs ≃ ⟦ ⌜ k r' as ⌝ ⟧[ T' ] ρ'')
    → binds n (⟦ Ns ⟧s[ T ] ρ) H ≃ ⟦ ⌜ atomizes Ns r k ⌝ ⟧[ T' ] ρ'
  atomizes-sem [] r k h hk = hk (λ y → y) R'-id [] (λ ()) (λ ())
  atomizes-sem (N ∷ Ns) r k h hk = atomize-sem N r _ h λ r' h' a {X} v e →
    atomizes-sem Ns (λ x → r' (r x)) _ (R-∘ h h') λ r'' h'' as {Xs} vs es →
      hk (λ x → r'' (r' x)) (mkR' λ x → ≃-trans (R'.at h' x) (R'.at h'' _)) (ren r'' a ∷ as)
         (λ { zero → v ; (suc i) → vs i }) λ { zero → ≃-trans e (ren-𝒜 h'' a) ; (suc i) → es i }

  rco-sem (` x) r h = proj₁ (R.at h x)
  rco-sem (fun-ref f) r h = TT _
  rco-sem (pack L N) r h = op₂ L N r M.pack pair-good (λ _ _ → refl) h
  rco-sem (callc L N) r h = op₂ L N r M.callc callc-good (λ _ _ → refl) h
  rco-sem (lit B c) r h = ≃-refl
  rco-sem (tuple {n = n} Ns) r h = atomizes-sem Ns r (λ _ as → M.tuple as) h λ r' h' as vs es →
    βₙ n (𝒯-good n) (λ i → Val-≃ (es i) (vs i)) es
  rco-sem (get i N) r h = op₁ N r (M.get i) (proj-good i) (λ _ → refl) h
  rco-sem (inl N) r h = op₁ N r M.inl inl-good (λ _ → refl) h
  rco-sem (inr N) r h = op₁ N r M.inr inr-good (λ _ → refl) h
  rco-sem (case L N₁ N₂) r {ρ} {ρ'} h =
    atomize-sem L r _ {H = λ Y → 𝒞 ⟨ Y ⇂ ValPayload , ⟨ (λ Z → ⟦ N₁ ⟧[ T ] (Z • ρ)) , ⟨ (λ Z → ⟦ N₂ ⟧[ T ] (Z • ρ)) , ptt ⟩ ⟩ ⟩} h
      λ r' {ρ''} h' a v e → case-val {F = λ Z → ⟦ N₁ ⟧[ T ] (Z • ρ)} {λ Z → ⟦ ⌜ rco N₁ (ext λ x → r' (r x)) ⌝ ⟧[ T' ] (Z • ρ'')}
        {λ Z → ⟦ N₂ ⟧[ T ] (Z • ρ)} {λ Z → ⟦ ⌜ rco N₂ (ext λ x → r' (r x)) ⌝ ⟧[ T' ] (Z • ρ'')} v e (br N₁ r' {ρ''} h') (br N₂ r' {ρ''} h')
    where
    br : ∀ {Δ'} N (r' : Ren _ Δ') {ρ''} → R' r' ρ' ρ'' → BodyEq (λ Z → ⟦ N ⟧[ T ] (Z • ρ)) (λ Z → ⟦ ⌜ rco N (ext λ x → r' (r x)) ⌝ ⟧[ T' ] (Z • ρ''))
    br N r' h' V ne _ n = rco-sem N _ (R-ext (R-∘ h h') ≃-refl (noerr-val V ne n))
  rco-sem (prim p L N) r h = op₂ L N r (M.prim p) (primD-good p) (λ _ _ → refl) h
  rco-sem (let′ N₁ N₂) r {ρ} {ρ'} h =
    ≫=-≃ {F = λ X → ⟦ N₂ ⟧[ T ] (X • ρ)} {λ X → ⟦ ⌜ rco N₂ (ext r) ⌝ ⟧[ T' ] (X • ρ')} (rco-sem N₁ r h)
      λ _ c → rco-sem N₂ (ext r) (R-ext h (⌊⌋-≃ (rco-sem N₁ r h)) (⌊⌋-val c))
  rco-sem (inject G N) r h = ≃-trans (≃-sym ≫=-η) (atomize-sem N r _ h λ r' h' a v e → e)
  rco-sem (project t N) r h = op₁ N r (M.project t) (pk t) (λ _ → refl) h

{- Programs -------------------------------------------------------------------------}

map-map : ∀ {P Q S : ℕ → Set} {ns} (f : ∀ {n} → P n → Q n) (g : ∀ {n} → Q n → S n) (ds : All P ns)
  → All-map g (All-map f ds) ≡ All-map (λ d → g (f d)) ds
map-map f g [] = refl
map-map f g (d ∷ ds) = cong₂ _∷_ refl (map-map f g ds)

rco-correct : ∀ (P : Program) → ⟦ P ⟧₅ ≃ ⟦ ⌜ rco-program P ⌝ₚ ⟧₅
rco-correct (program {Σ} ds N) = rco-sem TT (tbl-val (λ _ → ΛΛᵐ-val) ds) N (λ x → x) (mkR λ ())
  where
  TT : ∀ k → tbl code₅ ds k ≃ tbl code₅ (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)) k
  TT k rewrite map-map (λ D → rco D (λ x → x)) ⌜_⌝ ds = ≃-trans (≃-reflexive (cong (λ es → tbl code₅ es k) (sym (map-id ds)))) $
    tbl-map (λ T → ∀ k → Val (T k)) (λ D → D) (λ D → ⌜ rco D (λ x → x) ⌝) (λ es → tbl-val {c = code₅} (λ _ → ΛΛᵐ-val) (All-map (λ D → D) es))
      (λ TT' TV' d → ΛΛᵐ-≃′ λ V U neV _ nV neU _ nU →
         rco-sem TT' TV' d (λ x → x) (mkR λ { Z → ⟨ ≃-refl , noerr-val U neU nU ⟩ ; (S Z) → ⟨ ≃-refl , noerr-val V neV nV ⟩ })) ds k
