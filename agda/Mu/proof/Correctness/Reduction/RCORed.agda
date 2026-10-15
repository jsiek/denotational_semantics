{-

  Correctness of remove complex operands (Clos5μ → Monμ) by a forward
  simulation of the Clos5μ reduction semantics by itself, as for typed
  rco (proof/Correctness/Reduction/RCORed.agda): the source runs with
  its definitions ds, the target, the embedding of the Monμ program
  (⌜_⌝ₚ), with the definitions rco makes of them.

  As for the typed pass:
  values contain no code, so both compute the same values. A complex
  operand M in the context h of the source is reduced by the target
  under a let (letc≈); once it is a value W, the target substitutes it,
  and is then related to h W. Every substitution is that of a call, a
  case or a let into code, which is related by the pass under that
  substitution (the fundamental lemma rco≈: sub σ M is related to
  sub τ ⌜ rco M ρ ⌝ when τ agrees with σ through ρ). The continuations
  of the pass take an atom under more binders (atomize≈): they are
  related for every substitution that agrees through the renaming.

-}

module Mu.proof.Correctness.Reduction.RCORed where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos5 hiding (wk; wks)
import Mu.Language.Mon as Mon
open Mon using (Atm; var; lit; ref; atm; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.RCO
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup) renaming (map to All-map)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.Framework.ReductionAll Obs o-error using (Each; []; _∷_; each-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.Reduction.Clos5 as T
open T using (Value; value-red; sub; exts; tmK; _•_; ∅; _[_])

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (does)
open import Data.Bool using (true; false)
import Data.Integer as Z
import Language.Prim as Pr

{- a lookup in a map -}
map-lookup : ∀ {X : Set} {P Q : X → Set} {xs : List X} {a} (f : ∀ {x} → P x → Q x) (ps : All P xs) (i : xs ∋ a)
  → lookup (All-map f ps) i ≡ f (lookup ps i)
map-lookup f (_ ∷ ps) Z = refl
map-lookup f (_ ∷ ps) (S i) = map-lookup f ps i

module _ {Σ : List DSig} (ds : All (Code Σ) Σ) where

  ds' : All (Code Σ) Σ
  ds' = All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)

  red₁ = T.red ds
  red₂ = T.red ds'

  {- closing substitutions, and those of values -}
  Clo : Ctx → Set
  Clo Γ = ∀ {B} → Γ ∋ B → Tm Σ [] B

  Vals : ∀ {Γ} → Clo Γ → Set
  Vals σ = ∀ {B} (x : _ ∋ B) → Value (σ x)

  Agree : ∀ {Γ Δ} → Clo Γ → Clo Δ → Ren Γ Δ → Set
  Agree σ τ ρ = ∀ {B} (x : _ ∋ B) → τ (ρ x) ≡ σ x

  {- The relation ---------------------------------------------------------------}

  infix 4 _≈_
  data _≈_ : ∀ {A} → Tm Σ [] A → Tm Σ [] A → Set where
    val≈ : ∀ {A} {V : Tm Σ [] A} → Value V → V ≈ V
    {- an operand M in the context h of the source, and under a let in the target -}
    letc≈ : ∀ {A B} {h : Tm Σ [] A → Tm Σ [] B} {M M' N} → Frame red₁ red₁ h → M ≈ M'
      → (∀ W → Value W → h W ≈ N [ W ]) → h M ≈ let′ M' N
    {- the constructs whose operands are values, and case and let, in both -}
    call≈ : ∀ {A B} {F : Tm Σ [] (A ⇒ B)} {W} → Value F → Value W → callc F W ≈ callc F W
    get≈ : ∀ {Δ A} {i : Δ ∋ A} {V : Tm Σ [] (tup Δ)} → Value V → get i V ≈ get i V
    prim≈ : ∀ {p V W} → Value V → Value W → prim p V W ≈ prim p V W
    unfold≈ : ∀ {A c} {V : Tm Σ [] (μ A {c})} → Value V → unfold V ≈ unfold V
    case≈ : ∀ {Γ Δ A B C} {σ : Clo Γ} {τ : Clo Δ} {ρ : Ren Γ Δ} {V : Tm Σ [] (A ⊹ B)} {M : Tm Σ (A ∷ Γ) C} {N : Tm Σ (B ∷ Γ) C} → Agree σ τ ρ → Vals σ → Value V
      → case V (sub (exts tmK σ) M) (sub (exts tmK σ) N)
        ≈ case V (sub (exts tmK τ) ⌜ rco M (ext ρ) ⌝) (sub (exts tmK τ) ⌜ rco N (ext ρ) ⌝)
    let≈ : ∀ {Γ Δ A B} {σ : Clo Γ} {τ : Clo Δ} {ρ : Ren Γ Δ} {M M' : Tm Σ [] A} {N : Tm Σ (A ∷ Γ) B} → Agree σ τ ρ → Vals σ
      → M ≈ M' → let′ M (sub (exts tmK σ) N) ≈ let′ M' (sub (exts tmK τ) ⌜ rco N (ext ρ) ⌝)

  {- a target value is the source's -}
  ≈-val : ∀ {A} {M V : Tm Σ [] A} → M ≈ V → Value V → M ≡ V
  ≈-val (val≈ _) _ = refl
  ≈-val (letc≈ _ _ _) ()
  ≈-val (call≈ _ _) ()
  ≈-val (get≈ _) ()
  ≈-val (prim≈ _ _) ()
  ≈-val (unfold≈ _) ()
  ≈-val (case≈ _ _ _) ()
  ≈-val (let≈ _ _ _) ()

  {- The fundamental lemma --------------------------------------------------------}

  ext-agree : ∀ {Γ Δ A} {σ : Clo Γ} {τ : Clo Δ} {ρ : Ren Γ Δ} (W : Tm Σ [] A) → Agree σ τ ρ → Agree (W • σ) (W • τ) (ext ρ)
  ext-agree W a Z = refl
  ext-agree W a (S x) = a x

  ext-vals : ∀ {Γ A} {σ : Clo Γ} {W : Tm Σ [] A} → Value W → Vals σ → Vals (W • σ)
  ext-vals w vs Z = w
  ext-vals w vs (S x) = vs x

  {- an atom, renamed -}
  atm-ren : ∀ {Δ Δ' A} (a : Atm Σ Δ A) {r : Ren Δ Δ'} {τ : Clo Δ} {τ' : Clo Δ'} → Agree τ τ' r
    → sub τ' ⌜ Mon.ren r a ⌝ᵃ ≡ sub τ ⌜ a ⌝ᵃ
  atm-ren (var x) e = e x
  atm-ren (lit B c) e = refl
  atm-ren (ref f) e = refl

  {- what a continuation of rco gives: related terms, for every atom that is a value under a substitution
     that agrees -}
  Kont : ∀ {Δ A B} → (Tm Σ [] A → Tm Σ [] B) → Clo Δ → K Σ Δ A B → Set
  Kont {Δ} {A} {B} h τ k = ∀ {Δ'} (r : Ren Δ Δ') (τ' : Clo Δ') (a : Atm Σ Δ' A) → Agree τ τ' r
    → Value (sub τ' ⌜ a ⌝ᵃ) → h (sub τ' ⌜ a ⌝ᵃ) ≈ sub τ' ⌜ k r a ⌝

  rco≈ : ∀ {Γ Δ A} (M : Tm Σ Γ A) (ρ : Ren Γ Δ) (σ : Clo Γ) (τ : Clo Δ) → Agree σ τ ρ → Vals σ
    → sub σ M ≈ sub τ ⌜ rco M ρ ⌝
  atomize≈ : ∀ {Γ Δ A B} (M : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) (σ : Clo Γ) (τ : Clo Δ) → Agree σ τ ρ → Vals σ
    → {h : Tm Σ [] A → Tm Σ [] B} → Frame red₁ red₁ h → Kont h τ k → h (sub σ M) ≈ sub τ ⌜ atomize M ρ k ⌝
  atomizes≈ : ∀ {Γ Δ Δs B} (Ms : All (Tm Σ Γ) Δs) (ρ : Ren Γ Δ) (k : ∀ {Δ'} → Ren Δ Δ' → All (Atm Σ Δ') Δs → Mon.Exp Σ Δ' B)
    (σ : Clo Γ) (τ : Clo Δ) → Agree σ τ ρ → Vals σ → {g : All (Tm Σ []) Δs → Tm Σ [] B} → Frame (T.reds ds) red₁ g
    → (∀ {Δ'} (r : Ren Δ Δ') (τ' : Clo Δ') (as : All (Atm Σ Δ') Δs) → Agree τ τ' r
         → Each Value (T.travs tmK τ' ⌜ as ⌝ᵛ) → g (T.travs tmK τ' ⌜ as ⌝ᵛ) ≈ sub τ' ⌜ k r as ⌝)
    → g (T.travs tmK σ Ms) ≈ sub τ ⌜ atomizes Ms ρ k ⌝
  atomize₂≈ : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (M : Tm Σ Γ A₂) (ρ : Ren Γ Δ)
    (k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Mon.Exp Σ Δ' B) (σ : Clo Γ) (τ : Clo Δ) → Agree σ τ ρ → Vals σ
    → {h : Tm Σ [] A₁ → Tm Σ [] A₂ → Tm Σ [] B} → (∀ {Y} → Frame red₁ red₁ (λ X → h X Y))
    → (∀ {X} → Value X → Frame red₁ red₁ (h X))
    → (∀ {Δ'} (τ' : Clo Δ') a b → Value (sub τ' ⌜ a ⌝ᵃ) → Value (sub τ' ⌜ b ⌝ᵃ)
         → h (sub τ' ⌜ a ⌝ᵃ) (sub τ' ⌜ b ⌝ᵃ) ≈ sub τ' ⌜ k a b ⌝)
    → h (sub σ L) (sub σ M) ≈ sub τ ⌜ atomize₂ L M ρ k ⌝

  {- a complex operand: a let -}
  let-op : ∀ {Γ Δ A B} (M : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) (σ : Clo Γ) (τ : Clo Δ) → Agree σ τ ρ → Vals σ
    → {h : Tm Σ [] A → Tm Σ [] B} → Frame red₁ red₁ h → Kont h τ k
    → h (sub σ M) ≈ sub τ ⌜ Mon.let′ (rco M ρ) (k S (var Z)) ⌝
  let-op M ρ k σ τ a vs F kk =
    letc≈ F (rco≈ M ρ σ τ a vs)
      λ W w → subst (_ ≈_) (sym (T.exts-[] τ W ⌜ k S (var Z) ⌝)) (kk S (W • τ) (var Z) (λ _ → refl) w)

  rco≈ (` x) ρ σ τ a vs = subst (_≈ _) (a x) (val≈ (subst Value (sym (a x)) (vs x)))
  rco≈ (fun-ref f) ρ σ τ a vs = val≈ T.fun-ref
  rco≈ (pack L M) ρ σ τ a vs =
    atomize₂≈ L M ρ Mon.pack σ τ a vs {h = pack} (frame _ λ _ → refl) (λ v → frame _ λ _ → val-in (value-red v))
      λ τ' a b v w → val≈ (T.pack v w)
  rco≈ (callc L M) ρ σ τ a vs =
    atomize₂≈ L M ρ Mon.callc σ τ a vs {h = callc} (frame _ λ _ → refl) (λ v → frame _ λ _ → val-in (value-red v))
      λ τ' a b v w → call≈ v w
  rco≈ (lit B c) ρ σ τ a vs = val≈ T.lit
  rco≈ (tuple Ms) ρ σ τ a vs =
    atomizes≈ Ms ρ (λ _ as → Mon.tuple as) σ τ a vs {g = tuple} (frame _ λ _ → refl) λ r τ' as e vs' → val≈ (T.tuple vs')
  rco≈ (get i M) ρ σ τ a vs = atomize≈ M ρ _ σ τ a vs {h = get i} (frame _ λ _ → refl) λ r τ' b e v → get≈ v
  rco≈ (inl M) ρ σ τ a vs = atomize≈ M ρ _ σ τ a vs {h = inl} (frame _ λ _ → refl) λ r τ' b e v → val≈ (T.inl v)
  rco≈ (inr M) ρ σ τ a vs = atomize≈ M ρ _ σ τ a vs {h = inr} (frame _ λ _ → refl) λ r τ' b e v → val≈ (T.inr v)
  rco≈ (case L M N) ρ σ τ a vs =
    atomize≈ L ρ _ σ τ a vs {h = λ X → case X _ _} (frame _ λ _ → refl) λ r τ' b e v → case≈ {τ = τ'} {ρ = λ x → r (ρ x)} {M = M} {N = N} (λ x → trans (e (ρ x)) (a x)) vs v
  rco≈ (prim p L M) ρ σ τ a vs =
    atomize₂≈ L M ρ (Mon.prim p) σ τ a vs {h = prim p} (frame _ λ _ → refl) (λ v → frame _ λ _ → val-in (value-red v))
      λ τ' a b v w → prim≈ v w
  rco≈ (let′ M N) ρ σ τ a vs = let≈ {τ = τ} {ρ = ρ} {N = N} a vs (rco≈ M ρ σ τ a vs)
  rco≈ (fold M) ρ σ τ a vs = atomize≈ M ρ _ σ τ a vs {h = fold} (frame _ λ _ → refl) λ r τ' b e v → val≈ (T.fold v)
  rco≈ (unfold M) ρ σ τ a vs = atomize≈ M ρ _ σ τ a vs {h = unfold} (frame _ λ _ → refl) λ r τ' b e v → unfold≈ v

  atomize≈ (` x) ρ k σ τ a vs {h} F kk = subst (λ X → h X ≈ _) (a x) (kk (λ y → y) τ (var (ρ x)) (λ _ → refl) (subst Value (sym (a x)) (vs x)))
  atomize≈ (fun-ref f) ρ k σ τ a vs F kk = kk (λ y → y) τ (ref f) (λ _ → refl) T.fun-ref
  atomize≈ (lit B c) ρ k σ τ a vs F kk = kk (λ y → y) τ (lit B c) (λ _ → refl) T.lit
  atomize≈ M@(pack _ _) = let-op M
  atomize≈ M@(callc _ _) = let-op M
  atomize≈ M@(tuple _) = let-op M
  atomize≈ M@(get _ _) = let-op M
  atomize≈ M@(inl _) = let-op M
  atomize≈ M@(inr _) = let-op M
  atomize≈ M@(case _ _ _) = let-op M
  atomize≈ M@(prim _ _ _) = let-op M
  atomize≈ M@(let′ _ _) = let-op M
  atomize≈ M@(fold _) = let-op M
  atomize≈ M@(unfold _) = let-op M

  atomizes≈ [] ρ k σ τ a vs F kk = kk (λ y → y) τ [] (λ _ → refl) []
  atomizes≈ (M ∷ Ms) ρ k σ τ a vs {g} G kk =
    atomize≈ M ρ _ σ τ a vs (frame-∘ (frame {g = _∷ _} _ λ _ → refl) G)
      λ r τ' b e v → atomizes≈ Ms _ _ σ τ' (λ x → trans (e (ρ x)) (a x)) vs
        (frame-∘ (frame {g = _ ∷_} _ λ _ → val-in (value-red v)) G)
        λ r' τ'' as e' vs' → subst (λ X → g (X ∷ _) ≈ _) (atm-ren b e')
          (kk _ τ'' (Mon.ren r' b ∷ as) (λ x → trans (e' (r x)) (e x)) (subst Value (sym (atm-ren b e')) v ∷ vs'))

  atomize₂≈ L M ρ k σ τ a vs {h} F₁ F₂ kk =
    atomize≈ L ρ _ σ τ a vs F₁
      λ r τ' b e v → atomize≈ M _ _ σ τ' (λ x → trans (e (ρ x)) (a x)) vs (F₂ v)
        λ r' τ'' c e' w → subst (λ X → h X (sub τ'' ⌜ c ⌝ᵃ) ≈ _) (atm-ren b e') (kk τ'' (Mon.ren r' b) c (subst Value (sym (atm-ren b e')) v) w)

  {- The simulation ------------------------------------------------------------------}

  Ans′ : ∀ {A} → Tm Σ [] A → Red (Tm Σ [] A) → Tm Σ [] A → Set
  Ans′ = Ans red₂ Value _≈_

  out-value : ∀ p n m → Value (T.out {Σ} {[]} p n m)
  out-value Pr.sub n m = T.lit
  out-value Pr.eq n m with does (n Z.≟ m)
  ... | true = T.inl (T.tuple [])
  ... | false = T.inr (T.tuple [])

  sim : ∀ {A} {M M' : Tm Σ [] A} → M ≈ M' → Ans′ M (red₁ M) M'
  sim (val≈ v) = subst (λ x → Ans′ _ x _) (sym (value-red v)) (val ε v (val≈ v))
  sim (letc≈ {h = h} {M} F r k) =
    subst (λ x → Ans′ (h M) x _) (sym (Frame.eq F M))
      (ans-in (frame _ λ _ → refl) (λ r' → letc≈ F r' k) (sim r) λ v r' → cont v r')
    where
    cont : ∀ {V'} → Value V' → M ≈ V' → Ans′ (h M) (Frame.κ F M) (let′ V' _)
    cont v r' with ≈-val r' v
    ... | refl = ans-step (val-in (value-red v))
                   (subst (λ x → Ans′ (h M) x _) (trans (Frame.eq F M) (val-in (value-red v))) (sim (k M v)))
  sim (call≈ {W = W} f@(T.pack {M = E} (T.fun-ref {f = g}) e) w) rewrite value-red {ds = ds} f | value-red {ds = ds} w =
    to (one (trans (val-in (value-red f)) (trans (val-in (value-red w))
              (cong (λ D → to (sub (W • E • ∅) D)) (trans (map-lookup ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds) g) (cong ⌜_⌝ (map-lookup (λ D → rco D (λ x → x)) ds g)))))))
       (rco≈ (lookup ds g) (λ x → x) (W • E • ∅) (W • E • ∅) (λ _ → refl) (ext-vals w (ext-vals e λ ())))
  sim (get≈ {i = i} v@(T.tuple vs)) rewrite value-red {ds = ds} v = to (one (val-in (value-red v))) (val≈ (each-lookup vs i))
  sim (prim≈ {p} T.lit T.lit) = to (one refl) (val≈ (out-value p _ _))
  sim (unfold≈ v@(T.fold v')) rewrite value-red {ds = ds} v = to (one (val-in (value-red v))) (val≈ v')
  sim (case≈ {σ = σ} {τ} {ρ} {M = M} {N} a vs v) = ans-skip (value-red v) (case-sim v)
    where
    case-sim : ∀ {V : Tm Σ [] (_ ⊹ _)} → Value V → Ans′ (case V (sub (exts tmK σ) M) (sub (exts tmK σ) N)) (T.case? V refl (sub (exts tmK σ) M) (sub (exts tmK σ) N))
                 (case V (sub (exts tmK τ) ⌜ rco M (ext ρ) ⌝) (sub (exts tmK τ) ⌜ rco N (ext ρ) ⌝))
    case-sim v@(T.inl w) = to (one (val-in (value-red v)))
      (subst₂ _≈_ (sym (T.exts-[] σ _ M)) (sym (T.exts-[] τ _ ⌜ rco M (ext ρ) ⌝)) (rco≈ M _ _ _ (ext-agree _ a) (ext-vals w vs)))
    case-sim v@(T.inr w) = to (one (val-in (value-red v)))
      (subst₂ _≈_ (sym (T.exts-[] σ _ N)) (sym (T.exts-[] τ _ ⌜ rco N (ext ρ) ⌝)) (rco≈ N _ _ _ (ext-agree _ a) (ext-vals w vs)))
  sim (let≈ {σ = σ} {τ} {ρ} {N = N} a vs r) =
    ans-in (frame _ λ _ → refl) (let≈ {τ = τ} {ρ = ρ} {N = N} a vs) (sim r) λ v r' → let-sim v r'
    where
    let-sim : ∀ {M V'} → Value V' → M ≈ V'
      → Ans′ (let′ M (sub (exts tmK σ) N)) (to (sub (exts tmK σ) N [ M ])) (let′ V' (sub (exts tmK τ) ⌜ rco N (ext ρ) ⌝))
    let-sim v r' with ≈-val r' v
    ... | refl = to (one (val-in (value-red v)))
      (subst₂ _≈_ (sym (T.exts-[] σ _ N)) (sym (T.exts-[] τ _ ⌜ rco N (ext ρ) ⌝)) (rco≈ N _ _ _ (ext-agree _ a) (ext-vals v vs)))

{- The end theorem ---------------------------------------------------------------------}

rco-correct : ∀ {A} (P : Program A) → Equivalent (T.sem P) (T.sem ⌜ rco-program P ⌝ₚ)
rco-correct (program ds M) =
  red-equivalent value-red (_≈_ ds) (sim ds) (λ m _ v → cong T.obs (≈-val ds m v))
    (subst₂ (_≈_ ds) (T.sub-id (λ ()) M) (T.sub-id (λ ()) ⌜ rco M (λ x → x) ⌝) (rco≈ ds M (λ x → x) ∅ ∅ (λ ()) (λ ())))
