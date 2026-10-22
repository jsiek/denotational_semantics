{-

  Correctness of optimize (Clos2μ → Clos2μ) in Scott domains
  (Mu/Semantics/Scott/Clos2.agda), as in the graph model
  (Mu/proof/Correctness/Graph/OptimizeCorrect.agda), with equality of
  values in place of equality of sets and defined for nonempty.

  ⟦ M ⟧ ρ = ⟦ opt M r ⟧ ρ' when ρ and ρ' agree through r on the
  variables that M uses (Agree), and ρ is defined on all variables in
  scope (NE). Every case but the closure is a congruence. The free
  variables of a closure and the kept ones are related by the selection
  (Th): a kept one is equal, a dropped one is a variable, so defined.
  Hence the two closures' guards hold together (guard-iff,
  Mu/proof/Semantics/Scott/OptimizeLemmas.agda), and under them the
  environments of the codes agree through squeeze on the variables the
  code uses.

  Th of a free variable and the rest is a separate, non-recursive step
  (th-cons) rather than a `with` on keep? in th-ok as in the graph
  model: a `with` whose goal mentions meanings (here the tuples of the
  free variables) is very slow to check (th-ok by `with` does not
  check in 6 minutes).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type
open import Mu.Language.Clos2
open import Mu.Compiler.Optimize renaming (ext to ext-ren)
open import Mu.Framework.AllUtil using (All; []; _∷_; Flags; kept; select; sq; squeeze; pos; ∨-l; ∨-r; lookup)
open import Framework.abt.GSubst using (_•_)
open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (fromWitness)

module Mu.proof.Correctness.Scott.OptimizeCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Clos2 pt fe pe
open import Mu.proof.Semantics.Scott.OptimizeLemmas pt fe pe using (All-defined; guard-iff)

NE : Ctx → ⟨ Env ⟩ → 𝓤₀ ̇
NE Γ ρ = ∀ {C} (x : Γ ∋ C) → defined (ρ (idx x))

Agree : ∀ {Γ Γ'} (u : ∀ {C} → Γ ∋ C → Bool) → Ren u Γ' → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
Agree u r ρ ρ' = ∀ {C} x (t : T (u {C} x)) → ρ (idx x) ＝ ρ' (idx (r x t))

ext-ne : ∀ {Γ A ρ d} → defined d → NE Γ ρ → NE (A ∷ Γ) (d • ρ)
ext-ne p V Z = p
ext-ne p V (S x) = V x

Fs : ℕ → 𝓤₁ ̇
Fs n = Fin n → ⟨ 𝔻 ⟩

{- the kept free variables: equal; the dropped ones: defined -}
Th : ∀ {Δ : Ctx} (fl : Flags Δ) → Fs (length Δ) → Fs (length (kept fl)) → 𝓤₁ ̇
Th [] ds es = 𝟙
Th (true ∷ fl) ds es = (ds zero ＝ es zero) × Th fl (λ i → ds (suc i)) (λ i → es (suc i))
Th (false ∷ fl) ds es = defined (ds zero) × Th fl (λ i → ds (suc i)) es

th-ne→ : ∀ {Δ : Ctx} (fl : Flags Δ) {ds es} → Th fl ds es → All-defined _ ds → All-defined (length (kept fl)) es
th-ne→ (true ∷ fl) (e , th) ne zero = transport defined e (ne zero)
th-ne→ (true ∷ fl) (e , th) ne (suc j) = th-ne→ fl th (λ i → ne (suc i)) j
th-ne→ (false ∷ fl) (_ , th) ne j = th-ne→ fl th (λ i → ne (suc i)) j

th-ne← : ∀ {Δ : Ctx} (fl : Flags Δ) {ds es} → Th fl ds es → All-defined (length (kept fl)) es → All-defined _ ds
th-ne← (true ∷ fl) (e , th) ne zero = transport defined (e ⁻¹) (ne zero)
th-ne← (true ∷ fl) (e , th) ne (suc i) = th-ne← fl th (λ j → ne (suc j)) i
th-ne← (false ∷ fl) (p , th) ne zero = p
th-ne← (false ∷ fl) (p , th) ne (suc i) = th-ne← fl th ne i

{- a kept free variable is the same in the two -}
th-pos : ∀ {Δ : Ctx} {C} (fl : Flags Δ) {ds es} → Th fl ds es → (i : Δ ∋ C) (k : T (lookup fl i)) → ds (pos i) ＝ es (pos (sq fl i k))
th-pos (true ∷ fl) (e , th) Z k = e
th-pos (true ∷ fl) (e , th) (S i) k = th-pos fl th i k
th-pos (false ∷ fl) (_ , th) (S i) k = th-pos fl th i k

{- free variable i in the environment of a closure's code -}
fv-pos : ∀ {Δ : Ctx} {C} (ds : Fs (length Δ)) (Y : ⟨ 𝔻 ⟩) (i : Δ ∋ C) → fv-env (length Δ) ds Y (succ (idx i)) ＝ ds (pos i)
fv-pos ds Y Z = refl
fv-pos ds Y (S i) = fv-pos (λ j → ds (suc j)) (ds zero) i

fv-ne : ∀ {Δ : Ctx} {A} (ds : Fs (length Δ)) {Y} → defined Y → All-defined _ ds → NE (A ∷ Δ) (fv-env (length Δ) ds Y)
fv-ne ds p ne Z = p
fv-ne ds {Y} p ne (S i) = transport defined (fv-pos ds Y i ⁻¹) (ne (pos i))

opt-ok : ∀ {Γ Γ' A} (M : Tm Γ A) {r : Ren (uses M) Γ'} {ρ ρ'} → NE Γ ρ → Agree (uses M) r ρ ρ' → ⟦ M ⟧ · ρ ＝ ⟦ opt M r ⟧ · ρ'
opts-ok : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ ρ'} → NE Γ ρ → Agree (usesA Ms) r ρ ρ'
  → ⟦ Ms ⟧s · ρ ＝ ⟦ opts Ms r ⟧s · ρ'

{- a body under a binder, for the variables its binder's term uses -}
under : ∀ {Γ Γ' A B} (N : Tm (B ∷ Γ) A) {r : Ren (λ x → uses N (S x)) Γ'} {ρ ρ'} → NE Γ ρ → Agree (λ x → uses N (S x)) r ρ ρ'
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ) ＝ ⟦ opt N (ext-ren {u = uses N} r) ⟧ · (d • ρ')
under N V ag d p = opt-ok N (ext-ne p V) λ { Z _ → refl ; (S x) t → ag x t }

{- the free variables and the kept ones (a non-recursive step) -}
th-cons : ∀ {Γ Γ' Δ C} (M : Tm Γ C) (Ms : All (Tm Γ) Δ) (b : Bool) → Fl b M → (fl : Flags Δ)
  {r₁ : Ren (uses M) Γ'} {r₂ : Ren (usesA Ms) Γ'} {ρ ρ' : ⟨ Env ⟩} → NE Γ ρ
  → ⟦ M ⟧ · ρ ＝ ⟦ opt M r₁ ⟧ · ρ' → Th fl (⟦ Ms ⟧s · ρ) (⟦ select fl (opts Ms r₂) ⟧s · ρ')
  → Th (b ∷ fl) (⟦ M ∷ Ms ⟧s · ρ) (⟦ select (b ∷ fl) (opt M r₁ ∷ opts Ms r₂) ⟧s · ρ')
th-cons M Ms true kept-fv fl V e th = e , th
th-cons (` x) Ms false var-fv fl V e th = V x , th

th-ok : ∀ {Γ Γ' Δ} (u : ∀ {C} → Δ ∋ C → Bool) (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {ρ ρ'}
  → NE Γ ρ → Agree (usesA Ms) r ρ ρ' → Th (flags u Ms) (⟦ Ms ⟧s · ρ) (⟦ select (flags u Ms) (opts Ms r) ⟧s · ρ')
th-ok u [] V ag = ⋆
th-ok u (M ∷ Ms) V ag =
  th-cons M Ms (keep? M (u Z)) (fl-ok M (u Z)) (flags (λ x → u (S x)) Ms) V
    (opt-ok M V (λ x t → ag x (∨-l _ t))) (th-ok (λ x → u (S x)) Ms V (λ x t → ag x (∨-r (uses M x) t)))

opt-ok (` x) V ag = ag x (fromWitness Eq.refl)
opt-ok (clos {Δ} N Ms) {ρ = ρ} {ρ'} V ag =
  guard-iff n m xs ys _ _ (th-ne→ fl th) (th-ne← fl th) λ ne →
    Λ-cong (closure-fun n ⟦ N ⟧ xs) (closure-fun m ⟦ opt N rN ⟧ ys) λ W w →
      opt-ok N (fv-ne xs w ne) λ { Z _ → refl
                                 ; (S i) t → fv-pos xs W i ∙ th-pos fl th i _ ∙ fv-pos ys W (sq fl i _) ⁻¹ }
  where
  fl = keeps N Ms
  n = length Δ
  m = length (kept fl)
  rN = λ {C} (x : _ ∋ C) u → squeeze fl x (covers N Ms x u)
  xs = ⟦ Ms ⟧s · ρ
  ys = ⟦ select fl (opts Ms _) ⟧s · ρ'
  th = th-ok (λ x → uses N (S x)) Ms V ag
opt-ok (app L M) V ag =
  ap₂ (λ a b → appᵈ · a · b) (opt-ok L V (λ x t → ag x (∨-l _ t))) (opt-ok M V (λ x t → ag x (∨-r (uses L x) t)))
opt-ok (lit B c) V ag = refl
opt-ok (tuple {Δ} Ms) V ag = ap (tupleᵈ (length Δ) ·_) (opts-ok Ms V ag)
opt-ok (get i M) V ag = ap (proj (pos i) ·_) (opt-ok M V ag)
opt-ok (inl M) V ag = ap (inlᵈ ·_) (opt-ok M V ag)
opt-ok (inr M) V ag = ap (inrᵈ ·_) (opt-ok M V ag)
opt-ok (case L M N) {ρ = ρ} {ρ'} V ag =
  caseᶜ-cong ⟦ L ⟧ ⟦ opt L _ ⟧ ⟦ M ⟧ ⟦ opt M _ ⟧ ⟦ N ⟧ ⟦ opt N _ ⟧ ρ ρ'
    (opt-ok L V (λ x t → ag x (∨-l _ t)))
    (under M V λ x t → ag x (∨-r (uses L x) (∨-l (uses N (S x)) t)))
    (under N V λ x t → ag x (∨-r (uses L x) (∨-r (uses M (S x)) t)))
opt-ok (prim p L M) V ag =
  ap₂ (λ a b → primD p · a · b) (opt-ok L V (λ x t → ag x (∨-l _ t))) (opt-ok M V (λ x t → ag x (∨-r (uses L x) t)))
opt-ok (let′ M N) {ρ = ρ} {ρ'} V ag =
  letᶜ-cong ⟦ M ⟧ ⟦ opt M _ ⟧ ⟦ N ⟧ ⟦ opt N _ ⟧ ρ ρ' (opt-ok M V (λ x t → ag x (∨-l _ t))) (under N V λ x t → ag x (∨-r (uses M x) t))
opt-ok (fold M) V ag = opt-ok M V ag
opt-ok (unfold M) V ag = opt-ok M V ag

opts-ok [] V ag = refl
opts-ok (M ∷ Ms) V ag =
  dfunext fe λ { zero → opt-ok M V (λ x t → ag x (∨-l _ t)) ; (suc i) → happly (opts-ok Ms V (λ x t → ag x (∨-r (uses M x) t))) i }

optimize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ optimize-program M ⟧ · ρ₀
optimize-correct M = opt-ok M (λ ()) (λ ())
