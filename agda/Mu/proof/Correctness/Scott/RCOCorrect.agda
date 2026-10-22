{-

  Correctness of remove complex operands (Clos5μ → Monμ) in Scott
  domains (Mu/Semantics/Scott/Clos5.agda; Monμ means its embedding ⌜_⌝
  into Clos5μ), as in the graph model
  (Mu/proof/Correctness/Graph/RCOCorrect.agda): the embedding of the
  output means what the input means,

    rco-sem : ⟦ N ⟧[ T ] γ ＝ ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] σ

  for environments that agree through the renaming ρ (Ag) and tables
  that agree. Every operator rco names the operands of is strict in
  them: it is defined only when the operand is (Str). So binding an
  operand first by a let changes nothing: the let is seq of the operand
  (letᶜ-β), and seq d e is e when e defined implies d defined
  (seq-absorb). The continuation of atomize means the operator on the
  atom under any extension of the frame (atomize-sem, atomizes-sem,
  atomize₂-sem). Unlike the graph model, no environment need be
  defined or consistent.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Framework.Primitives using (Nat; Int; 𝔹; Unit; Void; Blame)
open import Mu.Language.Type using (_∋_; Z; S; idx; _⇒_)
open import Mu.Language.Clos5
import Mu.Language.Mon as M
open M using (Atm; Exp; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.RCO
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)
open import Framework.abt.GSubst using (_•_)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)

module Mu.proof.Correctness.Scott.RCOCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Sum pt fe using (copair)
open import proof.Framework.Scott.Ops pt fe pe
  renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; case to caseᵈ; ext to extᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; prim-br₁; prim-br₂)
open import proof.Framework.Scott.Values pt fe pe using (app-arg-⊥)
open import Mu.Semantics.Scott.Ops pt fe pe
open import Mu.Semantics.Scott.Clos5 pt fe pe
open import Mu.proof.Semantics.Scott.BackEndLemmas pt fe pe using (below-if; codeᶜ-cong; tables-cons)

{- seq d e is e when e defined implies d defined ------------------------------------}

seq-absorb : (d e : ⟨ 𝔻 ⟩) → (defined e → defined d) → seq · d · e ＝ e
seq-absorb d e h = antisymmetry 𝔻 (seq · d · e) e
  (∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → e) (defined-is-prop d) e (λ _ → reflexivity 𝔻 e))
  (below-if e (seq · d · e) (λ p → seq-defined d e (h p) ⁻¹))

{- a strict continuous map is defined only on defined values -}
strict-reflects : (κ : DCPO[ 𝔻 , 𝔻 ]) → κ · ⊥𝔻 ＝ ⊥𝔻 → (d : ⟨ 𝔻 ⟩) → defined (κ · d) → defined d
strict-reflects κ s d p =
  seq-defined-l d (κ · d) (transport defined (ap (κ ·_) (seq-absorb d d id ⁻¹) ∙ seq-strict κ s d d) p)

{- the operators that rco names the operands of are strict -------------------------}

Str : (⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩) → 𝓤₁ ̇
Str F = (v : ⟨ 𝔻 ⟩) → defined (F v) → defined v

opaque
 unfolding caseᵈ

 case-natural : (E E' : DCPO⊥ {𝓤₁} {𝓤₁}) (h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , E ⁻ ]) (k : DCPO[ E ⁻ , E' ⁻ ])
   → k · ⊥ E ＝ ⊥ E' → (d : ⟨ 𝔻 ⟩)
   → k · (caseᵈ E h · d) ＝ caseᵈ E' (λ t → ∘₁ (obj (Payload t) 𝔻) (E ⁻) (E' ⁻) (h t) k) · d
 case-natural E E' h k s d =
  ∐ˢˢ-＝-if-continuous-and-strict E E' (pr₁ k) (pr₂ k) s
    (λ p → copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h · value (unroll · d) p)
    (being-defined-is-prop (unroll · d))

 {- primD p n is strict: each of its branches is -}
 prim-⊥ : (p : _) (n : ⟨ 𝔻 ⟩) → primD p · n · ⊥𝔻 ＝ ⊥𝔻
 prim-⊥ p n =
   case-natural (𝔻 ⟹𝔻) 𝔻⊥ (prim-br₁ p) (at-point₁ 𝔻 𝔻 ⊥𝔻) refl n
   ∙ antisymmetry 𝔻 (caseᵈ 𝔻⊥ h · n) ⊥𝔻
       (∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ q → copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) 𝔻 h · value (unroll · n) q)
         (being-defined-is-prop (unroll · n)) ⊥𝔻
         (λ q → transport (λ - → - ⊑⟨ 𝔻 ⟩ ⊥𝔻) (br (pr₁ (value (unroll · n) q)) (pr₂ (value (unroll · n) q)) ⁻¹) (reflexivity 𝔻 ⊥𝔻)))
       (⊥-is-least 𝔻⊥ (caseᵈ 𝔻⊥ h · n))
  where
   h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]
   h t = ∘₁ (obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) 𝔻 (prim-br₁ p t) (at-point₁ 𝔻 𝔻 ⊥𝔻)
   br : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → h t · x ＝ ⊥𝔻
   br (con Int m) x = case-⊥ 𝔻⊥ (prim-br₂ p m)
   br (con Nat m) x = refl
   br (con 𝔹 m) x = refl
   br (con Unit m) x = refl
   br (con Void m) x = refl
   br (con Blame m) x = refl
   br (tup m) x = refl
   br left x = refl
   br right x = refl
   br fun x = refl
   br pr x = refl

{- callc applies the code of the closure a to its environment and to b -}
CALL : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
CALL a b = appᵈ · (appᵈ · (car · a) · (cdr · a)) · b

callc-str₁ : (b : ⟨ 𝔻 ⟩) → Str (λ a → CALL a b)
callc-str₁ b a p = strict-reflects car (case-⊥ 𝔻⊥ (component-br zero)) a
  (strict-reflects (app-at (cdr · a)) (app-⊥ (cdr · a)) (car · a)
    (strict-reflects (app-at b) (app-⊥ b) (appᵈ · (car · a) · (cdr · a)) p))

prim-str₁ : (p : _) (m : ⟨ 𝔻 ⟩) → Str (λ n → primD p · n · m)
prim-str₁ p m = strict-reflects (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (primD p) (at-point₁ 𝔻 𝔻 m)) (ap (_· m) (case-⊥ (𝔻 ⟹𝔻) (prim-br₁ p)))

cases-str : (br : ⟨ Br ⟩) → Str (λ v → cases · v · br)
cases-str br = strict-reflects (∘₁ 𝔻 (Br ⟹₁ 𝔻) 𝔻 cases (at-point₁ Br 𝔻 br)) (ap (_· br) (case-⊥ (Br ⟹𝔻) cases-br))

{- Terms ---------------------------------------------------------------------------}

module _ {Σ} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  {- the frames agree through the renaming ρ -}
  record Ag {Γ Δ} (ρ : Ren Γ Δ) (γ σ : ⟨ Env ⟩) : 𝓤₁ ̇ where
    constructor mk-ag
    field agr : ∀ {A} (x : Γ ∋ A) → γ (idx x) ＝ σ (idx (ρ x))
  open Ag

  _⨾_ : ∀ {Γ Δ Δ'} {ρ : Ren Γ Δ} {r : Ren Δ Δ'} {γ σ σ'} → Ag ρ γ σ → Ag r σ σ' → Ag (λ x → r (ρ x)) γ σ'
  _⨾_ {ρ = ρ} ag ag' = mk-ag λ x → agr ag x ∙ agr ag' (ρ x)

  ext-ag : ∀ {Γ Δ B} {ρ : Ren Γ Δ} {γ σ} {d : ⟨ 𝔻 ⟩} → Ag ρ γ σ → Ag (ext {B = B} ρ) (d • γ) (d • σ)
  ext-ag ag = mk-ag λ { Z → refl ; (S x) → agr ag x }

  id-ag : ∀ {Δ σ} → Ag {Δ} (λ y → y) σ σ
  id-ag = mk-ag λ y → refl

  ren-atm : ∀ {Δ Δ' A} {r : Ren Δ Δ'} (a : Atm Σ Δ A) {σ σ' : ⟨ Env ⟩} → Ag r σ σ'
    → ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ ＝ ⟦ ⌜ ren r a ⌝ᵃ ⟧[ T' ] · σ'
  ren-atm (var x) ag = agr ag x
  ren-atm (lit B c) ag = refl
  ren-atm (ref f) ag = refl

  {- the continuation of atomize means F of its atom -}
  KOK : ∀ {Δ A B} → K Σ Δ A B → ⟨ Env ⟩ → (⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩) → 𝓤₁ ̇
  KOK {Δ} k σ F = ∀ {Δ'} {r : Ren Δ Δ'} {σ'} a → Ag r σ σ' → F (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ') ＝ ⟦ ⌜ k r a ⌝ ⟧[ T' ] · σ'

  rco-sem : ∀ {Γ Δ A} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} {γ σ} → Ag ρ γ σ → ⟦ N ⟧[ T ] · γ ＝ ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] · σ

  atomize-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} (k : K Σ Δ A B) {γ σ} → Ag ρ γ σ
    → (F : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩) → Str F → KOK k σ F → F (⟦ N ⟧[ T ] · γ) ＝ ⟦ ⌜ atomize N ρ k ⌝ ⟧[ T' ] · σ
  {- a complex operand, bound by a let -}
  let-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} (k : K Σ Δ A B) {γ σ} → Ag ρ γ σ
    → (F : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩) → Str F → KOK k σ F → F (⟦ N ⟧[ T ] · γ) ＝ ⟦ ⌜ M.let′ (rco N ρ) (k S (var Z)) ⌝ ⟧[ T' ] · σ
  atomize-sem (` x) {ρ} k ag F sF ks = ap F (agr ag x) ∙ ks (var (ρ x)) id-ag
  atomize-sem (fun-ref f) k ag F sF ks = ap F (TT f) ∙ ks (ref f) id-ag
  atomize-sem (lit B c) k ag F sF ks = ks (lit B c) id-ag
  atomize-sem N@(pack _ _) = let-sem N
  atomize-sem N@(callc _ _) = let-sem N
  atomize-sem N@(tuple _) = let-sem N
  atomize-sem N@(get _ _) = let-sem N
  atomize-sem N@(inl _) = let-sem N
  atomize-sem N@(inr _) = let-sem N
  atomize-sem N@(case _ _ _) = let-sem N
  atomize-sem N@(prim _ _ _) = let-sem N
  atomize-sem N@(let′ _ _) = let-sem N
  atomize-sem N@(fold _) = let-sem N
  atomize-sem N@(unfold _) = let-sem N
  let-sem N {ρ} k {σ = σ} ag F sF ks =
    ap F (rco-sem N ag)
    ∙ seq-absorb v (F v) (sF v) ⁻¹
    ∙ seq-cong v (F v) (⟦ ⌜ k S (var Z) ⌝ ⟧[ T' ] · (v • σ)) (λ _ → ks (var Z) (mk-ag λ y → refl))
    ∙ letᶜ-β ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] ⟦ ⌜ k S (var Z) ⌝ ⟧[ T' ] σ ⁻¹
   where v = ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] · σ

  atomizes-sem : ∀ {Γ Δ Δs B} (Ns : All (Tm Σ Γ) Δs) {ρ : Ren Γ Δ}
    (k : ∀ {Δ'} → Ren Δ Δ' → All (Atm Σ Δ') Δs → Exp Σ Δ' B) {γ σ} → Ag ρ γ σ
    → (G : (Fin (length Δs) → ⟨ 𝔻 ⟩) → ⟨ 𝔻 ⟩) → ((ds : Fin (length Δs) → ⟨ 𝔻 ⟩) (i : Fin (length Δs)) → defined (G ds) → defined (ds i))
    → (∀ {Δ'} {r : Ren Δ Δ'} {σ'} as → Ag r σ σ' → G (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] · σ') ＝ ⟦ ⌜ k r as ⌝ ⟧[ T' ] · σ')
    → G (⟦ Ns ⟧s[ T ] · γ) ＝ ⟦ ⌜ atomizes Ns ρ k ⌝ ⟧[ T' ] · σ
  atomizes-sem [] k ag G sG ks = ks [] id-ag
  atomizes-sem (N ∷ Ns) k {γ} ag G sG ks =
    atomize-sem N _ ag (λ v → G (v ∷ᶠ (⟦ Ns ⟧s[ T ] · γ))) (λ v → sG (v ∷ᶠ (⟦ Ns ⟧s[ T ] · γ)) zero) λ {_} {r} {σ'} a ag₁ →
      atomizes-sem Ns _ (ag ⨾ ag₁) (λ ds → G ((⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ') ∷ᶠ ds)) (λ ds i → sG ((⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ') ∷ᶠ ds) (suc i))
        λ {_} {r'} {σ''} as ag₂ → ap (λ u → G (u ∷ᶠ (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] · σ''))) (ren-atm a ag₂) ∙ ks (ren r' a ∷ as) (ag₁ ⨾ ag₂)

  atomize₂-sem : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) {ρ : Ren Γ Δ}
    (k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Exp Σ Δ' B) {γ σ} → Ag ρ γ σ
    → (F : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩) → ((b : ⟨ 𝔻 ⟩) → Str (λ a → F a b)) → ((a : ⟨ 𝔻 ⟩) → Str (F a))
    → (∀ {Δ'} (σ' : ⟨ Env ⟩) (a : Atm Σ Δ' A₁) b → F (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ') (⟦ ⌜ b ⌝ᵃ ⟧[ T' ] · σ') ＝ ⟦ ⌜ k a b ⌝ ⟧[ T' ] · σ')
    → F (⟦ L ⟧[ T ] · γ) (⟦ N ⟧[ T ] · γ) ＝ ⟦ ⌜ atomize₂ L N ρ k ⌝ ⟧[ T' ] · σ
  atomize₂-sem L N k {γ} ag F s₁ s₂ ks =
    atomize-sem L _ ag (λ a → F a (⟦ N ⟧[ T ] · γ)) (s₁ (⟦ N ⟧[ T ] · γ)) λ {_} {r} {σ'} a ag₁ →
      atomize-sem N _ (ag ⨾ ag₁) (F (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ')) (s₂ (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ')) λ {_} {r'} {σ''} b ag₂ →
        ap (λ u → F u (⟦ ⌜ b ⌝ᵃ ⟧[ T' ] · σ'')) (ren-atm a ag₂) ∙ ks σ'' (ren r' a) b

  rco-sem (` x) ag = agr ag x
  rco-sem (fun-ref f) ag = TT f
  rco-sem (pack L N) ag =
    atomize₂-sem L N M.pack ag (λ a b → pair · a · b) (λ b a p → pr₁ (pair-defined← a b p)) (λ a b p → pr₂ (pair-defined← a b p))
      λ _ _ _ → refl
  rco-sem (callc L N) ag =
    atomize₂-sem L N M.callc ag CALL callc-str₁
      (λ a → strict-reflects (appᵈ · (appᵈ · (car · a) · (cdr · a))) (app-arg-⊥ (appᵈ · (car · a) · (cdr · a)))) λ _ _ _ → refl
  rco-sem (lit B c) ag = refl
  rco-sem (tuple {Δ} Ns) ag =
    atomizes-sem Ns _ ag (tupleᵈ (length Δ) ·_) (λ ds i p → tuple-defined← (length Δ) ds p i) λ _ _ → refl
  rco-sem (get i N) ag =
    atomize-sem N _ ag (proj (pos i) ·_) (strict-reflects (proj (pos i)) (case-⊥ 𝔻⊥ (proj-br (pos i)))) λ _ _ → refl
  rco-sem (inl N) ag = atomize-sem N _ ag (inlᵈ ·_) (λ v → seq-defined-l v (inj left · v)) λ _ _ → refl
  rco-sem (inr N) ag = atomize-sem N _ ag (inrᵈ ·_) (λ v → seq-defined-l v (inj right · v)) λ _ _ → refl
  rco-sem (case L N₁ N₂) {ρ} {γ} ag =
    atomize-sem L _ ag (λ v → cases · v · br) (cases-str br) λ {_} {r} {σ'} a ag₁ →
      ap (λ b → cases · (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] · σ') · b)
        (ap₂ _,_ (strict-cong (abs ⟦ N₁ ⟧[ T ] · γ) (abs ⟦ ⌜ rco N₁ (ext λ x → r (ρ x)) ⌝ ⟧[ T' ] · σ')
                   (λ d _ → rco-sem N₁ (ext-ag (ag ⨾ ag₁))))
                 (strict-cong (abs ⟦ N₂ ⟧[ T ] · γ) (abs ⟦ ⌜ rco N₂ (ext λ x → r (ρ x)) ⌝ ⟧[ T' ] · σ')
                   (λ d _ → rco-sem N₂ (ext-ag (ag ⨾ ag₁)))))
   where br = strict · (abs ⟦ N₁ ⟧[ T ] · γ) , strict · (abs ⟦ N₂ ⟧[ T ] · γ)
  rco-sem (prim p L N) ag =
    atomize₂-sem L N (M.prim p) ag (λ a b → primD p · a · b) (prim-str₁ p) (λ a → strict-reflects (primD p · a) (prim-⊥ p a))
      λ _ _ _ → refl
  rco-sem (let′ N₁ N₂) {ρ} {γ} {σ} ag =
    letᶜ-cong ⟦ N₁ ⟧[ T ] ⟦ ⌜ rco N₁ ρ ⌝ ⟧[ T' ] ⟦ N₂ ⟧[ T ] ⟦ ⌜ rco N₂ (ext ρ) ⌝ ⟧[ T' ] γ σ
      (rco-sem N₁ ag) (λ d _ → rco-sem N₂ (ext-ag ag))
  rco-sem (fold N) ag = atomize-sem N _ ag (λ v → v) (λ v p → p) λ _ _ → refl
  rco-sem (unfold N) ag = atomize-sem N _ ag (λ v → v) (λ v p → p) λ _ _ → refl

  {- the code of a definition means the code of its output -}
  code-rco : ∀ {s} (d : Code Σ s) → code′ T d ＝ code′ T' ⌜ rco d (λ x → x) ⌝
  code-rco d = codeᶜ-cong ⟦ d ⟧[ T ] ⟦ ⌜ rco d (λ x → x) ⌝ ⟧[ T' ] (λ X Y _ _ → rco-sem d id-ag)

{- Programs ---------------------------------------------------------------------------}

rco-defs : ∀ {Σ ss} → All (Code Σ) ss → All (Code Σ) ss
rco-defs ds = All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)

{- the table of the output means what the table of the input does -}
table-rco : ∀ {Σ ss} (ds : All (Code Σ) ss) {s} (f : Σ ∋ s) → tables code′ ds f ＝ tables code′ (rco-defs ds) f
table-rco [] f = refl
table-rco (d ∷ ds) f = tables-cons code′ code′ d ds ⌜ rco d (λ x → x) ⌝ (rco-defs ds) f (code-rco (table-rco ds) d) (table-rco ds f)

rco-correct : ∀ {A} (P : Program A) → ⟦ P ⟧ₚ ＝ ⟦ ⌜ rco-program P ⌝ₚ ⟧ₚ
rco-correct (program ds N) = rco-sem (table-rco ds) N (id-ag (table-rco ds))
