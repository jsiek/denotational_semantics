{-

  Adequacy of the graph model for the X86 machine: every element of the
  denotation of a well-formed program is witnessed by a run of the
  machine of its global definitions ds.

  As for Clos5 (Untyped/proof/Adequacy/Clos5LogRel.agda), a logical relation 𝕍 d v
  (Values.agda) relates denotational values to machine values, and the
  code of a definition, Λ X. Λ Y. …, is related to code k when the
  machine runs definition k on values related to X and Y, on any stack,
  to a return of a value related to the result (Run, Ret). The
  fundamental lemma (adequate) is by induction on the instructions of a
  block, given that the blocks it may jump to are adequate (AdeqB, by
  induction on the blocks); a location is related to what the machine
  holds there (𝕄), the flag to the machine's flag (Fl). A call returns
  the same value for every element of its denotation, since runs are
  deterministic (Ret-det).

  Each slot read is within the frame (WF): a slot beyond it reads as
  init = {ω}, which nothing in the machine is related to.

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse)
open import Language.X86 using (Body)

module proof.Adequacy.X86LogRel (ds : List Body) where

open import Framework.Primitives using (Int)
open import Language.Prim using (δ; sub; eq)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (⋆; ℬ; nthD; inl; inr; Λ) renaming (pair to dpair)
open import proof.Semantics.Graph.Prim using (primD) renaming (out to dout)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
  hiding (Body)
open import Semantics.Graph.X86
  renaming (Regs to SRegs; code to codeD; run to runD; put to putD; call to callD; args to argsD;
            read to readD; zeros to zerosD; _[_↦_] to _[_↦ₛ_]; flag to flagD)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (next)
open import proof.Framework.ListUtil using (_‼_)
open import Semantics.CEK.X86
  using (Val; code; pair; const; tup; out; prim?; Frame; State; Stack; halt; retK; run; step; block-at; global; get-field; build; is-inl; cmp; bit; zeros; arg; args; halt?; regs; upd; goto; callq?; back; test)
  renaming (read to readM; put to putM; call to callM; Regs to MRegs; _[_↦_] to _[_↦ₘ_])
import Semantics.CEK.X86 as T using (inl; inr)
open import proof.Adequacy.Values using (module Rel)
open import proof.Adequacy.X86WF
open import proof.Adequacy.X86Common ds
open import proof.Adequacy.X86Soundness using (_≟R_; ↦ₘ-here; ↦ₘ-other; ≔-here; ≔-other)

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (0ℤ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _∸_; _+_)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

{- Runs to a return ---------------------------------------------------------------}

{- from S stk, the machine returns v to stk -}
Ret : (Stack → State) → Val → Set
Ret S v = ∀ stk → Σ[ bs ∈ List Block ] Σ[ f ∈ Maybe Bool ] Σ[ φ ∈ Frame ] Σ[ ρ ∈ MRegs ]
  (S stk ↠ run [] retq bs stk f φ ρ) × ρ rax ≡ just v

Ret-det : ∀ {S v₁ v₂} → Ret S v₁ → Ret S v₂ → v₁ ≡ v₂
Ret-det r₁ r₂ with r₁ halt | r₂ halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ₁ , e₁ ⟩ ⟩ ⟩ ⟩ ⟩ | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ₂ , e₂ ⟩ ⟩ ⟩ ⟩ ⟩
    with ↠-final-det τ₁ τ₂ (cong halt? e₁) (cong halt? e₂)
... | refl with trans (sym e₁) e₂
... | refl = refl

Ret-step : ∀ {S S' v} → (∀ stk → step ds (S stk) ≡ next (S' stk)) → Ret S' v → Ret S v
Ret-step st r stk with r stk
... | ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ bs , ⟨ f , ⟨ φ , ⟨ ρ , ⟨ st stk ∷↠ τ , e ⟩ ⟩ ⟩ ⟩ ⟩

R : List Instr → Jump → List Block → Maybe Bool → Frame → MRegs → Val → Set
R is j bs f φ ρ = Ret (λ stk → run is j bs stk f φ ρ)

{- The logical relation (Values.agda): code k runs definition k -------------------}

Run : ℕ → Val → Val → (Val → Set) → Set
Run k e a P = Σ[ n ∈ ℕ ] Σ[ bs ∈ List Block ] Σ[ b ∈ Block ] global ds k ≡ just (body n bs b)
  × Σ[ v ∈ Val ] R (Block.instrs b) (Block.jump b) bs nothing (zeros (2 + (n ∸ 2))) (regs nothing (just e) (just a)) v × P v

open Rel Run public

{- a location holds a value related to every element of D -}
𝕄 : 𝒫 Value → Maybe Val → Set
𝕄 D m = ∀ d → d ∈ D → Σ[ v ∈ Val ] m ≡ just v × 𝕍 d v

Fl : 𝒫 Value → Maybe Bool → Set
Fl F f = ∀ d → d ∈ F → Σ[ b ∈ Bool ] f ≡ just b × 𝕍 d (bit b)

{- the frame, on its slots, and the registers -}
𝔽 : Store → Frame → Set
𝔽 σ φ = ∀ x → x < length φ → 𝕄 (σ x) (φ ‼ x)

ℝ : SRegs → MRegs → Set
ℝ ρs ρm = ∀ g → 𝕄 (ρs g) (ρm g)

{- every entry of the table is related to the code pointer -}
𝕋 : Table → Set
𝕋 T = ∀ k d → d ∈ T k → 𝕍 d (code k)

{- Operations ----------------------------------------------------------------------}

ℬ-𝕄 : ∀ B k → 𝕄 (ℬ B k ptt) (just (const B k))
ℬ-𝕄 B k (dconst k') ⟨ refl , refl ⟩ = ⟨ const B k , ⟨ refl , refl ⟩ ⟩

prim-𝕄 : ∀ p {Dd Da md ma} → 𝕄 Dd md → 𝕄 Da ma
  → 𝕄 (primD p ⟨ Dd , ⟨ Da , ptt ⟩ ⟩) (ma >>= λ w → md >>= λ u → prim? p u w)
prim-𝕄 p hd ha x ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ with hd (dconst n) n∈ | ha (dconst m) m∈
... | ⟨ _ , ⟨ refl , refl ⟩ ⟩ | ⟨ _ , ⟨ refl , refl ⟩ ⟩ = ⟨ out (δ p n m) , ⟨ refl , 𝕍-out (δ p n m) ⟩ ⟩

cmp-Fl : ∀ {D₁ D₂ m₁ m₂} → 𝕄 D₁ m₁ → 𝕄 D₂ m₂ → nonempty (primD eq ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩)
  → Σ[ b ∈ Bool ] (m₁ >>= λ v → m₂ >>= λ w → cmp v w) ≡ just b × Fl (primD eq ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩) (just b)
cmp-Fl {D₁} {D₂} h₁ h₂ ⟨ _ , ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ ⟩ with h₁ (dconst n) n∈ | h₂ (dconst m) m∈
... | ⟨ _ , ⟨ refl , refl ⟩ ⟩ | ⟨ _ , ⟨ refl , refl ⟩ ⟩ = ⟨ _ , ⟨ refl , F ⟩ ⟩
  where
  F : Fl (primD eq ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩) (cmp (const Int n) (const Int m))
  F y ⟨ n' , ⟨ m' , ⟨ n'∈ , ⟨ m'∈ , refl ⟩ ⟩ ⟩ ⟩ with h₁ (dconst n') n'∈ | h₂ (dconst m') m'∈
  ... | ⟨ _ , ⟨ e₁ , r₁ ⟩ ⟩ | ⟨ _ , ⟨ e₂ , r₂ ⟩ ⟩ with e₁ | e₂
  ... | refl | refl with r₁ | r₂
  ... | refl | refl = ⟨ _ , ⟨ refl , 𝕍-out (δ eq n m) ⟩ ⟩

isinl-Fl : ∀ {D m} → 𝕄 D m → nonempty (isinl D) → Σ[ b ∈ Bool ] (m >>= is-inl) ≡ just b × Fl (isinl D) (just b)
isinl-Fl {D} h ⟨ _ , inj₁ ⟨ u , ⟨ u∈ , _ ⟩ ⟩ ⟩ with h (left u) u∈
... | ⟨ T.inl v , ⟨ refl , _ ⟩ ⟩ = ⟨ true , ⟨ refl , F ⟩ ⟩
  where
  F : Fl (isinl D) (just true)
  F _ (inj₁ ⟨ u' , ⟨ _ , refl ⟩ ⟩) = ⟨ true , ⟨ refl , refl ⟩ ⟩
  F _ (inj₂ ⟨ u' , ⟨ u'∈ , refl ⟩ ⟩) with h (right u') u'∈
  ... | ⟨ _ , ⟨ refl , () ⟩ ⟩
isinl-Fl {D} h ⟨ _ , inj₂ ⟨ u , ⟨ u∈ , _ ⟩ ⟩ ⟩ with h (right u) u∈
... | ⟨ T.inr v , ⟨ refl , _ ⟩ ⟩ = ⟨ false , ⟨ refl , F ⟩ ⟩
  where
  F : Fl (isinl D) (just false)
  F _ (inj₂ ⟨ u' , ⟨ _ , refl ⟩ ⟩) = ⟨ false , ⟨ refl , refl ⟩ ⟩
  F _ (inj₁ ⟨ u' , ⟨ u'∈ , refl ⟩ ⟩) with h (left u') u'∈
  ... | ⟨ _ , ⟨ refl , () ⟩ ⟩

field-𝕄 : ∀ f {D m} → 𝕄 D m → 𝕄 (field′ f D) (m >>= get-field f)
field-𝕄 fstₛ h x ⟨ y , xy∈ ⟩ with h ⦅ x , y ⦆ xy∈
... | ⟨ pair v w , ⟨ refl , ⟨ r , _ ⟩ ⟩ ⟩ = ⟨ v , ⟨ refl , r ⟩ ⟩
field-𝕄 sndₛ h y ⟨ x , xy∈ ⟩ with h ⦅ x , y ⦆ xy∈
... | ⟨ pair v w , ⟨ refl , ⟨ _ , r ⟩ ⟩ ⟩ = ⟨ w , ⟨ refl , r ⟩ ⟩
field-𝕄 (getₛ i) h x x∈ with h (tup[ i ] x) x∈
... | ⟨ tup vs , ⟨ refl , r ⟩ ⟩ with 𝕍At-proj i x vs r
...   | ⟨ v , ⟨ e , r' ⟩ ⟩ = ⟨ v , ⟨ e , r' ⟩ ⟩
field-𝕄 payload h x (inj₁ x∈) with h (left x) x∈
... | ⟨ T.inl v , ⟨ refl , r ⟩ ⟩ = ⟨ v , ⟨ refl , r ⟩ ⟩
field-𝕄 payload h x (inj₂ x∈) with h (right x) x∈
... | ⟨ T.inr v , ⟨ refl , r ⟩ ⟩ = ⟨ v , ⟨ refl , r ⟩ ⟩

{- Related states ------------------------------------------------------------------}

module _ {T : Table} (𝕋T : 𝕋 T) where

  𝒪-𝕄 : ∀ {L n σ ρs φ ρm} a → OK L (_< n) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → 𝕄 (𝒪 T n σ ρs a) (arg φ ρm a)
  𝒪-𝕄 {n = n} (loc (var x)) x< refl F G with x <? n
  ... | yes _ = F x x<
  ... | no ¬x< = ⊥-elim (¬x< x<)
  𝒪-𝕄 (loc (reg g)) _ _ F G = G g
  𝒪-𝕄 (imm B k) _ _ F G = ℬ-𝕄 B k
  𝒪-𝕄 (label k) _ _ F G d d∈ = ⟨ code k , ⟨ refl , 𝕋T k d d∈ ⟩ ⟩

  {- the operands of alloc -}
  args-run : ∀ {L n σ ρs φ ρm} as acc (k : List Val → Maybe Val) → All (OK L (_< n)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → (∀ j → nonempty (nthD (𝒪s T n σ ρs as) j))
    → Σ[ vs ∈ List Val ] args φ ρm acc as k ≡ k (reverse acc ++ vs) × length vs ≡ length as
       × (∀ j x → x ∈ nthD (𝒪s T n σ ρs as) j → 𝕍At j x vs)
  args-run [] acc k _ _ _ _ _ = ⟨ [] , ⟨ cong k (sym (++-identityʳ (reverse acc))) , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
  args-run {φ = φ} {ρm} (a ∷ as) acc k (o ∷ os) nφ F G ne with ne zero
  ... | ⟨ x₀ , x₀∈ ⟩ with 𝒪-𝕄 a o nφ F G x₀ x₀∈
  ... | ⟨ v , ⟨ ea , _ ⟩ ⟩ with args-run as (v ∷ acc) k os nφ F G (λ j → ne (suc j))
  ... | ⟨ vs , ⟨ e , ⟨ len , rs ⟩ ⟩ ⟩ =
    ⟨ v ∷ vs , ⟨ trans (args-cons ea) (trans e (cong k (trans (cong (_++ vs) (unfold-reverse v acc)) (++-assoc (reverse acc) [ v ] vs))))
              , ⟨ cong suc len , G' ⟩ ⟩ ⟩
    where
    args-cons : ∀ {m} → m ≡ just v → (m >>= λ u → args φ ρm (u ∷ acc) as k) ≡ args φ ρm (v ∷ acc) as k
    args-cons refl = refl
    G' : ∀ j x → x ∈ nthD (𝒪s T _ _ _ (a ∷ as)) j → 𝕍At j x (v ∷ vs)
    G' zero x x∈ with 𝒪-𝕄 a o nφ F G x x∈
    ... | ⟨ _ , ⟨ e' , r ⟩ ⟩ with trans (sym ea) e'
    ... | refl = ⟨ len , r ⟩
    G' (suc j) x x∈ = rs j x x∈

  bind≡ : ∀ {A B : Set} {m : Maybe A} {x} {f : A → Maybe B} → m ≡ just x → (m >>= f) ≡ f x
  bind≡ refl = refl

  object-𝕄 : ∀ {L n σ ρs φ ρm} sh as → All (OK L (_< n)) as → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → 𝕄 (object T n σ ρs sh as) (args φ ρm [] as (build sh))
  object-𝕄 pairₛ (a ∷ b ∷ []) (oa ∷ ob ∷ []) nφ F G ⦅ u , w ⦆ ⟨ u∈ , w∈ ⟩
      with 𝒪-𝕄 a oa nφ F G u u∈ | 𝒪-𝕄 b ob nφ F G w w∈
  ... | ⟨ v₁ , ⟨ e₁ , r₁ ⟩ ⟩ | ⟨ v₂ , ⟨ e₂ , r₂ ⟩ ⟩ = ⟨ pair v₁ v₂ , ⟨ trans (bind≡ e₁) (bind≡ e₂) , ⟨ r₁ , r₂ ⟩ ⟩ ⟩
  object-𝕄 tupleₛ [] [] nφ F G ⟨⟩ tt = ⟨ tup [] , ⟨ refl , refl ⟩ ⟩
  object-𝕄 tupleₛ (a ∷ as) os nφ F G (tup[ i ] x) ⟨ refl , ⟨ x∈ , ne ⟩ ⟩ with args-run (a ∷ as) [] (build tupleₛ) os nφ F G ne
  ... | ⟨ vs , ⟨ e , ⟨ _ , rs ⟩ ⟩ ⟩ = ⟨ tup vs , ⟨ e , rs i x x∈ ⟩ ⟩
  object-𝕄 inlₛ (a ∷ []) (oa ∷ []) nφ F G (left u) u∈ with 𝒪-𝕄 a oa nφ F G u u∈
  ... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ T.inl v , ⟨ bind≡ e , r ⟩ ⟩
  object-𝕄 inrₛ (a ∷ []) (oa ∷ []) nφ F G (right u) u∈ with 𝒪-𝕄 a oa nφ F G u u∈
  ... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ T.inr v , ⟨ bind≡ e , r ⟩ ⟩

  put-ne : ∀ {n} d {D κ σ ρ F w} → w ∈ putD n d D κ σ ρ F → nonempty D
  put-ne {n} (var x) w∈ with x <? n
  put-ne (var x) ⟨ V , ⟨ _ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ | yes _ with E≢[]⇒nonempty-mem neV
  ... | ⟨ d , d∈ ⟩ = ⟨ d , V⊆ d d∈ ⟩
  put-ne (reg g) ⟨ ne , _ ⟩ = ne

  {- d := D, in the semantics and the machine -}
  put-𝕄 : ∀ {n} d {D m κ σ ρs F φ ρm w} → length φ ≡ n → 𝕄 D m → 𝔽 σ φ → ℝ ρs ρm → w ∈ putD n d D κ σ ρs F
    → Σ[ φ' ∈ Frame ] Σ[ ρm' ∈ MRegs ] (∀ K → putM d m φ ρm K ≡ next (K φ' ρm')) × length φ' ≡ n
       × Σ[ σ' ∈ Store ] Σ[ ρs' ∈ SRegs ] 𝔽 σ' φ' × ℝ ρs' ρm' × w ∈ κ σ' ρs' F
  put-𝕄 (var x) {σ = σ} {ρs} {φ = φ} {ρm} refl h F G w∈ with x <? length φ
  put-𝕄 (var x) {σ = σ} {ρs} {φ = φ} {ρm} refl h F G ⟨ V , ⟨ ⟨ w∈ , ⟨ neV , _ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ | yes x<
      with E≢[]⇒nonempty-mem neV
  ... | ⟨ d₀ , d₀∈ ⟩ with h d₀ (V⊆ d₀ d₀∈)
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ with ≔-ok φ x v x<
  ... | ⟨ φ' , e ⟩ =
    ⟨ φ' , ⟨ ρm , ⟨ (λ K → cong (λ mφ → upd mφ ρm K) e) , ⟨ Assigned.len a
    , ⟨ σ [ x ↦ₛ mem V ] , ⟨ ρs , ⟨ F' , ⟨ G , w∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    a = ≔-inv φ x e
    F' : 𝔽 (σ [ x ↦ₛ mem V ]) φ'
    F' y y< with y ≟ x
    ... | yes refl = λ d d∈ → G' d (h d (V⊆ d d∈))
      where
      G' : ∀ d → Σ[ v' ∈ Val ] just v ≡ just v' × 𝕍 d v' → Σ[ v' ∈ Val ] φ' ‼ x ≡ just v' × 𝕍 d v'
      G' d ⟨ _ , ⟨ refl , r ⟩ ⟩ = ⟨ v , ⟨ Assigned.here a , r ⟩ ⟩
    ... | no ne = subst (𝕄 (σ y)) (sym (Assigned.other a y ne)) (F y (subst (y <_) (Assigned.len a) y<))
  put-𝕄 (reg g) {D} {ρs = ρs} {φ = φ} {ρm} nφ h F G ⟨ ⟨ d₀ , d₀∈ ⟩ , w∈ ⟩ with h d₀ d₀∈
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ =
    ⟨ φ , ⟨ ρm [ g ↦ₘ just v ] , ⟨ (λ K → refl) , ⟨ nφ , ⟨ _ , ⟨ ρs [ g ≔ D ] , ⟨ F , ⟨ G' , w∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    G' : ℝ (ρs [ g ≔ D ]) (ρm [ g ↦ₘ just v ])
    G' g' with g' ≟R g
    ... | yes refl rewrite ≔-here ρs g D | ↦ₘ-here ρm g (just v) = h
    ... | no ne rewrite ≔-other ρs g D g' ne | ↦ₘ-other ρm g (just v) g' ne = G g'

  {- the related values of a set that holds some -}
  𝕄→𝕍s : ∀ {D m} → 𝕄 D m → ∀ V → mem V ⊆ D → V ≢ [] → Σ[ v ∈ Val ] m ≡ just v × 𝕍s V v
  𝕄→𝕍s h V V⊆ ne with E≢[]⇒nonempty-mem ne
  ... | ⟨ d₀ , d₀∈ ⟩ with h d₀ (V⊆ d₀ d₀∈)
  ... | ⟨ v , ⟨ refl , _ ⟩ ⟩ = ⟨ v , ⟨ refl , all→𝕍s V (λ d d∈ → G d (h d (V⊆ d d∈))) ⟩ ⟩
    where
    G : ∀ d → Σ[ v' ∈ Val ] just v ≡ just v' × 𝕍 d v' → 𝕍 d v
    G d ⟨ _ , ⟨ refl , r ⟩ ⟩ = r

  {- an element of the result of a call: the callee returns a value related to it -}
  record Calls (φ : Frame) (ρm : MRegs) (a : Arg) (w : Value) : Set where
    constructor calls
    field
      k : ℕ
      e₁ e₂ : Val
      m : ℕ
      bbs : List Block
      bst : Block
      v : Val
      ea : arg φ ρm a ≡ just (code k)
      er₁ : ρm rdi ≡ just e₁
      er₂ : ρm rsi ≡ just e₂
      eg : global ds k ≡ just (body m bbs bst)
      ret : R (Block.instrs bst) (Block.jump bst) bbs nothing (zeros (2 + (m ∸ 2))) (regs nothing (just e₁) (just e₂)) v
      rel : 𝕍 w v

  call-𝕄 : ∀ {L n σ ρs φ ρm} a → OK L (_< n) a → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → ∀ w
    → w ∈ ⋆ ⟨ ⋆ ⟨ 𝒪 T n σ ρs a , ⟨ ρs rdi , ptt ⟩ ⟩ , ⟨ ρs rsi , ptt ⟩ ⟩ → Calls φ ρm a w
  call-𝕄 a oa nφ F G w ⟨ Y , ⟨ ⟨ X , ⟨ e∈ , ⟨ X⊆ , neX ⟩ ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩
      with 𝒪-𝕄 a oa nφ F G _ e∈ | 𝕄→𝕍s (G rdi) X X⊆ neX | 𝕄→𝕍s (G rsi) Y Y⊆ neY
  ... | ⟨ code k , ⟨ ea , r ⟩ ⟩ | ⟨ e₁ , ⟨ er₁ , X𝕍 ⟩ ⟩ | ⟨ e₂ , ⟨ er₂ , Y𝕍 ⟩ ⟩ with r e₁ X𝕍 e₂ Y𝕍
  ... | ⟨ m , ⟨ bbs , ⟨ bst , ⟨ eg , ⟨ v , ⟨ ret , rv ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rv

  {- the same call returns the same value -}
  calls-det : ∀ {φ ρm a w w'} (c : Calls φ ρm a w) (c' : Calls φ ρm a w') → 𝕍 w' (Calls.v c)
  calls-det (calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel) (calls k' e₁' e₂' m' bbs' bst' v' ea' er₁' er₂' eg' ret' rel')
      with trans (sym ea) ea' | trans (sym er₁) er₁' | trans (sym er₂) er₂'
  ... | refl | refl | refl with trans (sym eg) eg'
  ... | refl with Ret-det ret ret'
  ... | refl = rel'

  {- The fundamental lemma ----------------------------------------------------------}

  {- the blocks bs are adequate -}
  AdeqB : ℕ → List Block → Set₁
  AdeqB n bs = ∀ l {σ ρs F φ ρm f w} → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f → w ∈ blocks T n bs l σ ρs F
    → Σ[ v ∈ Val ] (Σ[ b ∈ Block ] Σ[ bs' ∈ List Block ] block-at bs l ≡ just ⟨ b , bs' ⟩
                     × R (Block.instrs b) (Block.jump b) bs' f φ ρm v) × 𝕍 w v

  adequate : ∀ {L n} is j bs {σ ρs F φ ρm f w} → Code L (_< n) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f
    → w ∈ ⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs)) σ ρs F → Σ[ v ∈ Val ] R is j bs f φ ρm v × 𝕍 w v

  {- a write to d, then the rest -}
  put-case : ∀ {L n} d {D m} is j bs {σ ρs F φ ρm f w} {S : Stack → State}
    → (∀ stk → step ds (S stk) ≡ putM d m φ ρm (run is j bs stk f)) → 𝕄 D m
    → Code L (_< n) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm → Fl F f
    → w ∈ putD n d D (⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs))) σ ρs F → Σ[ v ∈ Val ] Ret S v × 𝕍 w v
  put-case d is j bs st h c AB nφ F G Fl' w∈ with put-𝕄 d nφ h F G w∈
  ... | ⟨ φ' , ⟨ ρm' , ⟨ st' , ⟨ nφ' , ⟨ σ' , ⟨ ρs' , ⟨ F' , ⟨ G' , w∈' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with adequate is j bs c AB nφ' F' G' Fl' w∈'
  ... | ⟨ v , ⟨ r , rv ⟩ ⟩ = ⟨ v , ⟨ Ret-step (λ stk → trans (st stk) (st' _)) r , rv ⟩ ⟩

  {- a test that sets the flag, then the rest -}
  flag-case : ∀ {L n} is j bs {σ ρs F φ ρm b w} {S : Stack → State}
    → (∀ stk → step ds (S stk) ≡ next (run is j bs stk (just b) φ ρm)) → Fl F (just b)
    → Code L (_< n) is → AdeqB n bs → length φ ≡ n → 𝔽 σ φ → ℝ ρs ρm
    → w ∈ ⟦ is ⟧ˢ T n (⟦ j ⟧ʲ (blocks T n bs)) σ ρs F → Σ[ v ∈ Val ] Ret S v × 𝕍 w v
  flag-case is j bs st Fl' c AB nφ F G w∈ with adequate is j bs c AB nφ F G Fl' w∈
  ... | ⟨ v , ⟨ r , rv ⟩ ⟩ = ⟨ v , ⟨ Ret-step st r , rv ⟩ ⟩

  adequate (movq a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (𝒪-𝕄 a oa nφ F G) c AB nφ F G Fl' w∈
  adequate (subq a d ∷ is) j bs ⟨ ⟨ oa , od ⟩ , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (prim-𝕄 sub (𝒪-𝕄 (loc d) od nφ F G) (𝒪-𝕄 a oa nφ F G)) c AB nφ F G Fl' w∈
  adequate (cmpq a₂ a₁ ∷ is) j bs {φ = φ} {ρm} ⟨ ⟨ o₂ , o₁ ⟩ , c ⟩ AB nφ F G Fl' ⟨ ne , w∈ ⟩
      with cmp-Fl (𝒪-𝕄 a₁ o₁ nφ F G) (𝒪-𝕄 a₂ o₂ nφ F G) ne
  ... | ⟨ b , ⟨ eb , Fl'' ⟩ ⟩ = flag-case is j bs (λ stk → cong (λ mb → test mb (λ f' → run is j bs stk f' φ ρm)) eb) Fl'' c AB nφ F G w∈
  adequate (sete d ∷ is) j bs {F = Fl₀} ⟨ _ , c ⟩ AB nφ F G Fl' w∈ with put-ne d w∈
  ... | ⟨ d₀ , d₀∈ ⟩ with Fl' d₀ d₀∈
  ... | ⟨ b , ⟨ refl , _ ⟩ ⟩ = put-case d is j bs (λ _ → refl) h c AB nφ F G Fl' w∈
    where
    h : 𝕄 Fl₀ (just (bit b))
    h y y∈ with Fl' y y∈
    ... | ⟨ _ , ⟨ refl , r ⟩ ⟩ = ⟨ bit b , ⟨ refl , r ⟩ ⟩
  adequate (testinl a ∷ is) j bs {φ = φ} {ρm} ⟨ oa , c ⟩ AB nφ F G Fl' ⟨ ne , w∈ ⟩ with isinl-Fl (𝒪-𝕄 a oa nφ F G) ne
  ... | ⟨ b , ⟨ eb , Fl'' ⟩ ⟩ = flag-case is j bs (λ stk → cong (λ mb → test mb (λ f' → run is j bs stk f' φ ρm)) eb) Fl'' c AB nφ F G w∈
  adequate (alloc sh as d ∷ is) j bs ⟨ os , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (object-𝕄 sh as os nφ F G) c AB nφ F G Fl' w∈
  adequate (load fl a d ∷ is) j bs ⟨ oa , c ⟩ AB nφ F G Fl' w∈ =
    put-case d is j bs (λ _ → refl) (field-𝕄 fl (𝒪-𝕄 a oa nφ F G)) c AB nφ F G Fl' w∈
  adequate (callq a ∷ is) j bs {σ} {ρs} {φ = φ} {ρm} {f} ⟨ oa , c ⟩ AB nφ F G Fl' ⟨ ⟨ w₀ , w₀∈ ⟩ , w∈ ⟩
      with call-𝕄 a oa nφ F G w₀ w₀∈
  ... | cl@(calls k e₁ e₂ m bbs bst v ea er₁ er₂ eg ret rel)
      with adequate is j bs c AB nφ F G' (λ _ ()) w∈
    where
    G' : ℝ (called _) (regs (just v) nothing nothing)
    G' rax w' w'∈ = ⟨ v , ⟨ refl , calls-det cl (call-𝕄 a oa nφ F G w' w'∈) ⟩ ⟩
    G' rdi _ ()
    G' rsi _ ()
  ... | ⟨ v' , ⟨ r , rv ⟩ ⟩ = ⟨ v' , ⟨ r' , rv ⟩ ⟩
    where
    r' : R (callq a ∷ is) j bs f φ ρm v'
    r' stk with ret (retK is j bs φ stk)
    ... | ⟨ bs₁ , ⟨ f₁ , ⟨ φ₁ , ⟨ ρ₁ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ with r stk
    ... | ⟨ bs₂ , ⟨ f₂ , ⟨ φ₂ , ⟨ ρ₂ , ⟨ τ' , e' ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ bs₂ , ⟨ f₂ , ⟨ φ₂ , ⟨ ρ₂ , ⟨ st ∷↠ (τ ++↠ (cong (λ m → back m is j bs φ stk) e ∷↠ τ')) , e' ⟩ ⟩ ⟩ ⟩ ⟩
      where
      st : step ds (run (callq a ∷ is) j bs stk f φ ρm) ≡ next _
      st = trans (cong (λ mv → callq? ds mv (retK is j bs φ stk) ρm) ea)
             (trans (cong (λ mb → callM mb (retK is j bs φ stk) (ρm rdi) (ρm rsi)) eg)
                    (cong₂ (callM (just (body m bbs bst)) (retK is j bs φ stk)) er₁ er₂))
  adequate [] retq bs _ AB nφ F G Fl' w∈ with G rax _ w∈
  ... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ (λ stk → ⟨ bs , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ done , e ⟩ ⟩ ⟩ ⟩ ⟩) , r ⟩ ⟩
  adequate [] (jmp l) bs {φ = φ} {ρm} {f} _ AB nφ F G Fl' w∈ with AB l nφ F G Fl' w∈
  ... | ⟨ v , ⟨ ⟨ b , ⟨ bs' , ⟨ eb , r ⟩ ⟩ ⟩ , rv ⟩ ⟩ =
    ⟨ v , ⟨ Ret-step (λ stk → cong (λ mb → goto mb stk f φ ρm) eb) r , rv ⟩ ⟩
  adequate [] (je l₁ l₂) bs {φ = φ} {ρm} _ AB nφ F G Fl' (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
      with Fl' (left u) (allL u (here refl))
  ... | ⟨ true , ⟨ refl , _ ⟩ ⟩ with AB l₁ nφ F G Fl' w∈
  ... | ⟨ v , ⟨ ⟨ b , ⟨ bs' , ⟨ eb , r ⟩ ⟩ ⟩ , rv ⟩ ⟩ =
    ⟨ v , ⟨ Ret-step (λ stk → cong (λ mb → goto mb stk (just true) φ ρm) eb) r , rv ⟩ ⟩
  adequate [] (je l₁ l₂) bs {φ = φ} {ρm} _ AB nφ F G Fl' (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
      with Fl' (right u) (allR u (here refl))
  ... | ⟨ false , ⟨ refl , _ ⟩ ⟩ with AB l₂ nφ F G Fl' w∈
  ... | ⟨ v , ⟨ ⟨ b , ⟨ bs' , ⟨ eb , r ⟩ ⟩ ⟩ , rv ⟩ ⟩ =
    ⟨ v , ⟨ Ret-step (λ stk → cong (λ mb → goto mb stk (just false) φ ρm) eb) r , rv ⟩ ⟩

  blocks-adeq : ∀ {L n} bs → All (λ b → Code L (_< n) (Block.instrs b)) bs → AdeqB n bs
  blocks-adeq (b ∷ bs) (c ∷ cs) l nφ F G Fl' w∈ with l ≟ length bs
  ... | no _ = blocks-adeq bs cs l nφ F G Fl' w∈
  ... | yes _ with adequate (Block.instrs b) (Block.jump b) bs c (blocks-adeq bs cs) nφ F G Fl' w∈
  ...   | ⟨ v , ⟨ r , rv ⟩ ⟩ = ⟨ v , ⟨ ⟨ b , ⟨ bs , ⟨ refl , r ⟩ ⟩ ⟩ , rv ⟩ ⟩

{- The table of the program -------------------------------------------------------}

{- a fresh frame of n slots -}
zeros-𝔽 : ∀ m → 𝔽 zerosD (zeros m)
zeros-𝔽 m x x< rewrite replicate-‼ m {const Int 0ℤ} x (subst (x <_) (length-replicate m) x<) = ℬ-𝕄 Int _

tab : ∀ Ns xs → ds ≡ xs ++ Ns → DefsWF Ns → 𝕋 (table Ns)
tab (b ∷ Ns) xs e ⟨ ok , wf ⟩ k d d∈ with k ≟ length Ns
... | no _ = tab Ns (xs ++ [ b ]) (trans e (sym (++-assoc xs [ b ] Ns))) wf k d d∈
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) ν d∈ | yes refl = tt
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) (X ↦ ν) d∈ | yes refl = tt
tab (body m bbs bst ∷ Ns) xs e ⟨ c ∷ cs , wf ⟩ .(length Ns) (X ↦ (Y ↦ w)) ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ | yes refl = rel
  where
  𝕋' = tab Ns (xs ++ [ body m bbs bst ]) (trans e (sym (++-assoc xs [ body m bbs bst ] Ns))) wf
  rel : 𝕍code X (Y ↦ w) (length Ns)
  rel e₁ X𝕍 e₂ Y𝕍 with adequate 𝕋' (Block.instrs bst) (Block.jump bst) bbs c
         (blocks-adeq 𝕋' bbs cs) (frame-size m) (zeros-𝔽 (2 + (m ∸ 2))) G (λ _ ()) w∈
    where
    G : ℝ (argsD (mem X) (mem Y)) (regs nothing (just e₁) (just e₂))
    G rdi d d∈ = ⟨ e₁ , ⟨ refl , 𝕍s-∈ X X𝕍 d∈ ⟩ ⟩
    G rsi d d∈ = ⟨ e₂ , ⟨ refl , 𝕍s-∈ Y Y𝕍 d∈ ⟩ ⟩
  ... | ⟨ v , ⟨ r , rv ⟩ ⟩ =
    ⟨ m , ⟨ bbs , ⟨ bst , ⟨ trans (cong (λ L → global L (length Ns)) e) (reverse-‼-suffix xs _ Ns) , ⟨ v , ⟨ r , rv ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

{- Adequacy -----------------------------------------------------------------------}

adequate-main : ∀ {n bs b w} → DefsWF ds → BodyOK (length ds) n (body n bs b)
  → w ∈ ⟦ program ds (body n bs b) ⟧ₚ
  → Σ[ v ∈ Val ] R (Block.instrs b) (Block.jump b) bs nothing (zeros n) (regs (just (const Int _)) nothing nothing) v × 𝕍 w v
adequate-main {n} {bs} {b} wf (c ∷ cs) w∈ =
  adequate (tab ds [] refl wf) (Block.instrs b) (Block.jump b) bs c (blocks-adeq (tab ds [] refl wf) bs cs) (length-replicate n) (zeros-𝔽 n) G (λ _ ()) w∈
  where
  G : ℝ (called (zerosD 0)) (regs (just (const Int _)) nothing nothing)
  G rax = ℬ-𝕄 Int _
