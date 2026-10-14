{-

  Correctness of cast insertion (ISWIM → ISWIMᵀ) by a forward simulation
  between their reduction semantics (Semantics/Reduction/ISWIM.agda and
  Semantics/Reduction/Typed/ISWIM.agda).

  The relation on terms (_⊢_≈_) follows the shape of cast's output: a
  value of the source is related to the injection of the typed value,
  an eliminator to the eliminator of the projected operand, and a
  primitive to the two lets that bind its operands. It relates a source
  variable to a target variable through a partial map ρ of the target's
  variables (skip: the variable bound by the let of a primitive's first
  operand is no source variable). It is closed under substitution by
  related substitutions (≈-trav, for both kits), and cast M is related
  to M (cast≈). Besides cast's output, it has the states after an
  operator has been projected to a function (appᵥ≈) and after the first
  operand of a primitive is a value and has been bound (primR≈).

  The target takes a few more steps than the source: a project (the
  check that the source makes on an operand) and the lets of a
  primitive. Where the source errs on an operand of the wrong kind, the
  target errs at the project. The simulation is by recursion on the
  source term.

-}

module proof.Correctness.Typed.Reduction.CastRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
import Language.Typed.ISWIM as I
open import Compiler.Typed.Cast
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws)
open import proof.Compiler.Typed.CastScope using (cast-closed-≡)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import Semantics.Reduction.Smallstep using (Equivalent)
import Semantics.Reduction.ISWIM as S
import proof.Semantics.Reduction.Typed.ISWIM as T
open T using (Kit; varK; tmK; trav; Value; value-red; values-red)
import proof.Framework.Syntax.Subst Op sig as IS
open IS using (sub; exts)
open import Framework.ListUtil using (proj; args→list; has-length)
open import Framework.Primitives using (Base; Nat; Int; 𝔹; Unit; Void; Blame)
import Language.Prim as P

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
import Data.Integer as Z
open import Data.List using (replicate; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Mb
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
import Data.Nat as N
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no; does)

{- The relation ------------------------------------------------------------}

{- the source variable of each target variable, if any -}
VM : ℕ → Set
VM k = Fin k → Maybe ℕ

extρ skip : ∀ {k} → VM k → VM (suc k)
extρ ρ zero = just 0
extρ ρ (suc y) = Mb.map suc (ρ y)
skip ρ zero = nothing
skip ρ (suc y) = ρ y

{- the body of the lets of a primitive, before and after the first -}
pbody : ∀ {k} p → I.Tm (suc (suc k)) Any
pbody p = I.inject (out-flat p) (I.prim p (I.project tint (I.` suc zero)) (I.project tint (I.` zero)))

pbodyR : ∀ {k} p → I.Tm k Any → I.Tm (suc k) Any
pbodyR p V = I.inject (out-flat p) (I.prim p (I.project tint (T.ren suc V)) (I.project tint (I.` zero)))

infix 4 _⊢_≈_ _⊢_≈*_
data _⊢_≈_ {k} (ρ : VM k) : AST → I.Tm k Any → Set
data _⊢_≈*_ {k} (ρ : VM k) : ∀ {n} → Args (replicate n ■) → Vec (I.Tm k Any) n → Set

data _⊢_≈_ {k} ρ where
  var≈ : ∀ {x y} → ρ y ≡ just x → ρ ⊢ ` x ≈ I.` y
  lam≈ : ∀ {N N'} → extρ ρ ⊢ N ≈ N' → ρ ⊢ lam ⦅ ⟩ N ,, Nil ⦆ ≈ I.inject fun (I.lam N')
  lit≈ : ∀ {B c} → ρ ⊢ lit B c ⦅ Nil ⦆ ≈ I.inject (base B) (I.lit B c)
  tuple≈ : ∀ {n Ms Ms'} → ρ ⊢ Ms ≈* Ms' → ρ ⊢ tuple n ⦅ Ms ⦆ ≈ I.inject (tup n) (I.tuple Ms')
  inl≈ : ∀ {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inl-op ⦅ M ,, Nil ⦆ ≈ I.inject sum (I.inl M')
  inr≈ : ∀ {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inr-op ⦅ M ,, Nil ⦆ ≈ I.inject sum (I.inr M')
  app≈ : ∀ {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ app ⦅ L ,, M ,, Nil ⦆ ≈ I.app (I.project tfun L') M'
  appᵥ≈ : ∀ {N N' M M'} → extρ ρ ⊢ N ≈ N' → ρ ⊢ M ≈ M'
    → ρ ⊢ app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆ ≈ I.app (I.lam N') M'
  get≈ : ∀ {n} {i : Fin (suc n)} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ get i ⦅ M ,, Nil ⦆ ≈ I.get i (I.project (ttup n i) M')
  case≈ : ∀ {L L' M M' N N'} → ρ ⊢ L ≈ L' → extρ ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N'
    → ρ ⊢ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ I.case (I.project tsum L') M' N'
  primL≈ : ∀ {p L L' M M'} → ρ ⊢ L ≈ L' → skip ρ ⊢ M ≈ M'
    → ρ ⊢ prim p ⦅ L ,, M ,, Nil ⦆ ≈ I.let′ L' (I.let′ M' (pbody p))
  primR≈ : ∀ {p L L' M M'} → Value L' → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M'
    → ρ ⊢ prim p ⦅ L ,, M ,, Nil ⦆ ≈ I.let′ M' (pbodyR p L')
  let≈ : ∀ {M M' N N'} → ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N' → ρ ⊢ let-op ⦅ M ,, ⟩ N ,, Nil ⦆ ≈ I.let′ M' N'

data _⊢_≈*_ {k} ρ where
  [] : ρ ⊢ Nil ≈* []
  _∷_ : ∀ {n M M'} {Ms : Args (replicate n ■)} {Ms'} → ρ ⊢ M ≈ M' → ρ ⊢ Ms ≈* Ms' → ρ ⊢ (M ,, Ms) ≈* (M' ∷ Ms')

{- The fundamental lemma ----------------------------------------------------}

cast≈ : ∀ {k k'} {r : Fin k → Fin k'} {ρ : VM k'} → (∀ x (lt : x < k) → ρ (r (fromℕ< lt)) ≡ just x)
  → ∀ M (w : WS k M) → ρ ⊢ M ≈ cast r M w
casts≈ : ∀ {k k' n} {r : Fin k → Fin k'} {ρ : VM k'} → (∀ x (lt : x < k) → ρ (r (fromℕ< lt)) ≡ just x)
  → (Ms : Args (replicate n ■)) (ws : WS-args k Ms) → ρ ⊢ Ms ≈* casts r Ms ws

private
  ext-ok : ∀ {k k'} {r : Fin k → Fin k'} {ρ : VM k'} → (∀ x (lt : x < k) → ρ (r (fromℕ< lt)) ≡ just x)
    → ∀ x (lt : x < suc k) → extρ ρ (ext r (fromℕ< lt)) ≡ just x
  ext-ok h zero (s≤s z≤n) = refl
  ext-ok h (suc x) (s≤s lt) rewrite h x lt = refl

cast≈ h (` x) lt = var≈ (h x lt)
cast≈ h (lam ⦅ ⟩ N ,, Nil ⦆) (w , _) = lam≈ (cast≈ (ext-ok h) N w)
cast≈ h (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) = app≈ (cast≈ h L wL) (cast≈ h M wM)
cast≈ h (lit B c ⦅ Nil ⦆) _ = lit≈
cast≈ h (tuple n ⦅ Ms ⦆) ws = tuple≈ (casts≈ h Ms ws)
cast≈ h (get {suc n} i ⦅ M ,, Nil ⦆) (w , _) = get≈ (cast≈ h M w)
cast≈ h (inl-op ⦅ M ,, Nil ⦆) (w , _) = inl≈ (cast≈ h M w)
cast≈ h (inr-op ⦅ M ,, Nil ⦆) (w , _) = inr≈ (cast≈ h M w)
cast≈ h (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
  case≈ (cast≈ h L wL) (cast≈ (ext-ok h) M wM) (cast≈ (ext-ok h) N wN)
cast≈ h (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) = primL≈ (cast≈ h L wL) (cast≈ h M wM)
cast≈ h (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) = let≈ (cast≈ h M wM) (cast≈ (ext-ok h) N wN)
casts≈ {n = zero} h Nil _ = []
casts≈ {n = suc n} h (M ,, Ms) (w , ws) = cast≈ h M w ∷ casts≈ h Ms ws

{- Closure under substitution -------------------------------------------------}

{- related substitutions, for a kit of the target -}
OK : ∀ {k j} (𝒦 : Kit) → VM k → VM j → IS.Subst → T.Sub 𝒦 k j → Set
OK 𝒦 ρ ρ₂ σ τ = ∀ y {x} → ρ y ≡ just x → ρ₂ ⊢ σ x ≈ Kit.tm 𝒦 (τ y)

record KR (𝒦 : Kit) : Set where
  field
    laws : T.Laws 𝒦
    ok-ext : ∀ {k j ρ ρ₂ σ} {τ : T.Sub 𝒦 k j} → OK 𝒦 ρ ρ₂ σ τ → OK 𝒦 (extρ ρ) (extρ ρ₂) (exts σ) (T.exts 𝒦 τ)
    ok-skip : ∀ {k j ρ ρ₂ σ} {τ : T.Sub 𝒦 k j} → OK 𝒦 ρ ρ₂ σ τ → OK 𝒦 (skip ρ) (skip ρ₂) σ (T.exts 𝒦 τ)
    pbody-trav : ∀ {k j p} {τ : T.Sub 𝒦 k j} → trav 𝒦 (T.exts 𝒦 (T.exts 𝒦 τ)) (pbody p) ≡ pbody p

module Trav {𝒦} (K : KR 𝒦) where
  open KR K
  open T.Laws laws

  ≈-trav : ∀ {k j ρ ρ₂ σ} {τ : T.Sub 𝒦 k j} {M M'} → ρ ⊢ M ≈ M' → OK 𝒦 ρ ρ₂ σ τ → ρ₂ ⊢ sub σ M ≈ trav 𝒦 τ M'
  ≈*-trav : ∀ {k j ρ ρ₂ σ n} {τ : T.Sub 𝒦 k j} {Ms : Args (replicate n ■)} {Ms'} → ρ ⊢ Ms ≈* Ms' → OK 𝒦 ρ ρ₂ σ τ
    → ρ₂ ⊢ IS.sub-args σ Ms ≈* T.travs 𝒦 τ Ms'
  ≈-trav (var≈ e) ok = ok _ e
  ≈-trav (lam≈ n) ok = lam≈ (≈-trav n (ok-ext ok))
  ≈-trav lit≈ ok = lit≈
  ≈-trav (tuple≈ rs) ok = tuple≈ (≈*-trav rs ok)
  ≈-trav (inl≈ r) ok = inl≈ (≈-trav r ok)
  ≈-trav (inr≈ r) ok = inr≈ (≈-trav r ok)
  ≈-trav (app≈ r s) ok = app≈ (≈-trav r ok) (≈-trav s ok)
  ≈-trav (appᵥ≈ n s) ok = appᵥ≈ (≈-trav n (ok-ext ok)) (≈-trav s ok)
  ≈-trav (get≈ r) ok = get≈ (≈-trav r ok)
  ≈-trav (case≈ r s t) ok = case≈ (≈-trav r ok) (≈-trav s (ok-ext ok)) (≈-trav t (ok-ext ok))
  ≈-trav {ρ₂ = ρ₂} {σ} {τ} (primL≈ {p} {L} {L'} {M} {M'} r s) ok =
    subst (λ B → ρ₂ ⊢ sub σ (prim p ⦅ L ,, M ,, Nil ⦆) ≈ I.let′ (trav 𝒦 τ L') (I.let′ (trav 𝒦 (T.exts 𝒦 τ) M') B))
      (sym (pbody-trav {p = p} {τ = τ})) (primL≈ (≈-trav r ok) (≈-trav s (ok-skip ok)))
  ≈-trav {ρ₂ = ρ₂} {σ} {τ} (primR≈ {p} {L} {L'} {M} {M'} v r s) ok =
    subst₂ (λ X Y → ρ₂ ⊢ sub σ (prim p ⦅ L ,, M ,, Nil ⦆) ≈ I.let′ (trav 𝒦 τ M') (I.inject (out-flat p) (I.prim p (I.project tint X) (I.project tint Y))))
      (sym (exts-ren τ L')) (sym (tm-vr zero)) (primR≈ (T.value-trav v) (≈-trav r ok) (≈-trav s ok))
  ≈-trav (let≈ r s) ok = let≈ (≈-trav r ok) (≈-trav s (ok-ext ok))
  ≈*-trav [] ok = []
  ≈*-trav (r ∷ rs) ok = ≈-trav r ok ∷ ≈*-trav rs ok

inv-var : ∀ {k} {ρ : VM k} {M y} → ρ ⊢ M ≈ I.` y → Σ[ x ∈ ℕ ] M ≡ ` x × ρ y ≡ just x
inv-var (var≈ e) = _ , refl , e

varKR : KR varK
varKR = record { laws = T.varL ; ok-ext = ex ; ok-skip = sk ; pbody-trav = refl }
  where
  ex : ∀ {k j ρ ρ₂ σ} {τ : T.Sub varK k j} → OK varK ρ ρ₂ σ τ → OK varK (extρ ρ) (extρ ρ₂) (exts σ) (T.exts varK τ)
  ex ok zero refl = var≈ refl
  ex {ρ = ρ} ok (suc y) e with ρ y in eq | e
  ... | just x | refl with inv-var (ok y eq)
  ...   | _ , e' , e'' rewrite e' = var≈ (cong (Mb.map suc) e'')
  sk : ∀ {k j ρ ρ₂ σ} {τ : T.Sub varK k j} → OK varK ρ ρ₂ σ τ → OK varK (skip ρ) (skip ρ₂) σ (T.exts varK τ)
  sk ok (suc y) e with inv-var (ok y e)
  ... | _ , e' , e'' rewrite e' = var≈ e''

tmKR : KR tmK
tmKR = record { laws = T.tmL ; ok-ext = ex ; ok-skip = sk ; pbody-trav = refl }
  where
  ex : ∀ {k j ρ ρ₂ σ} {τ : T.Sub tmK k j} → OK tmK ρ ρ₂ σ τ → OK tmK (extρ ρ) (extρ ρ₂) (exts σ) (T.exts tmK τ)
  ex ok zero refl = var≈ refl
  ex {ρ = ρ} {σ = σ} ok (suc y) e with ρ y in eq | e
  ... | just x | refl = subst (λ X → _ ⊢ X ≈ _) (sym (IS.rename-sub suc (σ x)))
                          (Trav.≈-trav varKR (ok y eq) λ _ e' → var≈ (cong (Mb.map suc) e'))
  sk : ∀ {k j ρ ρ₂ σ} {τ : T.Sub tmK k j} → OK tmK ρ ρ₂ σ τ → OK tmK (skip ρ) (skip ρ₂) σ (T.exts tmK τ)
  sk {σ = σ} ok (suc y) {x} e = subst (λ X → _ ⊢ X ≈ _) (IS.sub-id (σ x)) (Trav.≈-trav varKR (ok y e) λ _ e' → var≈ e')

{- The simulation -----------------------------------------------------------}

ρ₀ : VM 0
ρ₀ ()

R : AST → I.Tm 0 Any → Set
R = ρ₀ ⊢_≈_

Ans′ = Ans T.red Value R

{- substituting a value for the variable of a binder -}
≈-[] : ∀ {N N' V V'} → extρ ρ₀ ⊢ N ≈ N' → R V V' → R (N IS.[ V ]) (N' T.[ V' ])
≈-[] n m = Trav.≈-trav tmKR n λ { zero refl → m ; (suc ()) _ }

{- a closed operand, after the let of a first operand -}
≈-skip : ∀ {M M' V'} → skip ρ₀ ⊢ M ≈ M' → R M (M' T.[ V' ])
≈-skip {M} s = subst (λ X → R X _) (IS.sub-id M) (Trav.≈-trav tmKR s λ { zero () ; (suc ()) _ })

{- a source term related to a value reduces to val -}
≈-val : ∀ {V V'} → Value V' → R V V' → S.red V ≡ val
≈*-val : ∀ {n} {Vs : Args (replicate n ■)} {Vs'} → All Value Vs' → ρ₀ ⊢ Vs ≈* Vs' → S.red-args Vs ≡ val
≈-val _ (lam≈ _) = refl
≈-val _ lit≈ = refl
≈-val (T.inject (T.tuple vs)) (tuple≈ rs) rewrite ≈*-val vs rs = refl
≈-val (T.inject (T.inl v)) (inl≈ r) rewrite ≈-val v r = refl
≈-val (T.inject (T.inr v)) (inr≈ r) rewrite ≈-val v r = refl
≈*-val [] [] = refl
≈*-val (v ∷ vs) (r ∷ rs) rewrite ≈-val v r | ≈*-val vs rs = refl

obs≈ : ∀ {V V'} → R V V' → S.obs V ≡ T.obs V'
obs≈* : ∀ {n} {Vs : Args (replicate n ■)} {Vs'} → ρ₀ ⊢ Vs ≈* Vs' → S.obs-args Vs ≡ T.obss Vs'
obs≈ (lam≈ _) = refl
obs≈ lit≈ = refl
obs≈ (tuple≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (app≈ _ _) = refl
obs≈ (appᵥ≈ _ _) = refl
obs≈ (get≈ _) = refl
obs≈ (case≈ _ _ _) = refl
obs≈ (primL≈ _ _) = refl
obs≈ (primR≈ _ _ _) = refl
obs≈ (let≈ _ _) = refl
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

{- one layer of context, and two -}
fr : ∀ {A B} {g : I.Tm 0 A → I.Tm 0 B} {κ : I.Tm 0 A → Red (I.Tm 0 B)}
  → (∀ X → T.red (g X) ≡ step-in g (T.red X) (κ X)) → Frame T.red T.red g
fr = frame _

{- a project of a value, in a context -}
proj-in : ∀ {A t V'} {g : I.Tm 0 ⟪ flat t ⟫ → I.Tm 0 A} → Value V' → (F : Frame T.red T.red g)
  → T.red (g (I.project t V')) ≡ step-in g (T.project? t V') (Frame.κ F (I.project t V'))
proj-in {t = t} {V'} {g} v F = trans (Frame.eq F _) (cong (λ r → step-in g r (Frame.κ F (I.project t V'))) (val-in (value-red v)))

project-ok : ∀ t (X : I.Tm 0 ⟪ flat t ⟫) → T.project? t (I.inject (flat t) X) ≡ to X
project-ok t X with flat t ≟F flat t
... | yes refl = refl
... | no ne = ⊥-elim (ne refl)

project-bad : ∀ {H t} (X : I.Tm 0 ⟪ H ⟫) → H ≢ flat t → T.project? t (I.inject H X) ≡ error
project-bad {H} {t} X ne with H ≟F flat t
... | yes e = ⊥-elim (ne e)
... | no _ = refl

{- a component of a tuple, of the right length or not -}
has-length-no : ∀ {m n} (Ms : Args (replicate m ■)) → m ≢ n → has-length n (args→list Ms) ≡ false
has-length-no {zero} {zero} Nil ne = ⊥-elim (ne refl)
has-length-no {zero} {suc n} Nil ne = refl
has-length-no {suc m} {zero} (M ,, Ms) ne = refl
has-length-no {suc m} {suc n} (M ,, Ms) ne = has-length-no Ms (λ e → ne (cong suc e))

proj-no : ∀ {m n} (i : Fin n) (Ms : Args (replicate m ■)) → m ≢ n → proj i (args→list Ms) ≡ nothing
proj-no {zero} zero Nil ne = refl
proj-no {zero} (suc i) Nil ne = refl
proj-no {suc m} {suc n} zero (M ,, Ms) ne rewrite has-length-no Ms (λ e → ne (cong suc e)) = refl
proj-no {suc m} (suc i) (M ,, Ms) ne = proj-no i Ms (λ e → ne (cong suc e))

proj-ok : ∀ {n} (i : Fin n) {Ms : Args (replicate n ■)} {Ms'} → ρ₀ ⊢ Ms ≈* Ms'
  → Σ[ V ∈ AST ] proj i (args→list Ms) ≡ just V × R V (lookup Ms' i)
proj-ok {suc n} zero {M ,, Ms} (r ∷ rs) rewrite has-length-args {n = n} Ms = M , refl , r
proj-ok (suc i) (r ∷ rs) = proj-ok i rs

{- whether an operand of a primitive is an integer -}
data IntView : AST → I.Tm 0 Any → Set where
  int : ∀ {n} → IntView (lit Int n ⦅ Nil ⦆) (I.inject (base Int) (I.lit Int n))
  other : ∀ {V V'} → T.project? tint V' ≡ error → (∀ p o → δ? p (S.obs V) o ≡ nothing)
    → (∀ p n → δ? p (o-const Int n) (S.obs V) ≡ nothing) → IntView V V'

int? : ∀ {V V'} → Value V' → R V V' → IntView V V'
int? (T.inject T.lam) (lam≈ _) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject T.lit) (lit≈ {Nat}) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject T.lit) (lit≈ {Int}) = int
int? (T.inject T.lit) (lit≈ {𝔹}) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject T.lit) (lit≈ {Unit}) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject T.lit) (lit≈ {Void}) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject T.lit) (lit≈ {Blame}) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject (T.tuple _)) (tuple≈ _) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject (T.inl _)) (inl≈ _) = other refl (λ _ _ → refl) (λ _ _ → refl)
int? (T.inject (T.inr _)) (inr≈ _) = other refl (λ _ _ → refl) (λ _ _ → refl)

{- the result of a primitive -}
out≈ : ∀ p n m → R (S.out (P.δ p n m)) (I.inject (out-flat p) (T.out p n m))
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (tuple≈ [])
... | false = inr≈ (tuple≈ [])

proj-in-to : ∀ {A t V' X} {g : I.Tm 0 ⟪ flat t ⟫ → I.Tm 0 A} → Value V' → (F : Frame T.red T.red g)
  → T.project? t V' ≡ to X → T.red (g (I.project t V')) ≡ to (g X)
proj-in-to {t = t} {V'} {g = g} v F e = trans (proj-in v F) (cong (λ r → step-in g r (Frame.κ F (I.project t V'))) e)

proj-in-err : ∀ {A t V'} {g : I.Tm 0 ⟪ flat t ⟫ → I.Tm 0 A} → Value V' → (F : Frame T.red T.red g)
  → T.project? t V' ≡ error → T.red (g (I.project t V')) ≡ error
proj-in-err {t = t} {V'} {g = g} v F e = trans (proj-in v F) (cong (λ r → step-in g r (Frame.κ F (I.project t V'))) e)

{- a primitive whose first, or second, operand is no integer -}
prim-err₁ : ∀ {p V' Y} → Value V' → T.project? tint V' ≡ error
  → T.red (I.inject (out-flat p) (I.prim p (I.project tint V') Y)) ≡ error
prim-err₁ v e rewrite value-red v | e = refl

prim-err₂ : ∀ {p n W'} → Value W' → T.project? tint W' ≡ error
  → T.red (I.inject (out-flat p) (I.prim p (I.lit Int n) (I.project tint W'))) ≡ error
prim-err₂ v e rewrite value-red v | e = refl

{- the lets of a primitive, once both operands are values -}
prim-β : ∀ {p V' W'} → Value W' → T.red (I.let′ W' (pbodyR p V'))
  ≡ to (I.inject (out-flat p) (I.prim p (I.project tint V') (I.project tint W')))
prim-β {p} {V'} {W'} w = trans (val-in (value-red w)) (cong (λ X → to (I.inject (out-flat p) (I.prim p (I.project tint X) (I.project tint W')))) (T.wk-[] V' W'))

sim : ∀ M {M'} → R M M' → Ans′ M (S.red M) M'
sims : ∀ {n} (Ms : Args (replicate n ■)) {Ms'} → ρ₀ ⊢ Ms ≈* Ms' → Ans T.reds (All Value) (ρ₀ ⊢_≈*_) Ms (S.red-args Ms) Ms'
appᵥ-sim : ∀ {N N'} M {M'} → extρ ρ₀ ⊢ N ≈ N' → R M M'
  → Ans′ (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) (S.app? (lam ⦅ ⟩ N ,, Nil ⦆) (S.red M) M) (I.app (I.lam N') M')
primR-sim : ∀ {p V V'} → Value V' → R V V' → ∀ M {M'} → R M M'
  → Ans′ (prim p ⦅ V ,, M ,, Nil ⦆) (step-in (λ X → prim p ⦅ V ,, X ,, Nil ⦆) (S.red M) (S.prim? p V M)) (I.let′ M' (pbodyR p V'))

sim (` x) (var≈ {y = ()} _)
sim (lam ⦅ ⟩ N ,, Nil ⦆) (lam≈ n) = val ε (T.inject T.lam) (lam≈ n)
sim (lit B c ⦅ Nil ⦆) lit≈ = val ε (T.inject T.lit) lit≈
sim (tuple n ⦅ Ms ⦆) (tuple≈ rs) =
  ans-in (frame-∘ {redU = T.red} {h = I.tuple} {f = I.inject (tup n)} (frame _ λ _ → refl) (frame _ λ _ → refl)) tuple≈ (sims Ms rs)
    λ vs ms → val ε (T.inject (T.tuple vs)) (tuple≈ ms)
sim (inl-op ⦅ M ,, Nil ⦆) (inl≈ r) =
  ans-in (frame-∘ {redU = T.red} {h = I.inl} {f = I.inject sum} (frame _ λ _ → refl) (frame _ λ _ → refl)) inl≈ (sim M r)
    λ v m → val ε (T.inject (T.inl v)) (inl≈ m)
sim (inr-op ⦅ M ,, Nil ⦆) (inr≈ r) =
  ans-in (frame-∘ {redU = T.red} {h = I.inr} {f = I.inject sum} (frame _ λ _ → refl) (frame _ λ _ → refl)) inr≈ (sim M r)
    λ v m → val ε (T.inject (T.inr v)) (inr≈ m)
sim (app ⦅ L ,, M ,, Nil ⦆) (app≈ {M' = M'} r s) =
  ans-in (frame-∘ {redU = T.red} {h = I.project tfun} {f = λ X → I.app X M'} (frame _ λ _ → refl) (frame _ λ _ → refl)) (λ m → app≈ m s) (sim L r) app-sim
  where
  F : Frame T.red T.red (λ X → I.app X M')
  F = frame _ λ _ → refl
  app-sim : ∀ {V V'} → Value V' → R V V' → Ans′ (app ⦅ V ,, M ,, Nil ⦆) (S.app? V (S.red M) M) (I.app (I.project tfun V') M')
  app-sim v@(T.inject T.lam) (lam≈ n) = ans-step (proj-in v F) (appᵥ-sim M n s)
  app-sim v@(T.inject T.lit) lit≈ = error ε (proj-in v F)
  app-sim v@(T.inject (T.tuple _)) (tuple≈ _) = error ε (proj-in v F)
  app-sim v@(T.inject (T.inl _)) (inl≈ _) = error ε (proj-in v F)
  app-sim v@(T.inject (T.inr _)) (inr≈ _) = error ε (proj-in v F)
sim (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) (appᵥ≈ n s) = appᵥ-sim M n s
sim (get i ⦅ M ,, Nil ⦆) (get≈ {n} r) =
  ans-in (frame-∘ {redU = T.red} {h = I.project (ttup n i)} {f = I.get i} (frame _ λ _ → refl) (frame _ λ _ → refl)) get≈ (sim M r) get-sim
  where
  F : Frame T.red T.red (I.get i)
  F = frame _ λ _ → refl
  get-sim : ∀ {V V'} → Value V' → R V V' → Ans′ (get i ⦅ V ,, Nil ⦆) (S.get? i V) (I.get i (I.project (ttup n i) V'))
  get-sim v@(T.inject (T.tuple vs)) (tuple≈ {m} {Ms} {Ms'} rs) with m N.≟ suc n
  ... | yes refl with proj-ok i rs
  ...   | V , e , r' rewrite e =
    to (plus (proj-in-to v F (project-ok (ttup n i) (I.tuple Ms'))) (val-in (value-red (T.tuple vs)) ◅ ε)) r'
  get-sim v@(T.inject (T.tuple vs)) (tuple≈ {m} {Ms} {Ms'} rs) | no ne rewrite proj-no i Ms ne =
    error ε (proj-in-err v F (project-bad (I.tuple Ms') λ { refl → ne refl }))
  get-sim v@(T.inject T.lam) (lam≈ _) = error ε (proj-in {t = ttup n i} v F)
  get-sim v@(T.inject T.lit) lit≈ = error ε (proj-in {t = ttup n i} v F)
  get-sim v@(T.inject (T.inl _)) (inl≈ _) = error ε (proj-in {t = ttup n i} v F)
  get-sim v@(T.inject (T.inr _)) (inr≈ _) = error ε (proj-in {t = ttup n i} v F)
sim (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (case≈ {M' = M'} {N' = N'} r s t) =
  ans-in (frame-∘ {redU = T.red} {h = I.project tsum} {f = λ X → I.case X M' N'} (frame _ λ _ → refl) (frame _ λ _ → refl))
    (λ m → case≈ m s t) (sim L r) case-sim
  where
  F : Frame T.red T.red (λ X → I.case X M' N')
  F = frame _ λ _ → refl
  case-sim : ∀ {V V'} → Value V' → R V V'
    → Ans′ (case-op ⦅ V ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (S.case? V M N) (I.case (I.project tsum V') M' N')
  case-sim v@(T.inject (T.inl w)) (inl≈ m) = to (plus (proj-in-to v F refl) (val-in (value-red (T.inl w)) ◅ ε)) (≈-[] s m)
  case-sim v@(T.inject (T.inr w)) (inr≈ m) = to (plus (proj-in-to v F refl) (val-in (value-red (T.inr w)) ◅ ε)) (≈-[] t m)
  case-sim v@(T.inject T.lam) (lam≈ _) = error ε (proj-in v F)
  case-sim v@(T.inject T.lit) lit≈ = error ε (proj-in v F)
  case-sim v@(T.inject (T.tuple _)) (tuple≈ _) = error ε (proj-in v F)
sim (prim p ⦅ L ,, M ,, Nil ⦆) (primL≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → primL≈ m s) (sim L r)
    λ v m → ans-step (val-in (value-red v)) (primR-sim v m M (≈-skip s))
sim (prim p ⦅ L ,, M ,, Nil ⦆) (primR≈ v m s) = ans-skip (≈-val v m) (primR-sim v m M s)
sim (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (let≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → let≈ m s) (sim M r) λ v m → to (one (val-in (value-red v))) (≈-[] s m)

sims Nil [] = val ε [] []
sims (M ,, Ms) (r ∷ rs) =
  ans-in (frame _ λ _ → refl) (_∷ rs) (sim M r)
    λ v m → ans-in (frame {g = λ Xs → _ ∷ Xs} _ (λ Xs → val-in (value-red v))) (m ∷_) (sims Ms rs)
      λ vs ms → val ε (v ∷ vs) (m ∷ ms)

appᵥ-sim M n s = ans-in (frame _ λ _ → refl) (appᵥ≈ n) (sim M s) λ v m → to (one (val-in (value-red v))) (≈-[] n m)

primR-sim {p} {V} {V'} v m M s = ans-in (frame _ λ _ → refl) (primR≈ v m) (sim M s) final
  where
  final : ∀ {W W'} → Value W' → R W W' → Ans′ (prim p ⦅ V ,, W ,, Nil ⦆) (S.prim? p V W) (I.let′ W' (pbodyR p V'))
  final {W} {W'} w m' with int? v m | int? w m'
  ... | int {n₁} | int {n₂} = to (plus (prim-β {V' = V'} w) (refl ◅ refl ◅ refl ◅ ε)) (out≈ p n₁ n₂)
  ... | other e d d' | _ rewrite d p (S.obs W) =
    error (prim-β {V' = V'} w ◅ ε)
          (prim-err₁ v e)
  ... | int {n} | other e d d' rewrite d' p n =
    error (prim-β {V' = V'} w ◅ refl ◅ ε)
          (prim-err₂ w e)

{- The end theorem ----------------------------------------------------------}

cast-program-correct : ∀ M (w : WS 0 M) → Equivalent (S.sem M) (T.sem (cast-program M w))
cast-program-correct M w = red-equivalent value-red R (λ {M} m → sim M m) (λ m _ _ → obs≈ m) (cast≈ (λ _ ()) M w)

cast-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (cast-closed M))
cast-correct M c rewrite cast-closed-≡ M (closed-ws {M} c) = cast-program-correct M (closed-ws {M} c)
