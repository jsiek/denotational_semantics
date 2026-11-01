{-

  Adequacy of the Scott-domain semantics of X86μ
  (Mu/Semantics/ScottDomains/X86.agda) for the X86μ interpreter
  (Mu/Semantics/ClockedInterpreters/X86.agda): if the meaning of a
  program is defined, the interpreter returns a value from some clock
  on. For every program (no premise on its table).

  The logical relation is FPC's (LogRel.agda), by the stages of the
  bilimit, for the values of the GlobalFunμ interpreter, which the X86μ
  interpreter shares: a closure is a pair (the tag pr) of its code and
  its environment, and its code is a code pointer, code f. The meaning
  of code f is the curried function Λ X. Λ Y. B (X , Y) of its body, so
  code f is related to an approximation h of depth n of a function value
  when h applied to an approximation x of depth n related to an
  environment e gives a function value (Fn) whose payload, applied to an
  approximation y of depth n - 1 related to an argument a, gives a
  result related to what the call of f on e and a returns (Ev): the two
  applications of a call go down one stage each. A computation (a
  function of the clock) returns v from some clock on (_⇓_), for a call,
  the run of a sequence or a jump.

  The fundamental lemma (adequate) is by induction on the sequence, given
  that the blocks it may jump to are adequate (AdeqB) and that the table
  is related to the code pointers (𝕋), as for the graph model
  (Mu/proof/Adequacy/X86LogRel.agda): the frame, the registers and the
  flag of the semantics are related to those of the interpreter
  (RelState), and the open closure is that of its slot (OpR). The table
  of the program is related (tab): each definition is related to its
  code pointer given that the table of the older ones is, by the
  fundamental lemma for its body.

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Base using (ap₂)

open import Framework.Primitives using (Base; base-rep; Int)
open import Framework.abt.GSubst using (_•_)
open import Framework.Lookup using (forget)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Language.Prim using (Prim; sub; eq; int; bool) renaming (δ to δᴾ)
open import Mu.Language.Type using (Type; Ctx; base; tup; _⊹_; _⇒_; μ; code; _∋_; Z; S; idx; lvl) renaming (unroll to unrollᵗ)
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import Mu.Semantics.ClockedInterpreters.X86
  using (RV; MV; RegVals; rv; Flag; Mach; regs; frame; clo; flag; _⦅_⦆; _[_≔_]; cast; forgetᵥ; wipeᵣ;
         arg; args; put; equal; bit; size; code-of; env-of; run; jump; call)
  renaming (⟨_,_,_,_⟩ to mach; obj to objᵢ)
open import Mu.proof.Adequacy.X86Common using (OpR; none; agree)
open import proof.Semantics.Interp.Clock using (Result; ret; _>>=_; Stable; st-now; st-bind; stable-unique)
open import proof.Framework.Lookup using (lvl-<)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_; s≤s; _≟_)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Unit using (tt)
open import Naturals.Order using (≤-succ)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (does; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
import Data.Nat as Nat
import Data.Empty
import Data.Product as P

module Mu.proof.Adequacy.ScottDomains.X86LogRel
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe hiding (Maps)
open import proof.Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe hiding (Val)
  renaming (Env to Envᵈ; app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ; case to caseᵈ)
import proof.Framework.Scott.Ops pt fe pe as Ops
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (Den; abs; init; init-defined; code₂; module Over)
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)
open import Mu.Semantics.ScottDomains.Ops pt fe pe using (Table; tables; tables-yes; tables-no)
open import Mu.Semantics.ScottDomains.CFG pt fe pe using (drop)
open import Mu.Semantics.ScottDomains.X86 pt fe pe
  using (RegsD; 𝕊; Kont; regsᶜ; flagᶜ; ⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ; 𝒪; 𝒪s; object; called-regs)
  renaming (put to putₛ; _[_≔_] to _[_≔ₛ_]; args to argsₛ; blocks to blocksₛ; run to runₛ)
open Over 𝕊 using (op₁; op₂)

{- the functor whose fixed point 𝔻 is (lifted) -}
VF : Functor
VF = Ops.Val

{- A computation returns v from some clock on -------------------------------------------}

infix 4 _⇓_
record _⇓_ {X : 𝓤₀ ̇ } (c : ℕ → Result X) (v : X) : 𝓤₀ ̇ where
  constructor ev
  field run⇓ : Stable c (ret v)
open _⇓_ public

private
 ret-inj : {X : 𝓤₀ ̇ } {a b : X} → _≡_ {A = Result X} (ret a) (ret b) → a ＝ b
 ret-inj ≡-refl = refl

∥⇓∥-det : ∀ {X : 𝓤₀ ̇ } {c : ℕ → Result X} {v₁ v₂} → ∥ c ⇓ v₁ ∥ → ∥ c ⇓ v₂ ∥ → v₁ ＝ v₂
∥⇓∥-det = ∥∥-rec₂ K-is-set (λ e₁ e₂ → ret-inj (stable-unique (run⇓ e₁) (run⇓ e₂)))

{- a value with a computation that returns it is unique -}
Σ⇓-prop : ∀ {X : 𝓤₀ ̇ } {c : ℕ → Result X} (P : X → 𝓤₁ ̇ ) → ((v : X) → is-prop (P v))
  → is-prop (Σ v ꞉ X , ∥ c ⇓ v ∥ × P v)
Σ⇓-prop {X} {c} P P-prop (v₁ , t₁ , m₁) (v₂ , t₂ , m₂) = go (∥⇓∥-det t₁ t₂) t₁ t₂ m₁ m₂
 where
  go : {v₁ v₂ : X} → v₁ ＝ v₂ → (t₁ : ∥ c ⇓ v₁ ∥) (t₂ : ∥ c ⇓ v₂ ∥) (m₁ : P v₁) (m₂ : P v₂)
     → (v₁ , t₁ , m₁) ＝ (v₂ , t₂ , m₂)
  go {v} refl t₁ t₂ m₁ m₂ = ap₂ (λ a b → v , a , b) (∥∥-is-prop t₁ t₂) (P-prop v m₁ m₂)

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

 open Vals Σ renaming (Env to Frame; const to cv; δ to δᵥ)

 {- the call of code f on e and a -}
 Call : ∀ {Δ A B} → Σ ∋ sig Δ A B → Val (tup Δ) → Val A → ℕ → Result (Val B)
 Call f e a ck = call ds ck (code f) e a

 {- The relation, by stages ------------------------------------------------------------}

 data Shape : Tag → {A : Type} → Val A → 𝓤₀ ̇ where
   s-con : ∀ {B} {c : base-rep B} → Shape (con B c) (cv c)
   s-tup : ∀ {Δ} {vs : All Val Δ} → Shape (tup (length Δ)) (tup vs)
   s-left : ∀ {A B} {v : Val A} → Shape left (inl {B = B} v)
   s-right : ∀ {A B} {v : Val B} → Shape right (inr {A = A} v)
   s-pack : ∀ {Δ A B} {c : Val (code Δ A B)} {e : Val (tup Δ)} → Shape pr (pack c e)
   s-code : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} → Shape fun (code f)
   s-fold : ∀ {t A} {v : Val (unrollᵗ A)} → Shape t v → Shape t (fold {A} v)

 Shape-prop : ∀ {t A} {v : Val A} → is-prop (Shape t v)
 Shape-prop s-con s-con = refl
 Shape-prop s-tup s-tup = refl
 Shape-prop s-left s-left = refl
 Shape-prop s-right s-right = refl
 Shape-prop s-pack s-pack = refl
 Shape-prop s-code s-code = refl
 Shape-prop (s-fold e) (s-fold e') = ap s-fold (Shape-prop e e')

 data IsFun : Tag → 𝓤₀ ̇ where
   is-fun : IsFun fun

 IsFun-prop : ∀ {t} → is-prop (IsFun t)
 IsFun-prop is-fun is-fun = refl

 {- R n s v: the approximation s of depth n is related to v; Match and
    Pay, the same for its unrolling and payload; Fn n s f e: if s is
    defined, it is a function value whose payload Pay₂ calls f on e; Ev n
    s c: if s is defined, c returns a value related to it -}
 R : (n : ℕ) {A : Type} → ⟨ 𝓓 n ⟩ → Val A → 𝓤₁ ̇
 Match : (n : ℕ) {A : Type} → ⟨ obj VF (𝓓 n) ⟩ → Val A → 𝓤₁ ̇
 Pay : (n : ℕ) {t : Tag} {A : Type} {v : Val A} → Shape t v → ⟨ obj (Payload t) (𝓓 n) ⟩ → 𝓤₁ ̇
 Tup : (n : ℕ) {Δ : Ctx} → All Val Δ → (Fin (length Δ) → ⟨ 𝓓 n ⟩) → 𝓤₁ ̇
 Fn : (n : ℕ) {Δ : Ctx} {A B : Type} → ⟨ 𝓓 n ⟩ → Σ ∋ sig Δ A B → Val (tup Δ) → 𝓤₁ ̇
 FnV : (n : ℕ) {Δ : Ctx} {A B : Type} → ⟨ obj VF (𝓓 n) ⟩ → Σ ∋ sig Δ A B → Val (tup Δ) → 𝓤₁ ̇
 Pay₂ : (n : ℕ) {t : Tag} {Δ : Ctx} {A B : Type} → IsFun t → ⟨ obj (Payload t) (𝓓 n) ⟩ → Σ ∋ sig Δ A B → Val (tup Δ) → 𝓤₁ ̇
 Ev : (n : ℕ) {B : Type} → ⟨ 𝓓 n ⟩ → (ℕ → Result (Val B)) → 𝓤₁ ̇

 R zero s v = 𝟙
 R (succ n) s v = (p : is-defined s) → Match n (value s p) v

 Match n (t , x) v = Σ e ꞉ Shape t v , Pay n e x

 Pay n s-con x = 𝟙
 Pay n (s-tup {vs = vs}) xs = Tup n vs xs
 Pay n (s-left {v = v}) x = R n x v
 Pay n (s-right {v = v}) x = R n x v
 Pay n (s-pack {c = c} {e}) xy = R n (xy zero) c × R n (xy (suc zero)) e
 Pay n (s-code {f = f}) h = (x : ⟨ 𝓓 n ⟩) (e : Val _) → R n x e → Fn n (h · x) f e
 Pay n (s-fold e) x = Pay n e x

 Tup n [] xs = 𝟙
 Tup n (v ∷ vs) xs = R n (xs zero) v × Tup n vs (λ i → xs (suc i))

 Fn zero s f e = 𝟙
 Fn (succ n) s f e = (p : is-defined s) → FnV n (value s p) f e

 FnV n (t , h) f e = Σ i ꞉ IsFun t , Pay₂ n i h f e

 Pay₂ n {A = A} is-fun h f e = (y : ⟨ 𝓓 n ⟩) (a : Val A) → R n y a → Ev n (h · y) (Call f e a)

 Ev zero s c = 𝟙
 Ev (succ n) {B} s c = (p : is-defined s) → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Match n (value s p) v

 {- The relation is a proposition ---------------------------------------------------}

 R-prop : (n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Val A) → is-prop (R n s v)
 Match-prop : (n : ℕ) {A : Type} (u : ⟨ obj VF (𝓓 n) ⟩) (v : Val A) → is-prop (Match n u v)
 Pay-prop : (n : ℕ) {t : Tag} {A : Type} {v : Val A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 n) ⟩) → is-prop (Pay n e x)
 Tup-prop : (n : ℕ) {Δ : Ctx} (vs : All Val Δ) (xs : Fin (length Δ) → ⟨ 𝓓 n ⟩) → is-prop (Tup n vs xs)
 Fn-prop : (n : ℕ) {Δ : Ctx} {A B : Type} (s : ⟨ 𝓓 n ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ)) → is-prop (Fn n s f e)
 Pay₂-prop : (n : ℕ) {t : Tag} {Δ : Ctx} {A B : Type} (i : IsFun t) (h : ⟨ obj (Payload t) (𝓓 n) ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ))
   → is-prop (Pay₂ n i h f e)
 Ev-prop : (n : ℕ) {B : Type} (s : ⟨ 𝓓 n ⟩) (c : ℕ → Result (Val B)) → is-prop (Ev n s c)

 R-prop zero s v = 𝟙-is-prop
 R-prop (succ n) s v = Π-is-prop fe (λ p → Match-prop n (value s p) v)

 Match-prop n (t , x) v = Σ-is-prop Shape-prop (λ e → Pay-prop n e x)

 Pay-prop n s-con x = 𝟙-is-prop
 Pay-prop n (s-tup {vs = vs}) xs = Tup-prop n vs xs
 Pay-prop n (s-left {v = v}) x = R-prop n x v
 Pay-prop n (s-right {v = v}) x = R-prop n x v
 Pay-prop n (s-pack {c = c} {e}) xy = ×-is-prop (R-prop n (xy zero) c) (R-prop n (xy (suc zero)) e)
 Pay-prop n (s-code {f = f}) h = Π-is-prop fe (λ x → Π-is-prop fe (λ e → Π-is-prop fe (λ _ → Fn-prop n (h · x) f e)))
 Pay-prop n (s-fold e) x = Pay-prop n e x

 Tup-prop n [] xs = 𝟙-is-prop
 Tup-prop n (v ∷ vs) xs = ×-is-prop (R-prop n (xs zero) v) (Tup-prop n vs (λ i → xs (suc i)))

 Fn-prop zero s f e = 𝟙-is-prop
 Fn-prop (succ n) s f e = Π-is-prop fe (λ p → Σ-is-prop IsFun-prop (λ i → Pay₂-prop n i (pr₂ (value s p)) f e))

 Pay₂-prop n is-fun h f e = Π-is-prop fe (λ y → Π-is-prop fe (λ a → Π-is-prop fe (λ _ → Ev-prop n (h · y) (Call f e a))))

 Ev-prop zero s c = 𝟙-is-prop
 Ev-prop (succ n) s c = Π-is-prop fe (λ p → Σ⇓-prop {c = c} (Match n (value s p)) (Match-prop n (value s p)))

 Pay-at : ∀ {n t A} {v : Val A} {x : ⟨ obj (Payload t) (𝓓 n) ⟩} (e : Shape t v) → Match n (t , x) v → Pay n e x
 Pay-at {n} {x = x} e (e' , m) = transport (λ e → Pay n e x) (Shape-prop e' e) m

 Pay₂-at : ∀ {n t Δ A B} {f : Σ ∋ sig Δ A B} {e : Val (tup Δ)} {h : ⟨ obj (Payload t) (𝓓 n) ⟩} (i : IsFun t)
   → FnV n (t , h) f e → Pay₂ n i h f e
 Pay₂-at {n} {f = f} {e} {h} i (i' , m) = transport (λ i → Pay₂ n i h f e) (IsFun-prop i' i) m

 Res→Match : ∀ {n B} {u : ⟨ obj VF (𝓓 n) ⟩} {c : ℕ → Result (Val B)} {v}
   → (Σ v' ꞉ Val B , ∥ c ⇓ v' ∥ × Match n u v') → ∥ c ⇓ v ∥ → Match n u v
 Res→Match {n} {u = u} (v' , t' , m) t = transport (Match n u) (∥⇓∥-det t' t) m

 Ev→R : ∀ {n B} {s : ⟨ 𝓓 n ⟩} {c : ℕ → Result (Val B)} {v} → Ev n s c → ∥ c ⇓ v ∥ → R n s v
 Ev→R {zero} h t = ⋆
 Ev→R {succ n} h t p = Res→Match (h p) t

 {- Downward closed in the approximation ---------------------------------------------}

 R-mono : (n : ℕ) {A : Type} (s s' : ⟨ 𝓓 n ⟩) (v : Val A) → s' ⊑⟨ 𝓓 n ⟩ s → R n s v → R n s' v
 Match-mono : (n : ℕ) {A : Type} (u u' : ⟨ obj VF (𝓓 n) ⟩) (v : Val A)
   → u' ⊑⟨ obj VF (𝓓 n) ⟩ u → Match n u v → Match n u' v
 Pay-mono : (n : ℕ) {t : Tag} {A : Type} {v : Val A} (e : Shape t v) (x x' : ⟨ obj (Payload t) (𝓓 n) ⟩)
   → x' ⊑⟨ obj (Payload t) (𝓓 n) ⟩ x → Pay n e x → Pay n e x'
 Tup-mono : (n : ℕ) {Δ : Ctx} (vs : All Val Δ) (xs xs' : Fin (length Δ) → ⟨ 𝓓 n ⟩)
   → ((i : Fin (length Δ)) → xs' i ⊑⟨ 𝓓 n ⟩ xs i) → Tup n vs xs → Tup n vs xs'
 Fn-mono : (n : ℕ) {Δ : Ctx} {A B : Type} (s s' : ⟨ 𝓓 n ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ))
   → s' ⊑⟨ 𝓓 n ⟩ s → Fn n s f e → Fn n s' f e
 Ev-mono : (n : ℕ) {B : Type} (s s' : ⟨ 𝓓 n ⟩) (c : ℕ → Result (Val B)) → s' ⊑⟨ 𝓓 n ⟩ s → Ev n s c → Ev n s' c

 R-mono zero s s' v le h = ⋆
 R-mono (succ n) s s' v (f , g) h p' = Match-mono n (value s (f p')) (value s' p') v (g p') (h (f p'))

 Match-mono n (t , x) (.t , x') v (refl , le) (e , m) = e , Pay-mono n e x x' le m

 Pay-mono n s-con x x' le m = ⋆
 Pay-mono n (s-tup {vs = vs}) xs xs' le m = Tup-mono n vs xs xs' le m
 Pay-mono n (s-left {v = v}) x x' le m = R-mono n x x' v le m
 Pay-mono n (s-right {v = v}) x x' le m = R-mono n x x' v le m
 Pay-mono n (s-pack {c = c} {e}) xy xy' le (r₀ , r₁) =
   R-mono n (xy zero) (xy' zero) c (le zero) r₀ , R-mono n (xy (suc zero)) (xy' (suc zero)) e (le (suc zero)) r₁
 Pay-mono n (s-code {f = f}) h h' le m x e r = Fn-mono n (h · x) (h' · x) f e (le x) (m x e r)
 Pay-mono n (s-fold e) x x' le m = Pay-mono n e x x' le m

 Tup-mono n [] xs xs' le m = ⋆
 Tup-mono n (v ∷ vs) xs xs' le (r , m) =
   R-mono n (xs zero) (xs' zero) v (le zero) r , Tup-mono n vs _ _ (λ i → le (suc i)) m

 Fn-mono zero s s' f e le h = ⋆
 Fn-mono (succ n) s s' f e (g , g') h p' = FnV-mono (value s (g p')) (value s' p') (g' p') (h (g p'))
  where
   FnV-mono : (u u' : ⟨ obj VF (𝓓 n) ⟩) → u' ⊑⟨ obj VF (𝓓 n) ⟩ u → FnV n u f e → FnV n u' f e
   FnV-mono (t , x) (.t , x') (refl , le) (is-fun , m) =
     is-fun , (λ y a r → Ev-mono n (x · y) (x' · y) (Call f e a) (le y) (m y a r))

 Ev-mono zero s s' c le h = ⋆
 Ev-mono (succ n) s s' c (f , g) h p' =
   let (v , t , m) = h (f p') in v , t , Match-mono n (value s (f p')) (value s' p') v (g p') m

 {- Admissible: closed under directed sups of the approximation ------------------------}

 R-sup : (n : ℕ) {A : Type} (v : Val A) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩) (δ : is-Directed (𝓓 n) α)
   → ((i : I) → R n (α i) v) → R n (∐ (𝓓 n) {I} {α} δ) v
 Match-sup : (n : ℕ) {A : Type} (v : Val A) {K : 𝓤₀ ̇ } (β : K → ⟨ obj VF (𝓓 n) ⟩)
   (ε : is-Directed (obj VF (𝓓 n)) β) → ((k : K) → Match n (β k) v) → Match n (∐ (obj VF (𝓓 n)) {K} {β} ε) v
 Pay-sup : (n : ℕ) {t : Tag} {A : Type} {v : Val A} (e : Shape t v) {I : 𝓤₀ ̇ }
   (β : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (δ : is-Directed (obj (Payload t) (𝓓 n)) β)
   → ((i : I) → Pay n e (β i)) → Pay n e (∐ (obj (Payload t) (𝓓 n)) {I} {β} δ)
 Tup-sup : (n : ℕ) {Δ : Ctx} (vs : All Val Δ) {I : 𝓤₀ ̇ } (β : I → Fin (length Δ) → ⟨ 𝓓 n ⟩)
   (δs : (i : Fin (length Δ)) → is-Directed (𝓓 n) (λ j → β j i))
   → ((j : I) → Tup n vs (β j)) → Tup n vs (λ i → ∐ (𝓓 n) (δs i))
 Fn-sup : (n : ℕ) {Δ : Ctx} {A B : Type} (f : Σ ∋ sig Δ A B) (e : Val (tup Δ)) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩)
   (δ : is-Directed (𝓓 n) α) → ((i : I) → Fn n (α i) f e) → Fn n (∐ (𝓓 n) {I} {α} δ) f e
 Ev-sup : (n : ℕ) {B : Type} (c : ℕ → Result (Val B)) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩)
   (δ : is-Directed (𝓓 n) α) → ((i : I) → Ev n (α i) c) → Ev n (∐ (𝓓 n) {I} {α} δ) c

 R-sup zero v α δ h = ⋆
 R-sup (succ n) v α δ h = stage-sup-ind n α δ (λ u → Match n u v) (Match-sup n v) h

 Match-sup n v β ε h =
   Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n)) (λ t x → Match n (t , x) v) Q-sup β ε h
  where
   Q-sup : (t : Tag) {I : 𝓤₀ ̇ } (β' : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (δ : is-Directed (obj (Payload t) (𝓓 n)) β')
     → ((i : I) → Match n (t , β' i) v) → Match n (t , ∐ (obj (Payload t) (𝓓 n)) {I} {β'} δ) v
   Q-sup t β' δ h' =
     ∥∥-rec (Match-prop n _ v)
       (λ i → pr₁ (h' i) , Pay-sup n (pr₁ (h' i)) β' δ (λ j → Pay-at (pr₁ (h' i)) (h' j)))
       (inhabited-if-Directed (obj (Payload t) (𝓓 n)) β' δ)

 Pay-sup n s-con β δ h = ⋆
 Pay-sup n (s-tup {vs = vs}) β δ h = Tup-sup n vs β (component-is-directed (Fin _) (𝓓 n) β δ) h
 Pay-sup n (s-left {v = v}) β δ h = R-sup n v β δ h
 Pay-sup n (s-right {v = v}) β δ h = R-sup n v β δ h
 Pay-sup n (s-pack {c = c} {e}) β δ h =
   R-sup n c (λ j → β j zero) (component-is-directed (Fin 2) (𝓓 n) β δ zero) (λ j → pr₁ (h j)) ,
   R-sup n e (λ j → β j (suc zero)) (component-is-directed (Fin 2) (𝓓 n) β δ (suc zero)) (λ j → pr₂ (h j))
 Pay-sup n (s-code {f = f}) β δ h x e r =
   Fn-sup n f e (λ j → β j · x) (pointwise-directed (𝓓 n) (𝓓 n) β δ x) (λ j → h j x e r)
 Pay-sup n (s-fold e) β δ h = Pay-sup n e β δ h

 Tup-sup n [] β δs h = ⋆
 Tup-sup n (v ∷ vs) β δs h =
   R-sup n v (λ j → β j zero) (δs zero) (λ j → pr₁ (h j)) ,
   Tup-sup n vs (λ j i → β j (suc i)) (λ i → δs (suc i)) (λ j → pr₂ (h j))

 Fn-sup zero f e α δ h = ⋆
 Fn-sup (succ n) {A = A} f e α δ h = stage-sup-ind n α δ (λ u → FnV n u f e) FnV-sup h
  where
   FnV-sup : {K : 𝓤₀ ̇ } (β : K → ⟨ obj VF (𝓓 n) ⟩) (ε : is-Directed (obj VF (𝓓 n)) β)
     → ((k : K) → FnV n (β k) f e) → FnV n (∐ (obj VF (𝓓 n)) {K} {β} ε) f e
   FnV-sup β ε hβ =
     Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n)) (λ t x → FnV n (t , x) f e) Q-sup β ε hβ
    where
     Q-sup : (t : Tag) {I : 𝓤₀ ̇ } (β' : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (δ' : is-Directed (obj (Payload t) (𝓓 n)) β')
       → ((i : I) → FnV n (t , β' i) f e) → FnV n (t , ∐ (obj (Payload t) (𝓓 n)) {I} {β'} δ') f e
     Q-sup t β' δ' h' =
       ∥∥-rec (Σ-is-prop IsFun-prop (λ i → Pay₂-prop n i _ f e))
         (λ i → pr₁ (h' i) , sup₂ (pr₁ (h' i)) β' δ' (λ j → Pay₂-at (pr₁ (h' i)) (h' j)))
         (inhabited-if-Directed (obj (Payload t) (𝓓 n)) β' δ')
      where
       sup₂ : ∀ {t} (i : IsFun t) {I : 𝓤₀ ̇ } (β' : I → ⟨ obj (Payload t) (𝓓 n) ⟩)
         (δ' : is-Directed (obj (Payload t) (𝓓 n)) β') → ((j : I) → Pay₂ n i (β' j) f e)
         → Pay₂ n i (∐ (obj (Payload t) (𝓓 n)) {I} {β'} δ') f e
       sup₂ is-fun β' δ' h₂ y a r =
         Ev-sup n (Call f e a) (λ j → β' j · y) (pointwise-directed (𝓓 n) (𝓓 n) β' δ' y) (λ j → h₂ j y a r)

 Ev-sup zero c α δ h = ⋆
 Ev-sup (succ n) {B} c α δ h = stage-sup-ind n α δ (λ u → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Match n u v) Res-sup h
  where
   Res-sup : {K : 𝓤₀ ̇ } (β : K → ⟨ obj VF (𝓓 n) ⟩) (ε : is-Directed (obj VF (𝓓 n)) β)
     → ((k : K) → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Match n (β k) v)
     → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Match n (∐ (obj VF (𝓓 n)) {K} {β} ε) v
   Res-sup {K} β ε hβ =
     ∥∥-rec (Σ⇓-prop {c = c} (Match n u) (Match-prop n u)) go (inhabited-if-Directed (obj VF (𝓓 n)) β ε)
    where
     u = ∐ (obj VF (𝓓 n)) {K} {β} ε
     go : K → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Match n u v
     go k₀ = let (v , t , _) = hβ k₀ in v , t , Match-sup n v β ε (λ k → Res→Match (hβ k) t)

 {- Moving between stages -------------------------------------------------------------}

 R-π : (n : ℕ) {A : Type} (s : ⟨ 𝓓 (succ n) ⟩) (v : Val A) → R (succ n) s v → R n (π n s) v
 R-ε : (n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Val A) → R n s v → R (succ n) (ε n s) v
 Pay-π : (n : ℕ) {t : Tag} {A : Type} {v : Val A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 (succ n)) ⟩)
   → Pay (succ n) e x → Pay n e (fmap (Payload t) (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) x)
 Pay-ε : (n : ℕ) {t : Tag} {A : Type} {v : Val A} (e : Shape t v) (x : ⟨ obj (Payload t) (𝓓 n) ⟩)
   → Pay n e x → Pay (succ n) e (fmap (Payload t) (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) x)
 Tup-π : (n : ℕ) {Δ : Ctx} (vs : All Val Δ) (xs : Fin (length Δ) → ⟨ 𝓓 (succ n) ⟩)
   → Tup (succ n) vs xs → Tup n vs (λ i → π n (xs i))
 Tup-ε : (n : ℕ) {Δ : Ctx} (vs : All Val Δ) (xs : Fin (length Δ) → ⟨ 𝓓 n ⟩)
   → Tup n vs xs → Tup (succ n) vs (λ i → ε n (xs i))
 Fn-π : (n : ℕ) {Δ : Ctx} {A B : Type} (s : ⟨ 𝓓 (succ n) ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ))
   → Fn (succ n) s f e → Fn n (π n s) f e
 Fn-ε : (n : ℕ) {Δ : Ctx} {A B : Type} (s : ⟨ 𝓓 n ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ))
   → Fn n s f e → Fn (succ n) (ε n s) f e
 Ev-π : (n : ℕ) {B : Type} (s : ⟨ 𝓓 (succ n) ⟩) (c : ℕ → Result (Val B)) → Ev (succ n) s c → Ev n (π n s) c
 Ev-ε : (n : ℕ) {B : Type} (s : ⟨ 𝓓 n ⟩) (c : ℕ → Result (Val B)) → Ev n s c → Ev (succ n) (ε n s) c

 R-π zero s v h = ⋆
 R-π (succ n) s v h = transport (λ - → R (succ n) - v) (π-succ n s ⁻¹) (λ p →
   pr₁ (h p) , Pay-π n (pr₁ (h p)) (pr₂ (value s p)) (pr₂ (h p)))

 R-ε zero s v h p = 𝟘-elim (ε-zero-undefined s p)
 R-ε (succ n) s v h = transport (λ - → R (succ (succ n)) - v) (ε-succ n s ⁻¹) (λ p →
   pr₁ (h p) , Pay-ε n (pr₁ (h p)) (pr₂ (value s p)) (pr₂ (h p)))

 Pay-π n s-con x m = ⋆
 Pay-π n (s-tup {vs = vs}) xs m = Tup-π n vs xs m
 Pay-π n (s-left {v = v}) x m = R-π n x v m
 Pay-π n (s-right {v = v}) x m = R-π n x v m
 Pay-π n (s-pack {c = c} {e}) xy (r₀ , r₁) = R-π n (xy zero) c r₀ , R-π n (xy (suc zero)) e r₁
 Pay-π n (s-code {f = f}) h m x e r = Fn-π n (h · ε n x) f e (m (ε n x) e (R-ε n x e r))
 Pay-π n (s-fold e) x m = Pay-π n e x m

 Pay-ε n s-con x m = ⋆
 Pay-ε n (s-tup {vs = vs}) xs m = Tup-ε n vs xs m
 Pay-ε n (s-left {v = v}) x m = R-ε n x v m
 Pay-ε n (s-right {v = v}) x m = R-ε n x v m
 Pay-ε n (s-pack {c = c} {e}) xy (r₀ , r₁) = R-ε n (xy zero) c r₀ , R-ε n (xy (suc zero)) e r₁
 Pay-ε n (s-code {f = f}) h m x e r = Fn-ε n (h · π n x) f e (m (π n x) e (R-π n x e r))
 Pay-ε n (s-fold e) x m = Pay-ε n e x m

 Tup-π n [] xs m = ⋆
 Tup-π n (v ∷ vs) xs (r , m) = R-π n (xs zero) v r , Tup-π n vs (λ i → xs (suc i)) m

 Tup-ε n [] xs m = ⋆
 Tup-ε n (v ∷ vs) xs (r , m) = R-ε n (xs zero) v r , Tup-ε n vs (λ i → xs (suc i)) m

 Fn-π zero s f e h = ⋆
 Fn-π (succ n) s f e h = transport (λ - → Fn (succ n) - f e) (π-succ n s ⁻¹) (λ p → FnV-π (value s p) (h p))
  where
   FnV-π : (u : ⟨ obj VF (𝓓 (succ n)) ⟩) → FnV (succ n) u f e
     → FnV n (fmap VF (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) u) f e
   FnV-π (.fun , x) (is-fun , m) = is-fun , (λ y a r → Ev-π n (x · ε n y) (Call f e a) (m (ε n y) a (R-ε n y a r)))

 Fn-ε zero s f e h p = 𝟘-elim (ε-zero-undefined s p)
 Fn-ε (succ n) s f e h = transport (λ - → Fn (succ (succ n)) - f e) (ε-succ n s ⁻¹) (λ p → FnV-ε (value s p) (h p))
  where
   FnV-ε : (u : ⟨ obj VF (𝓓 n) ⟩) → FnV n u f e → FnV (succ n) (fmap VF (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) u) f e
   FnV-ε (.fun , x) (is-fun , m) = is-fun , (λ y a r → Ev-ε n (x · π n y) (Call f e a) (m (π n y) a (R-π n y a r)))

 Ev-π zero s c h = ⋆
 Ev-π (succ n) s c h = transport (λ - → Ev (succ n) - c) (π-succ n s ⁻¹) (λ p →
   let (v , t , e , m) = h p in v , t , e , Pay-π n e (pr₂ (value s p)) m)

 Ev-ε zero s c h p = 𝟘-elim (ε-zero-undefined s p)
 Ev-ε (succ n) s c h = transport (λ - → Ev (succ (succ n)) - c) (ε-succ n s ⁻¹) (λ p →
   let (v , t , e , m) = h p in v , t , e , Pay-ε n e (pr₂ (value s p)) m)

 R-πs : (k n : ℕ) {A : Type} (s : ⟨ 𝓓 (k + n) ⟩) (v : Val A) → R (k + n) s v → R n (πs k n s) v
 R-πs zero n s v h = h
 R-πs (succ k) n s v h = R-πs k n (π (k + n) s) v (R-π (k + n) s v h)

 R-εs : (k n : ℕ) {A : Type} (s : ⟨ 𝓓 n ⟩) (v : Val A) → R n s v → R (k + n) (εs k n s) v
 R-εs zero n s v h = h
 R-εs (succ k) n s v h = R-ε (k + n) (εs k n s) v (R-εs k n s v h)

 Fn-πs : (k n : ℕ) {Δ : Ctx} {A B : Type} (s : ⟨ 𝓓 (k + n) ⟩) (f : Σ ∋ sig Δ A B) (e : Val (tup Δ))
   → Fn (k + n) s f e → Fn n (πs k n s) f e
 Fn-πs zero n s f e h = h
 Fn-πs (succ k) n s f e h = Fn-πs k n (π (k + n) s) f e (Fn-π (k + n) s f e h)

 {- The relation between elements of 𝔻 and values: every approximation is related -------}

 record Rel {A : Type} (d : ⟨ 𝔻 ⟩) (v : Val A) : 𝓤₁ ̇ where
   constructor rel
   field stage : (n : ℕ) → R n (π∞ n · d) v
 open Rel public

 Rel-prop : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Val A} → is-prop (Rel d v)
 Rel-prop {d = d} {v} (rel f) (rel g) = ap rel (dfunext fe (λ n → R-prop n (π∞ n · d) v (f n) (g n)))

 Rel-ε : ∀ {A} (n : ℕ) {s : ⟨ 𝓓 n ⟩} {v : Val A} → R n s v → Rel (ε∞ n · s) v
 Rel-ε n {s} {v} h = rel λ m → go m (split m n)
  where
   down : (m k n : ℕ) → n ＝ k + m → (s : ⟨ 𝓓 n ⟩) → R n s v → R m (π∞ m · (ε∞ n · s)) v
   down m k .(k + m) refl s h = transport (λ - → R m - v) (π∞-ε∞-down k m s ⁻¹) (R-πs k m s v h)
   up : (k m : ℕ) → m ＝ k + n → R m (π∞ m · (ε∞ n · s)) v
   up k .(k + n) refl = transport (λ - → R (k + n) - v) (π∞-ε∞-up k n s ⁻¹) (R-εs k n s v h)
   go : (m : ℕ) → Split m n → R m (π∞ m · (ε∞ n · s)) v
   go m (lower k e) = down m k n e s h
   go m (higher k e) = up k m e

 approx : (n : ℕ) (t : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t) (𝓓 n) ⟩
 approx n t x = fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x

 Rel-inj : ∀ {t A} {v : Val A} (x : ⟨ obj (Payload t) 𝔻 ⟩) (e : Shape t v)
   → ((n : ℕ) → Pay n e (approx n t x)) → Rel (inj t · x) v
 Rel-inj {t} {v = v} x e h = rel λ
   { zero → ⋆
   ; (succ n) → transport (λ - → R (succ n) - v) (π∞-inj n t x ⁻¹) (λ _ → e , h n) }

 Inv : ∀ {A} → ⟨ 𝔻 ⟩ → Val A → 𝓤₁ ̇
 Inv {A} d v = Σ t ꞉ Tag , Σ x ꞉ ⟨ obj (Payload t) 𝔻 ⟩ , (d ＝ inj t · x) × (Σ e ꞉ Shape t v , ((n : ℕ) → Pay n e (approx n t x)))

 Rel-inv : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Val A} → Rel d v → defined d → Inv d v
 Rel-inv {d = d} {v} r q = t , x , inj-view d q , pr₁ (V 0) , (λ n → Pay-at (pr₁ (V 0)) (V n))
  where
   t = pr₁ (view d q)
   x = pr₂ (view d q)
   V : (n : ℕ) → Match n (t , approx n t x) v
   V n = transport (λ - → R (succ n) - v) (π∞-inj n t x)
           (stage (transport (λ - → Rel - v) (inj-view d q) r) (succ n)) ⋆

 Rel-fold : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Val (unrollᵗ A)} → Rel d v → Rel d (fold {A} v)
 Rel-fold r = rel λ { zero → ⋆ ; (succ n) p → s-fold (pr₁ (stage r (succ n) p)) , pr₂ (stage r (succ n) p) }

 private
  unfold-Match : ∀ {n A} {u : ⟨ obj VF (𝓓 n) ⟩} {v : Val (unrollᵗ A)} → Match n u (fold {A} v) → Match n u v
  unfold-Match (s-fold e , m) = e , m

 Rel-unfold : ∀ {A} {d : ⟨ 𝔻 ⟩} (v : Val (μ A)) → Rel d v → Rel d (unfold-v v)
 Rel-unfold (fold v) r = rel λ { zero → ⋆ ; (succ n) p → unfold-Match (stage r (succ n) p) }

 {- only a defined element needs to be related -}
 Rel-from-defined : ∀ {A} {d : ⟨ 𝔻 ⟩} {v : Val A} → (defined d → Rel d v) → Rel d v
 Rel-from-defined {d = d} h = rel λ { zero → ⋆ ; (succ n) p → stage (h (π∞-defined n d p)) (succ n) p }

 Rel-⊥ : ∀ {A} {v : Val A} → Rel ⊥𝔻 v
 Rel-⊥ = Rel-from-defined (λ q → 𝟘-elim (⊥-undefined q))

 {- Related results -------------------------------------------------------------------}

 {- if d is defined, c returns a value related to d -}
 RelE : ∀ {B} → ⟨ 𝔻 ⟩ → (ℕ → Result (Val B)) → 𝓤₁ ̇
 RelE {B} d c = defined d → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Rel d v

 RelE-＝ : ∀ {B} {d d' : ⟨ 𝔻 ⟩} {c : ℕ → Result (Val B)} → d ＝ d' → RelE d' c → RelE d c
 RelE-＝ refl h = h

 strict-is : (h : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩) → strict · h · a ＝ seq · a · (h · a)
 strict-is h a = refl

 RelE-strict : ∀ {B} {c : ℕ → Result (Val B)} (g : DCPO[ 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩)
   → (defined d → RelE (g · d) c) → RelE (strict · g · d) c
 RelE-strict {c = c} g d h q = RelE-＝ {c = c} (strict-defined g d q') (h q') q
  where
   q' = seq-defined-l d (g · d) (transport defined (strict-is g d) q)

 Ev-from-RelE : ∀ {B} {d : ⟨ 𝔻 ⟩} {c : ℕ → Result (Val B)} → RelE d c → (n : ℕ) → Ev n (π∞ n · d) c
 Ev-from-RelE h zero = ⋆
 Ev-from-RelE {d = d} h (succ n) p = let (v , t , r) = h (π∞-defined n d p) in v , t , stage r (succ n) p

 {- the results on the approximations e k a of a, related at depth k, give a
    result related to the result on a, their sup -}
 lim : ∀ {B} {c : ℕ → Result (Val B)} (f : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩)
   → ((k : ℕ) → Ev k (π∞ k · (f · e k a)) c) → RelE (f · a) c
 lim {B} {c} f a h q = ∥∥-rec (Σ⇓-prop {c = c} (Rel (f · a)) (λ v → Rel-prop)) found some
  where
   g : (n : ℕ) → DCPO[ 𝔻 , 𝓓 n ]
   g n = ∘₁ 𝔻 𝔻 (𝓓 n) f (π∞ n)
   δ : (n : ℕ) → is-Directed (𝓓 n) (λ k → g n · e k a)
   δ n = image-is-directed' 𝔻 (𝓓 n) (g n) {ℕ} {λ k → e k a} (e-directed a)
   sup : (n : ℕ) → π∞ n · (f · a) ＝ ∐ (𝓓 n) (δ n)
   sup n = approx-∐ (𝓓 n) (g n) a
   some : ∥ Σ k ꞉ ℕ , defined (f · e k a) ∥
   some = ∥∥-functor (λ (k , p) → k , π∞-defined 0 (f · e k a) p)
            (stage-sup-defined 0 (λ k → g 1 · e k a) (δ 1)
               (transport is-defined (sup 1) (defined-π∞ 0 (f · a) q)))
   found : (Σ k ꞉ ℕ , defined (f · e k a)) → Σ v ꞉ Val B , ∥ c ⇓ v ∥ × Rel (f · a) v
   found (k , qk) = v , t , rel stages
    where
     qK : defined (f · e (succ k) a)
     qK = defined-mono _ _ (monotone-if-continuous 𝔻 𝔻 f _ _ (e-mono a k (succ k) (≤-succ k))) qk
     v = pr₁ (h (succ k) (defined-π∞ k _ qK))
     t = pr₁ (pr₂ (h (succ k) (defined-π∞ k _ qK)))
     below : (n k : ℕ) → R n (π∞ n · (f · e k a)) v
     below n k = R-mono n (π∞ n · (f · e (k + n) a)) (π∞ n · (f · e k a)) v
                   (monotone-if-continuous 𝔻 (𝓓 n) (g n) _ _ (e-mono a k (k + n) (≤+ k n)))
                   (transport (λ - → R n - v) (πs-π∞ k n (f · e (k + n) a))
                      (R-πs k n _ v (Ev→R {c = c} (h (k + n)) t)))
     stages : (n : ℕ) → R n (π∞ n · (f · a)) v
     stages n = transport (λ - → R n - v) (sup n ⁻¹) (R-sup n v (λ k → g n · e k a) (δ n) (below n))

 {- Calls of code pointers -----------------------------------------------------------------}

 {- every approximation of G is a function value that calls f on e -}
 RelFn : ∀ {Δ A B} → ⟨ 𝔻 ⟩ → Σ ∋ sig Δ A B → Val (tup Δ) → 𝓤₁ ̇
 RelFn G f e = (n : ℕ) → Fn n (π∞ n · G) f e

 {- as lim, for the first application of a call -}
 lim₁ : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} {env : Val (tup Δ)} (h : DCPO[ 𝔻 , 𝔻 ]) (X : ⟨ 𝔻 ⟩)
   → ((k : ℕ) → Fn k (π∞ k · (h · e k X)) f env) → RelFn (h · X) f env
 lim₁ {f = f} {env = e'} h X hk n =
   transport (λ - → Fn n - f e') (approx-∐ (𝓓 n) (g n) X ⁻¹) (Fn-sup n f e' (λ k → g n · e k X) (δ n) below)
  where
   g : (n : ℕ) → DCPO[ 𝔻 , 𝓓 n ]
   g n = ∘₁ 𝔻 𝔻 (𝓓 n) h (π∞ n)
   δ : (n : ℕ) → is-Directed (𝓓 n) (λ k → g n · e k X)
   δ n = image-is-directed' 𝔻 (𝓓 n) (g n) {ℕ} {λ k → e k X} (e-directed X)
   below : (k : ℕ) → Fn n (π∞ n · (h · e k X)) f e'
   below k = Fn-mono n (π∞ n · (h · e (k + n) X)) (π∞ n · (h · e k X)) f e'
               (monotone-if-continuous 𝔻 (𝓓 n) (g n) _ _ (e-mono X k (k + n) (≤+ k n)))
               (transport (λ - → Fn n - f e') (πs-π∞ k n (h · e (k + n) X)) (Fn-πs k n _ f e' (hk (k + n))))

 {- a defined G with RelFn is a function value whose payload calls f on e -}
 RelFn-inv : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} {e : Val (tup Δ)} {G : ⟨ 𝔻 ⟩} → RelFn G f e → defined G
   → Σ h₂ ꞉ DCPO[ 𝔻 , 𝔻 ] , (G ＝ inj fun · h₂) × ((n : ℕ) → Pay₂ n is-fun (approx n fun h₂) f e)
 RelFn-inv {f = f} {e} {G} hG q = go t x (inj-view G q) V (pr₁ (V 0))
  where
   t = pr₁ (view G q)
   x = pr₂ (view G q)
   V : (n : ℕ) → FnV n (t , approx n t x) f e
   V n = transport (λ - → Fn (succ n) - f e) (ap (π∞ (succ n) ·_) (inj-view G q) ∙ π∞-inj n t x) (hG (succ n)) ⋆
   go : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → G ＝ inj t · x → ((n : ℕ) → FnV n (t , approx n t x) f e) → IsFun t
     → Σ h₂ ꞉ DCPO[ 𝔻 , 𝔻 ] , (G ＝ inj fun · h₂) × ((n : ℕ) → Pay₂ n is-fun (approx n fun h₂) f e)
   go .fun x eqx V is-fun = x , eqx , (λ n → Pay₂-at is-fun (V n))

 {- a function value whose payload calls f on e -}
 RelFn-inj : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} {e : Val (tup Δ)} (h₂ : DCPO[ 𝔻 , 𝔻 ]) (G : ⟨ 𝔻 ⟩)
   → (defined G → G ＝ inj fun · h₂) → ((n : ℕ) → Pay₂ n is-fun (approx n fun h₂) f e) → RelFn G f e
 RelFn-inj h₂ G eqd h zero = ⋆
 RelFn-inj {f = f} {e} h₂ G eqd h (succ n) p =
   transport (λ - → Fn (succ n) - f e) ((ap (π∞ (succ n) ·_) (eqd (π∞-defined n G p)) ∙ π∞-inj n fun h₂) ⁻¹)
     (λ _ → is-fun , h n) p

 app-inj : (h : DCPO[ 𝔻 , 𝔻 ]) (a : ⟨ 𝔻 ⟩) → appᵈ · (inj fun · h) · a ＝ strict · h · a
 app-inj h a = ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br fun h)

 {- a call: the code applied to the environment, then to the argument -}
 call-rel : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} {e : Val (tup Δ)} {a : Val A} {F X Y : ⟨ 𝔻 ⟩}
   → Rel F (code f) → Rel X e → Rel Y a → RelE (appᵈ · (appᵈ · F · X) · Y) (Call f e a)
 call-rel {f = f} {e} {a} {F} {X} {Y} rF rX rY q = inv-case (Rel-inv rF qF)
  where
   qG : defined (appᵈ · F · X)
   qG = app-defined (appᵈ · F · X) Y q
   qF : defined F
   qF = app-defined F X qG
   inv-case : Inv F (code f) → Σ v ꞉ Val _ , ∥ Call f e a ⇓ v ∥ × Rel (appᵈ · (appᵈ · F · X) · Y) v
   inv-case (_ , h , eqF , s-code , mF) = RelE-＝ {c = Call f e a} eq₃ (lim h₂ Y (λ k → m₂ k (π∞ k · Y) a (stage rY k))) q
    where
     eq₁ : appᵈ · F · X ＝ strict · h · X
     eq₁ = ap (λ - → appᵈ · - · X) eqF ∙ app-inj h X
     qX : defined X
     qX = seq-defined-l X (h · X) (transport defined (eq₁ ∙ strict-is h X) qG)
     eqG : appᵈ · F · X ＝ h · X
     eqG = eq₁ ∙ strict-defined h X qX
     inv = RelFn-inv {f = f} {e} {h · X} (lim₁ {f = f} {env = e} h X (λ k → mF k (π∞ k · X) e (stage rX k)))
             (transport defined eqG qG)
     h₂ = pr₁ inv
     m₂ = pr₂ (pr₂ inv)
     eq₂ : appᵈ · (appᵈ · F · X) · Y ＝ strict · h₂ · Y
     eq₂ = ap (λ - → appᵈ · - · Y) (eqG ∙ pr₁ (pr₂ inv)) ∙ app-inj h₂ Y
     eq₃ : appᵈ · (appᵈ · F · X) · Y ＝ h₂ · Y
     eq₃ = eq₂ ∙ strict-defined h₂ Y (seq-defined-l Y (h₂ · Y) (transport defined (eq₂ ∙ strict-is h₂ Y) q))
