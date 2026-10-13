open import Data.List using (List; replicate)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-pred)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; sym; trans; cong)
open import Framework.abt.Sig using (Sig; ■; ν)
open import Framework.Syntax.SigUtil using (ν-n)

{-
  Substitution preserves well-scopedness (WS, Syntax.Scope).
-}
module proof.Framework.Syntax.ScopeSubst (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)
open import proof.Framework.Syntax.ScopeRename Op sig using (WS; WS-arg; WS-args; ws-shift)
open import Framework.Syntax.Subst Op sig using (Subst; sub; sub-arg; sub-args; exts; extend; _•_)

{- σ maps the variables below k to terms with the property P -}
Below : (AST → Set) → ℕ → Subst → Set
Below P k σ = ∀ x → x < k → P (σ x)

{- one more term, for variable 0 -}
below-• : ∀ {P k σ V} → P V → Below P k σ → Below P (suc k) (V • σ)
below-• p h zero _ = p
below-• p h (suc y) (s≤s y<) = h y y<

{- σ maps the variables below k to terms well scoped in j -}
SFits : ℕ → ℕ → Subst → Set
SFits k j σ = Below (WS j) k σ

sfits-• : ∀ {k j σ V} → WS j V → SFits k j σ → SFits (suc k) j (V • σ)
sfits-• = below-• {P = WS _}

sfits-exts : ∀ {k j σ} → SFits k j σ → SFits (suc k) (suc j) (exts σ)
sfits-exts h zero _ = s≤s z≤n
sfits-exts {σ = σ} h (suc x) (s≤s x<) = ws-shift (σ x) (h x x<)

ws-sub : ∀ {k j} σ M → SFits k j σ → WS k M → WS j (sub σ M)
ws-sub-arg : ∀ {k j b} σ (a : Arg b) → SFits k j σ → WS-arg k a → WS-arg j (sub-arg σ a)
ws-sub-args : ∀ {k j bs} σ (as : Args bs) → SFits k j σ → WS-args k as → WS-args j (sub-args σ as)
ws-sub σ (` x) h w = h x w
ws-sub σ (op ⦅ as ⦆) h w = ws-sub-args σ as h w
ws-sub-arg σ (ast M) h w = ws-sub σ M h w
ws-sub-arg σ (bind a) h w = ws-sub-arg (exts σ) a (sfits-exts h) w
ws-sub-arg σ (clear a) h w = w
ws-sub-args σ nil h w = tt
ws-sub-args σ (cons a as) h (w , ws) = ws-sub-arg σ a h w , ws-sub-args σ as h ws

{- σ extended by well-scoped operands -}
sfits-extend : ∀ {n k j σ} (Ms : Args (replicate n ■)) → WS-args j Ms → SFits k j σ
  → SFits (n + k) j (extend Ms σ)
sfits-extend {zero} nil _ h = h
sfits-extend {suc n} {k} (cons (ast M) Ms) (w , ws) h x x< =
  sfits-extend Ms ws (sfits-• w h) x (subst (x <_) (sym (+-suc n k)) x<)

{- the operands Ms alone -}
sfits-extend₀ : ∀ {n j σ} (Ms : Args (replicate n ■)) → WS-args j Ms → SFits n j (extend Ms σ)
sfits-extend₀ {n} Ms ws x x< = sfits-extend Ms ws (λ _ ()) x (subst (x <_) (sym (+-identityʳ n)) x<)

{- the body under n + 1 binders, taken out by unbind (and put back by
   bnd), for any such functions: each language's, whose equations hold by
   refl -}
module Unbind (unbind : ∀ n → Arg (ν-n n (ν ■)) → AST)
  (unbind-0 : ∀ N → unbind 0 (bind (ast N)) ≡ N) (unbind-s : ∀ n a → unbind (suc n) (bind a) ≡ unbind n a) where

  ws-unbind : ∀ n {k} (a : Arg (ν-n n (ν ■))) → WS-arg k a → WS (suc (n + k)) (unbind n a)
  ws-unbind zero (bind (ast N)) w = subst (WS _) (sym (unbind-0 N)) w
  ws-unbind (suc n) {k} (bind a) w = subst₂ (λ x M → WS (suc x) M) (+-suc n k) (sym (unbind-s n a)) (ws-unbind n a w)

  {- of a cleared argument -}
  ws-unbind₀ : ∀ n (a : Arg (ν-n n (ν ■))) → WS-arg 0 a → WS (suc n) (unbind n a)
  ws-unbind₀ n a w = subst (λ y → WS (suc y) (unbind n a)) (+-identityʳ n) (ws-unbind n a w)

  unbind-bind : (bnd : ∀ n → AST → Arg (ν-n n (ν ■))) → (∀ N → bnd 0 N ≡ bind (ast N))
    → (∀ n N → bnd (suc n) N ≡ bind (bnd n N)) → ∀ m N → unbind m (bnd m N) ≡ N
  unbind-bind bnd b0 bs zero N = trans (cong (unbind 0) (b0 N)) (unbind-0 N)
  unbind-bind bnd b0 bs (suc m) N =
    trans (cong (unbind (suc m)) (bs m N)) (trans (unbind-s m (bnd m N)) (unbind-bind bnd b0 bs m N))
