{-

  Correctness of delay, the backward half: the operators of Clos3μ and
  Clos4μ preserve the relation Refl of DelayReflect.agda; closures and
  calls are the cases where the two languages differ (Refl-clos,
  Refl-call). As DelayPreserve.agda's lemmas for the forward half.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Base using (transport₂; ap₂)

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Prim; Out; int; bool; δ)
open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)
open import Naturals.Order
open import Notation.Order
import Data.Nat as Nat
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.Scott.DelayReflectOps
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.StageCall pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)
open import Mu.proof.Correctness.Scott.DelayReflect pt fe pe

{- Making and taking apart related values -----------------------------------------}

{- the approximation of depth n of a payload -}
approx : (n : ℕ) (t : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t) (𝓓 n) ⟩
approx n t x = fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x

Refl-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → Refl (inj t · x) (inj t' · y)
Refl-inj t x t' y h zero = ⋆
Refl-inj t x t' y h (succ n) =
  transport (λ - → Rf (succ n) (inj t · x) -) (π∞-inj n t' y ⁻¹)
    (λ p → defined-inj t x ,
           transport (λ v → MatchR n (pr₁ v) t' (pr₂ v) (approx n t' y)) (view-inj t x (defined-inj t x) ⁻¹) (h n))

{- only a defined target needs to be related -}
Refl-from-defined : (d d' : ⟨ 𝔻 ⟩) → (defined d' → Refl d d') → Refl d d'
Refl-from-defined d d' h zero = ⋆
Refl-from-defined d d' h (succ n) p = h (π∞-defined n d' p) (succ n) p

Refl-⊥ : (d : ⟨ 𝔻 ⟩) → Refl d ⊥𝔻
Refl-⊥ d = Refl-from-defined d ⊥𝔻 (λ q → 𝟘-elim (⊥-undefined q))

{- a defined target has a defined source -}
Refl-defined : (d d' : ⟨ 𝔻 ⟩) → Refl d d' → defined d' → defined d
Refl-defined d d' h q = pr₁ (h 1 (defined-π∞ 0 d' q))

Refl-view : (d : ⟨ 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩) → Refl d (inj t' · y) → (q : defined d)
  → (n : ℕ) → MatchR n (pr₁ (view d q)) t' (pr₂ (view d q)) (approx n t' y)
Refl-view d t' y h q n =
  transport (λ q' → MatchR n (pr₁ (view d q')) t' (pr₂ (view d q')) (approx n t' y)) (defined-is-prop d _ q)
    (pr₂ (transport (λ - → Rf (succ n) d -) (π∞-inj n t' y) (h (succ n)) ⋆))

{- related values, with a defined target, are made with tags whose
   payloads are related -}
Refl-cases : (d d' : ⟨ 𝔻 ⟩) → Refl d d' → defined d'
  → (P : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇ )
  → ((t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
       → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → P (inj t · x) (inj t' · y))
  → P d d'
Refl-cases d d' h q' P k =
  transport₂ P (inj-view d q ⁻¹) (inj-view d' q' ⁻¹)
    (k (pr₁ (view d q)) (pr₂ (view d q)) (pr₁ (view d' q')) (pr₂ (view d' q'))
       (Refl-view d (pr₁ (view d' q')) (pr₂ (view d' q')) (transport (λ - → Refl d -) (inj-view d' q') h) q))
 where
  q = Refl-defined d d' h q'

{- seq -}
Refl-seq : (d d' e e' : ⟨ 𝔻 ⟩) → Refl d d' → Refl e e' → Refl (seq · d · e) (seq · d' · e')
Refl-seq d d' e e' hd he =
  Refl-from-defined (seq · d · e) (seq · d' · e') λ q →
    transport₂ Refl (seq-defined d e (Refl-defined d d' hd (seq-defined-l d' e' q)) ⁻¹)
                    (seq-defined d' e' (seq-defined-l d' e' q) ⁻¹) he

{- a target guarded by seq -}
Refl-seq-r : (d d' e' : ⟨ 𝔻 ⟩) → Refl d e' → Refl d (seq · d' · e')
Refl-seq-r d d' e' h =
  Refl-from-defined d (seq · d' · e') λ q →
    transport (λ - → Refl d -) (seq-defined d' e' (seq-defined-l d' e' q) ⁻¹) h

{- Constants, tuples, injections -}

Refl-const : (B : Base) (c : base-rep B) → Refl (const B c) (const B c)
Refl-const B c = Refl-inj (con B c) ⋆ (con B c) ⋆ (λ n → refl , ⋆)

Refl-unit : Refl unit unit
Refl-unit = Refl-inj (tup 0) (λ ()) (tup 0) (λ ()) (λ n → refl , (λ ()))

Refl-tuple : (k : ℕ) (ds ds' : Fin k → ⟨ 𝔻 ⟩) → ((i : Fin k) → Refl (ds i) (ds' i))
  → Refl (tupleᵈ k · ds) (tupleᵈ k · ds')
Refl-tuple k ds ds' h =
  Refl-from-defined (tupleᵈ k · ds) (tupleᵈ k · ds') λ q →
    transport₂ Refl (guard-defined k ds (λ i → Refl-defined (ds i) (ds' i) (h i) (tuple-defined← k ds' q i)) (inj (tup k) · ds) ⁻¹)
                    (guard-defined k ds' (tuple-defined← k ds' q) (inj (tup k) · ds') ⁻¹)
      (Refl-inj (tup k) ds (tup k) ds' (λ n → refl , (λ i → h i n)))

Refl-inl : (d d' : ⟨ 𝔻 ⟩) → Refl d d' → Refl (inlᵈ · d) (inlᵈ · d')
Refl-inl d d' h = Refl-seq d d' (inj left · d) (inj left · d') h (Refl-inj left d left d' h)

Refl-inr : (d d' : ⟨ 𝔻 ⟩) → Refl d d' → Refl (inrᵈ · d) (inrᵈ · d')
Refl-inr d d' h = Refl-seq d d' (inj right · d) (inj right · d') h (Refl-inj right d right d' h)

{- Components of tuples -}

private
 proj-br-ok : {k : ℕ} (i : Fin k) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → Refl (proj-br i t · x) (proj-br i t' · y)
 proj-br-ok {k} i (tup j) xs (tup j') ys m = aux j' (pr₁ (m 0)) ys m
  where
   aux : (j' : ℕ) → j ＝ j' → (ys : Fin j' → ⟨ 𝔻 ⟩) → ((n : ℕ) → MatchR n (tup j) (tup j') xs (approx n (tup j') ys))
       → Refl (at-tup j k i (j Nat.≟ k) · xs) (at-tup j' k i (j' Nat.≟ k) · ys)
   aux .j refl ys m = at-ok (j Nat.≟ k)
    where
     at-ok : (q : Dec (j Eq.≡ k)) → Refl (at-tup j k i q · xs) (at-tup j k i q · ys)
     at-ok (yes Eq.refl) n = transport (λ e' → Rf n (xs i) (π∞ n · ys (transport Fin e' i))) (K-is-set (pr₁ (m n)) refl) (pr₂ (m n) i)
     at-ok (no _) = Refl-⊥ ⊥𝔻
 proj-br-ok i (con B c) x (tup j') y m = 𝟘-elim (m 0)
 proj-br-ok i left x (tup j') y m = 𝟘-elim (m 0)
 proj-br-ok i right x (tup j') y m = 𝟘-elim (m 0)
 proj-br-ok i fun x (tup j') y m = 𝟘-elim (m 0)
 proj-br-ok i pr x (tup j') y m = 𝟘-elim (m 0)
 proj-br-ok i t x (con B' c') y m = Refl-⊥ (proj-br i t · x)
 proj-br-ok i t x left y m = Refl-⊥ (proj-br i t · x)
 proj-br-ok i t x right y m = Refl-⊥ (proj-br i t · x)
 proj-br-ok i t x fun y m = Refl-⊥ (proj-br i t · x)
 proj-br-ok i t x pr y m = Refl-⊥ (proj-br i t · x)

Refl-proj : {k : ℕ} (i : Fin k) (d d' : ⟨ 𝔻 ⟩) → Refl d d' → Refl (proj i · d) (proj i · d')
Refl-proj i d d' h =
  Refl-from-defined (proj i · d) (proj i · d') λ q →
    Refl-cases d d' h (proj-defined i d' q) (λ a b → Refl (proj i · a) (proj i · b))
      (λ t x t' y m → transport₂ Refl (case-inj 𝔻⊥ (proj-br i) t x ⁻¹) (case-inj 𝔻⊥ (proj-br i) t' y ⁻¹)
                        (proj-br-ok i t x t' y m))

{- Cases -}

private
 cases-br-ok : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → MatchR n t t' x (approx n t' y))
   → (f g f' g' : DCPO[ 𝔻 , 𝔻 ])
   → ((a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (f · a) (f' · a'))
   → ((a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (g · a) (g' · a'))
   → Refl (cases-br t · x · (strict · f , strict · g)) (cases-br t' · y · (strict · f' , strict · g'))
 cases-br-ok left x left y m f g f' g' hf hg = Refl-seq x y (f · x) (f' · y) m (hf x y m)
 cases-br-ok right x right y m f g f' g' hf hg = Refl-seq x y (g · x) (g' · y) m (hg x y m)
 cases-br-ok (con B c) x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok (tup k) x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok fun x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok pr x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok (con B c) x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok (tup k) x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok left x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok fun x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok pr x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok t x (con B' c') y m f g f' g' hf hg = Refl-⊥ (cases-br t · x · (strict · f , strict · g))
 cases-br-ok t x (tup k') y m f g f' g' hf hg = Refl-⊥ (cases-br t · x · (strict · f , strict · g))
 cases-br-ok t x fun y m f g f' g' hf hg = Refl-⊥ (cases-br t · x · (strict · f , strict · g))
 cases-br-ok t x pr y m f g f' g' hf hg = Refl-⊥ (cases-br t · x · (strict · f , strict · g))

Refl-case : (d d' : ⟨ 𝔻 ⟩) (f g f' g' : DCPO[ 𝔻 , 𝔻 ]) → Refl d d'
  → ((a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (f · a) (f' · a'))
  → ((a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (g · a) (g' · a'))
  → Refl (cases · d · (strict · f , strict · g)) (cases · d' · (strict · f' , strict · g'))
Refl-case d d' f g f' g' h hf hg =
  Refl-from-defined (cases · d · b) (cases · d' · b') λ q →
    Refl-cases d d' h (cases-defined d' b' q) (λ u v → Refl (cases · u · b) (cases · v · b'))
      (λ t x t' y m → transport₂ Refl (ap (_· b) (case-inj (Br ⟹𝔻) cases-br t x) ⁻¹)
                                      (ap (_· b') (case-inj (Br ⟹𝔻) cases-br t' y) ⁻¹)
                        (cases-br-ok t x t' y m f g f' g' hf hg))
 where
  b = (strict · f , strict · g)
  b' = (strict · f' , strict · g')

{- Primitives -}

Refl-out : (o : Out) → Refl (out o) (out o)
Refl-out (int z) = Refl-const Int z
Refl-out (bool true) = Refl-inl unit unit Refl-unit
Refl-out (bool false) = Refl-inr unit unit Refl-unit

private
 prim-br₂-ok : (p : Prim) (z : ℤ) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → Refl (prim-br₂ p z t · x) (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con B c) x (con Int w) y m = aux (pr₁ (m 0))
  where
   aux : con B c ＝ con Int w → Refl (prim-br₂ p z (con B c) · x) (prim-br₂ p z (con Int w) · y)
   aux refl = Refl-out (δ p z w)
 prim-br₂-ok p z (tup k) x (con Int w) y m = 𝟘-elim (m 0)
 prim-br₂-ok p z left x (con Int w) y m = 𝟘-elim (m 0)
 prim-br₂-ok p z right x (con Int w) y m = 𝟘-elim (m 0)
 prim-br₂-ok p z fun x (con Int w) y m = 𝟘-elim (m 0)
 prim-br₂-ok p z pr x (con Int w) y m = 𝟘-elim (m 0)
 prim-br₂-ok p z t x (con Nat c') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x (con 𝔹 c') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x (con Unit c') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x (con Void c') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x (con Blame c') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x (tup k') y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x left y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x right y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x fun y m = Refl-⊥ (prim-br₂ p z t · x)
 prim-br₂-ok p z t x pr y m = Refl-⊥ (prim-br₂ p z t · x)

 prim-br₁-ok : (p : Prim) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → (e e' : ⟨ 𝔻 ⟩) → Refl e e'
   → Refl (prim-br₁ p t · x · e) (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con B c) x (con Int z) y m e e' he = aux (pr₁ (m 0))
  where
   aux : con B c ＝ con Int z → Refl (prim-br₁ p (con B c) · x · e) (prim-br₁ p (con Int z) · y · e')
   aux refl =
     Refl-from-defined (case 𝔻⊥ (prim-br₂ p z) · e) (case 𝔻⊥ (prim-br₂ p z) · e') λ q →
       Refl-cases e e' he (case-defined (prim-br₂ p z) e' q)
         (λ u v → Refl (case 𝔻⊥ (prim-br₂ p z) · u) (case 𝔻⊥ (prim-br₂ p z) · v))
         (λ t x t' y m → transport₂ Refl (case-inj 𝔻⊥ (prim-br₂ p z) t x ⁻¹) (case-inj 𝔻⊥ (prim-br₂ p z) t' y ⁻¹)
                           (prim-br₂-ok p z t x t' y m))
 prim-br₁-ok p (tup k) x (con Int z) y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p left x (con Int z) y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p right x (con Int z) y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p fun x (con Int z) y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p pr x (con Int z) y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p t x (con Nat c') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x (con 𝔹 c') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x (con Unit c') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x (con Void c') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x (con Blame c') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x (tup k') y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x left y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x right y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x fun y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)
 prim-br₁-ok p t x pr y m e e' he = Refl-⊥ (prim-br₁ p t · x · e)

Refl-prim : (p : Prim) (d d' e e' : ⟨ 𝔻 ⟩) → Refl d d' → Refl e e' → Refl (primD p · d · e) (primD p · d' · e')
Refl-prim p d d' e e' hd he =
  Refl-from-defined (primD p · d · e) (primD p · d' · e') λ q →
    Refl-cases d d' hd (primD-defined₁ p d' e' q) (λ u v → Refl (primD p · u · e) (primD p · v · e'))
      (λ t x t' y m → transport₂ Refl (ap (_· e) (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t x) ⁻¹)
                                      (ap (_· e') (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t' y) ⁻¹)
                        (prim-br₁-ok p t x t' y m e e' he))

{- Closures --------------------------------------------------------------------------}

Refl-clos : (B B' : Den Env) (t t' : ⟨ 𝔻 ⟩) → Refl t t'
  → ((X X' Y Y' : ⟨ 𝔻 ⟩) → Refl X X' → Refl Y Y' → Refl (B · env₂ X Y) (B' · env₂ X' Y'))
  → Refl (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t')
Refl-clos B B' t t' ht hB =
  Refl-from-defined (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t') λ q →
    let qt' = pr₂ (pair-defined← (codeᶜ B') t' q)
        qt = Refl-defined t t' ht qt'
    in transport₂ Refl (code₂-env BE t qt ⁻¹)
                       (guard-defined 2 (pick₂ (codeᶜ B') t') (λ { zero → Λ-defined G' ; (suc zero) → qt' })
                          (inj pr · pick₂ (codeᶜ B') t') ⁻¹)
         (Refl-inj fun (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t)) pr (pick₂ (codeᶜ B') t') (calls qt'))
 where
  BE = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B
  G' = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B')) Λ
  s = curry₁ 𝔻 𝔻 𝔻 BE · t
  {- the closure, called on related arguments -}
  body : defined t' → (a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (strict · s · a) (appᵈ · (appᵈ · codeᶜ B' · t') · a')
  body qt' a a' ha =
    transport (λ - → Refl (strict · s · a) -) (codeᶜ-β B' t' a' ⁻¹)
      (Refl-seq-r (strict · s · a) t' (seq · a' · (B' · env₂ t' a'))
         (Refl-seq a a' (B · env₂ t a) (B' · env₂ t' a') ha (hB t t' a a' ht ha)))
  {- the payload of the function value is strict · s -}
  calls : defined t' → (n : ℕ) → Call n (strict · s) (approx n pr (pick₂ (codeᶜ B') t'))
  calls qt' zero = ⋆
  calls qt' (succ zero) = ⋆
  calls qt' (succ (succ m)) a v r =
    Rf-mono m (strict · (strict · s) · a) (π∞ m · (appᵈ · (appᵈ · codeᶜ B' · t') · (ε∞ m · v)))
      (callₛ m (approx (succ (succ m)) pr (pick₂ (codeᶜ B') t')) v)
      (callₛ-below m (pick₂ (codeᶜ B') t') v)
      (transport (λ - → Refl - (appᵈ · (appᵈ · codeᶜ B' · t') · (ε∞ m · v))) (seq-idem a (s · a) ⁻¹)
         (body qt' a (ε∞ m · v) (Refl-ε m a v r)) m)

{- Calls ------------------------------------------------------------------------------

   The approximation of depth n of the result of a call is the sup of the
   approximations of the calls of the approximations of the code, the
   environment and the argument; each of those is below the
   approximation of a call at a greater depth, of which the clause for
   pairs speaks. -}

{- a property of the approximations of a continuous map, at the
   approximations of its argument, holds at the argument -}
Rf-approx : (n : ℕ) (d : ⟨ 𝔻 ⟩) (F : DCPO[ 𝔻 , 𝓓 n ]) (x : ⟨ 𝔻 ⟩)
  → ((j : ℕ) → Rf n d (F · e j x)) → Rf n d (F · x)
Rf-approx n d F x h =
  transport (λ - → Rf n d -) (approx-∐ (𝓓 n) F x ⁻¹)
    (Rf-sup n d (λ j → F · e j x) (image-is-directed' 𝔻 (𝓓 n) F {ℕ} {λ k → e k x} (e-directed x)) h)

private
 ≤+' : (a b : ℕ) → b ≤ (a + b)
 ≤+' zero b = ≤-refl b
 ≤+' (succ a) b = ≤-trans b (a + b) (succ (a + b)) (≤+' a b) (≤-succ (a + b))

 app-mono : (f f' a a' : ⟨ 𝔻 ⟩) → f ⊑⟨ 𝔻 ⟩ f' → a ⊑⟨ 𝔻 ⟩ a' → appᵈ · f · a ⊑⟨ 𝔻 ⟩ appᵈ · f' · a'
 app-mono f f' a a' u w = transitivity 𝔻 _ _ _
   (monotone-if-continuous 𝔻 (𝔻 ⟹₁ 𝔻) appᵈ f f' u a)
   (monotone-if-continuous 𝔻 𝔻 (appᵈ · f') a a' w)

 {- maps for approximating one operand of a call at a time -}
 in-arg : (n : ℕ) (f : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
 in-arg n f = ∘₁ 𝔻 𝔻 (𝓓 n) (appᵈ · f) (π∞ n)
 in-env : (n : ℕ) (c a : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
 in-env n c a = ∘₁ 𝔻 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 𝔻 (appᵈ · c) (app-at a)) (π∞ n)
 in-code : (n : ℕ) (y a : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
 in-code n y a = ∘₁ 𝔻 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 𝔻 (app-at y) (app-at a)) (π∞ n)

 call-fun : (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝔻 ⟩) → ((n : ℕ) → Call n s (approx n pr cd))
   → (a a' : ⟨ 𝔻 ⟩) → Refl a a' → Refl (strict · s · a) (call cd a')
 call-fun s cd m a a' ha n =
   Rf-approx n (strict · s · a) (in-arg n (appᵈ · c · env)) a' λ j →
   Rf-approx n (strict · s · a) (in-env n c (e j a')) env λ i →
   Rf-approx n (strict · s · a) (in-code n (e i env) (e j a')) c λ l → core l i j
  where
   c = cd zero
   env = cd (suc zero)
   core : (l i j : ℕ) → Rf n (strict · s · a) (π∞ n · (appᵈ · (appᵈ · e l c · e i env) · e j a'))
   core l i j =
     Rf-mono n (strict · s · a) (π∞ n · G) (π∞ n · (appᵈ · (appᵈ · e l c · e i env) · e j a'))
       (monotone-if-continuous 𝔻 (𝓓 n) (π∞ n) _ _
          (app-mono _ _ _ _
             (app-mono _ _ _ _ (e-mono c l (succ (succ K)) (≤-trans l K (succ (succ K)) l≤ (≤-trans K (succ K) (succ (succ K)) (≤-succ K) (≤-succ (succ K)))))
                               (e-mono env i (succ K) (≤-trans i K (succ K) i≤ (≤-succ K))))
             (e-mono a' j K j≤)))
       (transport (λ - → Rf n (strict · s · a) -) (πs-π∞ k' n G)
          (Rf-πs k' n (strict · s · a) (π∞ K · G)
             (transport (λ - → Rf K (strict · s · a) (π∞ K · (appᵈ · (appᵈ · e (succ (succ K)) c · (ε∞ (succ K) · -)) · e K a')))
                (π-π∞ (succ K) env)
                (m (succ (succ K)) a (π∞ K · a') (ha K)))))
    where
     k' = (l + i) + j
     K = k' + n
     G = appᵈ · (appᵈ · e (succ (succ K)) c · e (succ K) env) · e K a'
     l≤ : l ≤ K
     l≤ = ≤-trans l (l + i) K (≤+ l i) (≤-trans (l + i) k' K (≤+ (l + i) j) (≤+ k' n))
     i≤ : i ≤ K
     i≤ = ≤-trans i (l + i) K (≤+' l i) (≤-trans (l + i) k' K (≤+ (l + i) j) (≤+ k' n))
     j≤ : j ≤ K
     j≤ = ≤-trans j k' K (≤+' (l + i) j) (≤+ k' n)

 call-ok : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → MatchR n t t' x (approx n t' y)) → (a a' : ⟨ 𝔻 ⟩) → Refl a a'
   → Refl (app-br t · x · a) (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok fun s pr cd m a a' ha = call-fun s cd m a a' ha
 call-ok (con B c) x pr y m a a' ha = 𝟘-elim (m 0)
 call-ok (tup k) x pr y m a a' ha = 𝟘-elim (m 0)
 call-ok left x pr y m a a' ha = 𝟘-elim (m 0)
 call-ok right x pr y m a a' ha = 𝟘-elim (m 0)
 call-ok pr x pr y m a a' ha = 𝟘-elim (m 0)
 call-ok t x (con B' c') y m a a' ha =
   transport (λ - → Refl (app-br t · x · a) -) ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) (Refl-⊥ (app-br t · x · a))
 call-ok t x (tup k') y m a a' ha =
   transport (λ - → Refl (app-br t · x · a) -) ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) (Refl-⊥ (app-br t · x · a))
 call-ok t x left y m a a' ha =
   transport (λ - → Refl (app-br t · x · a) -) ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) (Refl-⊥ (app-br t · x · a))
 call-ok t x right y m a a' ha =
   transport (λ - → Refl (app-br t · x · a) -) ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) (Refl-⊥ (app-br t · x · a))
 call-ok t x fun y m a a' ha =
   transport (λ - → Refl (app-br t · x · a) -) ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) (Refl-⊥ (app-br t · x · a))

Refl-call : (l l' a a' : ⟨ 𝔻 ⟩) → Refl l l' → Refl a a'
  → Refl (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a')
Refl-call l l' a a' hl ha =
  Refl-from-defined (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a') λ q →
    Refl-cases l l' hl (component-defined zero l' (app-defined (car · l') (cdr · l') (app-defined (appᵈ · (car · l') · (cdr · l')) a' q)))
      (λ u v → Refl (appᵈ · u · a) (appᵈ · (appᵈ · (car · v) · (cdr · v)) · a'))
      (λ t x t' y m → transport₂ Refl (ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br t x) ⁻¹)
                                      (ap₂ (λ c d → appᵈ · (appᵈ · c · d) · a') (case-inj 𝔻⊥ (component-br zero) t' y)
                                           (case-inj 𝔻⊥ (component-br (suc zero)) t' y) ⁻¹)
                        (call-ok t x t' y m a a' ha))
