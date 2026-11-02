{-

  Correctness of the remove-complex-operands pass (Clos5 → Clos5,
  Compiler/RCO.agda) by a forward simulation of the Clos5 reduction
  semantics by itself (see the design note in
  Semantics/Reduction/Smallstep.agda). The source runs with the table ds
  and the target with map rco ds.

  Values contain no code (a code reference is a number), so the source
  and the target compute the same values, as terms. A construct with
  operands M₁ … Mₙ becomes a chain of lets for the complex operands and
  then the construct on atoms. The source reduces a complex operand in
  the context h of the construct (an operand frame) while the target
  reduces it under its let (letc≈); once it is a value W, the target
  substitutes W, and is then related to h W (for every value W: this
  is not a logical relation, since the two sides get the same W). So
  the relation on terms needs no closure under substitution: every
  substitution is that of a β, a case or a let, into code, which is
  related by the compilation function under that substitution (the
  fundamental lemma rco≈: sub σ M is related to sub σ (rco M)).

  Precondition: the program is well scoped (Scoped). An unbound atom
  would error in the source before a later complex operand runs, but
  in the target only after it (see RCOSim).

-}

module Untyped.proof.Correctness.Reduction.RCORed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Untyped.Language.Clos5
open import Untyped.Language.Mon using (Atom; var; lit; ref; atom-rename)
open import Untyped.Compiler.RCO
open import Untyped.Compiler.Pipeline using (compile; compile-mon)
open import Untyped.Compiler.PipelineScope using (Scoped)
open import Untyped.proof.Compiler.PipelineScope using (compile-scoped)
open import Untyped.proof.Compiler.CaptureScope using (Closed)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.Simulation Obs using (equiv-trans)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Untyped.proof.Semantics.Reduction.Clos5 as T
open T using (Value; Values; value-red; values-red)
import Semantics.Reduction.ISWIM as S
open import Untyped.proof.Correctness.Reduction.CompilerRed using (compile-correct)
open import proof.Framework.Syntax.Subst Op sig
  using (Subst; sub; sub-args; exts; ids; extend; _[_]; sub-id; sub-cong; ren-sub; exts-[]; extend-skip; extend-top)
open import proof.Framework.Syntax.Rename Op sig using (ext; rename; rename-args; rename-fuse-args; rename-id-args)
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import proof.Framework.Syntax.ScopeSubst Op sig using (Below; below-•)
open import proof.Framework.ListUtil using (_‼_; proj; args→list; has-length; reverse-map-‼; ‼-any)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁻)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate; map; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- The let chains of rco ---------------------------------------------------------}

lift-keep : ∀ {n} (f : ℕ → Args (replicate (suc n) ■) → AST) M Ms → Atom M
  → lift f (M ,, Ms) ≡ lift (λ k As → f k (rename (k +_) M ,, As)) Ms
lift-keep f M Ms a with atom? M
... | yes _ = refl
... | no na = ⊥-elim (na a)

lift-let : ∀ {n} (f : ℕ → Args (replicate (suc n) ■) → AST) M Ms → (Atom M → ⊥)
  → lift f (M ,, Ms) ≡ let-op ⦅ M ,, ⟩ lift (λ k As → f (suc k) (` k ,, As)) (rename-args suc Ms) ,, Nil ⦆
lift-let f M Ms na with atom? M
... | yes a = ⊥-elim (na a)
... | no _ = refl

rco-atom : ∀ {M} → Atom M → rco M ≡ M
rco-atom (var x) = refl
rco-atom (lit B n) = refl
rco-atom (ref n) = refl

{- rco makes an atom only of an atom -}
lift-na : ∀ {n} g (f : ℕ → Args (replicate n ■) → AST) Ms
  → (∀ k As → Atom (rename g (f k As)) → ⊥) → Atom (rename g (lift f Ms)) → ⊥
lift-na g f Ms na with binds (atomize Ms)
... | [] = na _ _
... | _ ∷ _ = λ ()

atom-rco : ∀ M g → Atom (rename g (rco M)) → Atom M
atom-rco (` x) g a = var x
atom-rco (fun-ref n ⦅ Nil ⦆) g a = ref n
atom-rco (lit B n ⦅ Nil ⦆) g a = lit B n
atom-rco (app ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → app ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (pair-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → pair-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (fst-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → fst-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (snd-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → snd-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (tuple n ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → tuple n ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (get i ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → get i ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (inl-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → inl-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (inr-op ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → inr-op ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) g a =
  ⊥-elim (lift-na g (case-on (rco M) (rco N)) (rco L ,, Nil) (λ { k (A ,, Nil) () }) a)
atom-rco (prim p ⦅ Ms ⦆) g a = ⊥-elim (lift-na g (λ _ → prim p ⦅_⦆) (rco-args Ms) (λ k As → λ ()) a)
atom-rco (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) g ()

{- the definitions of the target table are rco of the source's -}
global-map : ∀ ds k → global (map rco ds) k ≡ mmap rco (global ds k)
global-map ds = reverse-map-‼ rco ds

global-all : ∀ {P : AST → Set} {ds} → All P ds → ∀ k {N} → global ds k ≡ just N → P N
global-all {ds = ds} ps k eq = lookup ps (reverse⁻ (‼-any (reverse ds) k eq))

{- the values of a primitive -}
out-value : ∀ o → Value (T.out o)
out-value (int n) = T.lit
out-value (bool true) = T.inl (T.tuple T.[])
out-value (bool false) = T.inr (T.tuple T.[])

{- The simulation, for a program with table ds whose definitions are scoped -------}

module Sim (ds : List AST) (wds : All (WS 2) ds) where

  red₁ = T.red ds
  red₂ = T.red (map rco ds)

  {- σ maps the variables below k to values -}
  Vals : ℕ → Subst → Set
  Vals = Below Value

  {- The relation on terms -----------------------------------------------------}

  infix 4 _≈_
  data _≈_ : AST → AST → Set where
    val≈ : ∀ {V} → Value V → V ≈ V
    {- an operand M in the context h of the source, and under a let in the target -}
    letc≈ : ∀ {h M M' B} → Frame red₁ red₁ h → M ≈ M'
      → (∀ W → Value W → h W ≈ B [ W ]) → h M ≈ let-op ⦅ M' ,, ⟩ B ,, Nil ⦆
    {- the constructs whose operands are values, and let, in both -}
    call≈ : ∀ {F E W} → Value F → Value E → Value W → app ⦅ F ,, E ,, W ,, Nil ⦆ ≈ app ⦅ F ,, E ,, W ,, Nil ⦆
    fst≈ : ∀ {V} → Value V → fst-op ⦅ V ,, Nil ⦆ ≈ fst-op ⦅ V ,, Nil ⦆
    snd≈ : ∀ {V} → Value V → snd-op ⦅ V ,, Nil ⦆ ≈ snd-op ⦅ V ,, Nil ⦆
    get≈ : ∀ {n} {i : Fin n} {V} → Value V → get i ⦅ V ,, Nil ⦆ ≈ get i ⦅ V ,, Nil ⦆
    prim≈ : ∀ {p V W} → Value V → Value W → prim p ⦅ V ,, W ,, Nil ⦆ ≈ prim p ⦅ V ,, W ,, Nil ⦆
    case≈ : ∀ {k σ V M N} → Vals k σ → WS (suc k) M → WS (suc k) N → Value V
      → case-op ⦅ V ,, ⟩ sub (exts σ) M ,, ⟩ sub (exts σ) N ,, Nil ⦆
        ≈ case-op ⦅ V ,, ⟩ sub (exts σ) (rco M) ,, ⟩ sub (exts σ) (rco N) ,, Nil ⦆
    let≈ : ∀ {k σ M M' N} → Vals k σ → WS (suc k) N → M ≈ M'
      → let-op ⦅ M ,, ⟩ sub (exts σ) N ,, Nil ⦆ ≈ let-op ⦅ M' ,, ⟩ sub (exts σ) (rco N) ,, Nil ⦆

  {- a target value is the source's -}
  ≈-val : ∀ {M V} → Value V → M ≈ V → M ≡ V
  ≈-val v (val≈ _) = refl

  {- The fundamental lemma: code under a substitution of values -----------------}

  rco≈ : ∀ {k} σ M → Vals k σ → WS k M → sub σ M ≈ sub σ (rco M)
  rco≈s : ∀ {n k} σ (Ms : Args (replicate n ■)) → Vals k σ → WS-args k Ms
    → Pw (λ M M' → sub σ M ≈ sub σ M') Ms (rco-args Ms)

  {- a construct h on the operands Ms after σ, and the target's chain for
     them, renamed by r, after ρ, which agrees with σ through r, with g
     on the atoms at the end -}
  chain : ∀ {n k} σ (Ms : Args (replicate n ■)) → Vals k σ → WS-args k Ms
    → Pw (λ M M' → sub σ M ≈ sub σ M') Ms (rco-args Ms) → ∀ r ρ (h : Args (replicate n ■) → AST) (g : ℕ → Args (replicate n ■) → AST)
    → (∀ x → ρ (r x) ≡ σ x) → LR red₁ Value h
    → (∀ j (Ws : Args (replicate j ■)) As → Values (sub-args (extend Ws ρ) As)
         → h (sub-args (extend Ws ρ) As) ≈ sub (extend Ws ρ) (g j As))
    → h (sub-args σ Ms) ≈ sub ρ (lift g (rename-args r (rco-args Ms)))
  chain {zero} σ Nil vs ws fs r ρ h g eq lr fin = fin 0 Nil Nil T.[]
  chain {suc n} {k} σ (M ,, Ms) vs (w , ws) (f ∷ fs) r ρ h g eq lr fin with atom? M
  ... | yes a rewrite rco-atom a | lift-keep g (rename r M) (rename-args r (rco-args Ms)) (atom-rename r a) =
    chain σ Ms vs ws fs r ρ (λ As → h (sub σ M ,, As)) (λ j As → g j (rename (j +_) (rename r M) ,, As)) eq (proj₂ lr (atom-val a w)) fin'
    where
    atom-val : ∀ {M} → Atom M → WS k M → Value (sub σ M)
    atom-val (var x) w = vs x w
    atom-val (lit B n) w = T.lit
    atom-val (ref n) w = T.fun
    same : ∀ j (Ws : Args (replicate j ■)) → sub (extend Ws ρ) (rename (j +_) (rename r M)) ≡ sub σ M
    same j Ws = trans (ren-sub _ _ (rename r M)) (trans (ren-sub _ r M)
                  (sub-cong (λ x → trans (extend-skip Ws ρ (r x)) (eq x)) M))
    fin' : ∀ j (Ws : Args (replicate j ■)) As → Values (sub-args (extend Ws ρ) As)
      → h (sub σ M ,, sub-args (extend Ws ρ) As) ≈ sub (extend Ws ρ) (g j (rename (j +_) (rename r M) ,, As))
    fin' j Ws As vs' = subst (λ X → h (X ,, sub-args (extend Ws ρ) As) ≈ sub (extend Ws ρ) (g j (rename (j +_) (rename r M) ,, As))) (same j Ws)
                             (fin j Ws (rename (j +_) (rename r M) ,, As) (subst Value (sym (same j Ws)) (atom-val a w) T.∷ vs'))
  ... | no na rewrite lift-let g (rename r (rco M)) (rename-args r (rco-args Ms)) (λ a → na (atom-rco M r a))
                    | rename-fuse-args suc r (rco-args Ms) =
    letc≈ (proj₁ lr (sub-args σ Ms))
          (subst (λ X → sub σ M ≈ X) (sym (trans (ren-sub ρ r (rco M)) (sub-cong eq (rco M)))) f)
          λ W v → subst (λ X → h (W ,, sub-args σ Ms) ≈ X) (sym (exts-[] W ρ (lift (λ j As → g (suc j) (` j ,, As)) (rename-args (λ x → suc (r x)) (rco-args Ms)))))
                        (chain σ Ms vs ws fs (λ x → suc (r x)) (W • ρ) (λ As → h (W ,, As)) (λ j As → g (suc j) (` j ,, As)) eq (proj₂ lr v)
                               (λ j Ws As vs' → subst (λ X → h (X ,, sub-args (extend Ws (W • ρ)) As) ≈ sub (extend Ws (W • ρ)) (g (suc j) (` j ,, As))) (extend-top Ws W ρ)
                                                      (fin (suc j) (W ,, Ws) (` j ,, As)
                                                           (subst Value (sym (extend-top Ws W ρ)) v T.∷ vs'))))

  {- the chain of a construct -}
  chain₀ : ∀ {n k} σ (Ms : Args (replicate n ■)) → Vals k σ → WS-args k Ms
    → Pw (λ M M' → sub σ M ≈ sub σ M') Ms (rco-args Ms) → (h : Args (replicate n ■) → AST) (g : ℕ → Args (replicate n ■) → AST) → LR red₁ Value h
    → (∀ j (Ws : Args (replicate j ■)) As → Values (sub-args (extend Ws σ) As)
         → h (sub-args (extend Ws σ) As) ≈ sub (extend Ws σ) (g j As))
    → h (sub-args σ Ms) ≈ sub σ (lift g (rco-args Ms))
  chain₀ σ Ms vs ws fs h g lr fin =
    subst (λ X → h (sub-args σ Ms) ≈ sub σ (lift g X)) (rename-id-args (λ _ → refl) (rco-args Ms))
          (chain σ Ms vs ws fs (λ x → x) σ h g (λ _ → refl) lr fin)

  rco≈ σ (` x) vs w = val≈ (vs x w)
  rco≈ σ (fun-ref n ⦅ Nil ⦆) vs w = val≈ T.fun
  rco≈ σ (lit B n ⦅ Nil ⦆) vs w = val≈ T.lit
  rco≈ σ (app ⦅ Ms@(M₁ ,, M₂ ,, M₃ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (app ⦅_⦆) (λ _ → app ⦅_⦆) lr
      λ { j Ws (A ,, B ,, C ,, Nil) (a T.∷ b T.∷ c T.∷ T.[]) → call≈ a b c }
    where lr : LR red₁ Value (app ⦅_⦆)
          lr = (λ { (Y ,, Z ,, Nil) → frame _ (λ _ → refl) })
             , λ v → (λ { (Z ,, Nil) → frame _ (λ _ → val-in (value-red v)) })
             , λ w → (λ { Nil → frame _ (λ _ → trans (val-in (value-red v)) (val-in (value-red w))) }) , λ _ → tt
  rco≈ σ (pair-op ⦅ Ms@(M₁ ,, M₂ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (pair-op ⦅_⦆) (λ _ → pair-op ⦅_⦆) lr
      λ { j Ws (A ,, B ,, Nil) (a T.∷ b T.∷ T.[]) → val≈ (T.pair a b) }
    where lr : LR red₁ Value (pair-op ⦅_⦆)
          lr = (λ { (Y ,, Nil) → frame _ (λ _ → refl) })
             , λ v → (λ { Nil → frame _ (λ _ → val-in (value-red v)) }) , λ _ → tt
  rco≈ σ (fst-op ⦅ Ms@(M₁ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (fst-op ⦅_⦆) (λ _ → fst-op ⦅_⦆) (lr1 (fst-op ⦅_⦆) _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → fst≈ a }
  rco≈ σ (snd-op ⦅ Ms@(M₁ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (snd-op ⦅_⦆) (λ _ → snd-op ⦅_⦆) (lr1 (snd-op ⦅_⦆) _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → snd≈ a }
  rco≈ σ (tuple n ⦅ Ms ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (tuple n ⦅_⦆) (λ _ → tuple n ⦅_⦆) (lr-args (T.red-args ds) (λ _ _ → refl) value-red (frame _ (λ _ → refl)))
      λ j Ws As as → val≈ (T.tuple as)
  rco≈ σ (get i ⦅ Ms@(M₁ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (get i ⦅_⦆) (λ _ → get i ⦅_⦆) (lr1 (get i ⦅_⦆) _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → get≈ a }
  rco≈ σ (inl-op ⦅ Ms@(M₁ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (inl-op ⦅_⦆) (λ _ → inl-op ⦅_⦆) (lr1 (inl-op ⦅_⦆) _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → val≈ (T.inl a) }
  rco≈ σ (inr-op ⦅ Ms@(M₁ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (inr-op ⦅_⦆) (λ _ → inr-op ⦅_⦆) (lr1 (inr-op ⦅_⦆) _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → val≈ (T.inr a) }
  rco≈ {k} σ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) vs (wL , wM , wN , _) =
    chain₀ σ (L ,, Nil) vs (wL , tt) (rco≈ σ L vs wL ∷ []) hc (case-on (rco M) (rco N)) (lr1 hc _ (λ _ → refl))
      λ { j Ws (A ,, Nil) (a T.∷ T.[]) → subst₂ (λ X Y → case-op ⦅ sub (extend Ws σ) A ,, ⟩ sub (exts σ) M ,, ⟩ sub (exts σ) N ,, Nil ⦆ ≈ case-op ⦅ sub (extend Ws σ) A ,, ⟩ X ,, ⟩ Y ,, Nil ⦆)
                                                (branch j Ws (rco M)) (branch j Ws (rco N)) (case≈ {M = M} {N = N} vs wM wN a) }
    where
    hc : Args (replicate 1 ■) → AST
    hc (X ,, Nil) = case-op ⦅ X ,, ⟩ sub (exts σ) M ,, ⟩ sub (exts σ) N ,, Nil ⦆
    branch : ∀ j (Ws : Args (replicate j ■)) X
      → sub (exts σ) X ≡ sub (exts (extend Ws σ)) (rename (ext (j +_)) X)
    branch j Ws X = sym (trans (ren-sub _ _ X) (sub-cong (λ { zero → refl ; (suc x) → cong (rename suc) (extend-skip Ws σ x) }) X))
  rco≈ σ (prim p ⦅ Ms@(M₁ ,, M₂ ,, Nil) ⦆) vs ws =
    chain₀ σ Ms vs ws (rco≈s σ Ms vs ws) (prim p ⦅_⦆) (λ _ → prim p ⦅_⦆) lr
      λ { j Ws (A ,, B ,, Nil) (a T.∷ b T.∷ T.[]) → prim≈ a b }
    where lr : LR red₁ Value (prim p ⦅_⦆)
          lr = (λ { (Y ,, Nil) → frame _ (λ _ → refl) })
             , λ v → (λ { Nil → frame _ (λ _ → val-in (value-red v)) }) , λ _ → tt
  rco≈ σ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) vs (wM , wN , _) = let≈ {N = N} vs wN (rco≈ σ M vs wM)
  rco≈s {zero} σ Nil vs ws = []
  rco≈s {suc n} σ (M ,, Ms) vs (w , ws) = rco≈ σ M vs w ∷ rco≈s σ Ms vs ws

  {- The simulation -----------------------------------------------------------------}

  Ans′ = Ans red₂ Value _≈_

  {- once the operands of a call are values -}
  call-step : ∀ {ds' F E W r} → Value F → Value E → Value W → T.call ds' F E W ≡ r
    → T.red ds' (app ⦅ F ,, E ,, W ,, Nil ⦆) ≡ r
  call-step {ds'} f e w eq rewrite value-red {ds'} f | value-red {ds'} e | value-red {ds'} w = eq

  call-sim : ∀ {F E W} → Value F → Value E → Value W → Ans′ (app ⦅ F ,, E ,, W ,, Nil ⦆) (T.call ds F E W) (app ⦅ F ,, E ,, W ,, Nil ⦆)
  call-sim {fun-ref k ⦅ Nil ⦆} {E} {W} f e w with global ds k in eq
  ... | nothing = error ε (call-step f e w (cong (λ m → T.call? m E W) (trans (global-map ds k) (cong (mmap rco) eq))))
  ... | just N = to (one (call-step f e w (cong (λ m → T.call? m E W) (trans (global-map ds k) (cong (mmap rco) eq)))))
                    (rco≈ (W • E • ids) N (below-• {P = Value} w (below-• {P = Value} e λ _ ())) (global-all wds k eq))
  call-sim f@(T.pair _ _) e w = error ε (call-step f e w refl)
  call-sim T.lit e w = error ε (call-step T.lit e w refl)
  call-sim f@(T.tuple _) e w = error ε (call-step f e w refl)
  call-sim f@(T.inl _) e w = error ε (call-step f e w refl)
  call-sim f@(T.inr _) e w = error ε (call-step f e w refl)

  sim : ∀ {M M'} → M ≈ M' → Ans′ M (red₁ M) M'
  sim (val≈ v) = subst (λ x → Ans′ _ x _) (sym (value-red v)) (val ε v (val≈ v))
  sim (letc≈ {h} {M} F r k) =
    subst (λ x → Ans′ (h M) x _) (sym (Frame.eq F M))
      (ans-in (frame _ (λ _ → refl)) (λ r' → letc≈ F r' k) (sim r) λ v r' → cont v r')
    where
    cont : ∀ {V'} → Value V' → M ≈ V' → Ans′ (h M) (Frame.κ F M) (let-op ⦅ V' ,, ⟩ _ ,, Nil ⦆)
    cont v r' with ≈-val v r'
    ... | refl = ans-step (val-in (value-red v))
                   (subst (λ x → Ans′ (h M) x _) (trans (Frame.eq F M) (val-in (value-red v))) (sim (k M v)))
  sim (call≈ f e w) = ans-skip (value-red f) (ans-skip (value-red e) (ans-skip (value-red w) (call-sim f e w)))
  sim (fst≈ v) = ans-skip (value-red v) (fst-sim v)
    where fst-sim : ∀ {V} → Value V → Ans′ (fst-op ⦅ V ,, Nil ⦆) (T.fst? V) (fst-op ⦅ V ,, Nil ⦆)
          fst-sim (T.pair a b) = to (one (val-in (value-red (T.pair a b)))) (val≈ a)
          fst-sim T.fun = error ε refl
          fst-sim T.lit = error ε refl
          fst-sim v@(T.tuple _) = error ε (val-in (value-red v))
          fst-sim v@(T.inl _) = error ε (val-in (value-red v))
          fst-sim v@(T.inr _) = error ε (val-in (value-red v))
  sim (snd≈ v) = ans-skip (value-red v) (snd-sim v)
    where snd-sim : ∀ {V} → Value V → Ans′ (snd-op ⦅ V ,, Nil ⦆) (T.snd? V) (snd-op ⦅ V ,, Nil ⦆)
          snd-sim (T.pair a b) = to (one (val-in (value-red (T.pair a b)))) (val≈ b)
          snd-sim T.fun = error ε refl
          snd-sim T.lit = error ε refl
          snd-sim v@(T.tuple _) = error ε (val-in (value-red v))
          snd-sim v@(T.inl _) = error ε (val-in (value-red v))
          snd-sim v@(T.inr _) = error ε (val-in (value-red v))
  sim (get≈ {i = i} v) = ans-skip (value-red v) (get-sim v)
    where get-sim : ∀ {V} → Value V → Ans′ (get i ⦅ V ,, Nil ⦆) (T.get? i V) (get i ⦅ V ,, Nil ⦆)
          get-sim v@(T.tuple {as = as} vs) with proj i (args→list as) in eq
          ... | nothing = error ε (trans (val-in (value-red v)) (cong ret? eq))
          ... | just V = to (one (trans (val-in (value-red v)) (cong ret? eq))) (val≈ (each-proj i vs eq))
          get-sim T.fun = error ε refl
          get-sim v@(T.pair _ _) = error ε (val-in (value-red v))
          get-sim T.lit = error ε refl
          get-sim v@(T.inl _) = error ε (val-in (value-red v))
          get-sim v@(T.inr _) = error ε (val-in (value-red v))
  sim (prim≈ {p} {V} {W} v w) = ans-skip (value-red v) (ans-skip (value-red w) prim-sim)
    where prim-sim : Ans′ (prim p ⦅ V ,, W ,, Nil ⦆) (T.prim? p V W) (prim p ⦅ V ,, W ,, Nil ⦆)
          prim-sim with δ? p (T.obs V) (T.obs W) in eq
          ... | nothing = error ε (trans (val-in (value-red v)) (trans (val-in (value-red w)) (cong (λ m → ret? (mmap T.out m)) eq)))
          ... | just o = to (one (trans (val-in (value-red v)) (trans (val-in (value-red w)) (cong (λ m → ret? (mmap T.out m)) eq))))
                            (val≈ (out-value o))
  sim (case≈ {σ = σ} {M = M} {N} vs wM wN v) = ans-skip (value-red v) (case-sim v)
    where case-sim : ∀ {V} → Value V
            → Ans′ (case-op ⦅ V ,, ⟩ sub (exts σ) M ,, ⟩ sub (exts σ) N ,, Nil ⦆)
                   (T.case? V (sub (exts σ) M) (sub (exts σ) N))
                   (case-op ⦅ V ,, ⟩ sub (exts σ) (rco M) ,, ⟩ sub (exts σ) (rco N) ,, Nil ⦆)
          case-sim v@(T.inl a) = to (one (val-in (value-red v)))
            (subst₂ _≈_ (sym (exts-[] _ σ M)) (sym (exts-[] _ σ (rco M))) (rco≈ _ M (below-• {P = Value} a vs) wM))
          case-sim v@(T.inr a) = to (one (val-in (value-red v)))
            (subst₂ _≈_ (sym (exts-[] _ σ N)) (sym (exts-[] _ σ (rco N))) (rco≈ _ N (below-• {P = Value} a vs) wN))
          case-sim T.fun = error ε refl
          case-sim v@(T.pair _ _) = error ε (val-in (value-red v))
          case-sim T.lit = error ε refl
          case-sim v@(T.tuple _) = error ε (val-in (value-red v))
  sim (let≈ {σ = σ} {N = N} vs wN r) =
    ans-in (frame _ (λ _ → refl)) (let≈ {N = N} vs wN) (sim r)
      λ v r' → let-sim v r'
    where let-sim : ∀ {M V'} → Value V' → M ≈ V'
            → Ans′ (let-op ⦅ M ,, ⟩ sub (exts σ) N ,, Nil ⦆) (to (sub (exts σ) N [ M ])) (let-op ⦅ V' ,, ⟩ sub (exts σ) (rco N) ,, Nil ⦆)
          let-sim v r' with ≈-val v r'
          ... | refl = to (one (val-in (value-red v)))
                          (subst₂ _≈_ (sym (exts-[] _ σ N)) (sym (exts-[] _ σ (rco N))) (rco≈ _ N (below-• {P = Value} v vs) wN))

{- The end theorem: for well-scoped programs ---------------------------------}

rco-correct : ∀ P → Scoped P → Equivalent (T.sem P) (T.sem (rco-program P))
rco-correct (program ds M) (wds , wM) =
  red-equivalent value-red _≈_ sim (λ m _ v → cong T.obs (≈-val v m))
    (subst₂ _≈_ (sub-id M) (sub-id (rco M)) (rco≈ ids M (λ _ ()) wM))
  where open Sim ds wds

{- The whole compiler, into monadic normal form --------------------------------}

compile-mon-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (compile-mon M))
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct (compile M) (compile-scoped M c))
