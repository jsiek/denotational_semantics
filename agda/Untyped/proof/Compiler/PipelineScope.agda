{-

  The compiler produces well-scoped Clos5 programs (Scoped,
  Compiler/PipelineScope.agda) from closed ISWIM programs
  (compile-scoped). Scoped is the precondition of the operational proofs
  of remove complex operands (RCOSim, RCOFuel).

  Each pass preserves well-scopedness (WS, Framework/Syntax/Scope.agda), starting
  from capture-closed (proof/Compiler/CaptureScope.agda):

  * prune: the code of a closure, renamed by ext-var (index P), uses
    only the free variables that prune-fvs keeps, whose new positions are
    below the count of kept ones (prune-used), since it drops a free
    variable only when the code does not use it;
  * concretize: a variable becomes a variable or a projection from a
    variable in scope (RefOK); in the code of a closure, the argument and
    the tuple of free variables (fv-ref-fits);
  * delay: the operand of an application goes under one more binder
    (ws-shift);
  * globalize: the code of each function, closed in Clos4, becomes a
    definition.

-}

module Untyped.proof.Compiler.PipelineScope where

open import Untyped.Compiler.PipelineScope public using (Scoped)

open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_; !_,,_)
import Untyped.Language.Clos2 as C2
import Untyped.Language.Clos3 as C3
import Untyped.Language.Clos4 as C4
import Untyped.Language.Clos5 as C5
import proof.Framework.Syntax.Scope
import proof.Framework.Syntax.ScopeRename
import Untyped.proof.Compiler.CaptureScope as ES
open ES using (Closed)
open import Untyped.Compiler.Capture using (capture)
open import Compiler.Simplify using (simplify)
open import proof.Compiler.SimplifyScope using (simplify-closed)
import Untyped.Compiler.Prune
import Untyped.Compiler.Concretize
open import Untyped.Compiler.Pipeline using (compile; compile₄)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n; _<?_)
open import Data.Nat.Properties
  using (+-suc; +-identityʳ; m≤n⇒m<n∨m≡n; m<n⇒m<1+n; ≤-reflexive; ≤-pred)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Framework.abt.Var using (Var)

module W2 = proof.Framework.Syntax.Scope C2.Op C2.sig
module W3 = proof.Framework.Syntax.ScopeRename C3.Op C3.sig
module W4 = proof.Framework.Syntax.ScopeRename C4.Op C4.sig
module W5 = proof.Framework.Syntax.Scope C5.Op C5.sig

split< : ∀ {j m} → j < suc m → j < m ⊎ j ≡ m
split< (s≤s le) = m≤n⇒m<n∨m≡n le

{- prune ----------------------------------------------------------------------}

module Opt where
  open C2
  open import Untyped.Compiler.Prune
  open W2 using (WS; WS-arg; WS-args; ws-uses)

  module _ (r : Var → Var) {U : ℕ → Set} (dec : ∀ j → Dec (U j)) where

    {- the positions past the free variables are renumbered by b, after
       the kept ones -}
    prune-past : ∀ m (fvs : Args (replicate m ■)) b k
      → index (prune-fvs m r dec fvs b) (m + k) ≡ count (prune-fvs m r dec fvs b) + b k
    prune-past zero Nil b k = refl
    prune-past (suc m) ((` y) ,, fvs) b k with dec m
    ... | yes _ =
      trans (cong (index (prune-fvs m r dec fvs (keep-base b))) (sym (+-suc m k)))
            (trans (prune-past m fvs (keep-base b) (suc k)) (+-suc _ _))
    ... | no _ =
      trans (cong (index (prune-fvs m r dec fvs (drop-base b))) (sym (+-suc m k)))
            (prune-past m fvs (drop-base b) (suc k))
    prune-past (suc m) ((op ⦅ args ⦆) ,, fvs) b k =
      trans (cong (index (prune-fvs m r dec fvs (keep-base b))) (sym (+-suc m k)))
            (trans (prune-past m fvs (keep-base b) (suc k)) (+-suc _ _))

    {- the position m of a kept free variable, just below the ones kept
       before it -}
    kept-top : ∀ m (fvs : Args (replicate m ■)) b
      → index (prune-fvs m r dec fvs (keep-base b)) m < suc (count (prune-fvs m r dec fvs (keep-base b)))
    kept-top m fvs b =
      subst (λ x → index P x < suc (count P)) (+-identityʳ m)
        (subst (_< suc (count P)) (sym (prune-past m fvs (keep-base b) 0))
          (s≤s (≤-reflexive (+-identityʳ (count P)))))
      where P = prune-fvs m r dec fvs (keep-base b)

    {- a used free variable is kept, below the count of kept ones -}
    prune-used : ∀ m (fvs : Args (replicate m ■)) b j → j < m → U j
      → index (prune-fvs m r dec fvs b) j < count (prune-fvs m r dec fvs b)
    prune-used (suc m) ((` y) ,, fvs) b j j< u with dec m | split< j<
    ... | yes _ | inj₁ lt = m<n⇒m<1+n (prune-used m fvs (keep-base b) j lt u)
    ... | yes _ | inj₂ refl = kept-top m fvs b
    ... | no _ | inj₁ lt = prune-used m fvs (drop-base b) j lt u
    ... | no nu | inj₂ refl = ⊥-elim (nu u)
    prune-used (suc m) ((op ⦅ args ⦆) ,, fvs) b j j< u with split< j<
    ... | inj₁ lt = m<n⇒m<1+n (prune-used m fvs (keep-base b) j lt u)
    ... | inj₂ refl = kept-top m fvs b

  ws-unbind : ∀ n {k} (a : Arg (ν-n n (ν ■))) → WS-arg k a → WS (suc (n + k)) (unbind-n n a)
  ws-unbind zero (bind (ast N)) w = w
  ws-unbind (suc n) {k} (bind a) w =
    subst (λ x → WS (suc x) (unbind-n n a)) (+-suc n k) (ws-unbind n a w)

  prune-ws : ∀ r {j k} M → WS j M → (∀ x → Uses x M → r x < k) → WS k (prune r M)
  opt-args-ws : ∀ r {n j k} (args : Args (replicate n ■)) → WS-args j args
    → (∀ x → UsesArgs x args → r x < k) → WS-args k (opt-args r args)
  opt-body-ws : ∀ r {k k'} n (a : Arg (ν-n n (ν ■))) → WS-arg k a
    → (∀ x → Uses x (unbind-n n a) → r x < k') → WS k' (opt-body r n a)
  kept-ws : ∀ r {U : ℕ → Set} (dec : ∀ j → Dec (U j)) m {j k} (fvs : Args (replicate m ■)) b
    → WS-args j fvs → (∀ x → UsesArgs x fvs → r x < k) → WS-args k (kept (prune-fvs m r dec fvs b))

  prune-ws r (` x) w h = h x refl
  prune-ws r (clos-op n ⦅ ! clear a ,, fvs ⦆) (wa , ws) h =
    ES.Captured.bind-n-ws c 0 body'
      (subst (λ x → WS (suc x) body') (sym (+-identityʳ c))
        (opt-body-ws (ext-var (index P)) n a wa h'))
    , kept-ws r dec n fvs (λ k → k) ws (λ x u → h x (inj₂ u))
    where
    dec = λ j → uses? (suc j) (unbind-n n a)
    P = prune-fvs n r dec fvs (λ k → k)
    c = count P
    body' = opt-body (ext-var (index P)) n a
    h' : ∀ x → Uses x (unbind-n n a) → ext-var (index P) x < suc c
    h' zero _ = s≤s z≤n
    h' (suc x) u =
      s≤s (prune-used r dec n fvs (λ k → k) x
             (subst (suc x ≤_) (+-identityʳ n) (≤-pred (ws-uses (unbind-n n a) (ws-unbind n a wa) u)))
             u)
  prune-ws r (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h =
    prune-ws r L wL (λ x u → h x (inj₁ u)) , prune-ws r M wM (λ x u → h x (inj₂ (inj₁ u))) , tt
  prune-ws r (lit B k ⦅ Nil ⦆) w h = tt
  prune-ws r (tuple n ⦅ args ⦆) w h = opt-args-ws r args w h
  prune-ws r (get i ⦅ M ,, Nil ⦆) (w , _) h = prune-ws r M w (λ x u → h x (inj₁ u)) , tt
  prune-ws r (inl-op ⦅ M ,, Nil ⦆) (w , _) h = prune-ws r M w (λ x u → h x (inj₁ u)) , tt
  prune-ws r (inr-op ⦅ M ,, Nil ⦆) (w , _) h = prune-ws r M w (λ x u → h x (inj₁ u)) , tt
  prune-ws r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) h =
    prune-ws r L wL (λ x u → h x (inj₁ u))
    , prune-ws (ext-var r) M wM hM
    , prune-ws (ext-var r) N wN hN
    , tt
    where
    hM : ∀ x → Uses x M → ext-var r x < suc _
    hM zero _ = s≤s z≤n
    hM (suc x) u = s≤s (h x (inj₂ (inj₁ u)))
    hN : ∀ x → Uses x N → ext-var r x < suc _
    hN zero _ = s≤s z≤n
    hN (suc x) u = s≤s (h x (inj₂ (inj₂ (inj₁ u))))
  prune-ws r (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h =
    prune-ws r L wL (λ x u → h x (inj₁ u)) , prune-ws r M wM (λ x u → h x (inj₂ (inj₁ u))) , tt
  prune-ws r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) h =
    prune-ws r M wM (λ x u → h x (inj₁ u)) , prune-ws (ext-var r) N wN hN , tt
    where
    hN : ∀ x → Uses x N → ext-var r x < suc _
    hN zero _ = s≤s z≤n
    hN (suc x) u = s≤s (h x (inj₂ (inj₁ u)))

  opt-args-ws r {zero} Nil w h = tt
  opt-args-ws r {suc n} (M ,, args) (w , ws) h =
    prune-ws r M w (λ x u → h x (inj₁ u)) , opt-args-ws r args ws (λ x u → h x (inj₂ u))

  opt-body-ws r zero (bind (ast N)) w h = prune-ws r N w h
  opt-body-ws r (suc n) (bind a) w h = opt-body-ws r n a w h

  kept-ws r dec zero Nil b w h = tt
  kept-ws r dec (suc m) ((` y) ,, fvs) b (_ , ws) h with dec m
  ... | yes _ = h y (inj₁ refl) , kept-ws r dec m fvs (keep-base b) ws (λ x u → h x (inj₂ u))
  ... | no _ = kept-ws r dec m fvs (drop-base b) ws (λ x u → h x (inj₂ u))
  kept-ws r dec (suc m) ((op ⦅ args ⦆) ,, fvs) b (w , ws) h =
    prune-ws r (op ⦅ args ⦆) w (λ x u → h x (inj₁ u))
    , kept-ws r dec m fvs (keep-base b) ws (λ x u → h x (inj₂ u))

  prune-closed : ∀ M → WS 0 M → WS 0 (prune-program M)
  prune-closed M w = prune-ws (λ x → x) M w (λ x u → ws-uses M w u)

{- concretize ----------------------------------------------------------------------}

module Conc where
  open C2
  open import Untyped.Compiler.Concretize
  open W2 using (WS; WS-arg; WS-args)

  RefOK : ℕ → Ref → Set
  RefOK k (var x) = x < k
  RefOK k (prj i x) = x < k

  ref-ws : ∀ {k} ρ → RefOK k ρ → W3.WS k (ref-ast ρ)
  ref-ws (var x) ok = ok
  ref-ws (prj i x) ok = ok , tt

  Fits : ℕ → ℕ → (Var → Ref) → Set
  Fits k k' φ = ∀ x → x < k → RefOK k' (φ x)

  fits-ext : ∀ {k k' φ} → Fits k k' φ → Fits (suc k) (suc k') (ext-ref φ)
  fits-ext h zero _ = s≤s z≤n
  fits-ext {φ = φ} h (suc x) (s≤s x<) with φ x | h x x<
  ... | var y | ok = s≤s ok
  ... | prj i y | ok = s≤s ok

  {- the code of a closure sees its argument and the tuple of its free
     variables -}
  fv-ref-fits : ∀ n → Fits (suc n) 2 (fv-ref n)
  fv-ref-fits n zero _ = s≤s z≤n
  fv-ref-fits n (suc k) (s≤s k<n) with k <? n
  ... | yes _ = s≤s (s≤s z≤n)
  ... | no ¬k< = ⊥-elim (¬k< k<n)

  conc-ws : ∀ φ {k k'} M → WS k M → Fits k k' φ → W3.WS k' (concretize φ M)
  conc-body-ws : ∀ n m {k} (a : Arg (ν-n m (ν ■))) → WS-arg k a
    → Fits (suc (m + k)) 2 (fv-ref n) → W3.WS 2 (conc-body n m a)
  conc-args-ws : ∀ φ {n k k'} (args : Args (replicate n ■)) → WS-args k args → Fits k k' φ
    → W3.WS-args k' (conc-args φ args)

  conc-ws φ (` x) w h = ref-ws (φ x) (h x w)
  conc-ws φ (clos-op n ⦅ ! clear a ,, fvs ⦆) (wa , ws) h =
    conc-body-ws n n a wa (subst (λ x → Fits (suc x) 2 (fv-ref n)) (sym (+-identityʳ n)) (fv-ref-fits n))
    , conc-args-ws φ fvs ws h
  conc-ws φ (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h = conc-ws φ L wL h , conc-ws φ M wM h , tt
  conc-ws φ (lit B k ⦅ Nil ⦆) w h = tt
  conc-ws φ (tuple n ⦅ args ⦆) w h = conc-args-ws φ args w h
  conc-ws φ (get i ⦅ M ,, Nil ⦆) (w , _) h = conc-ws φ M w h , tt
  conc-ws φ (inl-op ⦅ M ,, Nil ⦆) (w , _) h = conc-ws φ M w h , tt
  conc-ws φ (inr-op ⦅ M ,, Nil ⦆) (w , _) h = conc-ws φ M w h , tt
  conc-ws φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) h =
    conc-ws φ L wL h , conc-ws (ext-ref φ) M wM (fits-ext h) , conc-ws (ext-ref φ) N wN (fits-ext h) , tt
  conc-ws φ (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) h = conc-ws φ L wL h , conc-ws φ M wM h , tt
  conc-ws φ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) h = conc-ws φ M wM h , conc-ws (ext-ref φ) N wN (fits-ext h) , tt

  conc-body-ws n zero (bind (ast N)) w h = conc-ws (fv-ref n) N w h
  conc-body-ws n (suc m) {k} (bind a) w h =
    conc-body-ws n m {suc k} a w (subst (λ x → Fits (suc x) 2 (fv-ref n)) (sym (+-suc m k)) h)

  conc-args-ws φ {zero} Nil w h = tt
  conc-args-ws φ {suc n} (M ,, args) (w , ws) h = conc-ws φ M w h , conc-args-ws φ args ws h

  concretize-closed : ∀ M → WS 0 M → W3.WS 0 (concretize-program M)
  concretize-closed M w = conc-ws var M w (λ x ())

{- delay ---------------------------------------------------------------------------}

module Del where
  open C3
  open import Untyped.Compiler.Delay
  open W3

  delay-ws : ∀ {k} M → WS k M → W4.WS k (delay M)
  del-args-ws : ∀ {n k} (args : Args (replicate n ■)) → WS-args k args
    → W4.WS-args k (del-map-args args)

  delay-ws (` x) w = w
  delay-ws (clos-op n ⦅ ! (clear (bind (bind (ast N)))) ,, FVs ⦆) (wN , ws) =
    (delay-ws N wN , tt) , del-args-ws FVs ws , tt
  delay-ws (app ⦅ M ,, N ,, Nil ⦆) (wM , wN , _) =
    delay-ws M wM
    , ((s≤s z≤n , tt) , (s≤s z≤n , tt) , W4.ws-shift (delay N) (delay-ws N wN) , tt) , tt
  delay-ws (lit B k ⦅ Nil ⦆) w = tt
  delay-ws (tuple n ⦅ Ms ⦆) w = del-args-ws Ms w
  delay-ws (get i ⦅ M ,, Nil ⦆) (w , _) = delay-ws M w , tt
  delay-ws (inl-op ⦅ M ,, Nil ⦆) (w , _) = delay-ws M w , tt
  delay-ws (inr-op ⦅ M ,, Nil ⦆) (w , _) = delay-ws M w , tt
  delay-ws (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
    delay-ws L wL , delay-ws M wM , delay-ws N wN , tt
  delay-ws (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) = delay-ws L wL , delay-ws M wM , tt
  delay-ws (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) = delay-ws M wM , delay-ws N wN , tt

  del-args-ws {zero} Nil w = tt
  del-args-ws {suc n} (M ,, args) (w , ws) = delay-ws M w , del-args-ws args ws

{- globalize -----------------------------------------------------------------------}

module Glob where
  open C4
  open import Untyped.Compiler.Globalize
  open W4

  glob-ws : ∀ {k} M ds → WS k M → All (W5.WS 2) ds
    → W5.WS k (proj₁ (glob M ds)) × All (W5.WS 2) (proj₂ (glob M ds))
  glob-ws-arg : ∀ {k b} (a : Arg b) ds → WS-arg k a → All (W5.WS 2) ds
    → W5.WS-arg k (proj₁ (glob-arg a ds)) × All (W5.WS 2) (proj₂ (glob-arg a ds))
  glob-ws-args : ∀ {k bs} (args : Args bs) ds → WS-args k args → All (W5.WS 2) ds
    → W5.WS-args k (proj₁ (glob-args args ds)) × All (W5.WS 2) (proj₂ (glob-args args ds))

  glob-ws (` x) ds w d = w , d
  glob-ws (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds (wN , _) d =
    tt , proj₁ IH ∷ proj₂ IH
    where IH = glob-ws N ds wN d
  glob-ws (app ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (lit B k ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (pair-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (fst-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (snd-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (tuple n ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (get i ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (inl-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (inr-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (case-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (let-op ⦅ args ⦆) ds w d = glob-ws-args args ds w d
  glob-ws (prim p ⦅ args ⦆) ds w d = glob-ws-args args ds w d

  glob-ws-arg (ast M) ds w d = glob-ws M ds w d
  glob-ws-arg (bind a) ds w d = glob-ws-arg a ds w d
  glob-ws-arg (clear a) ds w d = glob-ws-arg a ds w d

  glob-ws-args nil ds w d = tt , d
  glob-ws-args (cons a args) ds (w , ws) d =
    (proj₁ A , proj₁ R) , proj₂ R
    where
    A = glob-ws-arg a ds w d
    R = glob-ws-args args (proj₂ (glob-arg a ds)) ws (proj₂ A)

{- The compiler ----------------------------------------------------------------------}

{- the Clos4 program before globalize is closed -}
compile₄-closed : ∀ M → Closed M → W4.WS 0 (compile₄ M)
compile₄-closed M c =
  Del.delay-ws M₃ (Conc.concretize-closed M₂' (Opt.prune-closed M₂ (ES.capture-closed (simplify M) (simplify-closed M c))))
  where
  M₂ = capture (simplify M)
  M₂' = Untyped.Compiler.Prune.prune-program M₂
  M₃ = Untyped.Compiler.Concretize.concretize-program M₂'

compile-scoped : ∀ M → Closed M → Scoped (compile M)
compile-scoped M c = proj₂ G , proj₁ G
  where G = Glob.glob-ws (compile₄ M) [] (compile₄-closed M c) []
