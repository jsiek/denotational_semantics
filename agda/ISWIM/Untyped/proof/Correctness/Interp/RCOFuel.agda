{-

  Correctness of remove complex operands (Clos5 → Clos5, Compiler/RCO.agda),
  clock for clock (see the design note in Clock.agda).

  The pass only adds lets, which do not tick, and atoms evaluate without
  calling anything, so a term and its rco evaluate in the same
  environment to the same result, for every clock. Values are related by
  equality: a code pointer code k names definition k in either table, and
  definition k of map rco ds is rco of definition k of ds (glob-pw).

  The key lemma is the one for a chain of lets (lets≈): evaluating

    lets (binds (atomize Ms)) X

  evaluates the complex operands of Ms left to right, and then X in the
  environment extended with their values, where the atoms evaluate to
  the values of the operands. We state it with evals, which evaluates
  operands left to right and passes their values to a continuation K;
  each construct's evaluation is evals with its own K (c-app, c-pair, …).
  Operands under more lets are shifted, so we need that renaming commutes
  with evaluation (ren).

  Precondition. An atom is evaluated after the complex operands that
  follow it, so an unbound variable, which errors, would error
  later: pair (` 0) L, with L a loop, errors in the empty
  environment, but its rco, let x = L in pair (` 1) (` 0), diverges. So
  the variables must be in scope (Scoped): main in the empty
  environment, and each definition in its two parameters. The only fact
  about scoping that the proof uses is that a variable operand is bound
  (Bnd). The compiler produces such programs (compile-scoped,
  Compiler/PipelineScope.agda).

-}

module Untyped.proof.Correctness.Interp.RCOFuel where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Untyped.Language.Clos5
import Untyped.Language.Mon as Mon
open import Untyped.Compiler.RCO
open import proof.Framework.Syntax.Rename Op sig using (ext; rename; rename-args)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-args)
open import proof.Framework.ListUtil using (_‼_; ‼-<; ‼-++; length-snoc; ‼-pw)
open import proof.Semantics.Interp.Clock
open import Untyped.Semantics.Interp.Clos5
  using (Val; Env; code; pair; const; tup; inl; inr; eval; eval-args; call; code?; branch;
         first; second; project; prim?)
import Untyped.Semantics.Interp.Clos5 as T
import Semantics.Interp.ISWIM as ISWIM
open import Untyped.Compiler.Pipeline using (compile; compile-mon)
open import Untyped.proof.Compiler.CaptureScope using (Closed)
open import Untyped.proof.Correctness.Interp.CompilerFuel using (compile-correct)
open import Untyped.proof.Compiler.PipelineScope using (Scoped; compile-scoped)

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; [_]; length; replicate; reverse; map)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Scoping: a variable operand is bound -----------------------------------------}

Bnd : ℕ → AST → Set
Bnd k (` x) = x < k
Bnd k (_ ⦅ _ ⦆) = ⊤

Bnds : ℕ → ∀ {n} → Args (replicate n ■) → Set
Bnds k {zero} Nil = ⊤
Bnds k {suc n} (M ,, Ms) = Bnd k M × Bnds k Ms

bnds-suc : ∀ {k n} (Ms : Args (replicate n ■)) → Bnds k Ms → Bnds (suc k) (rename-args suc Ms)
bnds-suc {n = zero} Nil b = tt
bnds-suc {n = suc n} ((` x) ,, Ms) (b , bs) = s≤s b , bnds-suc Ms bs
bnds-suc {n = suc n} ((_ ⦅ _ ⦆) ,, Ms) (b , bs) = tt , bnds-suc Ms bs

lets-bnd : ∀ {k} bs {X} → Bnd k X → Bnd k (lets bs X)
lets-bnd [] b = b
lets-bnd (_ ∷ _) b = tt

{- rco M is a variable only if M is -}
rco-bnd : ∀ {k} M → WS k M → Bnd k (rco M)
rco-bnd (` x) w = w
rco-bnd (fun-ref k ⦅ Nil ⦆) w = tt
rco-bnd (app ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (lit B k ⦅ Nil ⦆) w = tt
rco-bnd (pair-op ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (fst-op ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (snd-op ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (tuple n ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (get i ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (inl-op ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (inr-op ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) w = lets-bnd _ (case-bnd (atoms (atomize (rco L ,, Nil))))
  where case-bnd : ∀ {k j} As → Bnd k (case-on (rco M) (rco N) j As)
        case-bnd (A ,, Nil) = tt
rco-bnd (prim p ⦅ Ms ⦆) w = lets-bnd _ tt
rco-bnd (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) w = tt

rco-bnds : ∀ {k n} (Ms : Args (replicate n ■)) → WS-args k Ms → Bnds k (rco-args Ms)
rco-bnds {n = zero} Nil w = tt
rco-bnds {n = suc n} (M ,, Ms) (w , ws) = rco-bnd M w , rco-bnds Ms ws

{- Evaluating operands, and evaluating under lets ---------------------------------}

‼-shift : ∀ (us ρ : Env) x → (us ++ ρ) ‼ (length us + x) ≡ ρ ‼ x
‼-shift [] ρ x = refl
‼-shift (u ∷ us) ρ x = ‼-shift us ρ x

{- the continuations of the constructs that do not call -}
K1 : (Val → Result Val) → Vec Val 1 → Result Val
K1 g (v ∷ []) = g v

K2 : (Val → Val → Result Val) → Vec Val 2 → Result Val
K2 g (v ∷ w ∷ []) = g v w

revapp : ∀ {n} → Vec Val n → List Val → List Val
revapp [] acc = acc
revapp (v ∷ vs) acc = revapp vs (v ∷ acc)

K-tup : ∀ {n} → Vec Val n → Result Val
K-tup vs = ret (tup (reverse (revapp vs [])))

{- for the interpreter with the table ds -}
module Gen (ds : List AST) where

  {- evaluate the operands left to right, then continue with their values -}
  evals : ∀ {n} → ℕ → Env → Args (replicate n ■) → (Vec Val n → Result Val) → Result Val
  evals {zero} ck ρ Nil K = K []
  evals {suc n} ck ρ (M ,, Ms) K = eval ds ck ρ M >>= λ v → evals ck ρ Ms (λ vs → K (v ∷ vs))

  K-app : ℕ → Vec Val 3 → Result Val
  K-app ck (f ∷ e ∷ w ∷ []) = call ds ck (code? ds f) (w ∷ e ∷ [])

  {- each construct evaluates its operands, then continues -}
  c-app : ∀ ck ρ As → eval ds ck ρ (app ⦅ As ⦆) ≡ evals ck ρ As (K-app ck)
  c-app ck ρ (L ,, M ,, N ,, Nil) = refl
  c-pair : ∀ ck ρ As → eval ds ck ρ (pair-op ⦅ As ⦆) ≡ evals ck ρ As (K2 λ v w → ret (pair v w))
  c-pair ck ρ (L ,, M ,, Nil) = refl
  c-fst : ∀ ck ρ As → eval ds ck ρ (fst-op ⦅ As ⦆) ≡ evals ck ρ As (K1 first)
  c-fst ck ρ (M ,, Nil) = refl
  c-snd : ∀ ck ρ As → eval ds ck ρ (snd-op ⦅ As ⦆) ≡ evals ck ρ As (K1 second)
  c-snd ck ρ (M ,, Nil) = refl
  c-get : ∀ {n} (i : _) ck ρ As → eval ds ck ρ (get {n} i ⦅ As ⦆) ≡ evals ck ρ As (K1 (project i))
  c-get i ck ρ (M ,, Nil) = refl
  c-inl : ∀ ck ρ As → eval ds ck ρ (inl-op ⦅ As ⦆) ≡ evals ck ρ As (K1 λ v → ret (inl v))
  c-inl ck ρ (M ,, Nil) = refl
  c-inr : ∀ ck ρ As → eval ds ck ρ (inr-op ⦅ As ⦆) ≡ evals ck ρ As (K1 λ v → ret (inr v))
  c-inr ck ρ (M ,, Nil) = refl
  c-prim : ∀ p ck ρ As → eval ds ck ρ (prim p ⦅ As ⦆) ≡ evals ck ρ As (K2 λ v w → from-maybe (prim? p v w))
  c-prim p ck ρ (L ,, M ,, Nil) = refl

  args-evals : ∀ ck ρ acc {n} (As : Args (replicate n ■)) (k : List Val → Result Val)
    → (eval-args ds ck ρ acc As >>= k) ≡ evals ck ρ As (λ vs → k (revapp vs acc))
  args-evals ck ρ acc {zero} Nil k = refl
  args-evals ck ρ acc {suc n} (M ,, As) k =
    trans (bind-assoc (eval ds ck ρ M))
      (bind-cong (eval ds ck ρ M) λ v → args-evals ck ρ (v ∷ acc) As k)

  c-tuple : ∀ ck ρ {n} (As : Args (replicate n ■)) → eval ds ck ρ (tuple n ⦅ As ⦆) ≡ evals ck ρ As K-tup
  c-tuple ck ρ As = args-evals ck ρ [] As _

  {- Renaming: r takes each variable of ρ₁ to one of ρ₂ with the same value -}
  Ren : (ℕ → ℕ) → Env → Env → Set
  Ren r ρ₁ ρ₂ = ∀ x → ρ₁ ‼ x ≡ ρ₂ ‼ r x

  ren-ext : ∀ {r ρ₁ ρ₂} v → Ren r ρ₁ ρ₂ → Ren (ext r) (v ∷ ρ₁) (v ∷ ρ₂)
  ren-ext v h zero = refl
  ren-ext v h (suc x) = h x

  shift-ren : ∀ us {ρ} j → length us ≡ j → Ren (j +_) ρ (us ++ ρ)
  shift-ren us _ refl x = sym (‼-shift us _ x)

  ren : ∀ ck r {ρ₁ ρ₂} M → Ren r ρ₁ ρ₂ → eval ds ck ρ₁ M ≡ eval ds ck ρ₂ (rename r M)
  ren-args : ∀ ck r {n ρ₁ ρ₂ vs} (Ms : Args (replicate n ■)) → Ren r ρ₁ ρ₂
    → eval-args ds ck ρ₁ vs Ms ≡ eval-args ds ck ρ₂ vs (rename-args r Ms)

  ren ck r (` x) h = cong from-maybe (h x)
  ren ck r (fun-ref k ⦅ Nil ⦆) h = refl
  ren ck r (app ⦅ L ,, M ,, N ,, Nil ⦆) h =
    bind≡ (ren ck r L h) λ f → bind≡ (ren ck r M h) λ e → bind≡ (ren ck r N h) λ w → refl
  ren ck r (lit B k ⦅ Nil ⦆) h = refl
  ren ck r (pair-op ⦅ L ,, M ,, Nil ⦆) h = bind≡ (ren ck r L h) λ v → bind≡ (ren ck r M h) λ w → refl
  ren ck r (fst-op ⦅ M ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → refl
  ren ck r (snd-op ⦅ M ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → refl
  ren ck r (tuple n ⦅ Ms ⦆) h = bind≡ (ren-args ck r Ms h) λ vs → refl
  ren ck r (get i ⦅ M ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → refl
  ren ck r (inl-op ⦅ M ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → refl
  ren ck r (inr-op ⦅ M ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → refl
  ren ck r {ρ₁} {ρ₂} (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) h = bind≡ (ren ck r L h) br
    where br : ∀ v → branch ds ck ρ₁ M N v ≡ branch ds ck ρ₂ (rename (ext r) M) (rename (ext r) N) v
          br (inl v) = ren ck (ext r) M (ren-ext v h)
          br (inr v) = ren ck (ext r) N (ren-ext v h)
          br (code k) = refl
          br (pair v w) = refl
          br (const B k) = refl
          br (tup vs) = refl
  ren ck r (prim p ⦅ L ,, M ,, Nil ⦆) h = bind≡ (ren ck r L h) λ v → bind≡ (ren ck r M h) λ w → refl
  ren ck r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) h = bind≡ (ren ck r M h) λ v → ren ck (ext r) N (ren-ext v h)

  ren-args ck r {zero} Nil h = refl
  ren-args ck r {suc n} (M ,, Ms) h = bind≡ (ren ck r M h) λ v → ren-args ck r Ms h

  ren-evals : ∀ ck r {n ρ₁ ρ₂} (Ms : Args (replicate n ■)) {K} → Ren r ρ₁ ρ₂
    → evals ck ρ₁ Ms K ≡ evals ck ρ₂ (rename-args r Ms) K
  ren-evals ck r {zero} Nil h = refl
  ren-evals ck r {suc n} (M ,, Ms) h = bind≡ (ren ck r M h) λ v → ren-evals ck r Ms h

  {- an atom whose variable is bound evaluates to a value, without calling -}
  atom-val : ∀ ck {ρ M} → Mon.Atom M → Bnd (length ρ) M → Σ[ v ∈ Val ] eval ds ck ρ M ≡ ret v
  atom-val ck {ρ} (Mon.var x) b with ‼-< ρ x b
  ... | v , e = v , cong from-maybe e
  atom-val ck (Mon.lit B k) b = const B k , refl
  atom-val ck (Mon.ref k) b = code k , refl

  {- the variable bound by the last let of a chain, under us -}
  var-step : ∀ ck us {v ρ n} j {As : Args (replicate n ■)} {K} → length us ≡ j
    → evals ck (us ++ v ∷ ρ) (` j ,, As) K ≡ evals ck (us ++ v ∷ ρ) As (λ vs → K (v ∷ vs))
  var-step ck us {v} {ρ} _ refl rewrite ‼-++ us {v} {ρ} = refl

  {- The let chain: evaluating lets (binds (atomize Ms)) X evaluates the
     complex operands of Ms, then X with the atoms bound to the values of
     the operands -}
  lets≈ : ∀ ck ρ {n} (Ms : Args (replicate n ■)) {K X} → Bnds (length ρ) Ms
    → (∀ us → length us ≡ length (binds (atomize Ms))
         → evals ck (us ++ ρ) (atoms (atomize Ms)) K ≡ eval ds ck (us ++ ρ) X)
    → evals ck ρ Ms K ≡ eval ds ck ρ (lets (binds (atomize Ms)) X)
  lets≈ ck ρ {zero} Nil b h = h [] refl
  lets≈ ck ρ {suc n} (M ,, Ms) {K} {X} (b , bs) h with atom? M
  ... | yes a with atom-val ck a b
  ...   | v , e = trans (cong (_>>= λ v → evals ck ρ Ms (λ vs → K (v ∷ vs))) e) (lets≈ ck ρ Ms bs h')
    where
    Bd = atomize Ms
    h' : ∀ us → length us ≡ length (binds Bd)
      → evals ck (us ++ ρ) (atoms Bd) (λ vs → K (v ∷ vs)) ≡ eval ds ck (us ++ ρ) X
    h' us eq =
      trans (cong (_>>= λ v → evals ck (us ++ ρ) (atoms Bd) (λ vs → K (v ∷ vs)))
                  (sym (trans (sym (ren ck (length (binds Bd) +_) M (shift-ren us _ eq))) e)))
            (h us eq)
  lets≈ ck ρ {suc n} (M ,, Ms) {K} {X} (b , bs) h | no _ =
    bind-cong (eval ds ck ρ M) λ v →
      trans (ren-evals ck suc Ms (λ x → refl))
            (lets≈ ck (v ∷ ρ) (rename-args suc Ms) (bnds-suc Ms bs) (h' v))
    where
    Bd = atomize (rename-args suc Ms)
    h' : ∀ v us → length us ≡ length (binds Bd)
      → evals ck (us ++ v ∷ ρ) (atoms Bd) (λ vs → K (v ∷ vs)) ≡ eval ds ck (us ++ v ∷ ρ) X
    h' v us eq =
      trans (sym (var-step ck us {v} {ρ} _ {atoms Bd} {K} eq))
        (subst (λ ρ' → evals ck ρ' (` length (binds Bd) ,, atoms Bd) K ≡ eval ds ck ρ' X)
               (++-assoc us [ v ] ρ)
               (h (us ∷ʳ v) (trans (length-snoc us v) (cong suc eq))))

  {- case on an atom, with the branches under j more lets -}
  case-hyp : ∀ ck ρ M N j us As → length us ≡ j
    → evals ck (us ++ ρ) As (K1 (branch ds ck ρ M N)) ≡ eval ds ck (us ++ ρ) (case-on M N j As)
  case-hyp ck ρ M N j us (A ,, Nil) eq = bind-cong (eval ds ck (us ++ ρ) A) br
    where br : ∀ v → branch ds ck ρ M N v
                   ≡ branch ds ck (us ++ ρ) (rename (ext (j +_)) M) (rename (ext (j +_)) N) v
          br (inl v) = ren ck (ext (j +_)) M (ren-ext v (shift-ren us j eq))
          br (inr v) = ren ck (ext (j +_)) N (ren-ext v (shift-ren us j eq))
          br (code k) = refl
          br (pair v w) = refl
          br (const B k) = refl
          br (tup vs) = refl

{- The table -------------------------------------------------------------------}

{- definition k of map rco ds is rco of definition k of ds -}
Def : AST → AST → Set
Def N N' = N' ≡ rco N × WS 2 N

glob-pw : ∀ {ds} → All (WS 2) ds → ∀ k → M.Pointwise Def (global ds k) (global (map rco ds) k)
glob-pw w = ‼-pw (reverse⁺ (defs-pw w))
  where defs-pw : ∀ {ds} → All (WS 2) ds → Pointwise Def ds (map rco ds)
        defs-pw [] = []
        defs-pw (w ∷ ws) = (refl , w) ∷ defs-pw ws

{- Clock for clock ----------------------------------------------------------------}

module _ (ds : List AST) (wds : All (WS 2) ds) where
  private
    ds' = map rco ds
    module S = Gen ds
    module R = Gen ds'

  run≈ : ∀ ck ρ M → WS (length ρ) M → eval ds ck ρ M ≡ eval ds' ck ρ (rco M)
  args≈ : ∀ ck ρ {n} (Ms : Args (replicate n ■)) {K K'} → WS-args (length ρ) Ms
    → (∀ vs → K vs ≡ K' vs) → S.evals ck ρ Ms K ≡ R.evals ck ρ (rco-args Ms) K'
  {- a construct: its operands, then the let chain of rco -}
  op≈ : ∀ ck ρ {n} (Ms : Args (replicate n ■)) f {K K'} → WS-args (length ρ) Ms
    → (∀ vs → K vs ≡ K' vs)
    → (∀ j us As → length us ≡ j → R.evals ck (us ++ ρ) As K' ≡ eval ds' ck (us ++ ρ) (f j As))
    → S.evals ck ρ Ms K ≡ eval ds' ck ρ (lift f (rco-args Ms))
  {- a construct that does not call -}
  plain≈ : ∀ ck ρ {n} (Ms : Args (replicate n ■)) (op : Args (replicate n ■) → AST) {K}
    → WS-args (length ρ) Ms → (∀ ρ' As → eval ds' ck ρ' (op As) ≡ R.evals ck ρ' As K)
    → S.evals ck ρ Ms K ≡ eval ds' ck ρ (lift (λ _ → op) (rco-args Ms))
  app≈ : ∀ ck vs → S.K-app ck vs ≡ R.K-app ck vs
  call≈ : ∀ ck f w e → call ds ck (code? ds f) (w ∷ e ∷ []) ≡ call ds' ck (code? ds' f) (w ∷ e ∷ [])
  call-pw : ∀ ck {mN mN'} → M.Pointwise Def mN mN' → ∀ w e
    → call ds ck mN (w ∷ e ∷ []) ≡ call ds' ck mN' (w ∷ e ∷ [])

  run≈ ck ρ (` x) w = refl
  run≈ ck ρ (fun-ref k ⦅ Nil ⦆) w = refl
  run≈ ck ρ (app ⦅ Ms ⦆) w =
    trans (S.c-app ck ρ Ms)
      (op≈ ck ρ Ms (λ _ → app ⦅_⦆) w (app≈ ck) λ _ us As _ → sym (R.c-app ck (us ++ ρ) As))
  run≈ ck ρ (lit B k ⦅ Nil ⦆) w = refl
  run≈ ck ρ (pair-op ⦅ Ms ⦆) w =
    trans (S.c-pair ck ρ Ms) (plain≈ ck ρ Ms (pair-op ⦅_⦆) w (R.c-pair ck))
  run≈ ck ρ (fst-op ⦅ Ms ⦆) w =
    trans (S.c-fst ck ρ Ms) (plain≈ ck ρ Ms (fst-op ⦅_⦆) w (R.c-fst ck))
  run≈ ck ρ (snd-op ⦅ Ms ⦆) w =
    trans (S.c-snd ck ρ Ms) (plain≈ ck ρ Ms (snd-op ⦅_⦆) w (R.c-snd ck))
  run≈ ck ρ (tuple n ⦅ Ms ⦆) w =
    trans (S.c-tuple ck ρ Ms) (plain≈ ck ρ Ms (tuple n ⦅_⦆) w (λ ρ' → R.c-tuple ck ρ'))
  run≈ ck ρ (get i ⦅ Ms ⦆) w =
    trans (S.c-get i ck ρ Ms) (plain≈ ck ρ Ms (get i ⦅_⦆) w (R.c-get i ck))
  run≈ ck ρ (inl-op ⦅ Ms ⦆) w =
    trans (S.c-inl ck ρ Ms) (plain≈ ck ρ Ms (inl-op ⦅_⦆) w (R.c-inl ck))
  run≈ ck ρ (inr-op ⦅ Ms ⦆) w =
    trans (S.c-inr ck ρ Ms) (plain≈ ck ρ Ms (inr-op ⦅_⦆) w (R.c-inr ck))
  run≈ ck ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
    trans (bind≡ (run≈ ck ρ L wL) br≈)
      (R.lets≈ ck ρ (rco L ,, Nil) {K1 (branch ds' ck ρ (rco M) (rco N))}
        {case-on (rco M) (rco N) (length (binds Bc)) (atoms Bc)}
        (rco-bnd L wL , tt) λ us eq → R.case-hyp ck ρ (rco M) (rco N) _ us (atoms Bc) eq)
    where Bc = atomize (rco L ,, Nil)
          br≈ : ∀ v → branch ds ck ρ M N v ≡ branch ds' ck ρ (rco M) (rco N) v
          br≈ (inl v) = run≈ ck (v ∷ ρ) M wM
          br≈ (inr v) = run≈ ck (v ∷ ρ) N wN
          br≈ (code k) = refl
          br≈ (pair v w) = refl
          br≈ (const B k) = refl
          br≈ (tup vs) = refl
  run≈ ck ρ (prim p ⦅ Ms ⦆) w =
    trans (S.c-prim p ck ρ Ms) (plain≈ ck ρ Ms (prim p ⦅_⦆) w (R.c-prim p ck))
  run≈ ck ρ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) =
    bind≡ (run≈ ck ρ M wM) λ v → run≈ ck (v ∷ ρ) N wN

  args≈ ck ρ {zero} Nil w k = k []
  args≈ ck ρ {suc n} (M ,, Ms) (wM , ws) k =
    bind≡ (run≈ ck ρ M wM) λ v → args≈ ck ρ Ms ws (λ vs → k (v ∷ vs))

  op≈ ck ρ Ms f w k h =
    trans (args≈ ck ρ Ms w k) (R.lets≈ ck ρ (rco-args Ms) (rco-bnds Ms w) (λ us eq → h _ us _ eq))

  plain≈ ck ρ Ms op w c = op≈ ck ρ Ms (λ _ → op) w (λ _ → refl) λ _ us As _ → sym (c (us ++ ρ) As)

  app≈ ck (f ∷ e ∷ w ∷ []) = call≈ ck f w e

  call≈ ck (code k) w e = call-pw ck (glob-pw wds k) w e
  call≈ ck (pair _ _) w e = refl
  call≈ ck (const B k) w e = refl
  call≈ ck (tup _) w e = refl
  call≈ ck (inl _) w e = refl
  call≈ ck (inr _) w e = refl

  call-pw ck M.nothing w e = refl
  call-pw zero (M.just _) w e = refl
  call-pw (suc ck) {just N} (M.just (refl , wN)) w e = run≈ ck (w ∷ e ∷ []) N wN

{- The end theorem: for every scoped Clos5 program --------------------------------}

rco-correct : ∀ P → Scoped P → Equivalent (T.sem P) (T.sem (rco-program P))
rco-correct (program ds M) (wds , w) = clocked-≡ λ ck → run≈ ds wds ck [] M w

{- The whole compiler, into monadic normal form ------------------------------------}

compile-mon-correct : ∀ M → Closed M → Equivalent (ISWIM.sem M) (T.sem (compile-mon M))
compile-mon-correct M c = equiv-trans (compile-correct M c) (rco-correct (compile M) (compile-scoped M c))
