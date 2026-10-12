{-

  Correctness of lift locals (monadic Clos5 → Imp, Compile/LiftLocals.agda),
  clock for clock (see the design note in Clock.agda). The pass maps each
  call to one call, so the interpreters tick in lock step, and values are
  related by equality (Imp has the values of Clos5): code k names
  definition k in either table, and definition k of the Imp program is
  the lifted definition k of the Clos5 program.

  The relation of an environment ρ to a frame φ of n slots (Fr): φ is
  ρ ʳ++ τ, the reversed environment then any other slots τ, and has n
  slots. So the variable x < length ρ is slot length ρ ∸ suc x (rev‼),
  the depth of lift is length ρ, and the slot length ρ that a let or
  case at that depth assigns is the head of τ (set-ʳ++); the frame of
  the body, (v ∷ ρ) ʳ++ τ, is ρ ʳ++ (v ∷ τ), so the frame it returns is
  still related to ρ. The frame has the slot, since n ≥ length ρ +
  height m. A variable out of scope (x ≥ length ρ) goes wrong on both
  sides: it is beyond ρ, and its slot n is beyond the frame. So there
  is no precondition.

-}

module proof.Compiler.Functional.Correctness.LiftLocalsFuel where

open import Compiler.Lang.Clos5 using (AST; program)
import Compiler.Lang.Clos5 as C5
open import Compiler.Lang.Mon
open import Compiler.Lang.Imp using (Body)
import Compiler.Lang.Imp as Imp
open import Compiler.Compile.LiftLocals
open import Framework.ListUtil using (_‼_; ‼-++; ‼-≥)
open import Compiler.Functional.Clock
import Compiler.Functional.Interp.Clos5 as C
import Compiler.Functional.Interp.Imp as I
open import Compiler.Functional.Interp.Imp using (Frame; zero-val; _[_]≔_; here)
open import Compiler.Functional.Interp.Clos5 using (Val; code; pair; const; tup; inl; inr; obs)
import Compiler.Functional.Interp.ISWIM as ISWIM
open import proof.Compiler.Functional.Correctness.RCOFuel using (bind≡; ≡→rel; ‼-pw; compile-mon-correct)
open import Compiler.Compile.Pipeline using (compile; compile-mon; compile-imp)
open import Compiler.Compile.RCO using (rco-program-mon)
open import Compiler.Compile.EncloseScope using (Closed)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_; _++_; length; reverse; replicate)
open import Data.List.Properties using (ʳ++-defn; length-ʳ++; length-reverse; length-replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; _<?_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≮⇒≥; n≮n; +-suc; +-identityʳ; +-monoʳ-≤; m≤m⊔n; m≤n⊔m; m+n≤o⇒m≤o)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

private variable A B C : Set

{- Results -------------------------------------------------------------------------}

{- equal results, then related continuations -}
rel : ∀ {r r' : Result A} {f : A → Result B} {g : A → Result C} {S}
  → r ≡ r' → (∀ v → RelResult S (f v) (g v)) → RelResult S (r >>= f) (r' >>= g)
rel {r = timeout} refl k = timeout
rel {r = wrong} refl k = wrong
rel {r = ret v} refl k = k v

{- related results, mapped -}
ret-rel : ∀ {R S} {r : Result A} {r' : Result B} {g : B → C}
  → (∀ {v w} → R v w → S v (g w)) → RelResult R r r' → RelResult S r (r' >>= λ w → ret (g w))
ret-rel h timeout = timeout
ret-rel h wrong = wrong
ret-rel h (ret r) = ret (h r)

{- Frames ---------------------------------------------------------------------------}

{- the frame φ of n slots holds the environment ρ, reversed, at the bottom -}
data Fr (n : ℕ) (ρ : List Val) : Frame → Set where
  fr : ∀ τ → length (ρ ʳ++ τ) ≡ n → Fr n ρ (ρ ʳ++ τ)

{- a value and the frame it left, related to a value with ρ -}
Out : ℕ → List Val → Val → Val × Frame → Set
Out n ρ v p = v ≡ proj₁ p × Fr n ρ (proj₂ p)

{- variable x is slot length ρ ∸ suc x -}
rev‼ : ∀ (ρ τ : List Val) x → x < length ρ → (ρ ʳ++ τ) ‼ (length ρ ∸ suc x) ≡ ρ ‼ x
rev‼ (u ∷ ρ) τ zero _ =
  trans (cong (_‼ length ρ) (ʳ++-defn ρ))
        (subst (λ k → (reverse ρ ++ u ∷ τ) ‼ k ≡ just u) (length-reverse ρ) (‼-++ (reverse ρ)))
rev‼ (u ∷ ρ) τ (suc x) (s≤s x<) = rev‼ ρ (u ∷ τ) x x<

set-++ : ∀ (ws : List Val) {t τ v} → (ws ++ t ∷ τ) [ length ws ]≔ v ≡ just (ws ++ v ∷ τ)
set-++ [] = refl
set-++ (w ∷ ws) {t} {τ} {v} rewrite set-++ ws {t} {τ} {v} = refl

{- assigning slot length ρ -}
set-ʳ++ : ∀ (ρ : List Val) {t τ v} → (ρ ʳ++ (t ∷ τ)) [ length ρ ]≔ v ≡ just (ρ ʳ++ (v ∷ τ))
set-ʳ++ ρ {t} {τ} {v} rewrite ʳ++-defn ρ {t ∷ τ} | ʳ++-defn ρ {v ∷ τ} | sym (length-reverse ρ) = set-++ (reverse ρ)

var≈ : ∀ {n ρ φ} → Fr n ρ φ → ∀ x → ρ ‼ x ≡ φ ‼ slot n (length ρ) x
var≈ {n} {ρ} (fr τ len) x with x <? length ρ
... | yes x< = sym (rev‼ ρ τ x x<)
... | no x≮ = trans (‼-≥ ρ x (≮⇒≥ x≮)) (sym (‼-≥ (ρ ʳ++ τ) n (≤-reflexive len)))

atom≈ : ∀ {ds ck n ρ φ M} (a : Atom M) → Fr n ρ φ → C.eval ds ck ρ M ≡ I.atom φ (lift-atom n (length ρ) a)
atom≈ (var x) ok = cong from-maybe (var≈ ok x)
atom≈ (lit B k) ok = refl
atom≈ (ref k) ok = refl

atoms≈ : ∀ {ds ck n ρ φ k Ms} (as : Atoms {k} Ms) vs → Fr n ρ φ
  → C.eval-args ds ck ρ vs Ms ≡ I.atoms φ vs (lift-atoms n (length ρ) as)
atoms≈ [] vs ok = refl
atoms≈ (a ∷ as) vs ok = bind≡ (atom≈ a ok) λ v → atoms≈ as (v ∷ vs) ok

here-rel : ∀ {n ρ φ r r'} → Fr n ρ φ → RelResult _≡_ r r' → RelResult (Out n ρ) r (here φ r')
here-rel ok = ret-rel λ e → e , ok

{- the heights of the subterms -}
sub : ∀ d {a b n} → a ≤ b → d + b ≤ n → d + a ≤ n
sub d a≤b = ≤-trans (+-monoʳ-≤ d a≤b)

up : ∀ d {a n} → d + suc a ≤ n → suc d + a ≤ n
up d {a} {n} = subst (_≤ n) (+-suc d a)

{- The table ------------------------------------------------------------------------}

Def : AST → Body → Set
Def N b = Σ[ m ∈ Mon N ] b ≡ lift-body 2 m

glob-pw : ∀ {ds} (ms : All Mon ds) k → M.Pointwise Def (C5.global ds k) (Imp.global (lift-defs ms) k)
glob-pw ms = ‼-pw (reverse⁺ (defs-pw ms))
  where defs-pw : ∀ {ds} (ms : All Mon ds) → Pointwise Def ds (lift-defs ms)
        defs-pw [] = []
        defs-pw (m ∷ ms) = (m , refl) ∷ defs-pw ms

{- Clock for clock ------------------------------------------------------------------}

module _ (ds : List AST) (ms : All Mon ds) where
  private ds' = lift-defs ms

  {- m at depth length ρ, in a frame of n slots -}
  sim : ∀ ck n ρ φ {M} (m : Mon M) → length ρ + height m ≤ n → Fr n ρ φ
    → RelResult (Out n ρ) (C.eval ds ck ρ M) (I.eval ds' ck φ (lift n (length ρ) m))
  {- v := slot length ρ, then m -}
  under : ∀ ck n ρ φ v {M} (m : Mon M) → suc (length ρ) + height m ≤ n → Fr n ρ φ
    → RelResult (Out n ρ) (C.eval ds ck (v ∷ ρ) M) (I.put ds' ck φ (length ρ) v (lift n (suc (length ρ)) m))
  call≈ : ∀ ck f e w → RelResult _≡_ (C.call ds ck (C.code? ds f) (w ∷ e ∷ [])) (I.call ds' ck (I.code? ds' f) e w)
  call-pw : ∀ ck {mN mb} → M.Pointwise Def mN mb → ∀ e w
    → RelResult _≡_ (C.call ds ck mN (w ∷ e ∷ [])) (I.call ds' ck mb e w)

  sim ck n ρ φ (atom a) h ok = here-rel ok (≡→rel (atom≈ a ok))
  sim ck n ρ φ (app (a ∷ b ∷ c ∷ [])) h ok =
    here-rel ok (rel (atom≈ a ok) λ f → rel (atom≈ b ok) λ e → rel (atom≈ c ok) λ w → call≈ ck f e w)
  sim ck n ρ φ (pair (a ∷ b ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → rel (atom≈ b ok) λ w → ret refl)
  sim ck n ρ φ (fst (a ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → ≡→rel refl)
  sim ck n ρ φ (snd (a ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → ≡→rel refl)
  sim ck n ρ φ (tuple as) h ok = here-rel ok (rel (atoms≈ as [] ok) λ vs → ret refl)
  sim ck n ρ φ (get (a ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → ≡→rel refl)
  sim ck n ρ φ (inl (a ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → ret refl)
  sim ck n ρ φ (inr (a ∷ [])) h ok = here-rel ok (rel (atom≈ a ok) λ v → ret refl)
  sim ck n ρ φ (prim (a ∷ b ∷ [])) h ok =
    here-rel ok (rel (atom≈ a ok) λ v → rel (atom≈ b ok) λ w → ≡→rel refl)
  sim ck n ρ φ (case a m₁ m₂) h ok = rel (atom≈ a ok) br
    where
    d = length ρ
    br : ∀ v → RelResult (Out n ρ) (C.branch ds ck ρ _ _ v) (I.inj? v >>= _)
    br (inl v) = under ck n ρ φ v m₁ (up d (sub d (s≤s (m≤m⊔n _ _)) h)) ok
    br (inr v) = under ck n ρ φ v m₂ (up d (sub d (s≤s (m≤n⊔m _ _)) h)) ok
    br (code k) = wrong
    br (pair v w) = wrong
    br (const B k) = wrong
    br (tup vs) = wrong
  sim ck n ρ φ (let′ m₁ m₂) h ok =
    bind-rel (sim ck n ρ φ m₁ (sub d (m≤m⊔n _ _) h) ok)
      λ { (refl , ok₁) → under ck n ρ _ _ m₂ (up d (sub d (m≤n⊔m _ _) h)) ok₁ }
    where d = length ρ

  under ck n ρ _ v m h (fr [] len) =
    ⊥-elim (n≮n d (subst (suc d ≤_) (trans (sym len) (trans (length-ʳ++ ρ) (+-identityʳ d)))
                                    (m+n≤o⇒m≤o (suc d) h)))
    where d = length ρ
  under ck n ρ _ v m h (fr (t ∷ τ) len) rewrite set-ʳ++ ρ {t} {τ} {v} =
    weaken (sim ck n (v ∷ ρ) (ρ ʳ++ (v ∷ τ)) m h (fr τ (trans (length-ʳ++ ρ) (trans (sym (length-ʳ++ ρ)) len))))
    where
    weaken : ∀ {r r'} → RelResult (Out n (v ∷ ρ)) r r' → RelResult (Out n ρ) r r'
    weaken timeout = timeout
    weaken wrong = wrong
    weaken (ret (e , fr τ' len')) = ret (e , fr (v ∷ τ') len')

  call≈ ck (code k) e w = call-pw ck (glob-pw ms k) e w
  call≈ ck (pair _ _) e w = wrong
  call≈ ck (const B k) e w = wrong
  call≈ ck (tup _) e w = wrong
  call≈ ck (inl _) e w = wrong
  call≈ ck (inr _) e w = wrong

  call-pw ck M.nothing e w = wrong
  call-pw zero (M.just _) e w = timeout
  call-pw (suc ck) (M.just (m , refl)) e w =
    ret-rel proj₁ (sim ck (2 + height m) (w ∷ e ∷ []) _ m ≤-refl
                     (fr (replicate (height m) zero-val) (cong (λ k → suc (suc k)) (length-replicate _))))

{- The end theorem: for every monadic Clos5 program ------------------------------------}

lift-correct : ∀ P (mp : MonProgram P) → Equivalent (C.sem P) (I.sem (lift-program P mp))
lift-correct (program ds M) (ms , m) = clocked _≡_ (cong obs) λ ck →
  ret-rel proj₁ (sim ds ms ck (height m) [] _ m ≤-refl (fr (replicate (height m) zero-val) (length-replicate _)))

{- The whole compiler, into Imp --------------------------------------------------------}

compile-imp-correct : ∀ M → Closed M → Equivalent (ISWIM.sem M) (I.sem (compile-imp M))
compile-imp-correct M c = equiv-trans (compile-mon-correct M c) (lift-correct (compile-mon M) (rco-program-mon (compile M)))
