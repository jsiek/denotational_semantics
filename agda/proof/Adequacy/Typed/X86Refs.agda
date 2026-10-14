{-

  The X86 programs that the typed compiler produces are well formed
  (proof/Adequacy/X86WF.agda), as far as their operands go: each label
  refers to an older definition and each slot read is within the frame.

  References: globalize makes only references to older definitions
  (proof/Compiler/Typed/GlobalizeOlder.agda), and rco, lift locals,
  explicate control and select instructions keep the references of the
  atoms (R*, for a bound K on their levels). Slots: a slot is a typed
  index into the frame context Δ of its tail, so its level is below the
  length of Δ, and select's frame is at least as deep as every tail's
  context (depth).

-}

module proof.Adequacy.Typed.X86Refs where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Language.Prim using (sub; eq)
import Language.Typed.Clos5 as C
import Language.Typed.Mon as Mo
open Mo using (Atm; var; lit; ref; ren)
import Language.Typed.Imp as I
import Language.Typed.CFG as G
open import Language.X86 using (Block; block; Body; var; reg; loc; imm; label; movq; subq; testinl; load; payload)
import Language.X86 as X
open import Compiler.Typed.RCO using (Ren; rco-program; rco; atomize; atomizes; atomize₂) renaming (K to Kont)
open import Compiler.Typed.LiftLocals using (lift; lift-program)
open import Compiler.Typed.Explicate using (Out; out; after; explicate-assign; explicate-tail; explicate-body; explicate)
open import Compiler.Typed.Select
open import proof.Adequacy.X86WF using (OK; Code; BodyOK; DefsWF)
open import proof.Compiler.Typed.GlobalizeOlder using (Older; Olders; OlderDefs)
open import proof.Framework.Lookup using (lvl-<)

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _⊔_)
open import Data.Nat.Properties using (<-≤-trans; ≤-trans; m≤m⊔n; m≤n⊔m; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; toList; map)

Code-++ : ∀ {L S} xs {ys} → Code L S xs → Code L S ys → Code L S (xs ++ ys)
Code-++ [] _ c = c
Code-++ (i ∷ xs) (r , cs) c = r , Code-++ xs cs c

module _ (K : ℕ) where

  RA : ∀ {Σ Γ A} → Atm Σ Γ A → Set
  RA (var x) = ⊤
  RA (lit B c) = ⊤
  RA (ref f) = lvl f < K

  RAs : ∀ {Σ Γ n} → Vec (Atm Σ Γ Any) n → Set
  RAs [] = ⊤
  RAs (a ∷ as) = RA a × RAs as

  RM : ∀ {Σ Γ A} → Mo.Exp Σ Γ A → Set
  RM (Mo.atm a) = RA a
  RM (Mo.pack a b) = RA a × RA b
  RM (Mo.callc a b) = RA a × RA b
  RM (Mo.tuple as) = RAs as
  RM (Mo.get i a) = RA a
  RM (Mo.inl a) = RA a
  RM (Mo.inr a) = RA a
  RM (Mo.case a e₁ e₂) = RA a × RM e₁ × RM e₂
  RM (Mo.prim p a b) = RA a × RA b
  RM (Mo.let′ e₁ e₂) = RM e₁ × RM e₂
  RM (Mo.inject G a) = RA a
  RM (Mo.project t a) = RA a

  RS : ∀ {Σ Δ A} → I.Simple Σ Δ A → Set
  RS (I.atm a) = RA a
  RS (I.pack a b) = RA a × RA b
  RS (I.callc a b) = RA a × RA b
  RS (I.tuple as) = RAs as
  RS (I.get i a) = RA a
  RS (I.inl a) = RA a
  RS (I.inr a) = RA a
  RS (I.prim p a b) = RA a × RA b
  RS (I.inject G a) = RA a
  RS (I.project t a) = RA a

  RI : ∀ {Σ Δ A} → I.Exp Σ Δ A → Set
  RI (I.simple s) = RS s
  RI (I.assign e₁ e₂) = RI e₁ × RI e₂
  RI (I.case a e₁ e₂) = RA a × RI e₁ × RI e₂

  RT : ∀ {Σ Bs Δ} → G.Tail Σ Bs Δ → Set
  RT (G.return s) = RS s
  RT (G.seq p s t) = RS s × RT t
  RT (G.goto l) = ⊤
  RT (G.case a p l₁ l₂) = RA a

  RB : ∀ {Σ Bs} → G.Blocks Σ Bs → Set
  RB G.[] = ⊤
  RB (bs G.▷ t) = RB bs × RT t

  {- remove complex operands -}

  ren-R : ∀ {Σ Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (a : Atm Σ Γ A) → RA a → RA (ren r a)
  ren-R r (var x) _ = tt
  ren-R r (lit B c) _ = tt
  ren-R r (ref f) h = h

  rco-R : ∀ {Σ Γ Δ A} (M : C.Tm Σ Γ A) (ρ : Ren Γ Δ) → Older K M → RM (rco M ρ)
  atomize-R : ∀ {Σ Γ Δ A B} (M : C.Tm Σ Γ A) (ρ : Ren Γ Δ) {k : Kont Σ Δ A B} → Older K M
    → (∀ {Δ'} (r : Ren Δ Δ') (a : Atm Σ Δ' A) → RA a → RM (k r a)) → RM (atomize {B = B} M ρ k)
  atomizes-R : ∀ {Σ Γ Δ n B} (Ms : Vec (C.Tm Σ Γ Any) n) (ρ : Ren Γ Δ) {k : ∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) n → Mo.Exp Σ Δ' B} → Olders K Ms
    → (∀ {Δ'} (r : Ren Δ Δ') (as : Vec (Atm Σ Δ' Any) n) → RAs as → RM (k r as)) → RM (atomizes {B = B} Ms ρ k)
  atomize₂-R : ∀ {Σ Γ Δ A₁ A₂ B} (L : C.Tm Σ Γ A₁) (M : C.Tm Σ Γ A₂) (ρ : Ren Γ Δ) {k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Mo.Exp Σ Δ' B} → Older K L → Older K M
    → (∀ {Δ'} (a : Atm Σ Δ' A₁) b → RA a → RA b → RM (k a b)) → RM (atomize₂ {B = B} L M ρ k)

  rco-R (C.` x) ρ o = tt
  rco-R (C.fun-ref f) ρ o = o
  rco-R (C.pack L M) ρ (o₁ , o₂) = atomize₂-R L M ρ {k = Mo.pack} o₁ o₂ λ _ _ → _,_
  rco-R (C.callc L M) ρ (o₁ , o₂) = atomize₂-R L M ρ {k = Mo.callc} o₁ o₂ λ _ _ → _,_
  rco-R (C.lit B c) ρ o = tt
  rco-R (C.tuple Ms) ρ o = atomizes-R Ms ρ o λ _ _ h → h
  rco-R (C.get i M) ρ o = atomize-R M ρ o λ _ _ h → h
  rco-R (C.inl M) ρ o = atomize-R M ρ o λ _ _ h → h
  rco-R (C.inr M) ρ o = atomize-R M ρ o λ _ _ h → h
  rco-R (C.case L M N) ρ (o₁ , o₂ , o₃) = atomize-R L ρ o₁ λ r a h → h , rco-R M _ o₂ , rco-R N _ o₃
  rco-R (C.prim p L M) ρ (o₁ , o₂) = atomize₂-R L M ρ {k = Mo.prim p} o₁ o₂ λ _ _ → _,_
  rco-R (C.let′ M N) ρ (o₁ , o₂) = rco-R M ρ o₁ , rco-R N _ o₂
  rco-R (C.inject G M) ρ o = atomize-R M ρ o λ _ _ h → h
  rco-R (C.project t M) ρ o = atomize-R M ρ o λ _ _ h → h

  atomize-R (C.` x) ρ o h = h _ _ tt
  atomize-R (C.fun-ref f) ρ o h = h _ _ o
  atomize-R (C.lit B c) ρ o h = h _ _ tt
  atomize-R M@(C.pack _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.callc _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.tuple _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.get _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.inl _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.inr _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.case _ _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.prim _ _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.let′ _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.inject _ _) ρ o h = rco-R M ρ o , h _ _ tt
  atomize-R M@(C.project _ _) ρ o h = rco-R M ρ o , h _ _ tt

  atomizes-R [] ρ o h = h _ [] tt
  atomizes-R (M ∷ Ms) ρ (o , os) h =
    atomize-R M ρ o λ r a ha → atomizes-R Ms _ os λ r' as has → h _ _ (ren-R r' a ha , has)

  atomize₂-R L M ρ o₁ o₂ h = atomize-R L ρ o₁ λ r a ha → atomize-R M _ o₂ λ r' b hb → h _ b (ren-R r' a ha) hb

  {- lift locals -}

  lift-R : ∀ {Σ Δ A} (e : Mo.Exp Σ Δ A) → RM e → RI (lift e)
  lift-R (Mo.atm a) h = h
  lift-R (Mo.pack a b) h = h
  lift-R (Mo.callc a b) h = h
  lift-R (Mo.tuple as) h = h
  lift-R (Mo.get i a) h = h
  lift-R (Mo.inl a) h = h
  lift-R (Mo.inr a) h = h
  lift-R (Mo.case a e₁ e₂) (h , h₁ , h₂) = h , lift-R e₁ h₁ , lift-R e₂ h₂
  lift-R (Mo.prim p a b) h = h
  lift-R (Mo.let′ e₁ e₂) (h₁ , h₂) = lift-R e₁ h₁ , lift-R e₂ h₂
  lift-R (Mo.inject G a) h = h
  lift-R (Mo.project t a) h = h

  {- explicate control -}

  ROut : ∀ {Σ Bs Δ} → Out Σ Bs Δ → Set
  ROut (out _ bs t) = RB bs × RT t

  after-R : ∀ {Σ Bs Bs₁ Δ} (g : Bs ⊑ Bs₁) (o : Out Σ Bs₁ Δ) → ROut o → ROut (after g o)
  after-R g (out _ _ _) h = h

  assign-R : ∀ {Σ Bs Δ Δ' A} (e : I.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : G.Tail Σ Bs (A ∷ Δ')) bs
    → RI e → RT k → RB bs → ROut (explicate-assign e p k bs)
  assign-R (I.simple s) p k bs he hk hb = hb , he , hk
  assign-R (I.assign e₁ e₂) p k bs (h₁ , h₂) hk hb with explicate-assign e₂ (_⊑_.there⊑ p) k bs | assign-R e₂ (_⊑_.there⊑ p) k bs h₂ hk hb
  ... | out g bs₁ t | (hb₁ , ht) = after-R g (explicate-assign e₁ _⊑_.here⊑ t bs₁) (assign-R e₁ _⊑_.here⊑ t bs₁ h₁ ht hb₁)
  assign-R (I.case a e₁ e₂) p k bs (ha , h₁ , h₂) hk hb
    with explicate-assign e₁ (_⊑_.there⊑ p) (G.goto Z) (bs G.▷ k) | assign-R e₁ (_⊑_.there⊑ p) (G.goto Z) (bs G.▷ k) h₁ tt (hb , hk)
  ... | out g₁ bs₁ t₁ | (hb₁ , ht₁) with explicate-assign e₂ (_⊑_.there⊑ p) (G.goto (⊑-∋ (_⊑_.there⊑ g₁) Z)) (bs₁ G.▷ t₁) | assign-R e₂ (_⊑_.there⊑ p) (G.goto (⊑-∋ (_⊑_.there⊑ g₁) Z)) (bs₁ G.▷ t₁) h₂ tt (hb₁ , ht₁)
  ...   | out g₂ bs₂ t₂ | (hb₂ , ht₂) = (hb₂ , ht₂) , ha

  tail-R : ∀ {Σ Bs Δ} (e : I.Exp Σ Δ Any) bs → RI e → RB bs → ROut (explicate-tail {Bs = Bs} e bs)
  tail-R (I.simple s) bs he hb = hb , he
  tail-R (I.assign e₁ e₂) bs (h₁ , h₂) hb with explicate-tail e₂ bs | tail-R e₂ bs h₂ hb
  ... | out g bs₁ t | (hb₁ , ht) = after-R g (explicate-assign e₁ _⊑_.here⊑ t bs₁) (assign-R e₁ _⊑_.here⊑ t bs₁ h₁ ht hb₁)
  tail-R (I.case a e₁ e₂) bs (ha , h₁ , h₂) hb with explicate-tail e₁ bs | tail-R e₁ bs h₁ hb
  ... | out g₁ bs₁ t₁ | (hb₁ , ht₁) with explicate-tail e₂ (bs₁ G.▷ t₁) | tail-R e₂ (bs₁ G.▷ t₁) h₂ (hb₁ , ht₁)
  ...   | out g₂ bs₂ t₂ | (hb₂ , ht₂) = (hb₂ , ht₂) , ha

  {- select instructions: labels below K, slots below n -}

  module _ (n : ℕ) where
    S< : ℕ → Set
    S< x = x < n

    atm-R : ∀ {Σ Δ A} (a : Atm Σ Δ A) → length Δ ≤ n → RA a → OK (_< K) S< (select-atm a)
    atm-R (var x) Δ≤ _ = <-≤-trans (lvl-< x) Δ≤
    atm-R (lit B c) Δ≤ _ = tt
    atm-R (ref f) Δ≤ h = h

    atms-R : ∀ {Σ Δ m} (as : Vec (Atm Σ Δ Any) m) → length Δ ≤ n → RAs as → All (OK (_< K) S<) (toList (map select-atm as))
    atms-R [] Δ≤ _ = []
    atms-R (a ∷ as) Δ≤ (h , hs) = atm-R a Δ≤ h ∷ atms-R as Δ≤ hs

    check-R : ∀ t a → OK (_< K) S< a → Code (_< K) S< (check t a)
    check-R tint a h = h , (tt , tt) , tt
    check-R tsum a h = h , tt
    check-R tfun a h = h , tt
    check-R (ttup m i) a h = h , tt

    simple-R : ∀ {Σ Δ A} (s : I.Simple Σ Δ A) d → length Δ ≤ n → RS s → Code (_< K) S< (select-simple s d)
    simple-R (I.atm a) d Δ≤ h = atm-R a Δ≤ h , tt
    simple-R (I.pack a b) d Δ≤ (h₁ , h₂) = (atm-R a Δ≤ h₁ ∷ atm-R b Δ≤ h₂ ∷ []) , tt
    simple-R (I.callc f a) d Δ≤ (h₁ , h₂) = atm-R f Δ≤ h₁ , atm-R f Δ≤ h₁ , atm-R a Δ≤ h₂ , tt , tt , tt
    simple-R (I.tuple as) d Δ≤ h = atms-R as Δ≤ h , tt
    simple-R (I.get i a) d Δ≤ h = atm-R a Δ≤ h , tt
    simple-R (I.inl a) d Δ≤ h = (atm-R a Δ≤ h ∷ []) , tt
    simple-R (I.inr a) d Δ≤ h = (atm-R a Δ≤ h ∷ []) , tt
    simple-R (I.prim sub a b) d Δ≤ (h₁ , h₂) = atm-R a Δ≤ h₁ , (atm-R b Δ≤ h₂ , tt) , tt , tt
    simple-R (I.prim eq a b) d Δ≤ (h₁ , h₂) = (atm-R b Δ≤ h₂ , atm-R a Δ≤ h₁) , tt , tt
    simple-R (I.inject G a) d Δ≤ h = atm-R a Δ≤ h , tt
    simple-R (I.project t a) d Δ≤ h = Code-++ (check t (select-atm a)) (check-R t _ (atm-R a Δ≤ h)) (atm-R a Δ≤ h , tt)

    tail-sel-R : ∀ {Σ Bs Δ} (t : G.Tail Σ Bs Δ) → depth t ≤ n → RT t → Code (_< K) S< (Block.instrs (select-tail t))
    tail-sel-R (G.return s) d≤ h = simple-R s _ d≤ h
    tail-sel-R (G.seq p s t) d≤ (h₁ , h₂) =
      Code-++ (select-simple s _) (simple-R s _ (≤-trans (m≤m⊔n _ _) d≤) h₁) (tail-sel-R t (≤-trans (m≤n⊔m _ _) d≤) h₂)
    tail-sel-R (G.goto l) d≤ h = tt
    tail-sel-R (G.case a p l₁ l₂) d≤ h = a≤ , a≤ , tt
      where a≤ = atm-R a (≤-trans (m≤m⊔n _ _) d≤) h

    blocks-sel-R : ∀ {Σ Bs} (bs : G.Blocks Σ Bs) → blocks-depth bs ≤ n → RB bs
      → All (λ c → Code (_< K) S< (Block.instrs c)) (select-blocks bs)
    blocks-sel-R G.[] d≤ h = []
    blocks-sel-R (bs G.▷ t) d≤ (hb , ht) =
      tail-sel-R t (≤-trans (m≤m⊔n _ _) d≤) ht ∷ blocks-sel-R bs (≤-trans (m≤n⊔m _ _) d≤) hb

{- every reference of a term is below the length of the table -}
older-all : ∀ {Σ Γ A} (M : C.Tm Σ Γ A) → Older (length Σ) M
olders-all : ∀ {Σ Γ n} (Ms : Vec (C.Tm Σ Γ Any) n) → Olders (length Σ) Ms
older-all (C.` x) = tt
older-all (C.fun-ref f) = lvl-< f
older-all (C.pack L M) = older-all L , older-all M
older-all (C.callc L M) = older-all L , older-all M
older-all (C.lit B c) = tt
older-all (C.tuple Ms) = olders-all Ms
older-all (C.get i M) = older-all M
older-all (C.inl M) = older-all M
older-all (C.inr M) = older-all M
older-all (C.case L M N) = older-all L , older-all M , older-all N
older-all (C.prim p L M) = older-all L , older-all M
older-all (C.let′ M N) = older-all M , older-all N
older-all (C.inject G M) = older-all M
older-all (C.project t M) = older-all M
olders-all [] = tt
olders-all (M ∷ Ms) = older-all M , olders-all Ms

{- a body that select makes of an expression that lift locals made -}
body-wf : ∀ K {Σ Δ} j pre (e : I.Exp Σ Δ Any) → RI K e
  → (∀ {n} → Code (_< K) (_< n) pre)
  → BodyOK K (j ⊔ Body.locals (select-body pre (explicate-body e))) (select-body pre (explicate-body e))
body-wf K j pre e h cpre with explicate-tail e G.[] | tail-R K e G.[] h tt
... | out _ bs t | (hb , ht) =
  Code-++ pre cpre (tail-sel-R K _ t (≤-trans (m≤n⊔m _ (depth t)) (m≤n⊔m j _)) ht)
  ∷ blocks-sel-R K _ bs (≤-trans (m≤m⊔n _ (depth t)) (m≤n⊔m j _)) hb

len-sel : ∀ {Σ ns} (xs : All (λ n → G.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) → length (select-defs xs) ≡ length ns
len-sel [] = refl
len-sel (x ∷ xs) = cong suc (len-sel xs)

defs-wf : ∀ {Σ ns} (ds : All (C.Code Σ) ns) → OlderDefs ds
  → DefsWF (select-defs (All-map explicate-body (All-map lift (All-map (λ D → rco D (λ x → x)) ds))))
defs-wf [] _ = tt
defs-wf {ns = _ ∷ ns} (d ∷ ds) (o , os) =
  subst (λ K → BodyOK K (2 ⊔ Body.locals B) B) (sym (len-sel (All-map explicate-body (All-map lift (All-map (λ D → rco D (λ x → x)) ds)))))
    (body-wf (length ns) 2 prologue (lift (rco d (λ x → x))) (lift-R (length ns) (rco d (λ x → x)) (rco-R (length ns) d (λ x → x) o)) (tt , tt , tt))
  , defs-wf ds os
  where B = select-body prologue (explicate-body (lift (rco d (λ x → x))))

{- the operands of the X86 program compiled from a Clos5ᵀ program whose
   definitions refer only to older ones -}
code-wf : ∀ (P : C.Program) → OlderDefs (C.Program.defs P)
  → let Q = select (explicate (lift-program (rco-program P))) in
    DefsWF (X.Program.defs Q) × BodyOK (length (X.Program.defs Q)) (Body.locals (X.Program.main Q)) (X.Program.main Q)
code-wf (C.program {Σ} ds M) os =
  defs-wf ds os
  , subst (λ K → BodyOK K (Body.locals B) B) (sym (len-sel (All-map explicate-body (All-map lift (All-map (λ D → rco D (λ x → x)) ds)))))
      (body-wf (length Σ) 0 [] (lift (rco M (λ x → x))) (lift-R (length Σ) (rco M (λ x → x)) (rco-R (length Σ) M (λ x → x) (older-all M))) tt)
  where B = select-body [] (explicate-body (lift (rco M (λ x → x))))
