{-

  The compiler produces well-formed X86 programs (X86WF.agda) from closed
  ISWIM programs: compile-x86-wf.

  The Clos5 program that compile produces is well formed (compile-wf,
  Adequacy/CompileWF.agda): its definitions use only their two
  parameters and main no variable (WS), and each refers only to older
  definitions (RB). Remove complex operands keeps both (ws-rco, rb-rco:
  the lets it adds bind the variables its atoms use, and it renames no
  reference). Lift locals then gives the variables in scope at depth d
  the slots below d, and the frame has at least d slots (lift-ok), and
  explicate control and select instructions keep the atoms (ex-tail).
  The instructions of a tail are what select-tail makes of it, so the
  conditions are stated on those (Code, through Sim and Exp).

  The table of the X86 program means the same as that of the Clos5 one
  (the table lemmas of the denotational proofs), which is consistent
  (table-con).

-}

module Compiler.Operational.Adequacy.X86CompileWF where

open import SetsAsPredicates
open import GraphModel.Domain using (Con-⊆)
open import Compiler.Lang.Clos5 as C5
  using (AST; Arg; Args; `_; _⦅_⦆; ast; bind; clear; nil; cons; fun-ref; app; lit; pair-op; fst-op; snd-op;
         tuple; get; inl-op; inr-op; case-op; prim; let-op)
open import Compiler.Lang.Mon as Mo using (Mon; Atom; Atoms; []; _∷_)
open import Compiler.Lang.Imp as I using (Exp; Simple; simple; assign; case; atm)
import Compiler.Lang.CFG as G
open import Compiler.Lang.X86 using (Instr; Block; body; program; movq; loc; reg; rdi; rsi; var)
import Compiler.Lang.Prim as P
open import Compiler.Compile.RCO
open import Compiler.Compile.LiftLocals renaming (lift to liftL)
open import Compiler.Compile.Explicate
open import Compiler.Compile.Select
open import Compiler.Compile.Pipeline using (compile; compile-x86)
open import Compiler.Compile.EncloseScope using (Closed)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect using (RB; RB-arg; RB-args)
open import Compiler.Model.Graph.Sem.Clos5IswimContinuous using (table-con)
open import Compiler.Model.Graph.Correctness.RCOCorrect using (table-rco)
open import Compiler.Model.Graph.Correctness.LiftLocalsCorrectK using (table-lift)
import Compiler.Model.Graph.Correctness.ExplicateCorrectK as EK
import Compiler.Model.Graph.Correctness.SelectCorrect as SC
import Compiler.Operational.Adequacy.Clos5WF as F
open import Compiler.Operational.Adequacy.CompileWF using (compile-wf)
open import Compiler.Operational.Adequacy.X86WF
open import Syntax.Rename C5.Op C5.sig using (rename; rename-arg; rename-args; ext)
open import Syntax.ScopeRename C5.Op C5.sig using (WS; WS-args; Fits; fits-ext; ws-rename; ws-rename-args)
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import abt.Sig using (■)

open import Data.List using (List; []; _∷_; _++_; length; map; replicate)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _∸_; _⊔_; _<?_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; +-comm; +-identityʳ; m≤m+n; m≤n+m; ≤-trans; <-≤-trans; +-monoʳ-≤; +-monoˡ-<; m≤m⊔n; m≤n⊔m; ∸-monoʳ-<)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Remove complex operands keeps scopes and references -------------------------------}

WS-lets : ℕ → List AST → Set
WS-lets k [] = ⊤
WS-lets k (M ∷ Ms) = WS k M × WS-lets (suc k) Ms

ws-lets : ∀ {k} bs N → WS-lets k bs → WS (k + length bs) N → WS k (lets bs N)
ws-lets {k} [] N _ w = subst (λ j → WS j N) (+-identityʳ k) w
ws-lets {k} (M ∷ Ms) N (wM , wl) w = wM , ws-lets Ms N wl (subst (λ j → WS j N) (+-suc k (length Ms)) w) , tt

ws-atomize : ∀ {k n} (Ms : Args (replicate n ■)) → WS-args k Ms
  → WS-lets k (binds (atomize Ms)) × WS-args (k + length (binds (atomize Ms))) (atoms (atomize Ms))
ws-atomize {n = zero} Nil _ = tt , tt
ws-atomize {k} {suc n} (M ,, Ms) (w , ws) with atom? M
... | yes _ = proj₁ IH , ws-rename (j +_) M (λ x x< → subst (_< k + j) (+-comm x j) (+-monoˡ-< j x<)) w , proj₂ IH
  where IH = ws-atomize {k} Ms ws
        j = length (binds (atomize Ms))
... | no _ = (w , proj₁ IH) , m≤n+m (suc j) k , subst (λ i → WS-args i (atoms B)) (sym (+-suc k j)) (proj₂ IH)
  where B = atomize (rename-args suc Ms)
        IH = ws-atomize {suc k} (rename-args suc Ms) (ws-rename-args {k} {suc k} suc Ms (λ x → s≤s) ws)
        j = length (binds B)

ws-lift : ∀ {k n} (f : ℕ → Args (replicate n ■) → AST) Ms → WS-args k Ms
  → (∀ j As → WS-args (k + j) As → WS (k + j) (f j As)) → WS k (lift f Ms)
ws-lift f Ms w hf = let (wl , wa) = ws-atomize Ms w in ws-lets (binds (atomize Ms)) _ wl (hf _ _ wa)

ws-rco : ∀ {k} M → WS k M → WS k (rco M)
ws-rco-args : ∀ {k n} (Ms : Args (replicate n ■)) → WS-args k Ms → WS-args k (rco-args Ms)
ws-rco (` x) w = w
ws-rco (fun-ref k ⦅ Nil ⦆) w = w
ws-rco (app ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (lit B k ⦅ Nil ⦆) w = w
ws-rco (pair-op ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (fst-op ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (snd-op ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (tuple n ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (get i ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (inl-op ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (inr-op ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco (prim p ⦅ Ms ⦆) w = ws-lift _ (rco-args Ms) (ws-rco-args Ms w) λ _ _ z → z
ws-rco {k} (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
  ws-lift (case-on (rco M) (rco N)) (rco L ,, Nil) (ws-rco L wL , tt) λ { j (A ,, Nil) (wA , _) →
    wA , ws-rename _ (rco M) (fits-ext (fits j)) (ws-rco M wM) , ws-rename _ (rco N) (fits-ext (fits j)) (ws-rco N wN) , tt }
  where
  fits : ∀ j → Fits k (k + j) (j +_)
  fits j x x< = subst (_< k + j) (+-comm x j) (+-monoˡ-< j x<)
ws-rco (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) = ws-rco M wM , ws-rco N wN , tt
ws-rco-args {n = zero} Nil _ = tt
ws-rco-args {n = suc n} (M ,, Ms) (w , ws) = ws-rco M w , ws-rco-args Ms ws

module _ {K : ℕ} where

  rb-rename : ∀ r M → RB K M → RB K (rename r M)
  rb-rename-arg : ∀ {b} r (a : Arg b) → RB-arg K a → RB-arg K (rename-arg r a)
  rb-rename-args : ∀ {bs} r (as : Args bs) → RB-args K as → RB-args K (rename-args r as)
  rb-rename r (` x) _ = tt
  rb-rename r (fun-ref k ⦅ as ⦆) k< = k<
  rb-rename r (app ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (lit B k ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (pair-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (fst-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (snd-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (tuple n ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (get i ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (inl-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (inr-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (case-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (prim p ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename r (let-op ⦅ as ⦆) rb = rb-rename-args r as rb
  rb-rename-arg r (ast M) rb = rb-rename r M rb
  rb-rename-arg r (bind a) rb = rb-rename-arg (ext r) a rb
  rb-rename-arg r (clear a) rb = rb
  rb-rename-args r nil _ = tt
  rb-rename-args r (cons a as) (ra , rs) = rb-rename-arg r a ra , rb-rename-args r as rs

  rb-lets : ∀ bs N → All (RB K) bs → RB K N → RB K (lets bs N)
  rb-lets [] N _ r = r
  rb-lets (M ∷ Ms) N (rM ∷ rs) r = rM , rb-lets Ms N rs r , tt

  rb-atomize : ∀ {n} (Ms : Args (replicate n ■)) → RB-args K Ms
    → All (RB K) (binds (atomize Ms)) × RB-args K (atoms (atomize Ms))
  rb-atomize {zero} Nil _ = [] , tt
  rb-atomize {suc n} (M ,, Ms) (r , rs) with atom? M
  ... | yes _ = let (rl , ra) = rb-atomize Ms rs in rl , rb-rename _ M r , ra
  ... | no _ = let (rl , ra) = rb-atomize (rename-args suc Ms) (rb-rename-args suc Ms rs) in (r ∷ rl) , tt , ra

  rb-lift : ∀ {n} (f : ℕ → Args (replicate n ■) → AST) Ms → RB-args K Ms
    → (∀ j As → RB-args K As → RB K (f j As)) → RB K (lift f Ms)
  rb-lift f Ms r hf = let (rl , ra) = rb-atomize Ms r in rb-lets (binds (atomize Ms)) _ rl (hf _ _ ra)

  rb-rco : ∀ M → RB K M → RB K (rco M)
  rb-rco-args : ∀ {n} (Ms : Args (replicate n ■)) → RB-args K Ms → RB-args K (rco-args Ms)
  rb-rco (` x) r = r
  rb-rco (fun-ref k ⦅ Nil ⦆) r = r
  rb-rco (app ⦅ Ms ⦆) r = rb-lift (λ _ → app ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (lit B k ⦅ Nil ⦆) r = r
  rb-rco (pair-op ⦅ Ms ⦆) r = rb-lift (λ _ → pair-op ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (fst-op ⦅ Ms ⦆) r = rb-lift (λ _ → fst-op ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (snd-op ⦅ Ms ⦆) r = rb-lift (λ _ → snd-op ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (tuple n ⦅ Ms ⦆) r = rb-lift (λ _ → tuple n ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (get i ⦅ Ms ⦆) r = rb-lift (λ _ → get i ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (inl-op ⦅ Ms ⦆) r = rb-lift (λ _ → inl-op ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (inr-op ⦅ Ms ⦆) r = rb-lift (λ _ → inr-op ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (prim p ⦅ Ms ⦆) r = rb-lift (λ _ → prim p ⦅_⦆) (rco-args Ms) (rb-rco-args Ms r) λ _ _ z → z
  rb-rco (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (rL , rM , rN , _) =
    rb-lift (case-on (rco M) (rco N)) (rco L ,, Nil) (rb-rco L rL , tt) λ { j (A ,, Nil) (rA , _) →
      rA , rb-rename _ (rco M) (rb-rco M rM) , rb-rename _ (rco N) (rb-rco N rN) , tt }
  rb-rco (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (rM , rN , _) = rb-rco M rM , rb-rco N rN , tt
  rb-rco-args {zero} Nil _ = tt
  rb-rco-args {suc n} (M ,, Ms) (r , rs) = rb-rco M r , rb-rco-args Ms rs

{- Lift locals, explicate control and select instructions keep the atoms ---------------}

Code-++ : ∀ {L S} xs {ys} → Code L S xs → Code L S ys → Code L S (xs ++ ys)
Code-++ [] _ c = c
Code-++ (i ∷ xs) (r , cs) c = r , Code-++ xs cs c

module _ (K n : ℕ) where

  {- what select instructions makes of a simple expression, an Imp
     expression and a tail reads only atoms within bounds -}
  Sim : Simple → Set
  Sim s = ∀ d → Code (_< K) (_< n) (select-simple s d)

  ExpOK : Exp → Set
  ExpOK (simple s) = Sim s
  ExpOK (case a x e₁ e₂) = OK (_< K) (_< n) (select-atm a) × ExpOK e₁ × ExpOK e₂
  ExpOK (assign x e₁ e₂) = ExpOK e₁ × ExpOK e₂

  TailOK : G.Tail → Set
  TailOK t = Code (_< K) (_< n) (Block.instrs (select-tail t))

  ex-assign : ∀ e x k bs → ExpOK e → TailOK k → All TailOK bs
    → TailOK (proj₁ (explicate-assign e x k bs)) × All TailOK (proj₂ (explicate-assign e x k bs))
  ex-assign (simple s) x k bs ok tk ab = Code-++ (select-simple s (var x)) (ok (var x)) tk , ab
  ex-assign (assign y e₁ e₂) x k bs (o₁ , o₂) tk ab =
    let (t , ab₁) = ex-assign e₂ x k bs o₂ tk ab in ex-assign e₁ y _ _ o₁ t ab₁
  ex-assign (case a y e₁ e₂) x k bs (oa , o₁ , o₂) tk ab =
    let (t₁ , ab₂) = ex-assign e₁ x (G.goto _) (k ∷ bs) o₁ tt (tk ∷ ab)
        (t₂ , ab₄) = ex-assign e₂ x (G.goto _) (_ ∷ _) o₂ tt (t₁ ∷ ab₂) in
    (oa , oa , tt) , t₂ ∷ ab₄

  ex-tail : ∀ e bs → ExpOK e → All TailOK bs → TailOK (proj₁ (explicate-tail e bs)) × All TailOK (proj₂ (explicate-tail e bs))
  ex-tail (simple s) bs ok ab = ok (reg Compiler.Lang.X86.rax) , ab
  ex-tail (assign x e₁ e₂) bs (o₁ , o₂) ab = let (t , ab₁) = ex-tail e₂ bs o₂ ab in ex-assign e₁ x _ _ o₁ t ab₁
  ex-tail (case a x e₁ e₂) bs (oa , o₁ , o₂) ab =
    let (t₁ , ab₁) = ex-tail e₁ bs o₁ ab
        (t₂ , ab₃) = ex-tail e₂ (_ ∷ _) o₂ (t₁ ∷ ab₁) in
    (oa , oa , tt) , t₂ ∷ ab₃

  {- the slots of the variables in scope at depth d are below d -}
  atom-ok : ∀ {d M} (a : Atom M) → WS d M → RB K M → d ≤ n → OK (_< K) (_< n) (select-atm (lift-atom n d a))
  atom-ok {d} (Mo.var x) x< _ d≤ with x <? d
  ... | yes _ = <-≤-trans (∸-monoʳ-< (s≤s z≤n) x<) d≤
  ... | no ¬x< = ⊥-elim (¬x< x<)
  atom-ok (Mo.lit B k) _ _ _ = tt
  atom-ok (Mo.ref k) _ k< _ = k<

  atoms-ok : ∀ {d m Ms} (as : Atoms {m} Ms) → WS-args d Ms → RB-args K Ms → d ≤ n
    → All (OK (_< K) (_< n)) (map select-atm (lift-atoms n d as))
  atoms-ok [] _ _ _ = []
  atoms-ok (a ∷ as) (w , ws) (r , rs) d≤ = atom-ok a w r d≤ ∷ atoms-ok as ws rs d≤

  lift-ok : ∀ {d M} (m : Mon M) → WS d M → RB K M → d + height m ≤ n → ExpOK (liftL n d m)
  lift-ok {d} m w r le = go m w r le (≤-trans (m≤m+n d (height m)) le)
    where
    go : ∀ {d M} (m : Mon M) → WS d M → RB K M → d + height m ≤ n → d ≤ n → ExpOK (liftL n d m)
    go (Mo.atom a) w r _ d≤ _ = atom-ok a w r d≤ , tt
    go (Mo.app (a ∷ b ∷ c ∷ [])) (wa , wb , wc , _) (ra , rb , rc , _) _ d≤ _ =
      atom-ok b wb rb d≤ , atom-ok c wc rc d≤ , atom-ok a wa ra d≤ , tt , tt
    go (Mo.pair (a ∷ b ∷ [])) (wa , wb , _) (ra , rb , _) _ d≤ _ = (atom-ok a wa ra d≤ ∷ atom-ok b wb rb d≤ ∷ []) , tt
    go (Mo.fst (a ∷ [])) (wa , _) (ra , _) _ d≤ _ = atom-ok a wa ra d≤ , tt
    go (Mo.snd (a ∷ [])) (wa , _) (ra , _) _ d≤ _ = atom-ok a wa ra d≤ , tt
    go (Mo.tuple as) ws rs _ d≤ _ = atoms-ok as ws rs d≤ , tt
    go (Mo.get (a ∷ [])) (wa , _) (ra , _) _ d≤ _ = atom-ok a wa ra d≤ , tt
    go (Mo.inl (a ∷ [])) (wa , _) (ra , _) _ d≤ _ = (atom-ok a wa ra d≤ ∷ []) , tt
    go (Mo.inr (a ∷ [])) (wa , _) (ra , _) _ d≤ _ = (atom-ok a wa ra d≤ ∷ []) , tt
    go (Mo.prim {P.sub} (a ∷ b ∷ [])) (wa , wb , _) (ra , rb , _) _ d≤ _ =
      atom-ok a wa ra d≤ , (atom-ok b wb rb d≤ , tt) , tt , tt
    go (Mo.prim {P.eq} (a ∷ b ∷ [])) (wa , wb , _) (ra , rb , _) _ d≤ _ =
      (atom-ok b wb rb d≤ , atom-ok a wa ra d≤) , tt , tt
    go {d} (Mo.case a m₁ m₂) (wa , w₁ , w₂ , _) (ra , r₁ , r₂ , _) le d≤ =
      atom-ok a wa ra d≤ , go m₁ w₁ r₁ l₁ (≤-trans (m≤m+n (suc d) _) l₁) , go m₂ w₂ r₂ l₂ (≤-trans (m≤m+n (suc d) _) l₂)
      where le₁ : ∀ {h} → h ≤ height m₁ ⊔ height m₂ → suc d + h ≤ n
            le₁ h≤ = ≤-trans (s≤s (+-monoʳ-≤ d h≤)) (subst (_≤ n) (+-suc d _) le)
            l₁ = le₁ (m≤m⊔n (height m₁) (height m₂))
            l₂ = le₁ (m≤n⊔m (height m₁) (height m₂))
    go {d} (Mo.let′ m₁ m₂) (w₁ , w₂ , _) (r₁ , r₂ , _) le d≤ =
      go m₁ w₁ r₁ (≤-trans (+-monoʳ-≤ d (m≤m⊔n _ _)) le) d≤
      , go m₂ w₂ r₂ (subst (_≤ n) (+-suc d (height m₂)) (≤-trans (+-monoʳ-≤ d (m≤n⊔m (height m₁) (suc (height m₂)))) le))
          (≤-trans (m≤m+n _ _) (subst (_≤ n) (+-suc d (height m₂)) (≤-trans (+-monoʳ-≤ d (m≤n⊔m (height m₁) (suc (height m₂)))) le)))

{- The compiled program ---------------------------------------------------------------}

{- a body compiled at depth d₀, with the instructions pre first -}
body-ok : ∀ {K} pre d₀ {M} (m : Mon M) → WS d₀ M → RB K M → (∀ {is} → Code (_< K) (_< (d₀ + height m)) is → Code (_< K) (_< (d₀ + height m)) (pre ++ is))
  → BodyOK K (d₀ + height m) (select-body pre (explicate-body (lift-body d₀ m)))
body-ok {K} pre d₀ m w r hp =
  let (t , ab) = ex-tail K _ _ [] (lift-ok K _ m w r Data.Nat.Properties.≤-refl) [] in hp t ∷ map⁺ ab
  where open import Data.List.Relation.Unary.All.Properties using (map⁺)

length-lift : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift [] = refl
length-lift (m ∷ ms) = cong suc (length-lift ms)

{- the definitions, newest first -}
defs-ok : ∀ ds (ms : All Mon (map rco ds)) → F.DefsWF ds
  → DefsWF (map (select-body prologue) (map explicate-body (lift-defs ms)))
defs-ok [] [] _ = tt
defs-ok (N ∷ Ns) (m ∷ ms) ((rb , ws) , wf) =
  subst (λ K → BodyOK K (2 + height m) (select-body prologue (explicate-body (lift-body 2 m)))) (sym len) (body-ok {length Ns} prologue 2 m (ws-rco N ws) (rb-rco N rb) λ c → tt , tt , c) , defs-ok Ns ms wf
  where
  len = trans (length-map _ (map explicate-body (lift-defs ms)))
          (trans (length-map _ (lift-defs ms)) (trans (length-lift ms) (length-map rco Ns)))

compile-x86-wf : ∀ M → Closed M → WF (compile-x86 M)
compile-x86-wf M c = wf (compile M) (compile-wf M c)
  where
  wf : ∀ P → F.WF P → WF (select (explicate (lift-program (rco-program P) (rco-program-mon P))))
  wf (C5.program ds M) (wfd , rb , ws) =
    defs-ok ds ms wfd
    , subst (λ K → BodyOK K (0 + height m) (select-body [] (explicate-body (lift-body 0 m)))) (sym len) (body-ok {length ds} [] 0 m (ws-rco M ws) (rb-rco M rb) λ c → c)
    , λ k → Con-⊆ (table-con ds k) λ x x∈ →
        proj₁ (table-rco ds k) x (proj₁ (table-lift ms k) x (proj₁ (EK.table-≃ (lift-defs ms) k) x (proj₁ (SC.table-≃ (map explicate-body (lift-defs ms)) (SC.defs-2 ms) k) x x∈)))
    where
    ms = proj₁ (rco-program-mon (C5.program ds M))
    m = proj₂ (rco-program-mon (C5.program ds M))
    len = trans (length-map _ (map explicate-body (lift-defs ms)))
            (trans (length-map _ (lift-defs ms)) (trans (length-lift ms) (length-map rco ds)))
