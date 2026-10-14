{-

  Adequacy of the graph model with errors (Semantics/GraphErr/Typed/X86.agda)
  for the X86ᵀ machine: every element of the denotation of a program is
  witnessed by a run of the machine of its definitions ds, and ω by a run
  that stops with an error, when the code of each definition depends only
  on the older ones and the table is consistent (see GraphErr/X86.agda).

  As for ISWIM (GraphErr/LogRel.agda), 𝕍 d v relates denotational values
  to machine values, by recursion on d, and Res relates an element of
  the meaning of a sequence to the run from its state (X86Common): ω to
  an error, any other element to the return of a related value. Code is
  related by its entries X ↦ (Y ↦ w): the callee, on values related to X
  and Y, gives Res w. The types of X86ᵀ say what each location holds,
  so a location is related to a set when all of its elements are related
  to its value (Locs 𝕍); the slots, registers and flag that a type does
  not have are unconstrained. So a register write needs no strictness:
  an operand is never ω, and every element of the result of a call is
  related to the one value that the callee returns (collect: the machine
  is deterministic). The only check is chk's, whose tag is read off the
  kinds of the related elements (𝕍-kind).

  The fundamental lemma (adequate) is by induction on the sequence, with
  the blocks it may jump to related (BR). The table is related to the
  code pointers by induction on the levels of the definitions (tbl-rel):
  the entry of definition f is its code under the older definitions and
  the empty function above them (fix-C), all related.

-}

open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Language.Typed.X86

module proof.Adequacy.GraphErr.X86LogRel {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

open import Framework.Primitives using (base-rep; Int)
open import Language.Prim using (Prim; sub; eq; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_; Con) renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD)
open import Framework.GraphModel.DOpSig using (Results; ■)
open import Framework.GraphModel.Ops using (𝒯; ⋆; car; cdr; 𝒞; payloadD) renaming (proj to projD) renaming (pair to pairD; inl to inlD; inr to inrD)
open import Framework.GraphModel.ErrorMonad using (Kind; kind; binds; isinlD; _≫=_; ⌊_⌋; Conv; _⇂_; ValPayload)
open import Semantics.Graph.Prim using (primD) renaming (out to dout)
open import Semantics.GraphErr.Typed.Ops using (init; kindᶠ; projectᵠ; primᵗ; checkedᵠ; keep)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Imp using (Table)
open import Semantics.GraphErr.Typed.CFG using (BEnv)
open import Semantics.GraphErr.Typed.X86 using (𝒪; 𝒪s; object; ⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ; called-regs)
  renaming (put to putᴰ; putˢ to putˢᴰ; field′ to fieldᴰ; blocks to blocksᴰ; run to runᴰ; args to argsᴰ)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Framework.Lookup using (_!_)
open import proof.Framework.Lookup using (lvl-<)
open import Semantics.Observation using (Obs; o-const; o-error)
open import Semantics.CEK.Smallstep using (next; stop)
open import Semantics.CEK.Typed.X86
open import proof.Adequacy.GraphErr.X86Common ds

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _<_; _≤_; s≤s; _<?_)
open import Data.Nat.Properties using (≤-refl; <-≤-trans)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

{- The logical relation ---------------------------------------------------------------}

{- definition f, called on the environment e and the argument a -}
callee : ∀ {n} → Σ ∋ n → Val Σ ⟪ tup n ⟫ → Val Σ Any → State Σ
callee {n} f e a = run (Body.start (ds ! f)) (Body.blocks (ds ! f)) halt n ⟨ rv tt e a , [] , tt , tt ⟩

{- an element of a value of flat type H is of its kind (through kind₄) -}
KOK : Ty → Value → Set
KOK ⟪ H ⟫ d = kind₄ (kind d) ≡ kindᶠ H
KOK _ d = ⊤

𝕍 : ∀ {A} → Value → Val Σ A → Set
𝕍₀ : ∀ {A} → Value → Val Σ A → Set
𝕍s : ∀ {A} → List Value → Val Σ A → Set
𝕍 {A} d v = KOK A d × 𝕍₀ d v
𝕍₀ d (dyn G v) = 𝕍 d v
𝕍₀ (dconst k) (const k') = dconst k ≡ dconst k'
𝕍₀ ν (code f) = ⊤
𝕍₀ (X ↦ ν) (code f) = ⊤
𝕍₀ (X ↦ (Y ↦ w)) (code f) = ∀ e a → 𝕍s X e → 𝕍s Y a → Res (callee f e a) w (𝕍 w)
𝕍₀ ⦅ u , u' ⦆ (pack c e) = 𝕍 u c × 𝕍 u' e
𝕍₀ ⟨⟩ (tup []) = ⊤
𝕍₀ (tup[_]_ {n'} i d) (tup {n} ws) = Σ[ e ∈ n' ≡ n ] 𝕍 d (lookup ws (subst Fin e i))
𝕍₀ (left d) (inl v) = 𝕍 d v
𝕍₀ (right d) (inr v) = 𝕍 d v
𝕍₀ _ _ = ⊥
𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

open Locs 𝕍

𝕍-ω : ∀ {A} (v : Val Σ A) → 𝕍 ω v → ⊥
𝕍-ω (dyn G v) ⟨ _ , r ⟩ = 𝕍-ω v r
𝕍-ω (code f) ⟨ _ , () ⟩
𝕍-ω (pack c e) ⟨ _ , () ⟩
𝕍-ω (const k) ⟨ _ , () ⟩
𝕍-ω (tup []) ⟨ _ , () ⟩
𝕍-ω (tup (w ∷ ws)) ⟨ _ , () ⟩
𝕍-ω (inl v) ⟨ _ , () ⟩
𝕍-ω (inr v) ⟨ _ , () ⟩

{- the observation of a value related to a constant is that constant -}
𝕍-const : ∀ {A B} {k : base-rep B} (v : Val Σ A) → 𝕍 (dconst k) v → obs v ≡ o-const B k
𝕍-const (dyn G v) ⟨ _ , r ⟩ = 𝕍-const v r
𝕍-const (const k) ⟨ _ , refl ⟩ = refl
𝕍-const (code f) ⟨ _ , () ⟩
𝕍-const (pack c e) ⟨ _ , () ⟩
𝕍-const (tup []) ⟨ _ , () ⟩
𝕍-const (tup (w ∷ ws)) ⟨ _ , () ⟩
𝕍-const (inl v) ⟨ _ , () ⟩
𝕍-const (inr v) ⟨ _ , () ⟩

no-ω : ∀ {A D} {v : Val Σ A} → PS D v → ω ∈ D → ⊥
no-ω {v = v} h ω∈ = 𝕍-ω v (h ω ω∈)

all→𝕍s : ∀ {A} V {v : Val Σ A} {D} → mem V ⊆ D → PS D v → 𝕍s V v
all→𝕍s [] V⊆ h = tt
all→𝕍s (d ∷ V) V⊆ h = ⟨ h d (V⊆ d (here refl)) , all→𝕍s V (λ d' d'∈ → V⊆ d' (there d'∈)) h ⟩

𝕍s-∈ : ∀ {A} V {v : Val Σ A} → 𝕍s V v → PS (mem V) v
𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ _ (here refl) = r
𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ d' (there d∈) = 𝕍s-∈ V rs d' d∈

{- a bind on an operand all of whose elements are related: never ω -}
bind-rel : ∀ {A D} {v : Val Σ A} (F : 𝒫 Value → 𝒫 Value) {Q : Value → Set} → PS D v
  → (∀ w → w ∈ F ⌊ D ⌋ → Q w) → ∀ w → w ∈ (D ≫= F) → Q w
bind-rel {v = v} F h k w (inj₁ ⟨ refl , ω∈ ⟩) = ⊥-elim (no-ω {v = v} h ω∈)
bind-rel F h k w (inj₂ ⟨ _ , w∈ ⟩) = k w w∈

{- an operand that holds only errors -}
bind-ω : ∀ {D w} {X : Set} → (∀ d → d ∈ D → d ≡ ω) → (w ≡ ω × ω ∈ D) ⊎ (Conv D × X) → w ≡ ω
bind-ω all (inj₁ ⟨ refl , _ ⟩) = refl
bind-ω all (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , _ ⟩) = ⊥-elim (d≢ (all d d∈))

{- Inversions of the operators whose elements have one shape -------------------------}

ℬ-inv : ∀ {B} {k : base-rep B} d → d ∈ ℬ B k ptt → d ≡ dconst k
ℬ-inv (dconst k) ⟨ refl , refl ⟩ = refl
ℬ-inv (V ↦ w) ()
ℬ-inv ν ()
ℬ-inv ω ()
ℬ-inv ⦅ u , v ⦆ ()
ℬ-inv (tup[ i ] d) ()
ℬ-inv (left d) ()
ℬ-inv (right d) ()
ℬ-inv ⟨⟩ ()

pair-inv : ∀ {D E} d → d ∈ pairD ⟨ D , ⟨ E , ptt ⟩ ⟩ → Σ[ u ∈ Value ] Σ[ u' ∈ Value ] d ≡ ⦅ u , u' ⦆ × u ∈ D × u' ∈ E
pair-inv ⦅ u , u' ⦆ ⟨ u∈ , u'∈ ⟩ = ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩
pair-inv (dconst k) ()
pair-inv (V ↦ w) ()
pair-inv ν ()
pair-inv ω ()
pair-inv (tup[ i ] d) ()
pair-inv (left d) ()
pair-inv (right d) ()
pair-inv ⟨⟩ ()

inl-rel : ∀ {D} {v : Val Σ Any} → PS D v → PS (inlD ⟨ D , ptt ⟩) (inl v)
inl-rel h (left u) u∈ = ⟨ refl , h u u∈ ⟩
inl-rel h (dconst k) ()
inl-rel h (V ↦ w) ()
inl-rel h ν ()
inl-rel h ω ()
inl-rel h ⦅ u , v ⦆ ()
inl-rel h (tup[ i ] d) ()
inl-rel h (right d) ()
inl-rel h ⟨⟩ ()

inr-rel : ∀ {D} {v : Val Σ Any} → PS D v → PS (inrD ⟨ D , ptt ⟩) (inr v)
inr-rel h (right u) u∈ = ⟨ refl , h u u∈ ⟩
inr-rel h (dconst k) ()
inr-rel h (V ↦ w) ()
inr-rel h ν ()
inr-rel h ω ()
inr-rel h ⦅ u , v ⦆ ()
inr-rel h (tup[ i ] d) ()
inr-rel h (left d) ()
inr-rel h ⟨⟩ ()

{- the elements of a tuple of sets of related elements -}
𝒯-rel : ∀ {j} (vs : Vec (Val Σ Any) j) Xs → (∀ i → PS (nthD Xs i) (lookup vs i)) → PS (𝒯 j Xs) (tup vs)
𝒯-rel [] Xs h ⟨⟩ _ = ⟨ refl , tt ⟩
𝒯-rel (v ∷ vs) Xs h (tup[ i ] d) ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ = ⟨ refl , ⟨ refl , h i d d∈ ⟩ ⟩
𝒯-rel [] Xs h (tup[ i ] d) ()
𝒯-rel (v ∷ vs) Xs h ⟨⟩ ()
𝒯-rel [] Xs h (dconst k) ()
𝒯-rel [] Xs h (V ↦ w) ()
𝒯-rel [] Xs h ν ()
𝒯-rel [] Xs h ω ()
𝒯-rel [] Xs h ⦅ u , u' ⦆ ()
𝒯-rel [] Xs h (left d) ()
𝒯-rel [] Xs h (right d) ()
𝒯-rel (v ∷ vs) Xs h (dconst k) ()
𝒯-rel (v ∷ vs) Xs h (V ↦ w) ()
𝒯-rel (v ∷ vs) Xs h ν ()
𝒯-rel (v ∷ vs) Xs h ω ()
𝒯-rel (v ∷ vs) Xs h ⦅ u , u' ⦆ ()
𝒯-rel (v ∷ vs) Xs h (left d) ()
𝒯-rel (v ∷ vs) Xs h (right d) ()

{- Values -----------------------------------------------------------------------------}

kindᶠ-inj : ∀ {G H} → kindᶠ G ≡ kindᶠ H → G ≡ H
kindᶠ-inj {G} {H} e = trans (sym (inv G)) (trans (cong back e) (inv H))
  where
  back : Kind → Flat
  back (Kind.base B) = base B
  back (Kind.tup n) = tup n
  back Kind.inj = sum
  back _ = fun
  inv : ∀ G → back (kindᶠ G) ≡ G
  inv (base B) = refl
  inv (tup n) = refl
  inv sum = refl
  inv fun = refl

{- the check of chk: the kinds of the elements related to a value of type Any
   are those of its flat type -}
proj-adeq : ∀ t (u : Val Σ Any) {X} → PS X u
  → (proj? t u ≡ nothing × (∀ w → w ∈ projectᵠ kind₄ t X → w ≡ ω))
    ⊎ Σ[ v ∈ Val Σ ⟪ flat t ⟫ ] proj? t u ≡ just v × PS (projectᵠ kind₄ t X) v
proj-adeq t (dyn H v) h with H ≟F flat t
... | yes refl = inj₂ ⟨ v , ⟨ refl , bind-rel {v = dyn H v} (λ X → checkedᵠ kind₄ (kindᶠ (flat t)) X (keep kind₄ t X)) h
  (λ { w (inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , bad ⟩ ⟩ ⟩) → ⊥-elim (bad (proj₁ (proj₂ (h d (proj₁ d∈)))))
     ; w (inj₂ ⟨ ⟨ w∈ , _ ⟩ , _ ⟩) → proj₂ (h w w∈) }) ⟩ ⟩
... | no ne = inj₁ ⟨ refl , (λ { w (inj₁ ⟨ refl , _ ⟩) → refl ; w (inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩) → refl
  ; w (inj₂ ⟨ _ , inj₂ ⟨ ⟨ w∈ , _ ⟩ , ⟨ _ , wk ⟩ ⟩ ⟩) → ⊥-elim (ne (kindᶠ-inj (trans (sym (proj₁ (proj₂ (h w w∈)))) wk))) }) ⟩

{- the fields of tuples and injections -}
field-adeq : ∀ {T A B} (f : Field A B) {D} (v : Val Σ A) → PS D v → PS (fieldᴰ {Σ} T f D) (field′ f v)
field-adeq (get i) (tup ws) h = bind-rel {v = tup ws} (λ X → projD i ⟨ X , ptt ⟩) h (λ d d∈ → gt (h _ (proj₁ d∈)))
  where
  gt : ∀ {d} → 𝕍 (tup[ i ] d) (tup ws) → 𝕍 d (lookup ws i)
  gt ⟨ _ , ⟨ refl , r ⟩ ⟩ = r
field-adeq payload (inl u) h = bind-rel {v = inl u} (λ X → payloadD (X ⇂ ValPayload)) h
  (λ { d (inj₁ l) → proj₂ (h _ (proj₁ (proj₁ l))) ; d (inj₂ r) → ⊥-elim (proj₂ (h _ (proj₁ (proj₁ r)))) })
field-adeq payload (inr u) h = bind-rel {v = inr u} (λ X → payloadD (X ⇂ ValPayload)) h
  (λ { d (inj₁ l) → ⊥-elim (proj₂ (h _ (proj₁ (proj₁ l)))) ; d (inj₂ r) → proj₂ (h _ (proj₁ (proj₁ r))) })

{- primitives, on integers -}
prim-adeq : ∀ p {D E} (u u' : Val Σ ⟪ base Int ⟫) → PS D u → PS E u' → PS (primᵗ p D E) (δᵀ p (int u) (int u'))
prim-adeq p {D} {E} (const k) (const k') hD hE = bind-rel {v = const k} (λ X → E ≫= λ Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩) hD (bind-rel {v = const k'} (λ Y → primD p ⟨ ⌊ D ⌋ , ⟨ Y , ptt ⟩ ⟩) hE
  λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ → out p (hD _ (proj₁ n∈)) (hE _ (proj₁ m∈)) })
  where
  out : ∀ p {n m} → 𝕍 (dconst n) (const {Σ} {Int} k) → 𝕍 (dconst m) (const {Σ} {Int} k') → 𝕍 (dout (δ p n m)) (δᵀ {Σ} p k k')
  out sub ⟨ _ , refl ⟩ ⟨ _ , refl ⟩ = ⟨ refl , refl ⟩
  out eq ⟨ _ , refl ⟩ ⟨ _ , refl ⟩ with does (k ≟ℤ k')
  ... | true = ⟨ refl , ⟨ tt , ⟨ refl , tt ⟩ ⟩ ⟩
  ... | false = ⟨ refl , ⟨ tt , ⟨ refl , tt ⟩ ⟩ ⟩

{- the flag that testinl sets -}
isinl-adeq : ∀ {D} (v : Val Σ ⟪ sum ⟫) → PS D v → PS (D ≫= isinlD) (bit (is-inl v))
isinl-adeq (inl v) h = bind-rel {v = inl v} isinlD h λ { w (inj₁ ⟨ u , ⟨ _ , refl ⟩ ⟩) → ⟨ refl , ⟨ tt , ⟨ refl , tt ⟩ ⟩ ⟩
                                                ; w (inj₂ ⟨ u , ⟨ r , refl ⟩ ⟩) → ⊥-elim (proj₂ (h _ (proj₁ r))) }
isinl-adeq (inr v) h = bind-rel {v = inr v} isinlD h λ { w (inj₁ ⟨ u , ⟨ l , refl ⟩ ⟩) → ⊥-elim (proj₂ (h _ (proj₁ l)))
                                                ; w (inj₂ ⟨ u , ⟨ _ , refl ⟩ ⟩) → ⟨ refl , ⟨ tt , ⟨ refl , tt ⟩ ⟩ ⟩ }

{- the code and environment of a closure -}
car-rel : ∀ (v : Val Σ ⟪ fun ⟫) {D} → PS D v → PS (car ⟨ D , ptt ⟩) (code-of v)
car-rel (pack c e) h u ⟨ u' , p∈ ⟩ = proj₁ (proj₂ (h _ p∈))

cdr-rel : ∀ {η} {v : Val Σ ⟪ fun ⟫} {c : Val Σ (code η)} {e D} → v ≡ pack c e → PS D v → PS (cdr ⟨ D , ptt ⟩) e
cdr-rel refl h u' ⟨ u , p∈ ⟩ = proj₂ (proj₂ (h _ p∈))

{- Calls ---------------------------------------------------------------------------------}

callee′ : ∀ {η} → Val Σ (code η) → Val Σ ⟪ tup η ⟫ → Val Σ Any → State Σ
callee′ (code f) = callee f

enter-eq : ∀ {η} (v : Val Σ (code η)) e a σ → enter ds v e a σ ≡ next (callee′ v e a ⊕ σ)
enter-eq (code f) e a σ = refl

{- an element of a call of code related to v, on related operands -}
call-res : ∀ {η} (v : Val Σ (code η)) {e a Fn Di Si} → PS Fn v → PS Di e → PS Si a
  → ∀ c → c ∈ ⋆ ⟨ ⋆ ⟨ Fn , ⟨ Di , ptt ⟩ ⟩ , ⟨ Si , ptt ⟩ ⟩ → Res (callee′ v e a) c (𝕍 c)
call-res (code f) hF hD hS c ⟨ V , ⟨ ⟨ U , ⟨ e∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ =
  proj₂ (hF _ e∈) _ _ (all→𝕍s U U⊆ hD) (all→𝕍s V V⊆ hS)

{- a result with a value: all of its elements are related to the one value returned -}
collect : ∀ {s C} → (∀ c → c ∈ C → Res s c (𝕍 c)) → Conv C → Σ[ v ∈ Val Σ Any ] Rets s v × PS C v
collect res ⟨ c₀ , ⟨ c₀∈ , c₀≢ ⟩ ⟩ with res c₀ c₀∈
... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (c₀≢ e)
... | inj₂ ⟨ v , ⟨ ok , _ ⟩ ⟩ = ⟨ v , ⟨ ok , all ⟩ ⟩
  where
  all : PS _ v
  all c c∈ with res c c∈
  ... | inj₁ ⟨ _ , er ⟩ = ⊥-elim (Rets-Errs ok er)
  ... | inj₂ ⟨ v' , ⟨ ok' , r ⟩ ⟩ = subst (𝕍 c) (Rets-det ok' ok) r

{- The fundamental lemma ---------------------------------------------------------------}

module _ (T : Table) (𝕋 : ∀ {n} (f : Σ ∋ n) → PS (T (lvl f)) (code f)) where

  𝒪-adeq : ∀ {η ψ τ} (a : Arg Σ ψ τ) {m : Mach Σ η ψ} {ρ R F} → Rel m ρ R F → PR τ (𝒪 T a ρ R) (arg a m)
  𝒪-adeq (atom (var x)) q = fr q x
  𝒪-adeq (atom (lit B c)) q d d∈ with ℬ-inv d d∈
  ... | refl = ⟨ refl , refl ⟩
  𝒪-adeq (atom (ref f)) q = 𝕋 f
  𝒪-adeq (reg r e) q = cast-rel e (rg q r)
  𝒪-adeq (a ↑) q d d∈ = ⟨ tt , 𝒪-adeq a q d d∈ ⟩

  {- the operands of a tuple, bound left to right -}
  args-adeq : ∀ {η ψ j} (as : Vec (Arg Σ ψ (ty Any)) j) {m : Mach Σ η ψ} {ρ R F} → Rel m ρ R F
    → ∀ {K : Results (𝒫 Value) (replicate j ■) → 𝒫 Value} {Q : Value → Set}
    → (∀ Xs → (∀ i → PS (nthD Xs i) (lookup (args as m) i)) → ∀ w → w ∈ K Xs → Q w)
    → ∀ w → w ∈ binds j (𝒪s T as ρ R) K → Q w
  args-adeq [] q k = k ptt (λ ())
  args-adeq (a ∷ as) {m} {ρ} {R} q {K} k = bind-rel {v = arg a m} (λ X → binds _ (𝒪s T as ρ R) (λ Xs → K ⟨ X , Xs ⟩)) (𝒪-adeq a q)
    (args-adeq as q (λ Xs hs → k ⟨ _ , Xs ⟩ (λ { zero d d∈ → 𝒪-adeq a q d (proj₁ d∈) ; (suc i) → hs i })))

  obj-adeq : ∀ {η ψ A} (o : Obj Σ ψ A) {m : Mach Σ η ψ} {ρ R F} → Rel m ρ R F → PS (object T o ρ R) (obj o m)
  obj-adeq (pair c e) {m} {ρ} {R} q = bind-rel {v = arg c m} (λ X → 𝒪 T e ρ R ≫= λ Y → pairD ⟨ X , ⟨ Y , ptt ⟩ ⟩) (𝒪-adeq c q)
    (bind-rel {v = arg e m} (λ Y → pairD ⟨ ⌊ 𝒪 T c ρ R ⌋ , ⟨ Y , ptt ⟩ ⟩) (𝒪-adeq e q) P)
    where
    P : ∀ w → w ∈ pairD ⟨ _ , ⟨ _ , ptt ⟩ ⟩ → 𝕍 w (pack (arg c m) (arg e m))
    P w w∈ with pair-inv w w∈
    ... | ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩ = ⟨ refl , ⟨ 𝒪-adeq c q u (proj₁ u∈) , 𝒪-adeq e q u' (proj₁ u'∈) ⟩ ⟩
  obj-adeq (tuple as) {m} q = args-adeq as q (λ Xs hs → 𝒯-rel (args as m) Xs hs)
  obj-adeq (inl a) {m} {ρ} {R} q = bind-rel {v = arg a m} (λ X → inlD ⟨ X , ptt ⟩) (𝒪-adeq a q) (inl-rel (λ d d∈ → 𝒪-adeq a q d (proj₁ d∈)))
  obj-adeq (inr a) {m} {ρ} {R} q = bind-rel {v = arg a m} (λ X → inrD ⟨ X , ptt ⟩) (𝒪-adeq a q) (inr-rel (λ d d∈ → 𝒪-adeq a q d (proj₁ d∈)))

  {- the blocks bs and their meanings B are related -}
  BR : ∀ {n Bs} → Blocks Σ n Bs → BEnv Bs → Set₁
  BR bs B = ∀ {Δ} (l : _ ∋ Δ) η (φ : Frame Σ Δ) ρ → (∀ {A} (x : Δ ∋ A) → PS (ρ (idx x)) (φ ! x))
    → ∀ w → w ∈ B l ρ → Res (go ds (block bs l) halt η φ) w (𝕍 w)

  adequate : ∀ {n Bs ψ} (k : Seq Σ n Bs ψ) {bs : Blocks Σ n Bs} {B : BEnv Bs} → BR bs B → ∀ {η} (m : Mach Σ η ψ) {ρ R F}
    → Rel m ρ R F → ∀ w → w ∈ ⟦_⟧ˢ T k B ρ R F → Res (run k bs halt η m) w (𝕍 w)

  put-adeq : ∀ {n Bs ψ τ ψ' η} (d : Dst n ψ τ ψ') (k : Seq Σ n Bs ψ') {bs} {B : BEnv Bs} {m : Mach Σ η ψ} {ρ R F v D}
    → BR bs B → Rel m ρ R F → PR τ D v → ∀ w → w ∈ putᴰ {Σ} T d D (⟦_⟧ˢ T k B) ρ R F → Res (run k bs halt η (put d v m)) w (𝕍 w)
  put-adeq (reg r) k br q h = adequate k br _ (reg-rel r h q)
  put-adeq (slot p _) k {v = v} br q h w (inj₁ ⟨ refl , ω∈ ⟩) = ⊥-elim (no-ω {v = v} h ω∈)
  put-adeq (slot p _) k br q h w (inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩) =
    adequate k br _ (slot-rel p (λ d d∈ → h d (proj₁ (V⊆ d d∈))) q) w w∈

  {- chk's strict write -}
  putˢ-adeq : ∀ {n Bs ψ A ψ' η} (d : Dst n ψ (ty A) ψ') (k : Seq Σ n Bs ψ') {bs} {B : BEnv Bs} {m : Mach Σ η ψ} {ρ R F v D}
    → BR bs B → Rel m ρ R F → PS D v → ∀ w → w ∈ putˢᴰ {Σ} T d D (⟦_⟧ˢ T k B) ρ R F → Res (run k bs halt η (put d v m)) w (𝕍 w)
  putˢ-adeq (reg r) k {v = v} br q h w (inj₁ ⟨ refl , ω∈ ⟩) = ⊥-elim (no-ω {v = v} h ω∈)
  putˢ-adeq (reg r) k br q h w (inj₂ ⟨ _ , w∈ ⟩) = adequate k br _ (reg-rel r h q) w w∈
  putˢ-adeq (slot p lt) = put-adeq (slot p lt)

  putˢ-ω : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {D κ ρ R F w} → (∀ d → d ∈ D → d ≡ ω) → w ∈ putˢᴰ {Σ} T d D κ ρ R F → w ≡ ω
  putˢ-ω (reg r) all = bind-ω all
  putˢ-ω (slot p _) all = bind-ω all

  adequate (movq a d ∷ k) br m q w w∈ = Res-step refl (put-adeq d k br q (𝒪-adeq a q) w w∈)
  adequate (subq a r e ∷ k) br m q w w∈ =
    Res-step refl (adequate k br _ (reg-rel r (prim-adeq sub _ _ (cast-rel e (rg q r)) (𝒪-adeq a q)) q) w w∈)
  adequate (cmpq a₂ a₁ ∷ k) br m q w w∈ =
    Res-step refl (adequate k br _ (flag-rel _ (prim-adeq eq _ _ (𝒪-adeq a₁ q) (𝒪-adeq a₂ q)) q) w w∈)
  adequate (sete d ∷ k) br m q w w∈ = Res-step refl (put-adeq d k br q (fl q) w w∈)
  adequate (testinl a ∷ k) br m q w w∈ = Res-step refl (adequate k br _ (flag-rel _ (isinl-adeq _ (𝒪-adeq a q)) q) w w∈)
  adequate (alloc o d ∷ k) br m q w w∈ = Res-step refl (put-adeq d k br q (obj-adeq o q) w w∈)
  adequate (load f a d ∷ k) br m q w w∈ = Res-step refl (put-adeq d k br q (field-adeq {T} f _ (𝒪-adeq a q)) w w∈)
  adequate (loadfst x r ∷ k) br m q w w∈ =
    Res-step refl (adequate k br _ (reg-rel r (car-rel (frame m ! x) (fr q x)) (wipe-rel x q)) w w∈)
  adequate (loadsnd {x = x} r ∷ k) br m q w w∈ = Res-step refl (adequate k br _ (reg-rel r (cdr-rel (op q) (fr q x)) q) w w∈)
  adequate (callq a e₁ e₂ ∷ k) {bs} {B} br m {ρ} {R} q = CALL
    where
    res = call-res (arg a m) (𝒪-adeq a q) (cast-rel e₁ (rg q rdi)) (cast-rel e₂ (rg q rsi))
    pre : ∀ σ → step ds (run (callq a e₁ e₂ ∷ k) bs σ _ m) ≡ next (callee′ (arg a m) _ _ ⊕ retK k bs (frame m) σ)
    pre σ = enter-eq (arg a m) _ _ (retK k bs (frame m) σ)
    C = ⋆ ⟨ ⋆ ⟨ 𝒪 T a ρ R , ⟨ R rdi , ptt ⟩ ⟩ , ⟨ R rsi , ptt ⟩ ⟩
    CALL : ∀ w → w ∈ (C ≫= λ _ → ⟦_⟧ˢ T k B ρ (called-regs C) init) → Res (run (callq a e₁ e₂ ∷ k) bs halt _ m) w (𝕍 w)
    CALL w (inj₁ ⟨ refl , ω∈ ⟩) with res ω ω∈
    ... | inj₁ ⟨ _ , er ⟩ = inj₁ ⟨ refl , (λ σ → let ⟨ t , ⟨ τ , q' ⟩ ⟩ = er (retK k bs (frame m) σ) in ⟨ t , ⟨ pre σ ∷↠ τ , q' ⟩ ⟩) ⟩
    ... | inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩ = ⊥-elim (𝕍-ω v r)
    CALL w (inj₂ ⟨ conv , w∈ ⟩) with collect res conv
    ... | ⟨ v , ⟨ ⟨ t , ⟨ τ , ok ⟩ ⟩ , all ⟩ ⟩ =
      Res-pre (pre halt ∷↠ ↠-⊕ _ τ ++↠ ret-next ok k bs (frame m) halt ∷↠ done) (adequate k br _ (ret-rel (fr q) all) w w∈)
  adequate (chk t x d ∷ k) {bs} br m q w w∈ with proj-adeq t (frame m ! x) (fr q x)
  ... | inj₁ ⟨ e , allω ⟩ with putˢ-ω d allω w∈
  ...   | refl = inj₁ ⟨ refl , (λ σ → ⟨ _ , ⟨ done , cong (λ p → checked ds p d k bs σ _) e ⟩ ⟩) ⟩
  adequate (chk t x d ∷ k) {bs} br m q w w∈ | inj₂ ⟨ v , ⟨ e , h ⟩ ⟩ =
    Res-step (cong (λ p → checked ds p d k bs halt _) e) (putˢ-adeq d k br (rax-rel q) h w w∈)
  adequate (retq e) br m q w w∈ = inj₂ ⟨ _ , ⟨ ⟨ _ , ⟨ done , rets e ⟩ ⟩ , cast-rel e (rg q rax) w w∈ ⟩ ⟩
  adequate (jmp l) br m q w w∈ = Res-step refl (br l _ (frame m) _ (fr q) w w∈)
  adequate (je l₁ l₂) {bs} {B} br m {ρ} {R} {F} q = bind-rel {v = bit (flag m)} (λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ _ → B l₁ ρ) , ⟨ (λ _ → B l₂ ρ) , ptt ⟩ ⟩ ⟩) (fl q) J
    where
    nx : Bool → _
    nx b = next (if b then go ds (block bs l₁) halt _ (frame m) else go ds (block bs l₂) halt _ (frame m))
    l : ∀ b {u} → 𝕍 (left u) (bit {Σ} b) → b ≡ true
    l true _ = refl
    l false ⟨ _ , () ⟩
    r : ∀ b {u} → 𝕍 (right u) (bit {Σ} b) → b ≡ false
    r false _ = refl
    r true ⟨ _ , () ⟩
    J : ∀ w → w ∈ 𝒞 ⟨ ⌊ F ⌋ ⇂ ValPayload , ⟨ (λ _ → B l₁ ρ) , ⟨ (λ _ → B l₂ ρ) , ptt ⟩ ⟩ ⟩ → Res (run (je l₁ l₂) bs halt _ m) w (𝕍 w)
    J w (inj₁ ⟨ u , ⟨ U , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) =
      Res-step (cong nx (l _ (fl q _ (proj₁ (proj₁ (ls u (here refl))))))) (br l₁ _ (frame m) _ (fr q) w w∈)
    J w (inj₂ ⟨ u , ⟨ U , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) =
      Res-step (cong nx (r _ (fl q _ (proj₁ (proj₁ (rs u (here refl))))))) (br l₂ _ (frame m) _ (fr q) w w∈)

  blocks-adeq : ∀ {n Bs} (bs : Blocks Σ n Bs) → BR bs (blocksᴰ T bs)
  blocks-adeq (bs ▷ k) Z η φ ρ f = adequate k (blocks-adeq bs) _ (mr f (λ { rax → tt ; rdi → tt ; rsi → tt }) tt tt)
  blocks-adeq (bs ▷ k) (S l) = blocks-adeq bs l

  run-adeq : ∀ {ψ} (b : Body Σ ψ) {η} (m : Mach Σ η ψ) {ρ R F} → Rel m ρ R F
    → ∀ w → w ∈ runᴰ T b ρ R F → Res (run (Body.start b) (Body.blocks b) halt η m) w (𝕍 w)
  run-adeq (body n bs k) = adequate k (blocks-adeq bs)

{- The table ------------------------------------------------------------------------}

{- the code of definition f, under a table related to the code pointers -}
code-rel : ∀ {n} (f : Σ ∋ n) {T} → (∀ {n} (g : Σ ∋ n) → PS (T (lvl g)) (code g)) → PS (codeₜ T (ds ! f)) (code f)
code-rel f 𝕋 ν _ = ⟨ tt , tt ⟩
code-rel f 𝕋 (X ↦ ν) _ = ⟨ tt , tt ⟩
code-rel f {T} 𝕋 (X ↦ (Y ↦ w)) ⟨ ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ , _ ⟩ = ⟨ tt , (λ e a Xe Ya →
  run-adeq T 𝕋 (ds ! f) _ (mr (λ ()) (λ { rax → tt ; rdi → 𝕍s-∈ X Xe ; rsi → 𝕍s-∈ Y Ya }) tt tt) w w∈) ⟩
code-rel f 𝕋 (dconst k) ()
code-rel f 𝕋 ω ()
code-rel f 𝕋 ⦅ u , v ⦆ ()
code-rel f 𝕋 (tup[ i ] d) ()
code-rel f 𝕋 (left d) ()
code-rel f 𝕋 (right d) ()
code-rel f 𝕋 ⟨⟩ ()
code-rel f 𝕋 (X ↦ dconst k) ()
code-rel f 𝕋 (X ↦ ω) ()
code-rel f 𝕋 (X ↦ ⦅ u , v ⦆) ()
code-rel f 𝕋 (X ↦ (tup[ i ] d)) ()
code-rel f 𝕋 (X ↦ left d) ()
code-rel f 𝕋 (X ↦ right d) ()
code-rel f 𝕋 (X ↦ ⟨⟩) ()

module _ (TC : ∀ k → Con (T⁺ k)) (ind : Indep) where

  {- each entry of the table is related to its code pointer, by induction on levels -}
  tbl-rel : ∀ {n} (f : Σ ∋ n) → PS (T⁺ (lvl f)) (code f)
  tbl-rel f = below (suc (lvl f)) f (s≤s ≤-refl)
    where
    below : ∀ p {n} (f : Σ ∋ n) → lvl f < p → PS (T⁺ (lvl f)) (code f)
    below (suc p) f (s≤s f≤) d d∈ = code-rel f 𝕋cut d (fix-C TC ind f d d∈)
      where
      𝕋cut : ∀ {n} (g : Σ ∋ n) → PS (cut (lvl f) ⌈ ν ⌉ T⁺ (lvl g)) (code g)
      𝕋cut g with lvl g <? lvl f
      ... | yes g< = below p g (<-≤-trans g< f≤)
      ... | no _ = λ { _ refl → ⟨ tt , tt ⟩ }

  {- the main sequence, from the start -}
  main-adeq : ∀ (b : Body Σ (entry [])) w → w ∈ runᴰ T⁺ b (λ _ → init) (λ _ → init) init
    → Res (run (Body.start b) (Body.blocks b) halt 0 ⟨ rv tt tt tt , [] , tt , tt ⟩) w (𝕍 w)
  main-adeq b = run-adeq T⁺ tbl-rel b _ (mr (λ ()) (λ { rax → tt ; rdi → tt ; rsi → tt }) tt tt)
