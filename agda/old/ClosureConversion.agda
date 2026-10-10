module ClosureConversion where

open import Function using (_∘_)
import Syntax
open import Primitives
open import ISWIMLanguage

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_; _+_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; n≤1+n; +-identityʳ; ≤-step; +-comm; ≤⇒≯;
         ≤-antisym; +-suc; ≤∧≢⇒<; _≤?_; 1+n≰n; suc-injective; ≤-pred; ≰⇒>; <⇒≢;
         <⇒≱)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (Dec; yes; no)

≤→<⊎≡ : ∀{a b : ℕ}
   → a ≤ b
   → a < b ⊎ a ≡ b
≤→<⊎≡ {.0} {zero} z≤n = inj₂ refl
≤→<⊎≡ {.0} {suc b} z≤n = inj₁ (s≤s z≤n)
≤→<⊎≡ {suc a}{suc b} (s≤s a≤b)
    with ≤→<⊎≡ {a}{b} a≤b
... | inj₁ lt = inj₁ (s≤s lt)
... | inj₂ refl = inj₂ refl

≤→Σ+ : ∀ m n → m ≤ n → Σ[ d ∈ ℕ ] n ≡ m + d
≤→Σ+ zero n m≤n = ⟨ n , refl ⟩
≤→Σ+ (suc m) (suc n) (s≤s m≤n)
    with ≤→Σ+ m (suc n) (≤-trans (≤-step ≤-refl) (s≤s m≤n))
... | ⟨ 0 , eq ⟩ rewrite +-comm m 0 | sym eq = ⊥-elim (1+n≰n m≤n)
... | ⟨ suc d , eq ⟩ rewrite +-suc m d | suc-injective eq =
      ⟨ d , refl ⟩

{-

  Target intermediate language of closure conversion

-}

data IROp : Set where
  fun : ℕ → IROp     {- number of parameters -}
  close : ℕ → IROp   {- number of free variables -}
  ir-app : IROp
  ir-lit : (p : Prim) → rep p → IROp

IR-sig : IROp → List ℕ
IR-sig (fun n) = n ∷ []
IR-sig (close n) = replicate (suc n) 0
IR-sig ir-app = 0 ∷ 0 ∷ []
IR-sig (ir-lit p k) = []

open Syntax using (Rename; _•_; ↑; ⦉_⦊; _⨟ᵣ_)
module IRMod = Syntax.OpSig IROp IR-sig
open IRMod renaming (ABT to IR; `_ to ^_; _⦅_⦆ to node; cons to ir-cons;
   nil to ir-nil; ast to ir-ast; bind to ir-bind; rename to ir-rename;
   WF to ir-WF; FV? to ir-FV?; WF-op to ir-WF-op; WF-cons to ir-WF-cons;
   WF-nil to ir-WF-nil; WF-ast to ir-WF-ast; WF-bind to ir-WF-bind;
   Arg to ir-Arg; Args to ir-Args; make-renaming to make-ir-renaming;
   ⦉make-renaming⦊ to ⦉make-ir-renaming⦊;
   rename→subst to ir-rename→subst) public
open IRMod using (_⨟_; exts-cons-shift; bind-ast)

pattern # p k = node (ir-lit p k) ir-nil 
pattern Ƒ n N = node (fun n) (ir-cons N ir-nil)
pattern ⟪_,_,_⟫ f n fvs = node (close n) (ir-cons (ir-ast f) fvs)
pattern _˙_ L M = node ir-app (ir-cons (ir-ast L) (ir-cons (ir-ast M) ir-nil))

num-FV : (n i : ℕ) → IR → ℕ
num-FV n 0 M = 0
num-FV n (suc i) M
    with ir-FV? M n
... | true = suc (num-FV (suc n) i M )
... | false = num-FV (suc n) i M 

{-

  The compress function produces a renaming that maps all the free
  variables above 0 in a term M into a contiguous sequence of numbers
  starting at 1. Inspired by counting sort, it does this by compute
  the cumulative sum of the number of free variables up to n, not
  including variable 0.

-}

sum-FV : ℕ → IR → ℕ
sum-FV zero M = 0
sum-FV (suc n) M
    with ir-FV? M (suc n)
... | true = suc (sum-FV n M)
... | false = sum-FV n M

compress : ℕ → IR → Rename
compress Γ M = make-ir-renaming (λ x → sum-FV x M) Γ

compress-sum-FV : ∀{Γ}{x}{M}
  → x < Γ
  → ⦉ compress Γ M ⦊ x ≡ sum-FV x M
compress-sum-FV {Γ} {x} {M} x<Γ = ⦉make-ir-renaming⦊ x<Γ

least-sum-FV : IR → ℕ → Set
least-sum-FV M x = ∀ y → sum-FV y M ≡ sum-FV x M → x ≤ y

search : (x : ℕ) → (M : IR) → (s : ℕ)
       → (Σ[ x' ∈ ℕ ] s ≡ sum-FV x' M × least-sum-FV M x')
         ⊎ (∀ y → y ≤ x → sum-FV y M < s)
search zero M s
    with s ≟ sum-FV 0 M
... | yes s=sum[0] = inj₁ ⟨ 0 , ⟨ s=sum[0] , (λ y _ → z≤n) ⟩ ⟩
... | no s≠sum[0] = inj₂ (G s≠sum[0])
    where
    G : ∀{s} → s ≢ 0 → (y : ℕ) → y ≤ 0 → suc (sum-FV y M) ≤ s
    G {0} s≢0 .0 z≤n = ⊥-elim (s≢0 refl)
    G {suc s} s≢0 .0 z≤n = s≤s z≤n
search (suc x) M s
    with search x M s
... | inj₁ ⟨ x' , ⟨ s=sum[x'] , least ⟩ ⟩ =
      inj₁ ⟨ x' , ⟨ s=sum[x'] , least ⟩ ⟩
... | inj₂ less
    with s ≟ sum-FV (suc x) M
... | yes s=sum[1+x] = inj₁ ⟨ (suc x) , ⟨ s=sum[1+x] , G ⟩ ⟩
    where
    G : (y : ℕ) →  sum-FV y M ≡ (sum-FV (suc x) M) → suc x ≤ y
    G y eq = ≰⇒> λ y≤x →
       let sum[y]<s = less y y≤x in
       let sum[y]=s = trans eq (sym s=sum[1+x]) in
       (<⇒≢ sum[y]<s) sum[y]=s
... | no s≢sum[1+x] = inj₂ G
    where
    G : (y : ℕ) → y ≤ suc x → suc (sum-FV y M) ≤ s
    G y y≤1+x
        with y ≤? x
    ... | yes y≤x = less y y≤x
    ... | no y≰x
        with ≤→<⊎≡ y≤1+x
    ... | inj₁ y<1+x = ⊥-elim (y≰x (≤-pred y<1+x))
    ... | inj₂ refl
        with ir-FV? M (suc x)
    ... | true =
          let sum[x]<x = less x ≤-refl in
          ≤∧≢⇒< sum[x]<x λ z → s≢sum[1+x] (sym z)
    ... | false = less x ≤-refl
    

sum-FV-inv : IR → ℕ → ℕ → ℕ
sum-FV-inv M Γ s
    with s ≤? sum-FV Γ M
... | no nlt = 0
... | yes s≤sum[Γ]
    with search Γ M s
... | inj₁ ⟨ x , ⟨ s=sum[x] , least ⟩ ⟩ = x
... | inj₂ less = ⊥-elim ((≤⇒≯ s≤sum[Γ]) (less Γ ≤-refl))

sum-FV-mono-≤-aux : ∀{M}{x}{d}
  → sum-FV x M ≤ sum-FV (x + d) M
sum-FV-mono-≤-aux {M} {x} {zero} rewrite +-comm x 0 = ≤-refl
sum-FV-mono-≤-aux {M} {x} {suc d}
    rewrite +-suc x d
    with ir-FV? M (suc (x + d))
... | true = ≤-step (sum-FV-mono-≤-aux {M} {x} {d})
... | false = sum-FV-mono-≤-aux {M} {x} {d}

sum-FV-mono-≤ : ∀{M}{x}{y}
  → x ≤ y
  → sum-FV x M ≤ sum-FV y M
sum-FV-mono-≤ {M} {x} {y} x≤y
    with ≤→Σ+ x y x≤y
... | ⟨ d , refl ⟩ = sum-FV-mono-≤-aux {M}{x}{d}

sum-FV-inverse : ∀{Γ}{M}{x}
  → x < Γ
  → least-sum-FV M x
  → sum-FV-inv M Γ (sum-FV x M) ≡ x
sum-FV-inverse {Γ}{M}{x} x<Γ least
    with sum-FV x M ≤? sum-FV Γ M
... | no nlt = ⊥-elim (nlt (sum-FV-mono-≤ (≤-trans (≤-step ≤-refl) x<Γ)))
... | yes lt
    with search Γ M (sum-FV x M)
... | inj₁ ⟨ x' , ⟨ eq , least' ⟩ ⟩ =
      ≤-antisym (least' x eq) (least x' (sym eq))
... | inj₂ less =
      let a = less x (≤-trans (≤-step ≤-refl) x<Γ) in
      ⊥-elim (1+n≰n a)


expand : ℕ → IR → Rename
expand Γ M = make-ir-renaming (sum-FV-inv M Γ) (suc (sum-FV Γ M))

expand-sum-FV-inv : ∀{x}{Γ}{M}
  → x < Γ
  → least-sum-FV M x
  → ⦉ expand Γ M ⦊ (sum-FV x M) ≡ x
expand-sum-FV-inv {x}{Γ}{M} x<Γ least =
    let xx = ⦉make-ir-renaming⦊ {Γ = suc (sum-FV Γ M)} {x = sum-FV x M}{ρ = (sum-FV-inv M Γ)} (s≤s (sum-FV-mono-≤ (≤-trans (≤-step ≤-refl) x<Γ))) in 
    begin
        ⦉ expand Γ M ⦊ (sum-FV x M)
    ≡⟨⟩
        ⦉ make-ir-renaming (sum-FV-inv M Γ) (suc (sum-FV Γ M)) ⦊ (sum-FV x M)
    ≡⟨ xx ⟩
        sum-FV-inv M Γ (sum-FV x M)
    ≡⟨ sum-FV-inverse x<Γ least ⟩
        x
    ∎

{- An example that includes 0 as a free variable. -}
test-M : IR
test-M = ((^ 7) ˙ (^ 1)) ˙ ((^ 0) ˙ (^ 4))

test-M′ : IR
test-M′ = ((^ 3) ˙ (^ 1)) ˙ ((^ 0) ˙ (^ 2))

{- An example that does not include 0 as a free variable. -}
test-N : IR
test-N = ((^ 7) ˙ (^ 1)) ˙ ((^ 3) ˙ (^ 4))

test-N′ : IR
test-N′ = ((^ 4) ˙ (^ 1)) ˙ ((^ 2) ˙ (^ 3))

_ : ir-rename (compress 8 test-M) test-M ≡ test-M′
_ = refl

_ : ir-rename (compress 8 test-N) test-N ≡ test-N′
_ = refl

_ : ⦉ compress 8 test-M ⦊ 0 ≡ 0
_ = refl

_ : ⦉ compress 8 test-M ⦊ 1 ≡ 1
_ = refl

_ : ⦉ compress 8 test-M ⦊ 4 ≡ 2
_ = refl

_ : ⦉ compress 8 test-M ⦊ 7 ≡ 3
_ = refl

_ : ir-rename (expand 8 test-M) test-M′ ≡ test-M
_ = refl

_ : ir-rename (expand 8 test-N) test-N′ ≡ test-N
_ = refl

_ : ⦉ expand 8 test-M ⦊ 0 ≡ 0
_ = refl

_ : ⦉ expand 8 test-M ⦊ 1 ≡ 1
_ = refl

_ : ⦉ expand 8 test-M ⦊ 2 ≡ 4
_ = refl

_ : ⦉ expand 8 test-M ⦊ 3 ≡ 7
_ = refl

{-

 Closure Conversion 

 -}

add-binds : (n : ℕ) → IR → ir-Arg n
add-binds zero N = ir-ast N
add-binds (suc n) N = ir-bind (add-binds n N)

fv-refs : (n i k : ℕ) → (M : IR) → ir-Args (replicate (num-FV n i M) 0)
fv-refs n zero k M = ir-nil
fv-refs n (suc i) k M
    with ir-FV? M n
... | true = ir-cons (ir-ast (^ n)) (fv-refs (suc n) i (suc k) M)
... | false = fv-refs (suc n) i k M

𝒞 : (M : Term) → ∀{Γ} → {wf : WF Γ M} → IR
𝒞 (` x) {Γ} {wfM} = ^ x
𝒞 (ƛ N) {Γ} {WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)} =
  let N′ = 𝒞 N {suc Γ} {wfN} in
  let ρ = compress Γ N′ in
  let rN′ = ir-rename ρ N′ in
  let nfv = num-FV 1 Γ N′ in
  let fun = Ƒ (suc nfv) (add-binds (suc nfv) rN′) in
  ⟪ fun , nfv , fv-refs 1 Γ 1 N′ ⟫
𝒞 (L · M) {Γ}
   {WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))} =
   let L′ = 𝒞 L {wf = wfL} in
   let M′ = 𝒞 M {wf = wfM} in
   L′ ˙ M′
𝒞 ($ p k) {Γ} {wf} = # p k

{-

 Semantics of the IR language

 -}

curry-n : (n : ℕ) → ir-Arg n → Denotation
apply-n : (n : ℕ) → Denotation → ir-Args (replicate n 0) → Denotation
    
ℳ : IR → Denotation
ℳ (# P k) γ v = ℘ {P} k v
ℳ (^ x) γ v = v ⊑ γ x
ℳ (Ƒ n bN) γ v =
    curry-n n bN `∅ v
ℳ ⟪ L , n , As ⟫ =
    apply-n n (ℳ L) As
ℳ (L ˙ M) = (ℳ L) ● (ℳ M)

curry-n 0 (ir-ast N) = ℳ N
curry-n (suc n) (ir-bind bN) = ℱ (curry-n n bN)

apply-n zero D ir-nil = D
apply-n (suc n) D (ir-cons (ir-ast M) As) =
    let D′ = D ● ℳ M in
    apply-n n D′ As

{-

Correctness of Closure Conversion

-}



{- Correctness of compressor -}

compress-pres : ∀{N : IR}{Γ}{γ : Env}{v w}
  → ℳ N (γ `, v) w
  → ℳ (ir-rename (compress Γ N) N) (γ ∘ ⦉ expand Γ N ⦊ `, v) w
compress-pres {N} {Γ} {γ}{v}{w} ℳN[γ,v]w =
{-
   need rename-pres-FV for the IR! -Jeremy
   let xx = rename-pres-FV (compress Γ N) {!!} {!!} ℳN[γ,v]w in
-}
   {!!}



apply-curry : ∀{Γ : ℕ} {N : Term} {wfN : WF (suc Γ) N} {wfλN : WF Γ (ƛ N)}
  → ℳ (𝒞 N {suc Γ}{wfN}) ≃ ℰ N
  → ℳ (𝒞 (ƛ N) {Γ} {wfλN}) ≃ ℱ (ℰ N)
apply-curry {Γ} {N} {wfN}{wfλN} ℳ𝒞N≃ℰN = {!!}

𝒞-correct : ∀ Γ (M : Term) (wf : WF Γ M)
   → (ℳ (𝒞 M {Γ}{wf})) ≃ (ℰ M)
𝒞-correct Γ ($ p k) wf = ≃-refl
𝒞-correct Γ (` x) wf = ≃-refl
𝒞-correct Γ (ƛ N) wf@(WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)) =
   let IH = 𝒞-correct (suc Γ) N wfN in
      ℳ (𝒞 (ƛ N) {Γ} {wf})
   ≃⟨ apply-curry {Γ}{N}{wfN}{wf} IH ⟩
      ℱ (ℰ N)
   ≃⟨⟩
      ℰ (ƛ N)
   ■
𝒞-correct Γ (L · M)
            (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))) =
  let IH1 = 𝒞-correct Γ L wfL in
  let IH2 = 𝒞-correct Γ M wfM in
  ●-cong IH1 IH2

{-

  Some experimentation

-}

_ : ⦉ 0 • ↑ 2 ⦊ 0 ≡ 0
_ = refl

_ : ⦉ 0 • ↑ 2 ⦊ 1 ≡ 2
_ = refl

_ : ⦉ 0 • ↑ 2 ⦊ 2 ≡ 3
_ = refl

curry-app-0a : ∀{M : Term}{γ : Env}{v w : Value}
  → wf v → wf w
  → ℰ M (γ `, v) w
  → ℰ ((ƛ (rename (0 • ↑ 2) M)) · (` 0)) (γ `, v) w
curry-app-0a {M}{γ}{v}{w} wfv wfw ℰMγvw =
  ⟨ v , ⟨ wfv , ⟨ rename-pres {M = M} (0 • ↑ 2) G wfw ℰMγvw , ⊑-refl ⟩ ⟩ ⟩
  where
  G : (γ `, v) `⊑ ((λ {x} → γ `, v `, v) ∘ ⦉ 0 • ↑ 2 ⦊)
  G zero = ⊑-refl
  G (suc x) = ⊑-refl

{-
rename-pres {M = M} (0 • ↑ 1) `⊑-refl wfw ℰMγvw

curry-app-0b : (ℱ (ℰ M) ● ℰ (` 0)) γ v → ℰ M γ v
curry-app-0b = ?

not quite true, need non-empty γ 

curry-app-0 : (M : Term)
  → ℰ M ≃ ℱ (ℰ M) ● ℰ (` 0)
-}


{-----------------------------------------------------------------------------

  A lower-level intermediate language that represents
  closures as tuples.

 -----------------------------------------------------------------------------}

data IR2Op : Set where
  ir2-fun : ℕ → IR2Op
  tuple-nil : IR2Op
  tuple-cons : IR2Op
  ir2-car : IR2Op
  ir2-cdr : IR2Op
  ir2-app : IR2Op
  ir2-lit : (p : Prim) → rep p → IR2Op

IR2-sig : IR2Op → List ℕ
IR2-sig (ir2-fun n) = n ∷ []
IR2-sig tuple-nil = []
IR2-sig tuple-cons = 0 ∷ 0 ∷ []
IR2-sig ir2-car = 0 ∷ []
IR2-sig ir2-cdr = 0 ∷ []
IR2-sig ir2-app = 0 ∷ 0 ∷ []
IR2-sig (ir2-lit p k) = []

module IR2Mod = Syntax.OpSig IR2Op IR2-sig
open IR2Mod
   renaming (ABT to IR2; Arg to Arg2; `_ to ´_; _⦅_⦆ to ir2-node;
      cons to ir2-cons; nil to ir2-nil;
      ast to ir2-ast; bind to ir2-bind)

pattern ! p k = ir2-node (ir2-lit p k) ir2-nil
pattern 𝑓 n N = ir2-node (ir2-fun n) (ir2-cons N ir2-nil)
pattern _∙_ L M = ir2-node ir2-app (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern 〈〉 = ir2-node tuple-nil ir2-nil
pattern pair L M = ir2-node tuple-cons (ir2-cons (ir2-ast L) (ir2-cons (ir2-ast M) ir2-nil))
pattern car M = ir2-node ir2-car (ir2-cons (ir2-ast M) ir2-nil)
pattern cdr M = ir2-node ir2-cdr (ir2-cons (ir2-ast M) ir2-nil)

⟬_,_⟭ : Denotation → Denotation → Denotation
⟬_,_⟭ D₁ D₂ γ ⊥ = False
⟬_,_⟭ D₁ D₂ γ (const k) = False
⟬_,_⟭ D₁ D₂ γ (v₁ ↦ v₂) = const 0 ⊑ v₁ × D₁ γ v₂ ⊎ const 1 ⊑ v₁ × D₂ γ v₂
⟬_,_⟭ D₁ D₂ γ (v₁ ⊔ v₂) = ⟬ D₁ , D₂ ⟭ γ v₁ × ⟬ D₁ , D₂ ⟭ γ v₂

π₁ : Denotation → Denotation
π₁ D = D ● (λ γ v → ℘ {base Nat} 0 v)

π₂ : Denotation → Denotation
π₂ D = D ● (λ γ v → ℘ {base Nat} 1 v)

ℒ : IR2 → Denotation
ℒ (! P k) γ v = ℘ {P} k v
ℒ (´ x) γ v = (v ⊑ γ x)
ℒ (𝑓 n bN) = curry-n' n bN
    where
    curry-n' : (n : ℕ) → Arg2 n → Denotation
    curry-n' 0 (ir2-ast N) = ℒ N
    curry-n' (suc n) (ir2-bind bN) = ℱ (curry-n' n bN)
ℒ (L ∙ M) = (ℒ L) ● (ℒ M)
ℒ 〈〉 γ v = v ⊑ ⊥
ℒ (pair L M) = ⟬ ℒ L , ℒ M ⟭
ℒ (car M) = π₁ (ℒ M)
ℒ (cdr M) = π₂ (ℒ M)
