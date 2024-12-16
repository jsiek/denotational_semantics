{-# OPTIONS --rewriting --prop #-}

module DTLC where

open import Level using (Lift)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import StepIndexedLogic2 renaming (_∈_ to _⋲_)
open import PropP

open import Sig
open import Var

data Val : Set where
  nat : ℕ → Val
  func : List (Val × Val) → Val

data Op : Set where
  op-lam : Op
  op-app : Op
  op-zero : Op
  op-suc : Op
  op-case : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-zero = []
sig op-suc = ■ ∷ []
sig op-case = ■ ∷ ■ ∷ (ν ■) ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

variable L L′ M M′ N N′ V V′ W W′ : Term

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `zero = op-zero ⦅ nil ⦆
pattern `suc M = op-suc ⦅ cons (ast M) nil ⦆
pattern case L M N = op-case ⦅ cons (ast L) (cons (ast M) (cons (bind (ast N)) nil)) ⦆

get : ∀{ℓ}{T : Set ℓ} → List T → ℕ → Maybe T
get [] x = nothing
get (v ∷ vs) zero = just v
get (v ∷ vs) (suc x) = get vs x


Denot : Set₁
Denot = Val → Set

Env : Set₁
Env = List Denot

ret : Val → Denot
ret v = λ w → v ≡ w

nat! : ℕ → Denot
nat! n = ret (nat n)

nat? : Denot → (ℕ → Denot) → Denot
nat? D f v = ∃[ n ] D (nat n) × f n v

fun! : (Denot → Denot) → Denot
fun! F (nat x) = ⊥
fun! F (func ls) = All (λ {(arg , res) → F (ret arg) res}) ls

fun? : Denot → Denot → Denot
fun? F D res = ∃[ tab ] ∃[ arg ] F (func tab) × D arg × (arg , res) ∈ tab

⟦_⟧ : Term → Env → Denot
⟦ ` x ⟧ ρ
    with get ρ x
... | nothing = λ v → ⊥
... | just D = D
⟦ ƛ N ⟧ ρ = fun! λ a → ⟦ N ⟧ (a ∷ ρ)
⟦ L · M ⟧ ρ = fun? (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ `zero ⟧ ρ = nat! 0
⟦ `suc M ⟧ ρ = nat? (⟦ M ⟧ ρ) λ n → nat! (suc n)
⟦ case L M N ⟧ ρ = nat? (⟦ L ⟧ ρ)
    λ{ zero → ⟦ M ⟧ ρ ;
      (suc n) → ⟦ N ⟧ (nat! n ∷ ρ) }

data Value : Set where
  natV : ℕ → Value
  closV : Term → List Value → Value

{--- Denotations for Values and Environments ---}

⟦_⟧ᴱ : List Value → Env
⟦_⟧ⱽ : Value → Denot

⟦ [] ⟧ᴱ = []
⟦ (v ∷ ls) ⟧ᴱ  = ⟦ v ⟧ⱽ ∷ ⟦ ls ⟧ᴱ

⟦ natV n ⟧ⱽ = nat! n
⟦ closV N ρ ⟧ⱽ = ⟦ ƛ N ⟧ ⟦ ρ ⟧ᴱ

get-E : ∀{V w ρ x}
  → ⟦ V ⟧ⱽ w
  → get ρ x ≡ just V
  → ∃[ D ] get ⟦ ρ ⟧ᴱ x ≡ just D × D w
get-E {V} {w} {[]} {x} ⟦V⟧w ()
get-E {V} {w} {V ∷ ρ} {zero} ⟦V⟧w refl = ⟦ V ⟧ⱽ , refl , ⟦V⟧w
get-E {V} {w} {W ∷ ρ} {suc x} ⟦V⟧w ρxV = get-E {ρ = ρ}{x} ⟦V⟧w ρxV

{--- A step-indexed interpreter ---}

interp : Term → List Value → ℕ → Maybe Value
interp M ρ 0 = nothing
interp (` x) ρ (suc i) = get ρ x
interp (ƛ N) ρ (suc i) = just (closV N ρ)
interp (L · M) ρ (suc i) =
  interp L ρ i >>=
    λ{ (natV n) → nothing ;
       (closV N ρ') → 
        interp M ρ i >>= λ w → interp N (w ∷ ρ') i }
interp `zero ρ (suc i) = just (natV 0)
interp (`suc M) ρ (suc i) =
  interp M ρ i >>=
  λ{ (natV n) → just (natV (suc n)) ;
     (closV N ρ') → nothing }
interp (case L M N) ρ (suc i) =
  interp L ρ i >>=
  λ{ (natV 0) → interp M ρ i ;
     (natV (suc n)) → interp N (natV n ∷ ρ) i ;
     (closV N ρ') → nothing }

{--- Logical Relation ---}

{- First some beaucratic setup. -}

Γ₁ : Context
Γ₁ = (Value ⊎ Term × List Value) ∷ []

pre-𝒱 : Value → Setᵒ Γ₁ (Later ∷ [])
pre-ℰ : Term → List Value → Setᵒ Γ₁ (Later ∷ [])

pre-𝒱⊎ℰ : (Value ⊎ Term × List Value) → Setᵒ Γ₁ (Later ∷ [])
pre-𝒱⊎ℰ (inj₁ V) = pre-𝒱 V
pre-𝒱⊎ℰ (inj₂ (M , ρ)) = pre-ℰ M ρ

𝒱⊎ℰ : (Value ⊎ Term × List Value) → Setᵒ [] []
𝒱⊎ℰ X = μᵒ pre-𝒱⊎ℰ X

𝒱⟦_⟧ : Value → Setᵒ [] []
𝒱⟦ V ⟧ = 𝒱⊎ℰ (inj₁ V)

ℰ⟦_⟧_ : Term → List Value → Setᵒ [] []
ℰ⟦ M ⟧ ρ = 𝒱⊎ℰ (inj₂ (M , ρ))

𝒱ᵒ⟦_⟧ : Value → Setᵒ Γ₁ (Now ∷ [])
𝒱ᵒ⟦ V ⟧ = inj₁ V ⋲ recᵒ

ℰᵒ⟦_⟧_ : Term → List Value → Setᵒ Γ₁ (Now ∷ [])
ℰᵒ⟦ M ⟧ ρ = inj₂ (M , ρ) ⋲ recᵒ

{- interp as a predicate in step-indexed logic -}

interpMono : ∀ M ρ i j V 
  → interp M ρ i ≡ just V
  → i ≤ j
  → interp M ρ j ≡ just V
interpMono (` x) ρ (suc i) .(suc _) V MiV (s≤s i≤j) = MiV
interpMono (ƛ N) ρ (suc i) j V MiV (s≤s i≤j) = MiV
interpMono (L · M) ρ (suc i) (suc j) V MiV (s≤s i≤j)
    with interp L ρ i in LiC | MiV
... | nothing | ()
... | just (closV N ρ′) | MiV′
    with interp M ρ i in MiW | MiV′
... | nothing | ()
... | just W | NiV
    rewrite interpMono L ρ i j (closV N ρ′) LiC i≤j
    | interpMono M ρ i j W MiW i≤j =
    interpMono N (W ∷ ρ′) i j V NiV i≤j
interpMono `zero ρ (suc i) (suc j) V MiV (s≤s i≤j) = MiV
interpMono (`suc M) ρ (suc i) (suc j) V MiV (s≤s i≤j)
    with interp M ρ i in MiW | MiV
... | nothing | ()
... | just (natV n) | refl
    rewrite interpMono M ρ i j (natV n) MiW i≤j =
    refl
interpMono (case L M N) ρ (suc i) (suc j) V MiV (s≤s i≤j)
    with interp L ρ i in LiC | MiV
... | nothing | ()
... | just (natV 0) | MiV′
    with interp M ρ i in MiW | MiV′ 
... | nothing | ()
... | just W | refl
    rewrite interpMono L ρ i j (natV 0) LiC i≤j
    | interpMono M ρ i j W MiW i≤j = refl
interpMono (case L M N) ρ (suc i) (suc j) V MiV (s≤s i≤j)
    | just (natV (suc n)) | NiV 
    rewrite interpMono L ρ i j (natV (suc n)) LiC i≤j =
    interpMono N (natV n ∷ ρ) i j V NiV i≤j

subtractLess : ∀ i k n 
   → k ≤ₚ n
   → i ∸ n ≤ i ∸ k
subtractLess zero zero zero k≤n = z≤n
subtractLess zero zero (suc n) k≤n = z≤n
subtractLess zero (suc k) (suc n) k≤n = z≤n
subtractLess (suc i) zero zero k≤n = s≤s (subtractLess i zero zero ttₚ)
subtractLess (suc i) zero (suc n) k≤n =
  let i∸n≤i = m∸n≤m i n in
  let i≤si = n≤1+n i in
  ≤-trans i∸n≤i i≤si 
subtractLess (suc i) (suc k) (suc n) k≤n = subtractLess i k n k≤n

interpTo : Term → List Value → Value → Setⁱ
interpTo M ρ V =
  record { # = λ { k → ⌊ ∃[ i ] interp M ρ (i ∸ k) ≡ just V ⌋ }
         ; down = λ { n (squash (i , Pi)) k k≤n →
                     let i-n≤i-k = subtractLess i k n k≤n in
                     squash (i , interpMono M ρ (i ∸ n) (i ∸ k) V Pi i-n≤i-k)}
         }

{- Here's the logical relation -}

{- This is essentially the theorem we want to prove. -}
pre-ℰ M ρ = ∀ᵒ[ V ] (∃[ i ] interp M ρ i ≡ just V) ᵒ
            →ᵒ (pre-𝒱 V ×ᵒ ((∃[ v ] (⟦ M ⟧ ⟦ ρ ⟧ᴱ v)) ᵒ))
pre-𝒱 (natV n) = ⊤ᵒ
pre-𝒱 (closV N ρ) = ∀ᵒ[ W ] ▷ᵒ 𝒱ᵒ⟦ W ⟧ →ᵒ ▷ᵒ (ℰᵒ⟦ N ⟧ (W ∷ ρ))


{- use fixpointᵒ to get the equations we want for ℰ and 𝒱. -}

ℰ-def : ∀ M ρ → ℰ⟦ M ⟧ ρ ≡ᵒ (∀ᵒ[ V ] (∃[ i ] interp M ρ i ≡ just V) ᵒ
                                →ᵒ (𝒱⟦ V ⟧ ×ᵒ ((∃[ v ] (⟦ M ⟧ ⟦ ρ ⟧ᴱ v)) ᵒ)))
ℰ-def M ρ = 
  ℰ⟦ M ⟧ ρ                               ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-𝒱⊎ℰ (inj₂ (M , ρ))             ⩦⟨ fixpointᵒ pre-𝒱⊎ℰ (inj₂ (M , ρ)) ⟩
  letᵒ (μᵒ pre-𝒱⊎ℰ) (pre-𝒱⊎ℰ (inj₂ (M , ρ))) 
      ⩦⟨ cong-∀ᵒ (λ V → cong-→ᵒ (≡ᵒ-refl refl)
           (cong-×ᵒ (≡ᵒ-sym (fixpointᵒ pre-𝒱⊎ℰ (inj₁ V)))
                    (≡ᵒ-refl refl))) ⟩
  (∀ᵒ[ V ] (∃[ i ] interp M ρ i ≡ just V) ᵒ
      →ᵒ (𝒱⟦ V ⟧ ×ᵒ ((∃[ v ] (⟦ M ⟧ ⟦ ρ ⟧ᴱ v)) ᵒ)))
  ∎

𝒱-nat : ∀{n} → 𝒱⟦ natV n ⟧ ≡ᵒ ⊤ᵒ
𝒱-nat {n} = fixpointᵒ pre-𝒱⊎ℰ (inj₁ (natV n))

𝒱-fun : ∀{N}{ρ} → 𝒱⟦ closV N ρ ⟧
    ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ W ⟧)) →ᵒ (▷ᵒ (ℰ⟦ N ⟧ (W ∷ ρ)))))
𝒱-fun {N}{ρ} = fixpointᵒ pre-𝒱⊎ℰ (inj₁ (closV N ρ))


𝓖 : List Value → List (Setᵒ [] [])
𝓖 [] = []
𝓖 (V ∷ ρ) = 𝒱⟦ V ⟧ ∷ 𝓖 ρ

interp-var-get : ∀ x ρ i V
  → interp (` x) ρ i ≡ just V
  → get ρ x ≡ just V
interp-var-get x ρ (suc i) V ixV = ixV

lookup-𝓖 : ∀ ρ y V → get ρ y ≡ just V → 𝓖 ρ ⊢ᵒ 𝒱⟦ V ⟧
lookup-𝓖 (V ∷ ρ) zero V refl = Zᵒ
lookup-𝓖 (W ∷ ρ) (suc y) V ρyV = Sᵒ (lookup-𝓖 ρ y V ρyV)

get-⟦ρ⟧ : ∀ {ρ x V}
  → get ρ x ≡ just V
  → get ⟦ ρ ⟧ᴱ x ≡ just ⟦ V ⟧ⱽ
get-⟦ρ⟧ {V ∷ ρ} {zero} refl = refl
get-⟦ρ⟧ {V ∷ ρ} {suc x} ρx = get-⟦ρ⟧{ρ}{x} ρx

exist-⟦⟧ⱽ : ∀ V → ∃[ v ] ⟦ V ⟧ⱽ v
exist-⟦⟧ⱽ (natV n) = (nat n) , refl
exist-⟦⟧ⱽ (closV N ρ) = (func []) , []

interp-app : ∀ {L M : Term}{ρ : List Value}{i : ℕ}{V : Value}
  → interp (L · M) ρ i ≡ just V
  → (∃[ j ] (∃[ N ] ∃[ ρ′ ] interp L ρ j ≡ just (closV N ρ′)
     × (∃[ W ] interp M ρ j ≡ just W
     × interp N (W ∷ ρ′) j ≡ just V)))
interp-app {L} {M} {ρ} {suc i} {V} iLMρV
    with interp L ρ i in iLC | iLMρV
... | nothing | ()
... | just (closV N ρ′) | iLMρV′
    with interp M ρ i in iMW | iLMρV′
... | nothing | ()
... | just W | iNWρV =
    i , N , ρ′ , iLC , W , iMW , iNWρV
    
interp-app-cont : ∀ {L M : Term}{ρ : List Value}{i : ℕ}{V : Value} {P : Prop}
  → interp (L · M) ρ i ≡ just V
  → (∀ j N ρ′ W → interp L ρ j ≡ just (closV N ρ′)
     → interp M ρ j ≡ just W
     → interp N (W ∷ ρ′) j ≡ just V
     → P)
  → P
interp-app-cont{L}{M}{ρ}{i} iLMρV cont
    with interp-app{L}{M}{ρ}{i} iLMρV
... | j , N , ρ′ , iLN , W , iMW , iNWV = cont j N ρ′ W iLN iMW iNWV


get-denot-var : ∀ ρ x V
  → get ρ x ≡ just V
 → ∃[ v ] ⟦ ` x ⟧ ⟦ ρ ⟧ᴱ v
get-denot-var ρ x V ρxV
  rewrite get-⟦ρ⟧{ρ} ρxV = exist-⟦⟧ⱽ V

fundamental : ∀ M ρ → 𝓖 ρ ⊢ᵒ ℰ⟦ M ⟧ ρ
fundamental (` x) ρ =
  substᵒ (≡ᵒ-sym (ℰ-def (` x) ρ)) (Λᵒ[ V ] →ᵒI
    (pureᵒE Zᵒ (λ {(i , ixρV) →
      let ρxV = interp-var-get x ρ i V ixρV in
      (Sᵒ (lookup-𝓖 ρ x V ρxV))
      ,ᵒ pureᵒI (get-denot-var ρ x V ρxV)})))

fundamental (ƛ N) ρ =
  substᵒ (≡ᵒ-sym (ℰ-def (ƛ N) ρ)) (Λᵒ[ V ] →ᵒI 
    (pureᵒE Zᵒ (λ {(suc i , refl) →
     (substᵒ (≡ᵒ-sym 𝒱-fun) (Λᵒ[ W ] →ᵒI
       let IH = →ᵒI-rev (▷→ (monoᵒ (→ᵒI (fundamental N (W ∷ ρ))))) in
       weaken{▷ᵒ 𝒱⟦ W ⟧ ∷ 𝓖 ρ}{ϕ = ▷ᵒ (ℰ⟦ N ⟧ (W ∷ ρ))} IH
       (Zᵒ ,ₚ (drop (drop ⊂-refl)))))
     ,ᵒ
     pureᵒI ((func []) , [])
     })))

fundamental (L · M) ρ =
  let IHL = substᵒ (ℰ-def L ρ) (fundamental L ρ) in
  let IHM = substᵒ (ℰ-def M ρ) (fundamental M ρ) in
  substᵒ (≡ᵒ-sym (ℰ-def (L · M) ρ)) (Λᵒ[ V ] →ᵒI
    (pureᵒE Zᵒ λ {(i , iLMV) →
            interp-app-cont{L}{M}{ρ}{i} iLMV
            (λ j N ρ′ W iLN iMW iNWV →
            let IHM′ = →ᵒE (∀ᵒE IHM W) (pureᵒI (j , iMW)) in
            let IHL′ = →ᵒE (∀ᵒE IHL (closV N ρ′)) (pureᵒI (j , iLN)) in
            let 𝒱⟦W⟧ = proj₁ᵒ IHM′ in
            let 𝒱⟦Nρ′⟧ = proj₁ᵒ IHL′ in
            let ▷ℰN = →ᵒE (∀ᵒE (substᵒ (𝒱-fun {N}{ρ′}) 𝒱⟦Nρ′⟧) W)
                          (monoᵒ 𝒱⟦W⟧) in
            pureᵒE (proj₂ᵒ (Sᵒ IHM′)) λ {(w , ⟦M⟧w) →
            {- Need to think about the ▷ᵒ's -}
            {!!}
            })}))
fundamental `zero ρ = {!!}
fundamental (`suc M) ρ = {!!}
fundamental (case L M N) ρ = {!!}


{---- Failed attempt, but so close. --}

{- The following is reminiscent of backward reduction preserves denotations! -}

val : Value → Val
val (natV n) = nat n
val (closV N ρ) = func []

denot-val : ∀ V → ⟦ V ⟧ⱽ (val V)
denot-val (natV n) = refl
denot-val (closV N ρ) = []

interpDenot : ∀{M ρ i V w}
  → interp M ρ i ≡ just V
  → ⟦ V ⟧ⱽ w
  → ⟦ M ⟧ ⟦ ρ ⟧ᴱ w
interpDenot{` x}{ρ}{suc i}{V} ρxV ⟦V⟧w
    with get-E{ρ = ρ}{x} ⟦V⟧w ρxV
... | D , ⟦ρ⟧x , Dw
    with get ⟦ ρ ⟧ᴱ x | ⟦ρ⟧x
... | nothing | ()
... | just D′ | refl = Dw
interpDenot{ƛ N}{ρ}{suc i} refl ⟦N⟧w = ⟦N⟧w
interpDenot{L · M}{ρ}{suc i}{V}{w} LMv ⟦V⟧w
    with interp L ρ i in Leq | LMv
... | nothing | ()
... | just W | LMv′
    with W | LMv′
... | natV n | ()
... | closV N ρ' | LMv″
    with interp M ρ i in Meq | LMv″
... | nothing | ()
... | just A | NV =
    let ⟦M⟧A = interpDenot{M}{ρ}{i}{w = val A} Meq (denot-val A) in
    {- Need a logical relation for this. -Jeremy -}
    let ⟦N⟧w : ⟦ N ⟧ (ret (val A) ∷ ⟦ ρ' ⟧ᴱ) w
        ⟦N⟧w = {!!} in
    let ⟦L⟧Aw = interpDenot{L}{ρ}{i}{w = func ((val A , w) ∷ [])} Leq (⟦N⟧w ∷ []) in
    (val A , w) ∷ [] , val A , ⟦L⟧Aw , ⟦M⟧A , here refl
    
interpDenot{`zero}{ρ}{suc i} refl ⟦V⟧w = ⟦V⟧w
interpDenot{`suc M}{ρ}{suc i}{V}{w} Mv ⟦V⟧w
    with interp M ρ i in Meq | Mv
... | nothing | ()
... | just W | Mv′
    with W | Mv′
... | closV N ρ' | ()
... | natV n | refl =
    let ⟦M⟧n = interpDenot{M}{ρ}{i} Meq refl in
    n , ⟦M⟧n , ⟦V⟧w
interpDenot{case L M N}{ρ}{suc i} Mv ⟦V⟧w
    with interp L ρ i in Leq | Mv
... | nothing | ()
... | just W | Mv′
    with W | Mv′
... | closV N ρ' | ()
interpDenot{case L M N}{ρ}{suc i} Mv ⟦V⟧w | just W | Mv′
    | natV 0 | Mv″
    with interp M ρ i in Meq | Mv″
... | nothing | ()
... | just V | refl =
      0 , (interpDenot{L}{ρ}{i} Leq refl) , (interpDenot{M}{ρ}{i} Meq ⟦V⟧w)
interpDenot{case L M N}{ρ}{suc i} Mv ⟦V⟧w | just W | Mv′
    | natV (suc n) | Neq =
    suc n , (interpDenot{L}{ρ}{i} Leq refl) , (interpDenot{N}{natV n ∷ ρ}{i} Neq ⟦V⟧w)

{--------- logical relation ---}

{--- Use SIL to define this logical relation! 

𝕍 : ℕ → Value → Set
𝔼 : ℕ → Term → List Value → Set

𝕍 0 V = ⊤
𝕍 (suc i) (natV n) = ⊤
𝕍 (suc i) (closV N ρ) = (∀ V → 𝕍 i V → 𝔼 i N (V ∷ ρ))

𝔼 i M ρ = ∀ V j → j ≤ i
      → interp M ρ j ≡ just V
      → 𝕍 j V × ∃[ v ] ⟦ M ⟧ ⟦ ρ ⟧ᴱ v

𝔾 : ℕ → List Value → Set
𝔾 i [] = ⊤
𝔾 i (V ∷ ρ) = 𝕍 i V × 𝔾 i ρ

get-𝔾 : ∀ {ρ x V i}
  → get ρ x ≡ just V
  → 𝔾 i ρ
  → 𝕍 i V
get-𝔾 {V ∷ ρ} {zero} refl (𝕍iV , 𝔾iρ) = 𝕍iV
get-𝔾 {V ∷ ρ} {suc x} ρx (𝕍iV , 𝔾iρ) = get-𝔾 ρx 𝔾iρ

𝔼mono : ∀ i M ρ → 𝔼 (suc i) M ρ → 𝔼 i M ρ
𝔼mono i M ρ 𝔼Mρ = {!!}

𝕍mono : ∀ i V → 𝕍 (suc i) V → 𝕍 i V
𝕍mono zero V 𝕍iV = ?
𝕍mono (suc i) (natV n) 𝕍iV = ?
𝕍mono (suc i) (closV N ρ) 𝕍iV =
  {!!}

𝔾mono : ∀ i ρ → 𝔾 (suc i) ρ → 𝔾 i ρ
𝔾mono i [] 𝔾ρ = tt
𝔾mono i (V ∷ ρ) (𝕍V , 𝔾ρ) = 𝕍mono i V 𝕍V , 𝔾mono i ρ 𝔾ρ

fundamental : ∀ i M ρ → 𝔾 i ρ → 𝔼 i M ρ
fundamental (suc i) (` x) ρ 𝔾ρ = ?
-- V ρx
--   rewrite get-⟦ρ⟧{ρ}{x} ρx =
--     (get-𝔾 ρx 𝔾ρ) , exist-⟦⟧ⱽ V
fundamental (suc i) (ƛ N) ρ 𝔾ρ V refl =
  (λ W 𝕍iW V′ iN=V′ →
    fundamental i N (W ∷ ρ) (𝕍iW , {!!}) V′ iN=V′)
  , (func []) , []
fundamental (suc i) (L · M) ρ 𝔾ρ V iM=V = {!!}
fundamental (suc i) `zero ρ 𝔾ρ V refl = tt , nat 0 , refl
fundamental (suc i) (`suc M) ρ 𝔾ρ V iM=V = {!!}
fundamental (suc i) (case L M N) ρ 𝔾ρ V iM=V = {!!}


--}
