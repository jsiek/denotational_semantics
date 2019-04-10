\begin{code}
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where

  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)

data CBN-Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M —→ N
      ----------
    → CBN-Progress M

  done :
      WHNF M
      ----------
    → CBN-Progress M

data ↦⊑ : Value → Set where
  _↦_ : ∀ {v v' : Value}
      → ↦⊑ (v ↦ v')
  ⊔L : ∀ {v v' : Value}
      → ↦⊑ v → ↦⊑ (v ⊔ v')
  ⊔R : ∀ {v v' : Value}
      → ↦⊑ v' → ↦⊑ (v ⊔ v')

sub-↦⊑ : ∀{v v' : Value} → ↦⊑ v → v ⊑ v' → ↦⊑ v'
sub-↦⊑ () Bot⊑
sub-↦⊑ (⊔L d) (ConjL⊑ lt lt₁) = sub-↦⊑ d lt
sub-↦⊑ (⊔R d) (ConjL⊑ lt lt₁) = sub-↦⊑ d lt₁
sub-↦⊑ _↦_ (ConjR1⊑ lt) = ⊔L (sub-↦⊑ _↦_ lt)
sub-↦⊑ (⊔L d) (ConjR1⊑ lt) = ⊔L (sub-↦⊑ (⊔L d) lt)
sub-↦⊑ (⊔R d) (ConjR1⊑ lt) = ⊔L (sub-↦⊑ (⊔R d) lt)
sub-↦⊑ _↦_ (ConjR2⊑ lt) = ⊔R (sub-↦⊑ _↦_ lt)
sub-↦⊑ (⊔L d) (ConjR2⊑ lt) = ⊔R (sub-↦⊑ (⊔L d) lt)
sub-↦⊑ (⊔R d) (ConjR2⊑ lt) = ⊔R (sub-↦⊑ (⊔R d) lt)
sub-↦⊑ d (Trans⊑ lt lt₁) = sub-↦⊑ (sub-↦⊑ d lt) lt₁
sub-↦⊑ d (Fun⊑ lt lt₁) = _↦_
sub-↦⊑ d Dist⊑ = ⊔L _↦_


cbn-progress : ∀{γ : Env ∅}{M : ∅ ⊢ ★ }{v}
             → γ ⊢ M ↓ v  →  ↦⊑ v  →  CBN-Progress M
cbn-progress (var {x = ()}) fun
cbn-progress (↦-elim d₁ d₂) fun
    with cbn-progress d₁ _↦_
... | step (ξ₁ ap r) = step (ξ₁ ap (ξ₁ ap r))
... | step (ξ₂ neu r) = step (ξ₁ ap (ξ₂ neu r))
... | step β = step (ξ₁ ap β)
... | step (ζ r) = step β
... | done (ƛ_) = step β
cbn-progress (↦-intro d) fun = done ƛ_
cbn-progress ⊥-intro ()
cbn-progress (⊔-intro d₁ d₂) (⊔L fun) = cbn-progress d₁ fun
cbn-progress (⊔-intro d₁ d₂) (⊔R fun) = cbn-progress d₂ fun
cbn-progress (sub d lt) fun = cbn-progress d (sub-↦⊑ fun lt)
\end{code}

## Evaluation (call-by-name)

\begin{code}
data WHNF-Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       WHNF N
       ----------
     → WHNF-Finished N

   out-of-gas :
       ----------
       WHNF-Finished N
\end{code}

\begin{code}
data CBN-Steps : ∀ {Γ A} → Γ ⊢ A → Set where

  steps : ∀ {Γ A} {L N : Γ ⊢ A}
    → L —↠ N
    → WHNF-Finished N
      ----------
    → CBN-Steps L
\end{code}

\begin{code}
call-by-name : ∀ {γ : Env ∅}{v}
  → Gas
  → (L : ∅ ⊢ ★) → (γ ⊢ L ↓ v) → (↦⊑ v)
    ----------------------------------
  → CBN-Steps L
call-by-name (gas zero)    L d lt        =  steps (L ∎) out-of-gas
call-by-name (gas (suc m)) L d lt with cbn-progress d lt
... | done NrmL                          =  steps (L ∎) (done NrmL)
... | step {M} L—→M with call-by-name (gas m) M (preserve d L—→M) lt
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
\end{code}



## Terminating

\begin{code}
data Deep-↦⊑ : Value → Set where
  _↦_ : ∀ {v v' : Value}
      → Deep-↦⊑ v'
      → Deep-↦⊑ (v ↦ v')
  ⊔L : ∀ {v v' : Value}
      → Deep-↦⊑ v → Deep-↦⊑ (v ⊔ v')
  ⊔R : ∀ {v v' : Value}
      → Deep-↦⊑ v' → Deep-↦⊑ (v ⊔ v')

sub-Deep-↦⊑ : ∀{v v' : Value} → Deep-↦⊑ v → v ⊑ v' → Deep-↦⊑ v'
sub-Deep-↦⊑ () Bot⊑
sub-Deep-↦⊑ (⊔L d) (ConjL⊑ lt lt₁) = sub-Deep-↦⊑ d lt
sub-Deep-↦⊑ (⊔R d) (ConjL⊑ lt lt₁) = sub-Deep-↦⊑ d lt₁
sub-Deep-↦⊑ (_↦_ d) (ConjR1⊑ lt) = ⊔L (sub-Deep-↦⊑ (_↦_ d) lt)
sub-Deep-↦⊑ (⊔L d) (ConjR1⊑ lt) = ⊔L (sub-Deep-↦⊑ (⊔L d) lt)
sub-Deep-↦⊑ (⊔R d) (ConjR1⊑ lt) = ⊔L (sub-Deep-↦⊑ (⊔R d) lt)
sub-Deep-↦⊑ (_↦_ d) (ConjR2⊑ lt) = ⊔R (sub-Deep-↦⊑ (_↦_ d) lt)
sub-Deep-↦⊑ (⊔L d) (ConjR2⊑ lt) = ⊔R (sub-Deep-↦⊑ (⊔L d) lt)
sub-Deep-↦⊑ (⊔R d) (ConjR2⊑ lt) = ⊔R (sub-Deep-↦⊑ (⊔R d) lt)
sub-Deep-↦⊑ d (Trans⊑ lt lt₁) = sub-Deep-↦⊑ (sub-Deep-↦⊑ d lt) lt₁
sub-Deep-↦⊑ (_↦_ d) (Fun⊑ lt lt₁) = _↦_ (sub-Deep-↦⊑ d lt₁)
sub-Deep-↦⊑ (_↦_ (⊔L d)) Dist⊑ = ⊔L (_↦_ d)
sub-Deep-↦⊑ (_↦_ (⊔R d)) Dist⊑ = ⊔R (_↦_ d)
\end{code}

\begin{code}
data Terminates {Γ A} (M : Γ ⊢ A) : Set where

  fini : ∀ {N : Γ ⊢ A}
    → M —↠ N → WHNF N
      ---------------
    → Terminates M
\end{code}
