\begin{code}

open import Data.List using (List; []; _∷_)

module LR.Base where

data Type : Set where
  `𝔹    : Type
  _⇒_  : Type → Type → Type

Context : Set
Context = List Type

data Var : Type → Context → Set where
  z  : ∀ {Γ σ} → Var σ (σ ∷ Γ)
  s  : ∀ {Γ σ τ} → Var σ Γ → Var σ (τ ∷ Γ)
\end{code}

%<*kind>
\begin{code}
data Kind : Set where
  `val `trm : Kind
\end{code}
%</kind>

\begin{code}
infix 3 _─Env

record _─Env (Γ : Context) (𝓥 : Type → Context → Set) (Δ : Context) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → 𝓥 σ Δ

open _─Env public

infixl 4 _∙_
infixr 5 _<$>_

ε : ∀ {𝓥 Δ} → ([] ─Env) 𝓥 Δ 
lookup ε ()

_∙_ : ∀ {Γ Δ σ 𝓥} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z = v
lookup (ρ ∙ v) (s x) = lookup ρ x

_<$>_ : ∀ {Γ Δ Θ 𝓥₁ 𝓥₂}
      → (∀ {σ} → 𝓥₁ σ Δ → 𝓥₂ σ Θ) → (Γ ─Env) 𝓥₁ Δ → (Γ ─Env) 𝓥₂ Θ
lookup (f <$> ρ) x = f (lookup ρ x)

Thinning : Context → Context → Set
Thinning Γ Δ = (Γ ─Env) Var Δ
\end{code}
