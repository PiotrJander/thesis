\begin{code}
--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

module StateOfTheArt.STLC where

-- open import indexed
-- open import var hiding (_<$>_ ; get)
-- open import environment as E hiding (_>>_ ; extend)
open import StateOfTheArt.Types

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

--------------------------------------------------------------------------------
-- Well scoped-and-typed Simply-Typed Lambda Calculus
\end{code}

%<*terms>
\begin{code}
data Lam : Type → Context → Set where
  V  : ∀ {Γ σ}    → Var σ Γ        → Lam σ Γ
  A  : ∀ {Γ σ τ}  → Lam (σ ⇒ τ) Γ  → Lam σ Γ  → Lam τ Γ
  L  : ∀ {Γ σ τ}  → Lam τ (σ ∷ Γ)  → Lam (σ ⇒ τ) Γ
\end{code}
%</terms>

\section{Renaming}

%<*rename>
\begin{code}
ext : ∀ {Γ Δ} {σ : Type} → Thinning Γ Δ → Thinning (σ ∷ Γ) (σ ∷ Δ) 
ext ρ = s <$> ρ ∙ z

rename : ∀ {Γ Δ σ} → Thinning Γ Δ → Lam σ Γ → Lam σ Δ
rename ρ (V x)          =  V (lookup ρ x)
rename ρ (L N)          =  L (rename (ext ρ) N)
rename ρ (A M N)        =  A (rename ρ M) (rename ρ N)
\end{code}
%</rename>

\section{Simultaneous substitution}

\begin{code}
Subst : Context → Context → Set
Subst Γ Δ = (Γ ─Env) Lam Δ
\end{code}

%<*subst>
\begin{code}
exts : ∀ {Γ Δ} {τ : Type} → (Γ ─Env) Lam Δ → ((τ ∷ Γ) ─Env) Lam (τ ∷ Δ) 
exts σ = rename (pack s) <$> σ ∙ V z

subst : ∀ {Γ Δ σ} → (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
subst σ (V x)          =  lookup σ x
subst σ (L N)          =  L (subst (exts σ) N)
subst σ (A M N)        =  A (subst σ M) (subst σ N)
\end{code}
%</subst>

--------------------
-- Identity substitution

%<*id-subst>
\begin{code}
id-subst : ∀ {Γ} → (Γ ─Env) Lam Γ
lookup id-subst x = V x
\end{code}
%</id-subst>

--------------------------
-- Single substitution

%<*single-subst>
\begin{code}
_/_ : ∀ {Γ σ τ} → Lam τ (σ ∷ Γ) → Lam σ Γ → Lam τ Γ
_/_ {σ} {_} {Γ} N M = subst (id-subst ∙ M) N
\end{code}
%</single-subst>

-------
-- Values

%<*values>
\begin{code}
data Value : ∀ {Γ σ} → Lam σ Γ → Set where

  V-L : ∀ {Γ σ τ} {N : Lam τ (σ ∷ Γ)}
      ---------------------------
    → Value (L N)
\end{code}
%</values>

-----------
-- Reductions

\begin{code}
infix 2 _—→_
\end{code}

%<*reductions>
\begin{code}
data _—→_ : ∀ {Γ σ} → (Lam σ Γ) → (Lam σ Γ) → Set where

  ξ-A₁ : ∀ {Γ σ τ} {M M′ : Lam (σ ⇒ τ) Γ} {N : Lam σ Γ}
    → M —→ M′
      ---------------
    → A M N —→ A M′ N

  ξ-A₂ : ∀ {Γ σ τ} {V : Lam (σ ⇒ τ) Γ} {N N′ : Lam σ Γ}
    → Value V
    → N —→ N′
      ---------------
    → A V N —→ A V N′

  β-L : ∀ {Γ σ τ} {N : Lam τ (σ ∷ Γ)} {V : Lam σ Γ}
    → Value V
      --------------------
    → A (L N) V —→ N / V
\end{code}
%</reductions>
