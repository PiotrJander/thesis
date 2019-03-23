\begin{code}
--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-} 
module StateOfTheArt.Closure where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open E.≡ᴱ-Reasoning
open import StateOfTheArt.Types

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function
\end{code}

--------------------------------------------------------------------------------
-- Well scoped-and-typed Simply-Typed Lambda Calculus

%<*terms>
\begin{code}
data Lam : Type → Context → Set where
  V  : ∀ {Γ σ}      → Var σ Γ        → Lam σ Γ
  A  : ∀ {Γ σ τ}    → Lam (σ ⇒ τ) Γ  → Lam σ Γ         → Lam τ Γ
  L  : ∀ {Γ Δ σ τ}  → Lam τ (σ ∷ Δ)  → (Δ ─Env) Lam Γ  → Lam (σ ⇒ τ) Γ
\end{code}
%</terms>

%<*syntactic>
\begin{code}
Subst : Context → Context → Set
Subst Γ Δ = (Γ ─Env) Lam Δ

Syntactic : Context → Context → Set
Syntactic Γ Δ = ∀ {σ} → Lam σ Γ → Lam σ Δ
\end{code}
%</syntactic>

\begin{code}
ext : ∀ {Γ Δ} {σ : Type} → Thinning Γ Δ  → Thinning (σ ∷ Γ) (σ ∷ Δ)
ext ρ = s <$> ρ ∙ z
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*rename>
\begin{code}
rename : ∀ {Γ Δ σ} → Thinning Γ Δ → Lam σ Γ → Lam σ Δ
rename ρ (V x)    =  V (lookup ρ x)
rename ρ (A M N)  =  A (rename ρ M) (rename ρ N)
rename ρ (L N E)  =  L N (rename ρ <$> E)
\end{code}
%</rename>

%<*exts>
\begin{code}
exts : ∀ {Γ Δ σ} → Subst Γ Δ → Subst (σ ∷ Γ) (σ ∷ Δ)
exts ρ = rename (pack s) <$> ρ ∙ V z
\end{code}
%</exts>

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*subst>
\begin{code}
subst : ∀ {Γ Δ σ} → Subst Γ Δ → Lam σ Γ → Lam σ Δ
subst ρ (V x)    =  lookup ρ x
subst ρ (A M N)  =  A (subst ρ M) (subst ρ N)
subst ρ (L N E)  =  L N (subst ρ <$> E)
\end{code}
%</subst>

\begin{code}
----------------------------
-- Substitution combinators

s-step : ∀ {Γ Δ τ} → Subst Γ Δ → Subst Γ (τ ∷ Δ)
s-step ρ = rename E.extend <$> ρ
\end{code}

%<*id-subst>
\begin{code}
id-subst : ∀ {Γ} → Subst Γ Γ
lookup id-subst x = V x
\end{code}
%</id-subst>

\begin{code}
-------
-- Values

data Value : ∀ {Γ σ} → Lam σ Γ → Set where

  V-L : ∀ {Γ Δ σ τ} {N : Lam τ (σ ∷ Δ)} {E : Subst Δ Γ}
      ---------------------------
    → Value (L N E)

-----------
-- Reductions
\end{code}

%<*beta>
\begin{code}
infix 2 _—→_
data _—→_ : ∀ {Γ σ} → (Lam σ Γ) → (Lam σ Γ) → Set where

  β-L : ∀ {Γ Δ σ τ} {N : Lam τ (σ ∷ Δ)} {E : Subst Δ Γ} {V : Lam σ Γ}
    → Value V
      --------------------
    → A (L N E) V —→ subst (E ∙ V) N
\end{code}
%</beta>

\begin{code}
  ξ-A₁ : ∀ {Γ σ τ} {M M′ : Lam (σ ⇒ τ) Γ} {N : Lam σ Γ}
    → M —→ M′
      ---------------
    → A M N —→ A M′ N

  ξ-A₂ : ∀ {Γ σ τ} {V : Lam (σ ⇒ τ) Γ} {N N′ : Lam σ Γ}
    → Value V
    → N —→ N′
      ---------------
    → A V N —→ A V N′
\end{code}
