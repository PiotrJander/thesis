\chapter{Merging subcontexts}

\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)

open import Common

⊆→ρ : {Γ Δ : Context} → Γ ⊆ Δ → Renaming Γ Δ
⊆→ρ base ()
⊆→ρ (skip Γ⊆Δ) with ⊆→ρ Γ⊆Δ
... | ρ = λ x → S (ρ x)
⊆→ρ (keep Γ⊆Δ) with ⊆→ρ Γ⊆Δ
... | ρ = λ { Z → Z ; (S v) → S (ρ v) }
\end{code}

\section{Sum of subcontexts}

A sum of two subcontexts Δ and Δ₁ contained in Γ is a context Γ₁ which contains Δ and Δ₁ and is contained in Γ.

\begin{code}
record SubContextSum (Γ Δ Δ₁ : Context) : Set where
  constructor subContextSum
  field
    Γ₁ : Context
    Γ₁⊆Γ : Γ₁ ⊆ Γ
    Δ⊆Γ₁ : Δ ⊆ Γ₁
    Δ₁⊆Γ₁ : Δ₁ ⊆ Γ₁

open SubContextSum
\end{code}

This notion of a sum can be generalised to any number of subcontexts, in particular, to three subcontexts.

\begin{code}
record SubContextSum₃ (Γ Δ Δ₁ Δ₂ : Context) : Set where
  constructor subContextSum
  field
    Γ₁ : Context
    Γ₁⊆Γ : Γ₁ ⊆ Γ
    Δ⊆Γ₁ : Δ ⊆ Γ₁
    Δ₁⊆Γ₁ : Δ₁ ⊆ Γ₁
    Δ₂⊆Γ₁ : Δ₂ ⊆ Γ₁

open SubContextSum₃
\end{code}

The `merge` function computes the sum of two subcontexts.

\begin{code}
merge : ∀ {Γ Δ Δ₁} → Δ ⊆ Γ → Δ₁ ⊆ Γ → SubContextSum Γ Δ Δ₁
merge {[]} {[]} {[]} base base = subContextSum [] base base base
merge {[]} {[]} {σ ∷ Γ} base ()
merge {[]} {σ ∷ Γ} ()
merge {σ ∷ Γ} (skip Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
... | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = subContextSum Γ₁ (skip Γ₁⊆Γ) Δ⊆Γ₁ Δ₁⊆Γ₁
merge {σ ∷ Γ} (skip Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
... | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = subContextSum (σ ∷ Γ₁) (keep Γ₁⊆Γ) (skip Δ⊆Γ₁) (keep Δ₁⊆Γ₁)
merge {σ ∷ Γ} (keep Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
... | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = subContextSum (σ ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (skip Δ₁⊆Γ₁)
merge {σ ∷ Γ} (keep Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
... | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = subContextSum (σ ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (keep Δ₁⊆Γ₁)

merge₃ : ∀ {Γ Δ Δ₁ Δ₂} → Δ ⊆ Γ → Δ₁ ⊆ Γ → Δ₂ ⊆ Γ → SubContextSum₃ Γ Δ Δ₁ Δ₂
merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ with merge Δ⊆Γ Δ₁⊆Γ
merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ with merge Γ₁⊆Γ Δ₂⊆Γ
merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ | subContextSum Γ₂ Γ₂⊆Γ Γ₁⊆Γ₂ Δ₂⊆Γ₂
  = subContextSum Γ₂ Γ₂⊆Γ (⊆-trans Δ⊆Γ₁ Γ₁⊆Γ₂) (⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ₂) Δ₂⊆Γ₂

\end{code}
