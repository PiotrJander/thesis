\chapter{Merging subcontexts}

\begin{code}
module StateOfTheArt.SubContext where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)

open import StateOfTheArt.Types
\end{code}

\section{Sum of subcontexts}

A sum of two subcontexts Δ and Δ₁ contained in Γ is a context Γ₁ which contains Δ and Δ₁ and is contained in Γ.

\begin{code}
record SubContextSum {Γ Δ Δ₁ : Context} (Δ⊆Γ : Δ ⊆ Γ) (Δ₁⊆Γ : Δ₁ ⊆ Γ) : Set where
  constructor subContextSum
  field
    Γ₁     : Context
    Γ₁⊆Γ   : Γ₁ ⊆ Γ
    Δ⊆Γ₁   : Δ ⊆ Γ₁
    Δ₁⊆Γ₁  : Δ₁ ⊆ Γ₁
    well   : ⊆-trans Δ⊆Γ₁  Γ₁⊆Γ ≡ Δ⊆Γ
    well₁  : ⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ ≡ Δ₁⊆Γ
\end{code}

The `merge` function computes the sum of two subcontexts.

\begin{code}

merge : ∀ {Γ Δ Δ₁} → (Δ⊆Γ : Δ ⊆ Γ) → (Δ₁⊆Γ : Δ₁ ⊆ Γ) → SubContextSum Δ⊆Γ Δ₁⊆Γ
merge base base = subContextSum [] base base ⊆-refl refl refl
merge (skip Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (skip Δ⊆Γ) (skip Δ₁⊆Γ) | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subContextSum Γ₁ (skip Γ₁⊆Γ) Δ⊆Γ₁ Δ₁⊆Γ₁ (cong skip well) (cong skip well₁)
merge (keep Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (keep {x = x} Δ⊆Γ) (skip Δ₁⊆Γ) | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subContextSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (skip Δ₁⊆Γ₁) (cong keep well) (cong skip well₁)
merge (skip Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (skip Δ⊆Γ) (keep {x = x} Δ₁⊆Γ) | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subContextSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (skip Δ⊆Γ₁) (keep Δ₁⊆Γ₁) (cong skip well) (cong keep well₁)
merge (keep {x = x} Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (keep {x} Δ⊆Γ) (keep Δ₁⊆Γ) | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subContextSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (keep Δ₁⊆Γ₁) (cong keep well) (cong keep well₁)

\end{code}
