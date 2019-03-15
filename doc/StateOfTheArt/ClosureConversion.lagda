\chapter{Conversion}

\section{Imports}

\begin{code}
module StateOfTheArt.ClosureConversion where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)

open import var
open import environment

open import StateOfTheArt.Types
import StateOfTheArt.STLC as S
open S using (_/_)
import StateOfTheArt.Closure as T
open import StateOfTheArt.SubContext
\end{code}

\section{Existential types for environments}

It is a well-known property of typed closure conversion that environments have existential types.
This implementation has the prperty that as it transforms the source term bottom-up, it maintains a minimal context,
which is the Δ field on the dependent record.

\begin{code}
record _⊩_ (Γ : Context) (A : Type) : Set where
  constructor ∃[_]_∧_
  field
    Δ : Context
    Δ⊆Γ : Δ ⊆ Γ
    N : T.Lam A Δ

Closure : Type → Context → Set
Closure A Γ = Γ ⊩ A
\end{code}

\section{Helper functions for closure conversion}

\begin{code}
Var→⊆ : ∀ {Γ} {A : Type} → Var A Γ → A ∷ [] ⊆ Γ
Var→⊆ {_ ∷ Γ} z = keep ([]⊆ Γ)
Var→⊆ (s x) = skip (Var→⊆ x)

record AdjustContext {A Γ Δ} (Δ⊆A∷Γ : Δ ⊆ A ∷ Γ) : Set where
  constructor adjust
  field
    Δ₁ : Context
    Δ₁⊆Γ : Δ₁ ⊆ Γ
    Δ⊆AΔ₁ : Δ ⊆ A ∷ Δ₁

adjust-context : ∀ {Γ Δ A} → (Δ⊆A∷Γ : Δ ⊆ A ∷ Γ) → AdjustContext Δ⊆A∷Γ
adjust-context (skip {xs = Δ₁} Δ⊆Γ) = adjust Δ₁ Δ⊆Γ (skip ⊆-refl)
adjust-context (keep {xs = Δ₁} Δ⊆Γ) = adjust Δ₁ Δ⊆Γ (keep ⊆-refl)
\end{code}

\section{Closure conversion}

This formulation of closure conversion is in its essence a simple mapping between syntactic counterparts in the source and target language.
The main source of compilcation is the need to merge minimal contexts.

The case of the lambda abstraction is most interesting. A recursive call on the body produces a minimal context which describes the minimal environment.

\begin{code}

⊆→ρ : {Γ Δ : Context} → Γ ⊆ Δ → Thinning Γ Δ
lookup (⊆→ρ base) ()
lookup (⊆→ρ (skip Γ⊆Δ)) x = s (lookup (⊆→ρ Γ⊆Δ) x)
lookup (⊆→ρ (keep Γ⊆Δ)) z = z
lookup (⊆→ρ (keep Γ⊆Δ)) (s x) = s (lookup (⊆→ρ Γ⊆Δ) x)

cc : ∀ {Γ A} → S.Lam A Γ → Closure A Γ
cc {A = A} (S.V x) = ∃[ A ∷ [] ] Var→⊆ x ∧ T.V z
cc (S.A M N) with cc M | cc N
cc (S.A M N) | ∃[ Δ ] Δ⊆Γ ∧ M† | ∃[ Δ₁ ] Δ₁⊆Γ ∧ N† with merge Δ⊆Γ Δ₁⊆Γ
cc (S.A M N) | ∃[ Δ ] Δ⊆Γ ∧ M† | ∃[ Δ₁ ] Δ₁⊆Γ ∧ N† | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.A (T.rename (⊆→ρ Δ⊆Γ₁) M†) (T.rename (⊆→ρ Δ₁⊆Γ₁) N†))
cc (S.L N) with cc N
cc (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N† with adjust-context Δ⊆Γ
cc (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N† | adjust Δ₁ Δ₁⊆Γ Δ⊆AΔ₁
  = ∃[ Δ₁ ] Δ₁⊆Γ ∧ (T.L (T.rename (⊆→ρ Δ⊆AΔ₁) N†) T.id-subst)

_† : ∀ {Γ A} → S.Lam A Γ → T.Lam A Γ
_† M with cc M
_† M | ∃[ Δ ] Δ⊆Γ ∧ N = T.rename (⊆→ρ Δ⊆Γ) N

\end{code}
