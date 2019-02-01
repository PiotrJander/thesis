\chapter{Conversion}

\section{Imports}

\begin{code}
module Conversion where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)

import PCF as S
import Closure as T
open S using (ƛ_)
open T using (⟪_,_⟫ ; Env)
open import Type
open import SubContext
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
    N : Δ T.⊢ A

Closure : Type → Context → Set
Closure A Γ = Γ ⊩ A
\end{code}

\section{Helper functions for closure conversion}

\begin{code}
Var→⊆ : ∀ {Γ A} → Γ ∋ A → A ∷ [] ⊆ Γ
Var→⊆ {_ ∷ Γ} Z = keep ([]⊆ Γ)
Var→⊆ (S x) = skip (Var→⊆ x)

record AdjustContext {A B Γ Δ} (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) : Set where
  constructor adjust
  field
    Δ₁ : Context
    Δ₁⊆Γ : Δ₁ ⊆ Γ
    Δ⊆ABΔ₁ : Δ ⊆ A ∷ B ∷ Δ₁

adjust-context : ∀ {Γ Δ A B} → (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) → AdjustContext Δ⊆ABΓ
adjust-context (skip (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (skip ⊆-refl))
adjust-context (skip (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (keep ⊆-refl))
adjust-context (keep (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (skip ⊆-refl))
adjust-context (keep (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (keep ⊆-refl))

make-env : (Δ : Context) → Env Δ Δ
make-env [] = T.[]
make-env (A ∷ Δ) =  (T.` Z) T.∷ T.rename-env T.weaken (make-env Δ)
\end{code}

\section{Closure conversion}

This formulation of closure conversion is in its essence a simple mapping between syntactic counterparts in the source and target language.
The main source of compilcation is the need to merge minimal contexts.

The case of the lambda abstraction is most interesting. A recursive call on the body produces a minimal context which describes the minimal environment.

\begin{code}
cc : ∀ {Γ A} → Γ S.⊢ A → Closure A Γ
cc {A = A} (S.` x) = ∃[ A ∷ [] ] Var→⊆ x ∧ (T.` Z)
cc (S.ƛ N) with cc N
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ with adjust-context Δ⊆Γ
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ | adjust Δ₁ Δ₁⊆Γ Δ⊆ABΔ₁ = ∃[ Δ₁ ] Δ₁⊆Γ ∧ ⟪ T.rename (⊆→ρ Δ⊆ABΔ₁) N₁ , make-env Δ₁ ⟫
cc (L S.· M) with cc L | cc M
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ with merge Δ⊆Γ Δ₁⊆Γ
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.rename (⊆→ρ Δ⊆Γ₁) L′ T.· T.rename (⊆→ρ Δ₁⊆Γ₁) M′)
cc {Γ} S.`zero = ∃[ [] ] []⊆ Γ ∧ T.`zero
cc (S.`suc N) with cc N
cc (S.`suc N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ = ∃[ Δ ] Δ⊆Γ ∧ (T.`suc N₁)
cc (S.case L M N) with cc L | cc M | cc N
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (skip Δ₂⊆Γ₁)) N′))
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (keep Δ₂⊆Γ₁)) N′))

cc-keep-Γ : ∀ {Γ A} → Γ S.⊢ A → Γ T.⊢ A
cc-keep-Γ M with cc M
cc-keep-Γ M | ∃[ Δ ] Δ⊆Γ ∧ N = T.rename (⊆→ρ Δ⊆Γ) N

\end{code}
