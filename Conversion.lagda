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

open import Isomorphism using (extensionality ; _≃_ ; make)
open _≃_
import PCF as S
import Closure as T
open S using (_,_ ; ∅ ; Z ; S_)
open T using (z ; s_ ; ⟪_,_⟫)
open import SubContext
\end{code}

\section{Type preservation}

The transformation preserves types up to the `to Type-iso` relation.

\begin{code}
module TypeIso where

  to' : S.Type → T.Type
  to' S.`ℕ = T.`ℕ
  to' (A S.⇒ B) = to' A T.⇒ to' B
  
  from' : T.Type → S.Type
  from' T.`ℕ = S.`ℕ
  from' (A T.⇒ B) = from' A S.⇒ from' B

  from∘to' : (A : S.Type) → from' (to' A) ≡ A
  from∘to' (S.`ℕ) = refl
  from∘to' (A S.⇒ B) rewrite from∘to' A | from∘to' B = refl

  to∘from' : (A : T.Type) → to' (from' A) ≡ A
  to∘from' (T.`ℕ) = refl
  to∘from' (A T.⇒ B) rewrite to∘from' A | to∘from' B = refl

  Type-iso : S.Type ≃ T.Type
  Type-iso = record { to = to' ; from = from' ; from∘to = from∘to' ; to∘from = to∘from' }
open TypeIso using (Type-iso) public
open TypeIso renaming (to' to t-to ; from' to t-from ; from∘to' to t-from∘to ; to∘from' to t-to∘from) public

module ContextIso where

  to' : S.Context → T.Context
  to' ∅ = []
  to' (Γ , A) = to Type-iso A ∷ to' Γ
  
  from' : List T.Type → S.Context
  from' [] = ∅
  from' (A ∷ Γ) = from' Γ , from Type-iso A

  from∘to' : (Γ : S.Context) → from' (to' Γ) ≡ Γ
  from∘to' (∅) = refl
  from∘to' (Γ , A) rewrite from∘to' Γ | from∘to Type-iso A = refl

  to∘from' : (Γ : T.Context) → to' (from' Γ) ≡ Γ
  to∘from' ([]) = refl
  to∘from' (A ∷ Γ) rewrite to∘from' Γ | to∘from Type-iso A = refl

  Context-iso : S.Context ≃ T.Context
  Context-iso = make to' from' from∘to' to∘from'
open ContextIso using (Context-iso) public
open ContextIso renaming (to' to c-to ; from' to c-from ; from∘to' to c-from∘to ; to∘from' to c-to∘from) public

\end{code}

\section{Existential types for environments}

It is a well-known property of typed closure conversion that environments have existential types.
This implementation has the prperty that as it transforms the source term bottom-up, it maintains a minimal context,
which is the Δ field on the dependent record.

\begin{code}
record _⊩_ (Γ : T.Context) (A : T.Type) : Set where
  constructor ∃[_]_∧_
  field
    Δ : T.Context
    Δ⊆Γ : Δ ⊆ Γ
    N : Δ T.⊢ A

Closure : S.Type → S.Context → Set
Closure A Γ = to Context-iso Γ ⊩ to Type-iso A
\end{code}

\section{Helper functions for closure conversion}

\begin{code}
Var→⊆ : ∀ {Γ A} → Γ S.∋ A → to Type-iso A ∷ [] ⊆ to Context-iso Γ
Var→⊆ {Γ , _} Z = keep ([]⊆ to Context-iso Γ)
Var→⊆ (S x) = skip (Var→⊆ x)

record AdjustContext {A B Γ Δ} (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) : Set where
  constructor adjust
  field
    Δ₁ : T.Context
    Δ₁⊆Γ : Δ₁ ⊆ Γ
    Δ⊆ABΔ₁ : Δ ⊆ A ∷ B ∷ Δ₁

adjust-context : ∀ {Γ Δ A B} → (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) → AdjustContext Δ⊆ABΓ
adjust-context (skip (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (skip ⊆-refl))
adjust-context (skip (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (keep ⊆-refl))
adjust-context (keep (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (skip ⊆-refl))
adjust-context (keep (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (keep ⊆-refl))

make-env : (Δ : T.Context) → T.Env Δ Δ
make-env [] = T.[]
make-env (A ∷ Δ) =  (T.` z) T.∷ T.rename-env T.weaken (make-env Δ)
\end{code}

\section{Closure conversion}

This formulation of closure conversion is in its essence a simple mapping between syntactic counterparts in the source and target language.
The main source of compilcation is the need to merge minimal contexts.

The case of the lambda abstraction is most interesting. A recursive call on the body produces a minimal context which describes the minimal environment.

\begin{code}
cc : ∀ {Γ A} → Γ S.⊢ A → Closure A Γ
cc {A = A} (S.` x) = ∃[ to Type-iso A ∷ [] ] Var→⊆ x ∧ (T.` z)
cc (S.ƛ N) with cc N
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ with adjust-context Δ⊆Γ
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ | adjust Δ₁ Δ₁⊆Γ Δ⊆ABΔ₁ = ∃[ Δ₁ ] Δ₁⊆Γ ∧ ⟪ T.rename (⊆→ρ Δ⊆ABΔ₁) N₁ , make-env Δ₁ ⟫
cc (L S.· M) with cc L | cc M
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ with merge Δ⊆Γ Δ₁⊆Γ
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.rename (⊆→ρ Δ⊆Γ₁) L′ T.· T.rename (⊆→ρ Δ₁⊆Γ₁) M′)
cc {Γ} S.`zero = ∃[ [] ] []⊆ to Context-iso Γ ∧ T.`zero
cc (S.`suc N) with cc N
cc (S.`suc N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ = ∃[ Δ ] Δ⊆Γ ∧ (T.`suc N₁)
cc (S.case L M N) with cc L | cc M | cc N
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (skip Δ₂⊆Γ₁)) N′))
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(T.`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(T.`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (keep Δ₂⊆Γ₁)) N′))

\end{code}
