\begin{code}
module StateOfTheArt.SubContext {A : Set} where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)
\end{code}

%<*sublistsum>
\begin{code}
record SubListSum {Γ Δ Δ₁ : List A} (Δ⊆Γ : Δ ⊆ Γ) (Δ₁⊆Γ : Δ₁ ⊆ Γ) : Set where
  constructor subListSum
  field
    Γ₁     : List A
    Γ₁⊆Γ   : Γ₁ ⊆ Γ
    Δ⊆Γ₁   : Δ ⊆ Γ₁
    Δ₁⊆Γ₁  : Δ₁ ⊆ Γ₁
    well   : ⊆-trans Δ⊆Γ₁  Γ₁⊆Γ ≡ Δ⊆Γ
    well₁  : ⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ ≡ Δ₁⊆Γ
\end{code}
%</sublistsum>

%<*merge>
\begin{code}
merge : ∀ {Γ Δ Δ₁} → (Δ⊆Γ : Δ ⊆ Γ) → (Δ₁⊆Γ : Δ₁ ⊆ Γ) → SubListSum Δ⊆Γ Δ₁⊆Γ
\end{code}
%</merge>

\begin{code}
merge base base = subListSum [] base base ⊆-refl refl refl
merge (skip Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (skip Δ⊆Γ) (skip Δ₁⊆Γ) | subListSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subListSum Γ₁ (skip Γ₁⊆Γ) Δ⊆Γ₁ Δ₁⊆Γ₁ (cong skip well) (cong skip well₁)
merge (keep Δ⊆Γ) (skip Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (keep {x = x} Δ⊆Γ) (skip Δ₁⊆Γ) | subListSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subListSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (skip Δ₁⊆Γ₁) (cong keep well) (cong skip well₁)
merge (skip Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (skip Δ⊆Γ) (keep {x = x} Δ₁⊆Γ) | subListSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subListSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (skip Δ⊆Γ₁) (keep Δ₁⊆Γ₁) (cong skip well) (cong keep well₁)
merge (keep {x = x} Δ⊆Γ) (keep Δ₁⊆Γ) with merge Δ⊆Γ Δ₁⊆Γ
merge (keep {x} Δ⊆Γ) (keep Δ₁⊆Γ) | subListSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ well well₁
  = subListSum (x ∷ Γ₁) (keep Γ₁⊆Γ) (keep Δ⊆Γ₁) (keep Δ₁⊆Γ₁) (cong keep well) (cong keep well₁)
\end{code}
