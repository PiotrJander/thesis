\section{Types}

\begin{code}
open import Data.List using (List; _∷_)

infixr 7 _⇒_
infix  4 _∋_
infix  9 S_
\end{code}

%<*type>
\begin{code}
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
\end{code}
%</type>

\section{Contexts}

Rather than define the context from scratch like in PLFA, I use lists so that I do not have to define the su-blist (or sub-context) relation from scratch.

%<*context>
\begin{code}
Context : Set
Context = List Type
\end{code}
%</context>

\section{Variables and the lookup judgment}

%<*var>
\begin{code}
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → A ∷ Γ ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → A ∷ Γ ∋ B
\end{code}
%</var>

\section{Type synonims}

\begin{code}
-- Renaming : Context → Context → Set
-- Renaming Γ Δ = ∀ {C} → Γ ∋ C → Δ ∋ C

-- Rebasing : (Context → Type → Set) → Context → Context → Set
-- Rebasing ⊢ Γ Δ = ∀ {C} → ⊢ Γ C → ⊢ Δ C

-- Substitution : (Context → Type → Set) → Context → Context → Set
-- Substitution ⊢ Γ Δ = ∀ {C} → Γ ∋ C → ⊢ Δ C

\end{code}
