\section{Types}

\begin{code}
open import Data.List using (List; _∷_)

infixr 7 _⇒_
infix  4 _∋_
infix  9 S_

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
\end{code}

\section{Contexts}

Rather than define the context from scratch like in PLFA, I use lists so that I do not have to define the su-blist (or sub-context) relation from scratch.

\begin{code}
Context : Set
Context = List Type
\end{code}

\section{Variables and the lookup judgment}

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
