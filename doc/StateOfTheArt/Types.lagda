\begin{code}
open import Data.List using (List; _∷_)

module StateOfTheArt.Types where

infixr 3 _⇒_
\end{code}

%<*type>
\begin{code}
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type
\end{code}
%</type>

%<*context>
\begin{code}
Context : Set
Context = List Type
\end{code}
%</context>

\begin{code}
private
\end{code}

%<*var>
\begin{code}
  data Var : Type → Context → Set where
    z  : ∀ {σ Γ}    → Var σ (σ ∷ Γ)
    s  : ∀ {σ τ Γ}  → Var σ Γ  → Var σ (τ ∷ Γ) 
\end{code}
%</var>





