\begin{code}
infixr 3 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type
\end{code}
