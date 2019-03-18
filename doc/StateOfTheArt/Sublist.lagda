\begin{code}
module StateOfTheArt.Sublist {A : Set} where

open import Data.List.Base using (List; []; _∷_; [_])

infix 3 _⊆_
\end{code}

%<*sublist>
\begin{code}
data _⊆_ : List A → List A → Set where
  base  : [] ⊆ []
  skip  : ∀ {xs y ys}  → xs ⊆ ys  → xs ⊆ (y ∷ ys)
  keep  : ∀ {x xs ys}  → xs ⊆ ys  → (x ∷ xs) ⊆ (x ∷ ys)
\end{code}
%</sublist>
