\begin{code}
module agda where
\end{code}

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>

%<*vec>
\begin{code}
data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_  : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
%</vec>

%<*le>
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  base     : zero ≤ zero
  step-r   : ∀ {m n} → m ≤ n → m ≤ suc n
  step-lr  : ∀ {m n} → m ≤ n → suc m ≤ suc n
\end{code}
%</le>

%<*ex-proof>
\begin{code}
n≤sn : (n : ℕ) → n ≤ suc n
n≤sn zero     = step-r base
n≤sn (suc n)  = step-lr (n≤sn n)
\end{code}
%</ex-proof>
