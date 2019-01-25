
\section{Imports}

\begin{code}
module Closure where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
\end{code}

\section{Syntax}

\begin{code}
infix  4 _⊢_
infix  4 _∋_
infix  5 ⟪_,_⟫
infixr 9 s_

infixr 7 _⇒_

infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_
\end{code}

\section{Types}

\begin{code}
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
\end{code}

\section{Contexts}

\begin{code}
Context : Set
Context = List Type
\end{code}

\section{Variables and the lookup judgment}

\begin{code}
data _∋_ : Context → Type → Set where

  z : ∀ {Γ A}
      ---------
    → A ∷ Γ ∋ A

  s_ : ∀ {Γ A B} 
    → Γ ∋ B
      ---------
    → A ∷ Γ ∋ B
\end{code}

\section{Terms, enviroments, and the typing judgment}

\begin{code}
data _⊢_ : Context → Type → Set 

data Env : Context → Context → Set where
  []  : ∀ {Γ} → Env [] Γ
  _∷_ : ∀ {Γ Δ A} → Γ ⊢ A → Env Δ Γ → Env (A ∷ Δ) Γ

data _⊢_ where

  -- variables

  `_    : ∀ {Γ A}
        → Γ ∋ A
          ---------
        → Γ ⊢ A

  -- functions

  _·_   : ∀ {Γ A B}
        → Γ ⊢ (A ⇒ B)
        → Γ ⊢ A
          ---------------
        → Γ ⊢ B

  -- closures

  ⟪_,_⟫ : ∀ {Γ Δ A B}
        → A ∷ A ⇒ B ∷ Δ ⊢ B
        → Env Δ Γ  -- Γ ⊢ Context→Env Δ 
          ------------
        → Γ ⊢ (A ⇒ B)

  -- naturals

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → `ℕ ∷ Γ ⊢ A
      ----------------
    → Γ ⊢ A
\end{code}

\section {Abbreviating de Bruijn indices}

\begin{code}
lookup : Context → ℕ → Type
lookup (A ∷ Γ) zero     =  A
lookup (_ ∷ Γ) (suc n)  =  lookup Γ n
lookup []      _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {_ ∷ Γ} zero     =  z
count {_ ∷ Γ} (suc n)  =  s (count n)
count {[]}    _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
\end{code}

\section{Renaming}

\begin{code}
Renaming : Context → Context → Set
Renaming Γ Δ = ∀ {C} → Γ ∋ C → Δ ∋ C

Rebasing : Context → Context → Set
Rebasing Γ Δ = ∀ {C} → Γ ⊢ C → Δ ⊢ C

ext  : ∀ {Γ Δ A}
        → Renaming Γ Δ
          -----------------------------------
        → Renaming (A ∷ Γ) (A ∷ Δ)
ext ρ z = z
ext ρ (s x) = s (ρ x)

rename : ∀ {Γ Δ}
        → Renaming Γ Δ
          ---------------------------
        → Rebasing Γ Δ
rename-env : ∀ {Γ Γ′ Δ}
    → Renaming Γ Γ′
    → Env Δ Γ
      -------------
    → Env Δ Γ′
        
rename ρ (` x) = ` ρ x
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ ⟪ N , E ⟫ = ⟪ N , rename-env ρ E ⟫
rename ρ `zero = `zero
rename ρ (`suc N) = `suc rename ρ N
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
-- rename ρ ⟨⟩ = ⟨⟩
-- rename ρ ⟨ M , N ⟩ = ⟨ rename ρ M , rename ρ N ⟩
rename-env ρ [] = []
rename-env ρ (M ∷ E) = rename ρ M ∷ rename-env ρ E

weaken : ∀ {Γ A} → Renaming Γ (A ∷ Γ)
weaken z = s z
weaken (s x) = s (weaken x)
\end{code}

\section{Simultaneous Substitution}

\begin{code}
Substitution : Context → Context → Set
Substitution Γ Δ = ∀ {C} → Γ ∋ C → Δ ⊢ C

exts : ∀ {Γ Δ A}
     → Substitution Γ Δ
       ----------------------------
     → Substitution (A ∷ Γ) (A ∷ Δ)
exts σ z = ` z
exts σ (s x) = rename s_ (σ x)

subst : ∀ {Γ Δ}
     → Substitution Γ Δ
       ----------------
     → Rebasing Γ Δ
subst-env : ∀ {Γ Γ′ Δ}
    → Substitution Γ Γ′
    → Env Δ Γ
      -------------
    → Env Δ Γ′

subst σ (` x) = σ x
subst σ (L · M) = subst σ L · subst σ M
subst σ ⟪ N , E ⟫ = ⟪ N , subst-env σ E ⟫
subst σ `zero = `zero
subst σ (`suc N) = `suc subst σ N
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst-env σ [] = []
subst-env σ (M ∷ E) = subst σ M ∷ subst-env σ E
\end{code}

\section{Single substitution}

\begin{code}
_[_] : ∀ {Γ A B}
  → A ∷ Γ ⊢ B
  → Γ ⊢ A
  ------------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {A ∷ Γ} {Γ} σ N
  where
  σ : ∀ {B} → A ∷ Γ ∋ B → Γ ⊢ B
  σ z      =  V
  σ (s x)  =  ` x
\end{code}

\section{Values}

\begin{code}
infix 4 V-⟪_,_⟫
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-⟪_,_⟫ : ∀ {Γ Δ A B}
    → (N : A ∷ A ⇒ B ∷ Δ ⊢ B)
    → (E : Env Δ Γ)
      ---------------------
    → Value (⟪ N , E ⟫)

  -- naturals

  V-zero : ∀ {Γ} →
      -----------------
      Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
\end{code}

\section{Helper functions for reduction}

\begin{code}
Env→σ : ∀ {Γ Δ}
  → Env Δ Γ
    -----------------
  → Substitution Δ Γ
Env→σ [] ()
Env→σ (M ∷ E) z = M
Env→σ (M ∷ E) (s x) = Env→σ E x

make-σ : ∀ {Γ Δ A B}  -- 
  → Env Δ Γ
  → A ∷ A ⇒ B ∷ Δ ⊢ B
  → Γ ⊢ A
    ------------------------------
  → Substitution (A ∷ A ⇒ B ∷ Δ) Γ
make-σ E F X z = X
make-σ E F X (s z) = ⟪ F , E ⟫
make-σ E F X (s s x) = Env→σ E x
\end{code}

\section{Reduction}

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-⟪⟫ : ∀ {Γ Δ A B} {N : A ∷ A ⇒ B ∷ Δ ⊢ B} {E : Env Δ Γ} {V : Γ ⊢ A}
    → Value ⟪ N , E ⟫
    → Value V
      --------------------
    → ⟪ N , E ⟫ · V —→ subst (make-σ E N V) N

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : `ℕ ∷ Γ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : `ℕ ∷ Γ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : `ℕ ∷ Γ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]
\end{code}

\section{Reflexive and transitive closure}

\begin{code}
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
\end{code}

\section{Progress}

\begin{code}
data Progress {A} (M : [] ⊢ A) : Set where

  step : ∀ {N : [] ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : [] ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (L · M) with progress L
progress (L · M) | step L—→L′ = step (ξ-·₁ L—→L′)
progress (L · M) | done V-L with progress M
progress (L · M) | done V-L | step M—→M′ = step (ξ-·₂ V-L M—→M′)
progress (.(⟪ N , E ⟫) · M) | done V-NE@(V-⟪ N , E ⟫) | done V-M = step (β-⟪⟫ V-NE V-M)
progress ⟪ N , E ⟫ = done V-⟪ N , E ⟫
progress `zero = done V-zero
progress (`suc N) with progress N
progress (`suc N) | step N—→N′ = step (ξ-suc N—→N′)
progress (`suc N) | done V-N = done (V-suc V-N)
progress (case L M N) with progress L
progress (case L M N) | step L—→L′ = step (ξ-case L—→L′)
progress (case .`zero M N) | done V-zero = step β-zero
progress (case .(`suc _) M N) | done (V-suc V-L) = step (β-suc V-L)
\end{code}

\section{Evaluation}

\begin{code}
data Gas : Set where
  gas : ℕ → Gas

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps : ∀ {A} → [] ⊢ A → Set where

  steps : ∀ {A} {L N : [] ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : [] ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
\end{code}

\section{Examples}

\begin{code}
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = ⟪ ⟪ case (# 2) (# 0) (`suc ((# 4) · # 0 · # 1)) , # 0 ∷ # 1 ∷ [] ⟫ , [] ⟫

2+2 : [] ⊢ `ℕ
2+2 = plus · two · two

\end{code}

