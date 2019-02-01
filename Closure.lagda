\chapter{Target Language}

The target language is defined similarly to the source language, except it has closures instead of lambda abstractions.
After the last meeting, I got rid of the tuple in the object language and now environements exist in the meta language only.

\section{Imports}

\begin{code}
module Closure where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])

open import Common
\end{code}

\section{Syntax}

\begin{code}
infix  4 _⊢_

infix  5 ⟪_,_⟫
infixl 7 _·_
infix  8 `suc_
infix  9 `_

infix  9 #_
\end{code}

\section{Terms, enviroments, and the typing judgment}

An `Env Δ Γ` defines the record for the environment Δ for a closure which exists in the context Γ.
The i-th element of `Env Δ Γ` has type `Γ ⊢ A` where A is the i-th type in Δ.

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
        → Env Δ Γ
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
count {_ ∷ Γ} zero     =  Z
count {_ ∷ Γ} (suc n)  =  S (count n)
count {[]}    _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
\end{code}

\section{Renaming}

\begin{code}
ext  : ∀ {Γ Δ A}
        → Renaming Γ Δ
          -----------------------------------
        → Renaming (A ∷ Γ) (A ∷ Δ)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ}
        → Renaming Γ Δ
          ---------------------------
        → Rebasing _⊢_ Γ Δ
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
rename-env ρ [] = []
rename-env ρ (M ∷ E) = rename ρ M ∷ rename-env ρ E

weaken : ∀ {Γ A} → Renaming Γ (A ∷ Γ)
weaken Z = S Z
weaken (S x) = S (weaken x)
\end{code}

\section{Simultaneous Substitution}

\begin{code}
exts : ∀ {Γ Δ A}
     → Substitution _⊢_ Γ Δ
       ----------------------------
     → Substitution _⊢_ (A ∷ Γ) (A ∷ Δ)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
     → Substitution _⊢_ Γ Δ
       ----------------
     → Rebasing _⊢_ Γ Δ
subst-env : ∀ {Γ Γ′ Δ}
    → Substitution _⊢_ Γ Γ′
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

\section{Single and double substitution}

\begin{code}
_[_] : ∀ {Γ A B}
  → A ∷ Γ ⊢ B
  → Γ ⊢ A
  ------------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {A ∷ Γ} {Γ} σ N
  where
  σ : ∀ {B} → A ∷ Γ ∋ B → Γ ⊢ B
  σ Z      =  V
  σ (S x)  =  ` x

_[_][_] : ∀ {Γ A B C}
  → B ∷ A ∷ Γ ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    ---------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {B ∷ A ∷ Γ} {Γ} σ N
  where
  σ : ∀ {C} → B ∷ A ∷ Γ ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x
\end{code}

\section{Values}

\begin{code}
infix 4 V-⟪⟫
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-⟪⟫ : ∀ {Γ Δ A B}
    → {N : A ∷ A ⇒ B ∷ Δ ⊢ B}
    → {E : Env Δ Γ}
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
  → Substitution _⊢_ Δ Γ
Env→σ [] ()
Env→σ (M ∷ E) Z = M
Env→σ (M ∷ E) (S x) = Env→σ E x

make-σ : ∀ {Γ Δ A B} 
  → Env Δ Γ
  → A ∷ A ⇒ B ∷ Δ ⊢ B
  → Γ ⊢ A
    ------------------------------
  → Substitution _⊢_ (A ∷ A ⇒ B ∷ Δ) Γ
make-σ E F X Z = X
make-σ E F X (S Z) = ⟪ F , E ⟫
make-σ E F X (S S x) = Env→σ E x

make-σ′ : ∀ {Γ Δ A B} 
  → Env Δ Γ
    ------------------------------
  → Substitution _⊢_ (A ∷ A ⇒ B ∷ Δ) (A ∷ A ⇒ B ∷ Γ)
make-σ′ E = exts (exts (Env→σ E))
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
progress (L · M) | done V-NE@(V-⟪⟫) | done V-M = step (β-⟪⟫ V-NE V-M)
progress ⟪ N , E ⟫ = done V-⟪⟫
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

