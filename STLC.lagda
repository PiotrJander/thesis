\chapter{Source Language}

The source language closely follows PCF formulation from PLFA. The only difference is that rather than having distinct lambda abstraction and fixpoint operator,
the lambda abstraction makes a variable containing itself available to its body, thus enabling recursion and subsuming the role of the fixpoint operator.
This was done to facilitate closure conversion, but I would be interested in seeing how the fixpoint operator could be closure converted.

\section{Imports}

\begin{code}
module STLC where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using ([] ; _∷_)

open import Common
\end{code}

\section{Syntax}

\begin{code}
infix  4 _⊢_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_

infix  9 #_

\end{code}

\section{Terms and the typing judgment}

\begin{code}
data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → A ∷ Γ ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

\end{code}

\section {Abbreviating de Bruijn indices}

\begin{code}
lookup : Context → ℕ → Type  --
lookup (A ∷ Γ) zero     =  A
lookup (_ ∷ Γ) (suc n)  =  lookup Γ n
lookup []       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {_ ∷ Γ} zero     =  Z
count {_ ∷ Γ} (suc n)  =  S (count n)
count {[]}     _        =  ⊥-elim impossible
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
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
        → Renaming Γ Δ
          ---------------------------
        → Rebasing _⊢_ Γ Δ
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ rename (ext ρ) N
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
\end{code}

\section{Simultaneous substitution}

\begin{code}
exts : ∀ {Γ Δ A}
     → Substitution _⊢_ Γ Δ
       ----------------------------
     → Substitution _⊢_ (A ∷ Γ) (A ∷ Δ)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
     → Substitution _⊢_ Γ Δ
       ----------------
     → Rebasing _⊢_ Γ Δ
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
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
\end{code}

\section{Values}

\begin{code}
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : A ∷ Γ ⊢ B}
      ---------------------------
    → Value (ƛ N)

\end{code}

\section{GReduction}

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

  β-ƛ : ∀ {Γ A B} {N : A ∷ Γ ⊢ B} {V : Γ ⊢ A}  -- TODO
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

V¬—→ : ∀ {Γ σ} {M N : Γ ⊢ σ}
     → Value M
       -------------
     → ¬ (M —→ N)
V¬—→ () (ξ-·₁ M—→N)
V¬—→ () (ξ-·₂ x M—→N)
V¬—→ () (β-ƛ V)

det : ∀ {Γ σ} {e e₁ e₂ : Γ ⊢ σ}
    → e —→ e₁
    → e —→ e₂
      ---------
    → e₁ ≡ e₂
det (ξ-·₁ e—→e₁) (ξ-·₁ e—→e₂)      =  cong₂ _·_ (det e—→e₁ e—→e₂) refl
det (ξ-·₁ e—→e₁) (ξ-·₂ V-L e—→e₂)  =  ⊥-elim (V¬—→ V-L e—→e₁)
det (ξ-·₁ e—→e₁) (β-ƛ _)           =  ⊥-elim (V¬—→ V-ƛ e—→e₁)
det (ξ-·₂ V-L e—→e₁) (ξ-·₁ e—→e₂)  =  ⊥-elim (V¬—→ V-L e—→e₂)
det (ξ-·₂ _ e—→e₁) (ξ-·₂ _ e—→e₂)  =  cong₂ _·_ refl (det e—→e₁ e—→e₂)
det (ξ-·₂ _ e—→e₁) (β-ƛ V)         =  ⊥-elim (V¬—→ V e—→e₁)
det (β-ƛ _) (ξ-·₁ e—→e₂)           =  ⊥-elim (V¬—→ V-ƛ e—→e₂)
det (β-ƛ V) (ξ-·₂ _ e—→e₂)         =  ⊥-elim (V¬—→ V e—→e₂)
det (β-ƛ V) (β-ƛ V')               =  refl

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
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
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
