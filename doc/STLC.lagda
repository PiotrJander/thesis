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
open import Function using (id)

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

%<*terms>
\begin{code}
data _⊢_ : Context → Type → Set where
  `_   : ∀ {Γ A}     → Γ ∋ A      → Γ ⊢ A
  ƛ_   : ∀ {Γ A B}   → A ∷ Γ ⊢ B  → Γ ⊢ A ⇒ B
  _·_  : ∀ {Γ A B}   → Γ ⊢ A ⇒ B  → Γ ⊢ A   → Γ ⊢ B
\end{code}
%</terms>

\section {Abbreviating de Bruijn indices}

\begin{code}
look-up : Context → ℕ → Type  --
look-up (A ∷ Γ) zero     =  A
look-up (_ ∷ Γ) (suc n)  =  look-up Γ n
look-up []       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ look-up Γ n
count {_ ∷ Γ} zero     =  Z
count {_ ∷ Γ} (suc n)  =  S (count n)
count {[]}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ look-up Γ n
# n  =  ` count n
\end{code}

\section{Semantics}

\begin{code}

Model : Set₁
Model = Type → Context → Set

Var : Model
Var σ Γ = Γ ∋ σ

Lam : Model
Lam σ Γ = Γ ⊢ σ

infix 4 _─Env
\end{code}

%<*env>
\begin{code}
record _─Env (Γ : Context) (𝓥 : Type → Context → Set) (Δ : Context) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → 𝓥 σ Δ
\end{code}
%</env>

\begin{code}
open _─Env public

infixl 4 _∙_
infixr 5 _<$>_
\end{code}

%<*thinning>
\begin{code}
Thinning : Context → Context → Set
Thinning Γ Δ = (Γ ─Env) Var Δ
\end{code}
%</thinning>

\begin{code}
Substitution : Context → Context → Set
Substitution Γ Δ = (Γ ─Env) Lam Δ
\end{code}

%<*envops>
\begin{code}
ε : ∀ {𝓥 Δ} → ([] ─Env) 𝓥 Δ 
lookup ε ()

_∙_ : ∀ {Γ Δ σ 𝓥} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) Z = v
lookup (ρ ∙ v) (S x) = lookup ρ x

_<$>_ : ∀ {Γ Δ Θ 𝓥₁ 𝓥₂}
      → (∀ {σ} → 𝓥₁ σ Δ → 𝓥₂ σ Θ) → (Γ ─Env) 𝓥₁ Δ → (Γ ─Env) 𝓥₂ Θ
lookup (f <$> ρ) x = f (lookup ρ x)
\end{code}
%</envops>

\begin{code}
extend : ∀ {Γ A} → Thinning Γ (A ∷ Γ)
lookup extend v = S v

-- extend : ∀ {Γ σ} → Thinning Γ (σ ∷ Γ)
-- lookup extend x = S x

record Sem (𝓥 𝓒 : Model) : Set where
  field  th^𝓥  :  ∀ {Γ Δ σ} → Thinning Γ Δ → 𝓥 σ Γ → 𝓥 σ Δ
         ⟦V⟧    :  ∀ {Δ σ} → 𝓥 Δ σ → 𝓒 Δ σ
         ⟦A⟧    :  ∀ {Δ σ τ} → 𝓒 (σ ⇒ τ) Δ → 𝓒 σ Δ → 𝓒 τ Δ
         ⟦L⟧    :  ∀ {Δ} → (σ : Type) → {τ : Type} → (Thinning Δ (σ ∷ Δ) → 𝓥 σ (σ ∷ Δ) → 𝓒 τ (σ ∷ Δ)) → 𝓒 (σ ⇒ τ) Δ  -- can we and should we generalise σ ∷ Δ to Θ ?

  sem : ∀ {Γ Δ σ} → (Γ ─Env) 𝓥 Δ → Γ ⊢ σ → 𝓒 σ Δ
  sem ρ (` x)    =  ⟦V⟧ (lookup ρ x)
  sem ρ (L · M)  =  ⟦A⟧ (sem ρ L) (sem ρ M)
  sem ρ (ƛ_ N)   =  ⟦L⟧ _ (λ γ v → sem (extend' ρ γ v) N)
    where
    extend' : ∀ {Γ Δ Θ σ} → (Γ ─Env) 𝓥 Δ → Thinning Δ Θ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
    extend' ρ γ v = th^𝓥 γ <$> ρ ∙ v

Renaming' : Sem Var Lam
Renaming' = record
  { th^𝓥  =  λ ρ v → lookup ρ v
  ; ⟦V⟧    =  `_
  ; ⟦A⟧    =  _·_
  ; ⟦L⟧    =  λ _ b → ƛ b (pack S_) Z }

ren : ∀ {Γ Δ σ} → Thinning Γ Δ → Γ ⊢ σ → Δ ⊢ σ
ren = Sem.sem Renaming'

Substitution' : Sem Lam Lam
Substitution' = record
  { th^𝓥  =  λ ρ v → Sem.sem Renaming' ρ v 
  ; ⟦V⟧    =  id
  ; ⟦A⟧    =  _·_
  ; ⟦L⟧    =  λ _ b → ƛ (b (pack S_) (` Z)) }

sub : ∀ {Γ Δ σ} → (Γ ─Env) Lam Δ → Γ ⊢ σ → Δ ⊢ σ
sub = Sem.sem Substitution'

Kripke : Model → Model → Context → Type → Type → Set
Kripke 𝓥 𝓒 Δ σ τ = Thinning Δ (σ ∷ Δ) → 𝓥 σ (σ ∷ Δ) → 𝓒 τ (σ ∷ Δ)

Applicative :  Model → Set
Applicative 𝓒 = {Γ : Context} {σ τ : Type} → 𝓒 (σ ⇒ τ) Γ → 𝓒 σ Γ → 𝓒 τ Γ

\end{code}

Now suppose that we could reduce under abstractions.
Then we'd need a proof of SN for all vars in the env.


\section{Renaming}

%<*rename>
\begin{code}
rename : ∀ {Γ Δ A}
        → Thinning Γ Δ
        → Γ ⊢ A
          ---------------------------
        → Δ ⊢ A
rename ρ (` x)          =  ` (lookup ρ x)
rename ρ (ƛ N)          =  ƛ rename (S_ <$> ρ ∙ Z) N
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
\end{code}
%</rename>

\section{Simultaneous substitution}

%<*subst>
\begin{code}
subst : ∀ {Γ Δ A}
     → Substitution Γ Δ
     → Γ ⊢ A
       ----------------
     → Δ ⊢ A
subst σ (` v)          =  lookup σ v
subst σ (ƛ N)          =  ƛ (subst (rename extend <$> σ ∙ ` Z) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
\end{code}
%</subst>

-- \section{Single substitution}

-- \begin{code}
-- _[_] : ∀ {Γ A B}
--   → A ∷ Γ ⊢ B
--   → Γ ⊢ A
--   ------------
--   → Γ ⊢ B
-- _[_] {Γ} {A} N V = {!!} -- subst {A ∷ Γ} {Γ} σ N
--   -- where
--   -- σ : ∀ {B} → A ∷ Γ ∋ B → Γ ⊢ B
--   -- σ Z      =  V
--   -- σ (S x)  =  ` x
-- \end{code}

-- \section{Values}

-- \begin{code}
-- data Value : ∀ {Γ A} → Γ ⊢ A → Set where

--   -- functions

--   V-ƛ : ∀ {Γ A B} {N : A ∷ Γ ⊢ B}
--       ---------------------------
--     → Value (ƛ N)

-- \end{code}

-- \section{Reduction}

-- \begin{code}
-- infix 2 _—→_

-- data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

--   -- functions

--   ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
--     → L —→ L′
--       ---------------
--     → L · M —→ L′ · M

--   ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
--     → Value V
--     → M —→ M′
--       ---------------
--     → V · M —→ V · M′

--   β-ƛ : ∀ {Γ A B} {N : A ∷ Γ ⊢ B} {V : Γ ⊢ A}  -- TODO
--     → Value V
--       --------------------
--     → (ƛ N) · V —→ N [ V ]

-- V¬—→ : ∀ {Γ σ} {M N : Γ ⊢ σ}
--      → Value M
--        -------------
--      → ¬ (M —→ N)
-- V¬—→ () (ξ-·₁ M—→N)
-- V¬—→ () (ξ-·₂ x M—→N)
-- V¬—→ () (β-ƛ V)

-- det : ∀ {Γ σ} {e e₁ e₂ : Γ ⊢ σ}
--     → e —→ e₁
--     → e —→ e₂
--       ---------
--     → e₁ ≡ e₂
-- det (ξ-·₁ e—→e₁) (ξ-·₁ e—→e₂)      =  cong₂ _·_ (det e—→e₁ e—→e₂) refl
-- det (ξ-·₁ e—→e₁) (ξ-·₂ V-L e—→e₂)  =  ⊥-elim (V¬—→ V-L e—→e₁)
-- det (ξ-·₁ e—→e₁) (β-ƛ _)           =  ⊥-elim (V¬—→ V-ƛ e—→e₁)
-- det (ξ-·₂ V-L e—→e₁) (ξ-·₁ e—→e₂)  =  ⊥-elim (V¬—→ V-L e—→e₂)
-- det (ξ-·₂ _ e—→e₁) (ξ-·₂ _ e—→e₂)  =  cong₂ _·_ refl (det e—→e₁ e—→e₂)
-- det (ξ-·₂ _ e—→e₁) (β-ƛ V)         =  ⊥-elim (V¬—→ V e—→e₁)
-- det (β-ƛ _) (ξ-·₁ e—→e₂)           =  ⊥-elim (V¬—→ V-ƛ e—→e₂)
-- det (β-ƛ V) (ξ-·₂ _ e—→e₂)         =  ⊥-elim (V¬—→ V e—→e₂)
-- det (β-ƛ V) (β-ƛ V')               =  refl

-- \end{code}

-- \section{Reflexive and transitive closure}

-- \begin{code}
-- infix  2 _—↠_
-- infix  1 begin_
-- infixr 2 _—→⟨_⟩_
-- infix  3 _∎

-- data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

--   _∎ : ∀ {Γ A} (M : Γ ⊢ A)
--       --------
--     → M —↠ M

--   _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
--     → L —→ M
--     → M —↠ N
--       ------
--     → L —↠ N

-- begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
--   → M —↠ N
--     ------
--   → M —↠ N
-- begin M—↠N = M—↠N
-- \end{code}

-- \section{Progress}

-- \begin{code}
-- data Progress {A} (M : [] ⊢ A) : Set where

--   step : ∀ {N : [] ⊢ A}
--     → M —→ N
--       ----------
--     → Progress M

--   done :
--       Value M
--       ----------
--     → Progress M

-- progress : ∀ {A}
--   → (M : [] ⊢ A)
--     -----------
--   → Progress M
-- progress (` ())
-- progress (ƛ N)                              =  done V-ƛ
-- progress (L · M) with progress L
-- ...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
-- ...    | done V-ƛ with progress M
-- ...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
-- ...        | done VM                        =  step (β-ƛ VM)
-- \end{code}

-- \section{Evaluation}

-- \begin{code}
-- data Gas : Set where
--   gas : ℕ → Gas

-- data Finished {Γ A} (N : Γ ⊢ A) : Set where

--    done :
--        Value N
--        ----------
--      → Finished N

--    out-of-gas :
--        ----------
--        Finished N

-- data Steps : ∀ {A} → [] ⊢ A → Set where

--   steps : ∀ {A} {L N : [] ⊢ A}
--     → L —↠ N
--     → Finished N
--       ----------
--     → Steps L

-- eval : ∀ {A}
--   → Gas
--   → (L : [] ⊢ A)
--     -----------
--   → Steps L
-- eval (gas zero)    L                     =  steps (L ∎) out-of-gas
-- eval (gas (suc m)) L with progress L
-- ... | done VL                            =  steps (L ∎) (done VL)
-- ... | step {M} L—→M with eval (gas m) M
-- ...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
-- \end{code}
