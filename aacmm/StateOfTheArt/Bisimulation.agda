module StateOfTheArt.Bisimulation where

open import Data.List using (List; []; _∷_)

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)

open import StateOfTheArt.Types
import StateOfTheArt.STLC as S
import StateOfTheArt.Closure as T

infix  4 _~_

data _~_ : ∀ {Γ σ} → S.Lam σ Γ → T.Lam σ Γ → Set where

  ~V : ∀ {Γ σ} {x : Var σ Γ}
     ---------------
   → S.V x ~ T.V x

  ~L : ∀ {Γ Δ σ τ} {N : S.Lam τ (σ ∷ Γ)} {N† : T.Lam τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    → N ~ T.subst (T.exts E) N†
      -----------------
    → S.L N ~ T.L N† E

  ~A : ∀ {Γ σ τ} {L : S.Lam (σ ⇒ τ) Γ} {L† : T.Lam (σ ⇒ τ) Γ}
           {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
    → L ~ L†
    → M ~ M†
      --------------------
    → S.A L M ~ T.A L† M†

~rename : ∀ {Γ Δ}
  → (ρ : Thinning Γ Δ)
    ----------------------------------------------------------
  → ∀ {σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ} → M ~ M† → S.rename ρ M ~ T.rename ρ M†
~rename ρ ~V = ~V
~rename ρ (~L ~N) = {!!}
~rename ρ (~A ~M ~N) = ~A (~rename ρ ~M) (~rename ρ ~N)


