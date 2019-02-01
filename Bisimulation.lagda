\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; inspect ; [_] ; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List using (_∷_ ; [] ; List)
open import Data.Unit using (⊤ ; tt)

open import Common
import PCF as S
open S using (ƛ_)
import Closure as T
open T using (Env ; ⟪_,_⟫)
open import Conversion using (_†)
open import SubContext using (⊆→ρ)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ S.⊢ A) → (Γ T.⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------------
   → S.` x ~ T.` x

  ~ƛ_ : ∀ {Γ Δ A B} {N : A ∷ A ⇒ B ∷ Γ S.⊢ B} {N† : A ∷ A ⇒ B ∷ Δ T.⊢ B} {E : Env Δ Γ}
    → N ~ T.subst (T.make-σ′ E) N†
      -----------------
    → ƛ N ~ ⟪ N† , E ⟫

  _~·_ : ∀ {Γ A B} {L : Γ S.⊢ A ⇒ B} {L† : Γ T.⊢ A ⇒ B} {M : Γ S.⊢ A} {M† : Γ T.⊢ A}
    → L ~ L†
    → M ~ M†
      --------------------
    → L S.· M ~ L† T.· M†

data SimulationRelevant : {Γ : Context} {A : Type} → Γ S.⊢ A → Set where

  †` : ∀ {Γ A}
     → (x : Γ ∋ A)
       --------------------
     → SimulationRelevant (S.` x)

  †ƛ_ : ∀ {Γ A B}
      → (N : A ∷ A ⇒ B ∷ Γ S.⊢ B)
        ------------------------
      → SimulationRelevant (ƛ N)

  _†·_ : ∀ {Γ A B}
       → (L : Γ S.⊢ A ⇒ B)
       → (M : Γ S.⊢ A)
         ----------------------
       → SimulationRelevant (L S.· M)

-- †≡→~ : ∀ {Γ A}
--     → (M : Γ S.⊢ A)
--     → {N : Γ T.⊢ A}
--     → SimulationRelevant M
--     → M † ≡ N
--       ------------
--     → M ~ N
-- †≡→~ (S.` x) _ with (S.` x) †  -- TODO we could prove that if M ≡ S.` x then M † ≡ T.` x but it's rather tedious
-- ... | p = {!p!}
-- †≡→~ M@(ƛ N) _ with M †
-- ... | p = {!!}
-- †≡→~ M@(L S.· N) _ with M †
-- ... | p = {!!}
-- †≡→~ S.`zero ()
-- †≡→~ (S.`suc M) ()
-- †≡→~ (S.case M M₁ M₂) ()

~val : ∀ {Γ A} {M  : Γ S.⊢ A} {M† : Γ T.⊢ A}
  → M ~ M†
  → S.Value M
    --------
  → T.Value M†
~val ~`           ()
~val (~ƛ ~N)      S.V-ƛ  =  T.V-⟪⟫
~val (~L ~· ~M)   ()

~rename : ∀ {Γ Δ}
  → (ρ : Renaming Γ Δ)
    ----------------------------------------------------------
  → ∀ {A} {M : Γ S.⊢ A} {M† : Γ T.⊢ A} → M ~ M† → S.rename ρ M ~ T.rename ρ M†
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ {!!}  -- (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)

~exts : ∀ {Γ Δ}
  → {σ  : Substitution S._⊢_ Γ Δ}
  → {σ† : Substitution T._⊢_ Γ Δ}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : B ∷ Γ ∋ A) → S.exts σ x ~ T.exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ  : Substitution S._⊢_ Γ Δ}
  → {σ† : Substitution T._⊢_ Γ Δ}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M : Γ S.⊢ A} {M† : Γ T.⊢ A} → M ~ M† → S.subst σ M ~ T.subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ {!!} -- (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)

data Leg {Γ A} (M† : Γ T.⊢ A) (N : Γ S.⊢ A) : Set where

  leg : ∀ {N† : Γ T.⊢ A}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

sim : ∀ {Γ A}
  → {M N : Γ S.⊢ A} {M† : Γ T.⊢ A}
  → M ~ M†
  → M S.—→ N
    ---------
  → Leg M† N
sim ~` ()
sim (~ƛ N) ()
sim (~L ~· ~M) (S.ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→             =  leg (~L′ ~· ~M) (T.ξ-·₁ L†—→)
sim (~L ~· ~M) (S.ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→             =  leg (~L ~· ~M′) (T.ξ-·₂ (~val ~L VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (S.β-ƛ VV)  =  leg {!!} (T.β-⟪⟫ T.V-⟪⟫ (~val ~V VV))  -- TODO use ~subst, but first prove that the two substitutions are (extensionally equivalent)

\end{code}
