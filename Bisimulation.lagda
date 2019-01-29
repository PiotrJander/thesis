\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; inspect ; [_])
open import Data.List using (_∷_ ; [] ; List)
import PCF as S
open S using (_,_ ; ƛ_ ; ∅ ; Z ; S_ ; Context)
import Closure as T
open T using (Env ; ⟪_,_⟫ ; z ; s_)
import Conversion
open Conversion using (Type-iso ; Context-iso ; cc ; ∃[_]_∧_)
open import Isomorphism using (_≃_)
open _≃_
open import SubContext using (⊆→ρ)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

cctx : S.Context → T.Context
cctx = to Context-iso

ct : S.Type → T.Type
ct = to Type-iso

data _~_ : ∀ {Γ A}
     → let Γ′ = cctx Γ in let A′ = ct A in 
       (Γ S.⊢ A) → (Γ′ T.⊢ A′) → Set where

  ~` : ∀ {Γ A}
   → let Γ′ = cctx Γ in let A′ = ct A in  -- let with multiple clauses?
     {x : Γ S.∋ A} {x′ : Γ′ T.∋ A′}
     ---------------
   → S.` x ~ T.` x′

  ~ƛ_ : ∀ {Γ Δ A B}
    → let Γ′ = cctx Γ in let A′ = ct A in let B′ = ct B in
      {N : Γ , A S.⇒ B , A S.⊢ B} {N† : A′ ∷ A′ T.⇒ B′ ∷ Δ T.⊢ B′} {E : Env Δ Γ′}
    → N ~ T.subst (T.make-σ′ E) N†
      -----------------
    → ƛ N ~ ⟪ N† , E ⟫

  _~·_ : ∀ {Γ A B}
    → let Γ′ = cctx Γ in let A′ = ct A in let B′ = ct B in
      {L : Γ S.⊢ A S.⇒ B} {L† : Γ′ T.⊢ A′ T.⇒ B′} {M : Γ S.⊢ A} {M† : Γ′ T.⊢ A′}
    → L ~ L†
    → M ~ M†
      --------------------
    → L S.· M ~ L† T.· M†

-- example

h : ∀ {Γ A} (M : Γ S.⊢ A) → Set
h M with cc M
h M | ∃[ Δ ] Δ⊆Γ ∧ N = M ~ T.rename (⊆→ρ Δ⊆Γ) N

foo : ∅ , S.`ℕ S.⇒ S.`ℕ , S.`ℕ S.⊢ S.`ℕ S.⇒ S.`ℕ
foo = ƛ ((S.# 3) S.· (S.# 0))

test : h foo
test with cc foo
test | _ = ~ƛ (~` ~· ~`)

-- sim

~val : ∀ {Γ A}
  → let Γ' = cctx Γ in let A' = ct A in
    {M  : Γ S.⊢ A} {M† : Γ' T.⊢ A'}
  → M ~ M†
  → S.Value M
    --------
  → T.Value M†
~val ~`           ()
~val (~ƛ ~N)      S.V-ƛ  =  T.V-⟪⟫
~val (~L ~· ~M)   ()

S∋→T∋ : ∀ {Γ A}
  → let Γ' = cctx Γ in let A' = ct A in
    Γ  S.∋ A
  → Γ' T.∋ A'
S∋→T∋ Z = z
S∋→T∋ (S x) = s (S∋→T∋ x)

T∋→S∋ : ∀ {Γ' A'}
  → let Γ = from Context-iso Γ' in let A = from Type-iso A' in
    Γ' T.∋ A'
  → Γ  S.∋ A
T∋→S∋ z = Z
T∋→S∋ (s x) = S (T∋→S∋ x)

Sρ→Tρ : ∀ {Γ Δ}
  → let Γ' = cctx Γ in let Δ' = cctx Δ in
    (∀ {A} → Γ S.∋ A → Δ S.∋ A)
  → T.Renaming Γ' Δ'
Sρ→Tρ {Γ} {Δ} ρ x with cctx Γ | inspect cctx Γ | cctx Δ | inspect cctx Δ
Sρ→Tρ {Γ} {Δ} ρ z | .(_ ∷ _) | [ Γ≡Γ' ] | Δ' | [ Δ≡Δ' ] = {!S∋→T∋ ?!}
Sρ→Tρ {Γ} {Δ} ρ (s x) | .(_ ∷ _) | [ Γ≡Γ' ] | Δ' | [ Δ≡Δ' ] = {!!}

-- Sρ→Tρ {∅} ρ ()
-- Sρ→Tρ {Γ , A} {∅} ρ with ρ Z
-- Sρ→Tρ {Γ , A} {∅} ρ | ()
-- Sρ→Tρ {Γ , A} {Δ , B} ρ z = S∋→T∋ (ρ Z)
-- Sρ→Tρ {Γ , A} {Δ , B} ρ (s x) with cctx Γ | inspect cctx Γ | cctx Δ | inspect cctx Δ  -- with ct B | inspect ct B
-- -- ... | B' | [ B≡B' ] = {!!}
-- ...  | Γ' | [ Γ≡Γ ] | Δ' | [ Δ≡Δ' ] = {!!}

-- ~rename : ∀ {Γ Δ}
--   → Renaming Γ Δ
--     ----------------------------------------------------------
--   → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
-- ~rename ρ (~`)          =  ~`
-- ~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
-- ~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)

~sub : ∀ {Γ A B}
  → let Γ' = cctx Γ in let A' = ct A in let B' = ct B in
    {N : Γ , A S.⇒ B , A S.⊢ B} {N† : A' ∷ A' T.⇒ B' ∷ Γ' T.⊢ B'}
    {M : Γ S.⊢ A} {M† : Γ' T.⊢ A'}
  → (E : Env Γ' Γ')
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N S.[ ƛ N ][ M ]) ~ (N† T.[ ⟪ N† , E ⟫ ][ M† ])
~sub = {!!}


data Leg {Γ A} (M† : cctx Γ T.⊢ ct A) (N : Γ S.⊢ A) : Set where

  leg : ∀ {N† : cctx Γ T.⊢ ct A}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

sim : ∀ {Γ A}
  → let Γ′ = cctx Γ in let A′ = ct A in
    {M N : Γ S.⊢ A} {M† : Γ′ T.⊢ A′}
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
sim ((~ƛ ~N) ~· ~V) (S.β-ƛ VV)  =  leg {!!} (T.β-⟪⟫ {!!} {!!})

\end{code}
