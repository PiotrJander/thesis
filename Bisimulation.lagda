\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; inspect ; [_] ; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.List using (_∷_ ; [] ; List)
open import Data.Unit using (⊤ ; tt)
import PCF as S
open S using (_,_ ; ƛ_ ; ∅ ; Z ; S_ ; Context)
import Closure as T
open T using (Env ; ⟪_,_⟫ ; z ; s_)
import Conversion
open Conversion using (cc ; ∃[_]_∧_ ; c-to ; c-from ; c-from∘to ; c-to∘from ; t-to ; t-from ; t-from∘to ; t-to∘from) -- Type-iso ; Context-iso
open import Isomorphism using (_≃_)
open _≃_
open import SubContext using (⊆→ρ)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

-- cctx : S.Context → T.Context
-- cctx = c-to

-- ct : S.Type → T.Type
-- ct = t-to

-- ct≡ : ∀ {A} → ct A ≡ t-to A
-- ct≡ = refl

-- ct⁻¹ : T.Type → S.Type
-- ct⁻¹ = from Type-iso

data _~_ : ∀ {Γ A}
     → let Γ′ = c-to Γ in let A′ = t-to A in 
       (Γ S.⊢ A) → (Γ′ T.⊢ A′) → Set where

  ~` : ∀ {Γ A}
   → let Γ′ = c-to Γ in let A′ = t-to A in  -- let with multiple clauses?
     {x : Γ S.∋ A} {x′ : Γ′ T.∋ A′}
     ---------------
   → S.` x ~ T.` x′

  ~ƛ_ : ∀ {Γ Δ A B}
    → let Γ′ = c-to Γ in let A′ = t-to A in let B′ = t-to B in
      {N : Γ , A S.⇒ B , A S.⊢ B} {N† : A′ ∷ A′ T.⇒ B′ ∷ Δ T.⊢ B′} {E : Env Δ Γ′}
    → N ~ T.subst (T.make-σ′ E) N†
      -----------------
    → ƛ N ~ ⟪ N† , E ⟫

  _~·_ : ∀ {Γ A B}
    → let Γ′ = c-to Γ in let A′ = t-to A in let B′ = t-to B in
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
  → let Γ' = c-to Γ in let A' = t-to A in
    {M  : Γ S.⊢ A} {M† : Γ' T.⊢ A'}
  → M ~ M†
  → S.Value M
    --------
  → T.Value M†
~val ~`           ()
~val (~ƛ ~N)      S.V-ƛ  =  T.V-⟪⟫
~val (~L ~· ~M)   ()

S∋→T∋ : ∀ {Γ A}
  → let Γ' = c-to Γ in let A' = t-to A in
    Γ  S.∋ A
  → Γ' T.∋ A'
S∋→T∋ Z = z
S∋→T∋ (S x) = s (S∋→T∋ x)

T∋→S∋ : ∀ {Γ' A'}
  → let Γ = c-from Γ' in let A = t-from A' in
    Γ' T.∋ A'
  → Γ  S.∋ A
T∋→S∋ z = Z
T∋→S∋ (s x) = S (T∋→S∋ x)

Sρ→Tρ : ∀ {Γ Δ}
  → let Γ' = c-to Γ in let Δ' = c-to Δ in
    (∀ {A} → Γ S.∋ A → Δ S.∋ A)
  → T.Renaming Γ' Δ'
Sρ→Tρ {Γ} {Δ} ρ {A'} x with c-to Γ | inspect (c-to) Γ | c-to Δ | inspect (c-to) Δ |  t-from A' | inspect t-from A'
Sρ→Tρ {Γ} {Δ} ρ {A'} x' | Γ' | [ Γ≡Γ' ] | Δ' | [ Δ≡Δ' ] | A | [ A'≡A ] with T∋→S∋ x'
... | x rewrite sym Γ≡Γ' | c-from∘to Γ = helper
  where
    xyz : t-to (t-from A') ≡ A'
    xyz = t-to∘from A'
    toA≡A' : t-to A ≡ A'
    toA≡A' rewrite sym A'≡A | t-to∘from A' = refl
    helper : Δ' T.∋ A'
    helper rewrite sym Δ≡Δ' | A'≡A | toA≡A' = {!S∋→T∋ (ρ x)!}

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ S.∋ A → Δ S.∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M : Γ S.⊢ A} {M† : c-to Γ T.⊢ t-to A} → M ~ M† → S.rename ρ M ~ T.rename (Sρ→Tρ ρ) M†)
~rename {Γ} {Δ} ρ {A} ~M with c-to Γ | inspect c-to Γ | c-to Δ | inspect c-to Δ | t-to A | inspect t-to A
~rename {Γ} {Δ} ρ {A} ~M | Γ' | [ Γ≡Γ' ] | Δ' | [ Δ≡Δ' ] | A' | [ A≡A' ] = ?
-- ~rename ρ (~`)          =  ~`
-- ~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
-- ~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
-- ~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)

~sub : ∀ {Γ A B}
  → let Γ' = c-to Γ in let A' = t-to A in let B' = t-to B in
    {N : Γ , A S.⇒ B , A S.⊢ B} {N† : A' ∷ A' T.⇒ B' ∷ Γ' T.⊢ B'}
    {M : Γ S.⊢ A} {M† : Γ' T.⊢ A'}
  → (E : Env Γ' Γ')
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N S.[ ƛ N ][ M ]) ~ (N† T.[ ⟪ N† , E ⟫ ][ M† ])
~sub = {!!}


data Leg {Γ A} (M† : c-to Γ T.⊢ t-to A) (N : Γ S.⊢ A) : Set where

  leg : ∀ {N† : c-to Γ T.⊢ t-to A}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

sim : ∀ {Γ A}
  → let Γ′ = c-to Γ in let A′ = t-to A in
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
