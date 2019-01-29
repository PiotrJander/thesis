\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List using (_∷_ ; [])
import PCF as S
open S using (_,_ ; ƛ_ ; ∅ ; Z ; S_)
import Closure as T
open T using (Env ; ⟪_,_⟫ ; z ; s_)
import Conversion
open Conversion renaming (convert-context to cctx ; convert-type to ct)
open import SubContext using (⊆→ρ)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

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
~val (~ƛ ~N)      S.V-ƛ  =  T.V-⟪ {!!} , {!!} ⟫
~val (~L ~· ~M)   ()

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
...  | leg ~L′ L†—→            =  leg (~L′ ~· ~M) (T.ξ-·₁ L†—→)
sim (~L ~· ~M) (S.ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→            =  leg (~L ~· ~M′) (T.ξ-·₂ {!!} {!!})
sim (~L ~· ~M) (S.β-ƛ x) = {!!}

-- sim {M = S.` x} (simil ρ M~ρM†) ()
-- sim {M = ƛ M} {M† = T.` x} (simil ρ ())
-- sim {M = ƛ M} {M† = M† T.· M†₁} (simil ρ ())
-- sim {M = ƛ N} {M† = ⟪ N† , E ⟫} (simil ρ (~ƛ ~N)) () 
-- sim {M = ƛ M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
-- sim {A = S.`ℕ} {L S.· M} {M† = T.` x} (simil ρ ())
-- sim {A = S.`ℕ} {L S.· M} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.ξ-·₁ {L′ = L′} L—→) with sim (simil ρ ~L) L—→
-- ... | leg (simil ρ₁ ~L′) L†—→ = {!!}  -- now need to show that ρ₁ is an identity renaming
-- sim {A = S.`ℕ} {L S.· M} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.ξ-·₂ V-L M—→) = {!!}
-- sim {A = S.`ℕ} {.(ƛ _) S.· L₁} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.β-ƛ V) = {!!}
-- sim {A = S.`ℕ} {L S.· M} {M† = T.`zero} (simil ρ ())
-- sim {A = S.`ℕ} {L S.· M} {M† = T.`suc M†} (simil ρ ())
-- sim {A = S.`ℕ} {L S.· M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
-- sim {A = A S.⇒ A₁} {L S.· M} {M† = T.` x} (simil ρ ())
-- sim {A = A S.⇒ A₁} {L S.· M} {M† = M† T.· M†₁} (simil ρ M~ρM†) y = {!!}
-- sim {A = A S.⇒ A₁} {L S.· M} {M† = ⟪ M† , x ⟫} (simil ρ ())
-- sim {A = A S.⇒ A₁} {L S.· M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
-- sim {M = S.`zero} (simil ρ ())
-- sim {M = S.`suc N} (simil ρ ())
-- sim {M = S.case L M N} (simil ρ ())

\end{code}
