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

infix  4 _~~_
infix  5 ~ƛ_
infix  7 _~·_

data _~~_ : ∀ {Γ A} → (Γ S.⊢ A) → (cctx Γ T.⊢ ct A) → Set 
record _~_ {Γ Δ A} (M : Γ S.⊢ A) (M† : Δ T.⊢ ct A) : Set 

data _~~_ where

  ~` : ∀ {Γ A}
   → let Γ′ = cctx Γ in let A′ = ct A in   -- let with multiple clauses?
     {x : Γ S.∋ A} {x′ : Γ′ T.∋ A′}
     ---------------
   → S.` x ~~ T.` x′

  ~ƛ_ : ∀ {Γ Δ A B}
    → let Γ′ = cctx Γ in let A′ = ct A in let B′ = ct B in
      {N : Γ , A S.⇒ B , A S.⊢ B} {N† : A′ ∷ A′ T.⇒ B′ ∷ Δ T.⊢ B′} {E : Env Δ Γ′}
    → N ~ N†
      -----------------
    → ƛ N ~~ ⟪ N† , E ⟫

  _~·_ : ∀ {Γ A B}
    → let Γ′ = cctx Γ in let A′ = ct A in let B′ = ct B in
      {L : Γ S.⊢ A S.⇒ B} {L† : Γ′ T.⊢ A′ T.⇒ B′} {M : Γ S.⊢ A} {M† : Γ′ T.⊢ A′}
    → L ~ L†
    → M ~ M†
      --------------------
    → L S.· M ~~ L† T.· M†

record _~_ {Γ Δ A} M M† where
  inductive
  constructor simil
  field
    ρ : T.Renaming Δ (cctx Γ)
    M~ρM† : M ~~ T.rename ρ M†

-- example

foo : ∅ , S.`ℕ S.⇒ S.`ℕ , S.`ℕ S.⊢ S.`ℕ S.⇒ S.`ℕ
foo = ƛ ((S.# 3) S.· (S.# 0))

foo′ : T.`ℕ T.⇒ T.`ℕ ∷ [] T.⊢ T.`ℕ T.⇒ T.`ℕ
foo′ = ⟪ (T.# 2) T.· (T.# 0) , (T.# 0) T.∷ T.[] ⟫

ρ' : let Δ = T.`ℕ T.⇒ T.`ℕ ∷ [] in T.Renaming Δ (T.`ℕ ∷ Δ)
ρ' z = s z
ρ' (s ())

_ : foo ~ foo′
_ = record { ρ = ρ' ; M~ρM† = ~ƛ (record { ρ = T.ext (T.ext ρ')  ; M~ρM† = (record { ρ = λ r → r ; M~ρM† = ~` }) ~· (record { ρ = λ r → r ; M~ρM† = ~` }) }) }

-- sim

data Leg {Γ Δ A} (M† : Δ T.⊢ ct A) (N : Γ S.⊢ A) : Set where

  leg : ∀ {N† : Δ T.⊢ ct A}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

sim : ∀ {Γ Δ A} {M N : Γ S.⊢ A} {M† : Δ T.⊢ ct A}
  → M ~ M†
  → M S.—→ N
    ---------
  → Leg M† N
sim {M = S.` x} (simil ρ M~ρM†) ()
sim {M = ƛ M} {M† = T.` x} (simil ρ ())
sim {M = ƛ M} {M† = M† T.· M†₁} (simil ρ ())
sim {M = ƛ N} {M† = ⟪ N† , E ⟫} (simil ρ (~ƛ ~N)) () 
sim {M = ƛ M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
sim {A = S.`ℕ} {L S.· M} {M† = T.` x} (simil ρ ())
sim {A = S.`ℕ} {L S.· M} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.ξ-·₁ {L′ = L′} L—→) with sim ~L L—→
... | leg {L†′} ~L′ L†—→ = leg (simil {!!} {!!}) {!!}
  where
  xyz : M ~ T.rename ρ M†
  xyz = ~M
sim {A = S.`ℕ} {L S.· M} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.ξ-·₂ V-L M—→) = {!!}
sim {A = S.`ℕ} {.(ƛ _) S.· L₁} {M† = L† T.· M†} (simil ρ (~L ~· ~M)) (S.β-ƛ V) = {!!}
sim {A = S.`ℕ} {L S.· M} {M† = T.`zero} (simil ρ ())
sim {A = S.`ℕ} {L S.· M} {M† = T.`suc M†} (simil ρ ())
sim {A = S.`ℕ} {L S.· M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
sim {A = A S.⇒ A₁} {L S.· M} {M† = T.` x} (simil ρ ())
sim {A = A S.⇒ A₁} {L S.· M} {M† = M† T.· M†₁} (simil ρ M~ρM†) y = {!!}
sim {A = A S.⇒ A₁} {L S.· M} {M† = ⟪ M† , x ⟫} (simil ρ ())
sim {A = A S.⇒ A₁} {L S.· M} {M† = T.case M† M†₁ M†₂} (simil ρ ())
sim {M = S.`zero} (simil ρ ())
sim {M = S.`suc N} (simil ρ ())
sim {M = S.case L M N} (simil ρ ())

\end{code}
