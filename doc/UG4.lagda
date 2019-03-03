\begin{code}
module UG4 where

import Data.Vec as V
open V using (Vec; zip; toList)
open V renaming ([] to v[]; _∷_ to _v∷_)
import Data.List as L
open L using (List; []; _∷_; filter)
open import Data.Nat -- using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties -- using (_≟_)
open import Data.Fin hiding (_≟_; _<_)
open import Relation.Nullary -- using (Dec)
open import Relation.Nullary.Negation
open import Function using (_∘_; _∘′_)
open import Data.Product using (uncurry′; _×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq -- using (_≡_; refl; trans; cong; sym; cong₂)

Num : Set
Num = ℕ

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec Num n) m

csr : ∀ {m n} → Matrix m n → Vec Num n → Vec Num m
csr matrix vec = V.map (V.sum ∘ V.map (uncurry′ _*_) ∘ zip vec) matrix
  -- where
  -- f1 : Vec Num n → Vec (Num × Num) n
  -- f1 xs = zip vec xs
  -- f2 : Vec (Num × Num) n → Vec Num n
  -- f2 = map (uncurry′ _*_)

lemma-1 : {m : ℕ}
  → (xs : Vec ℕ m)
  → V.sum xs ≡ L.sum (toList xs)
lemma-1 v[] = refl
lemma-1 (x v∷ xs) rewrite lemma-1 xs = refl

non-zero : (n : ℕ) → Dec (n ≢ zero)
non-zero n = ¬? (n ≟ zero)

postulate
  ¬¬ℕ : {m n : ℕ} → ¬ ¬ (n ≡ m) → n ≡ m

lemma-2 : (xs : List ℕ)
  → L.sum (filter non-zero xs) ≡ L.sum xs
lemma-2 [] = refl
lemma-2 (x ∷ xs) with non-zero x
lemma-2 (x ∷ xs) | yes p rewrite lemma-2 xs = refl
lemma-2 (x ∷ xs) | no ¬p rewrite ¬¬ℕ ¬p | lemma-2 xs = refl

suc-n<m : ∀ {n m}
  → suc n < m
  → n < m
suc-n<m {n} s-n<m = <-trans ≤-refl s-n<m

fins' : {m n : ℕ} (n<m : n < m) → Vec (Fin m) n
fins' {n = zero} n<m = v[]
fins' {n = suc n} n<m = fromℕ≤ n<m v∷ fins' (suc-n<m n<m)

fins : (m : ℕ) → Vec (Fin m) m
fins zero = v[]
fins (suc m) = fromℕ m v∷ fins' ≤-refl

enumeration : {m : ℕ} → Vec (Fin m) m
enumeration {m} = reverse (fins m)

-- foo : ∀ {m} → Fin m × ℕ → ℕ
-- foo (i , v) = {!!}

-- bar : ∀ {m} → Vec ℕ m → Vec (Fin m × ℕ) m
-- bar row = zip enumeration row

lemma-3 : ∀ {n} (row vec : Vec Num n)
  → V.map (uncurry′ _*_) (zip vec row) ≡ V.map (λ { (i , v) → lookup i vec * v }) (zip enumeration row)
lemma-3 v[] vec = {!!}
lemma-3 (x v∷ row) vec = {!!}

\end{code}
