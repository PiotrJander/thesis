\begin{code}
module UG4 where

import Data.Vec as V
open V using (Vec; zip; toList; allFin)
open V renaming ([] to v[]; _∷_ to _v∷_)
import Data.List as L
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open L using (List; []; _∷_; filter)
-- open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.Nat
open import Agda.Builtin.Nat using (_-_)
open import Data.Nat.Properties -- using (_≟_)
open import Data.Fin hiding (_≟_; _<_; _-_)
open import Relation.Nullary -- using (Dec)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation
open import Function using (_∘_; _∘′_)
open import Data.Product using (uncurry′; _×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq -- using (_≡_; refl; trans; cong; sym; cong₂)

Num : Set
Num = ℕ

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec Num n) m

csr : ∀ {m n} → Matrix m n → Vec Num n → Vec Num m
csr matrix vec = V.map (V.sum ∘ V.map (uncurry′ _*_) ∘ zip vec) matrix

lemma-1 : {m : ℕ}
  → (xs : Vec ℕ m)
  → V.sum xs ≡ L.sum (toList xs)
lemma-1 v[] = refl
lemma-1 (x v∷ xs) rewrite lemma-1 xs = refl

postulate
  ¬¬ℕ : {m n : ℕ} → ¬ ¬ (n ≡ m) → n ≡ m
\end{code}

%<*sum-filter>
\begin{code}
non-zero : (n : ℕ) → Dec (n ≢ zero)
non-zero n = ¬? (n ≟ zero)

lemma-2 : (xs : List ℕ)
  → L.sum (filter non-zero xs) ≡ L.sum xs
lemma-2 [] = refl
lemma-2 (x ∷ xs) with non-zero x
lemma-2 (x ∷ xs) | yes p rewrite lemma-2 xs = refl
lemma-2 (x ∷ xs) | no ¬p rewrite decidable-stable (x ≟ zero) ¬p | lemma-2 xs = refl
\end{code}
%</sum-filter>

\begin{code}
non-zero-proj₂ : (p : ℕ × ℕ) → Dec (proj₂ p ≢ zero)
non-zero-proj₂ = non-zero ∘ proj₂

non-zero-snd' : (p : ℕ × ℕ) → Dec (proj₂ p ≢ zero)
non-zero-snd' p = ¬? (proj₂ p ≟ zero)

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

module _ {A : Set} where

  data VecSuffix : ∀ {m n} → Vec A m → Vec A n → Set where
    here   :  ∀ {n} (v : Vec A n) → VecSuffix v v
    there  :  ∀ {m n} {v1 : Vec A m} {v2 : Vec A n} (e : A) → VecSuffix v1 v2 → VecSuffix v1 (e v∷ v2)

  tail-suffix : ∀ {m n} {x : A} {xs : Vec A m} {xs' : Vec A n} → VecSuffix (x v∷ xs) xs' → VecSuffix xs xs'
  tail-suffix (here (x v∷ xs)) = there x (here xs)
  tail-suffix (there e suffix) = there e (tail-suffix suffix)

  suffix-to-fin' : ∀ {m n : ℕ} {xs' : Vec A (suc m)} {xs : Vec A n} → VecSuffix xs' xs → Fin (suc m)
  suffix-to-fin' {xs' = x v∷ v[]} suffix = zero
  suffix-to-fin' {xs' = x v∷ x' v∷ xs'} suffix = suc (suffix-to-fin' (tail-suffix suffix))

  suffix-to-fin : ∀ {m n : ℕ} {xs' : Vec A (suc m)} {xs : Vec A n} → VecSuffix xs' xs → Fin n
  suffix-to-fin (here xs) = suffix-to-fin' (here xs)
  suffix-to-fin (there e suffix) = suc (suffix-to-fin suffix)

  enumerate' : {n m : ℕ} {xs' : Vec A m} {xs : Vec A n} → VecSuffix xs' xs → Vec (Fin n × A) m
  enumerate' {xs' = v[]} suffix = v[]
  enumerate' {xs' = x v∷ xs'} suffix = ((suffix-to-fin suffix) , x) v∷ (enumerate' (tail-suffix suffix))
  
  enumerate : {n : ℕ} → Vec A n → Vec (Fin n × A) n
  enumerate xs = enumerate' (here xs)

  -- drop-zip-allFin≡enumerate' : {n m : ℕ} {xs' : Vec A m} {xs : Vec A n} (suffix : VecSuffix xs' xs)
  --   → enumerate' suffix ≡ V.drop (n ∸ m) (zip (V.allFin n) xs)
  -- drop-zip-allFin≡enumerate' suffix = ?

  -- zip-allFin≡enumerate : ∀ {n} (xs : Vec A n) → enumerate xs ≡ zip (V.allFin n) xs
  -- zip-allFin≡enumerate xs = {!!}

postulate
  lemma-3 : ∀ {n m} {row' : Vec Num m} (row vec : Vec Num n)
    → V.map (uncurry′ _*_) (zip vec row) ≡ V.map (λ { (i , v) → lookup i vec * v }) (zip (V.allFin n) row)
-- lemma-3 v[] vec = {!!}
-- lemma-3 (x v∷ row) vec = {!!}

lemma-5 : {x y : ℕ}
  → x ≢ zero
  → y ≢ zero
  → x * y ≢ zero
lemma-5 {x} x≢0 y≢0 x*y≡0 = case-⊎ (λ p → ⊥-elim (x≢0 p)) (λ p → ⊥-elim (y≢0 p)) (i*j≡0⇒i≡0∨j≡0 x x*y≡0)

lemma-6 : {x y : ℕ} (x≢0 : x ≢ zero) (y≢0 : y ≢ zero)
  → ∃[ p ] (non-zero (x * y) ≡ yes p)
lemma-6 {x} {y} x≢0 y≢0 with non-zero (x * y) | inspect non-zero (x * y)
lemma-6 {x} {y} x≢0 y≢0 | yes p | [ eq ] = p , refl
lemma-6 {x} {y} x≢0 y≢0 | no ¬p | [ eq ] = ⊥-elim (lemma-5 x≢0 y≢0 (¬¬ℕ ¬p))

lemma-4 : (xs : List (ℕ × ℕ))
  → L.sum (filter non-zero (L.map (uncurry′ _*_) xs)) ≡ L.sum (L.map (uncurry′ _*_) (filter (non-zero ∘ proj₂) xs))
lemma-4 [] = refl
lemma-4 ((x , y) ∷ xs) with non-zero x | non-zero y
lemma-4 ((x , y) ∷ xs) | yes x0 | yes y0 with lemma-6 x0 y0
lemma-4 ((x , y) ∷ xs) | yes x0 | yes y0 | fst , snd rewrite snd | lemma-4 xs = refl
lemma-4 ((x , y) ∷ xs) | yes x0 | no ¬y0 rewrite ¬¬ℕ ¬y0 | *-zeroʳ x = lemma-4 xs
lemma-4 ((x , y) ∷ xs) | no ¬x0 | yes y0 rewrite ¬¬ℕ ¬x0 | *-zeroʳ y = lemma-4 xs
lemma-4 ((x , y) ∷ xs) | no ¬x0 | no ¬y0 rewrite ¬¬ℕ ¬x0 | *-zeroʳ y = lemma-4 xs

\end{code}
