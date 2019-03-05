module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


+-assoc : ∀(n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc zero m k =
  begin
    (zero + m) + k
  ≡⟨⟩
    m + k
  ≡⟨⟩
    zero + (m + k)
  ∎
+-assoc (suc n') m k =
  begin
    (suc n' + m) + k
  ≡⟨⟩
    suc (n' + m) + k
  ≡⟨⟩
    suc ((n' + m) + k)
  ≡⟨ cong suc (+-assoc n' m k) ⟩
    suc (n' + (m + k))
  ≡⟨⟩
    suc n' + (m + k)
  ∎

+-rightIdentity : ∀(n : ℕ) → n + 0 ≡ n
+-rightIdentity zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-rightIdentity (suc n') =
  begin
    suc n' + zero
  ≡⟨⟩
    suc (n' + zero)
  ≡⟨ cong suc (+-rightIdentity n') ⟩
    suc n'
  ∎

+-rightSuc : ∀(n m : ℕ) → n + suc m ≡ suc (n + m)
+-rightSuc zero m =
  begin
    zero + suc m
  ≡⟨⟩
    suc m
  ≡⟨⟩
    suc (zero + m)
  ∎
+-rightSuc (suc n) m =
  begin
    suc n + suc m
  ≡⟨⟩
    suc (n + suc m)
  ≡⟨ cong suc (+-rightSuc n m) ⟩
    suc (suc (n + m))
  ≡⟨⟩
    suc (suc n + m)
  ∎

+-commut : ∀(m n : ℕ) → m + n ≡ n + m
+-commut m zero =
  begin
    m + zero
  ≡⟨ +-rightIdentity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-commut m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-rightSuc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-commut m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎


+-rearrange₁ : ∀(n m p q : ℕ) → (n + m) + (p + q) ≡ n + (m + p) + q
+-rearrange₁ n m p q =
  begin
    (n + m) + (p + q)
  ≡⟨ +-assoc n m (p + q) ⟩
    n + (m + (p + q))
  ≡⟨ cong (n +_) (sym (+-assoc m p q)) ⟩
    n + ((m + p) + q)
  ≡⟨ sym (+-assoc n (m + p) q) ⟩
    n + (m + p) + q
  ∎

-- rewrite = magic
-- ???

+-assoc' : ∀(n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc' zero m k = refl
+-assoc' (suc n) m k rewrite +-assoc' n m k = refl

+-rightIdentity' : ∀(n : ℕ) → n + 0 ≡ n
+-rightIdentity' zero = refl
+-rightIdentity' (suc n) rewrite +-rightIdentity' n = refl

+-rightSuc' : ∀(n m : ℕ) → n + suc m ≡ suc (n + m)
+-rightSuc' zero m = refl
+-rightSuc' (suc n) m rewrite +-rightSuc' n m = refl

+-commut' : ∀(m n : ℕ) → m + n ≡ n + m
+-commut' m zero rewrite +-rightIdentity' m = refl
+-commut' m (suc n) rewrite +-rightSuc' m n | +-commut' m n = refl

+-swap : ∀(n m k : ℕ) → n + (m + k) ≡ m + (n + k)
+-swap n m k =
  begin
    n + (m + k)
  ≡⟨ sym (+-assoc n m k) ⟩
    (n + m) + k
  ≡⟨ cong (_+ k) (+-commut n m) ⟩
    (m + n) + k
  ≡⟨ +-assoc m n k ⟩
    m + (n + k)
  ∎

*-rightZero : ∀(n : ℕ) → n * 0 ≡ 0
*-rightZero zero = refl
*-rightZero (suc n) = *-rightZero n

*-leftIdentity : ∀(n : ℕ) → 1 * n ≡ n
*-leftIdentity zero = refl
*-leftIdentity (suc n) rewrite (*-leftIdentity n) = refl

*-rightSuc : ∀(n m : ℕ) → n * suc m ≡ n + n * m
*-rightSuc zero m =
  begin
    zero * suc m
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * m
  ≡⟨⟩
    zero + zero * m
  ∎
*-rightSuc (suc n) m rewrite (*-rightSuc n m) | (+-swap m n (n * m)) = refl
-- long proof:
--  begin
--    suc n * suc m
--  ≡⟨⟩
--    suc m + n * suc m
--  ≡⟨⟩
--    suc (m + n * suc m)
--  ≡⟨ cong suc (cong (m +_) (*-rightSuc n m)) ⟩
--    suc (m + (n + n * m))
--  ≡⟨ cong suc (+-swap m n (n * m)) ⟩
--    suc (n + (m + n * m))
--  ≡⟨⟩
--    suc (n + suc n * m)
--  ≡⟨⟩
--    suc n + suc n * m
--  ∎


*-commut : ∀ (n m : ℕ) → n * m ≡ m * n
*-commut zero m rewrite *-rightZero m = refl
*-commut (suc n) m rewrite *-commut n m | sym (*-rightSuc m n) = refl
-- long proof:
--  begin
--   suc n * m
--  ≡⟨⟩
--    m + n * m
--  ≡⟨ cong (m +_) (*-commut' n m) ⟩
--    m + m * n
--  ≡⟨ sym (*-rightSuc m n) ⟩
--    m * suc n
--  ∎
