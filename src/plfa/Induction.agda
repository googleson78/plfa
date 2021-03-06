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

*-rightIdentity : ∀(n : ℕ) → n * 1 ≡ n
*-rightIdentity n =
  begin
    n * 1
  ≡⟨ *-commut n 1 ⟩
    1 * n
  ≡⟨ *-leftIdentity n ⟩
    n
  ∎

*-distrib-+ : ∀(n m k : ℕ) → n * (m + k) ≡ n * m + n * k
*-distrib-+ zero m k = refl
*-distrib-+ (suc n) m k =
  begin
    suc n * (m + k)
  ≡⟨⟩
    (m + k) + n * (m + k)
  ≡⟨ cong ((m + k) +_) (*-distrib-+ n m k) ⟩
    m + k + (n * m + n * k)
  ≡⟨ +-assoc m k (n * m + n * k) ⟩
    m + (k + (n * m + n * k))
  ≡⟨ cong (m +_) (+-swap k (n * m) (n * k)) ⟩
    m + (n * m + (k + n * k))
  ≡⟨ sym (+-assoc m (n * m) (k + n * k)) ⟩
    (m + n * m) + (k + n * k)
  ≡⟨⟩
    suc n * m + suc n * k
  ∎

*-assoc : ∀(n m k : ℕ) → (n * m) * k ≡ n * (m * k)
*-assoc zero m k    = refl
*-assoc (suc n) m k =
  begin
    (suc n * m) * k
  ≡⟨⟩
    (m + n * m) * k
  ≡⟨ *-commut (m + n * m) k ⟩
    k * (m + n * m)
  ≡⟨ *-distrib-+ k m (n * m) ⟩
    k * m + k * (n * m)
  ≡⟨ cong (_+ (k * (n * m))) (*-commut k m) ⟩
    m * k + k * (n * m)
  ≡⟨ cong ((m * k) +_) (*-commut k (n * m)) ⟩
    m * k + (n * m) * k
  ≡⟨ cong ((m * k) +_) (*-assoc n m k) ⟩
    m * k + n * (m * k)
  ≡⟨⟩
    suc n * (m * k)
  ∎

∸-leftIdentity : ∀(n : ℕ) → 0 ∸ n ≡ 0
∸-leftIdentity zero = refl
∸-leftIdentity (suc _) = refl

∸-+-assoc : ∀(n m k : ℕ) → n ∸ m ∸ k ≡ n ∸ (m + k)
∸-+-assoc zero m k rewrite ∸-leftIdentity m | ∸-leftIdentity k | ∸-leftIdentity (m + k) = refl
∸-+-assoc (suc n) zero k =
  begin
    suc n ∸ zero ∸ k
  ≡⟨⟩
    suc n ∸ k
  ≡⟨⟩
    suc n ∸ (zero + k)
  ∎
∸-+-assoc (suc n) (suc m) k =
  begin
    suc n ∸ suc m ∸ k
  ≡⟨⟩
    n ∸ m ∸ k
  ≡⟨ ∸-+-assoc n m k ⟩
    n ∸ (m + k)
  ∎

data Bin : Set where
  nil : Bin
  c0_ : Bin → Bin
  c1_ : Bin → Bin

inc : Bin → Bin
inc nil    = c1 nil
inc (c0 x) = c1 x
inc (c1 x) = c0 (inc x)

to : ℕ → Bin
to zero        = c0 nil
to (suc x)    = inc (to x)

from : Bin → ℕ
from nil    = 0
from (c0 x) = 2 * from x
from (c1 x) = 1 + 2 * from x

from-homomorphism : ∀(x : Bin) → from (inc x) ≡ suc (from x)
from-homomorphism nil =
  begin
    from (inc nil)
  ≡⟨⟩
    from (c1 nil)
  ≡⟨⟩
    1
  ≡⟨⟩
    suc 0
  ≡⟨⟩
    suc (from nil)
  ∎
from-homomorphism (c0 x) =
  begin
    from (inc (c0 x))
  ≡⟨⟩
    from (c1 x)
  ≡⟨⟩
    suc (2 * from x)
  ≡⟨⟩
    suc (from (c0 x))
  ∎
from-homomorphism (c1 x) =
  begin
    from (inc (c1 x))
  ≡⟨⟩
    from (c0 (inc x))
  ≡⟨⟩
    2 * (from (inc x))
  ≡⟨ cong (2 *_) (from-homomorphism x) ⟩
    2 * (1 + (from x))
  ≡⟨ *-distrib-+ 2 1 (from x) ⟩
    (2 * 1) + 2 * from x
  ≡⟨ cong (_+ (2 * from x)) (*-rightIdentity 2) ⟩
    2 + 2 * from x
  ≡⟨⟩
    suc 1 + 2 * from x
  ≡⟨⟩
    1 + 1 + 2 * from x
  ≡⟨ +-assoc 1 1 (2 * from x) ⟩
    1 + (1 + (2 * from x))
  ≡⟨⟩
    suc (suc (2 * from x))
  ≡⟨⟩
    suc (from (c1 x))
  ∎

_ : to (from nil) ≡ c0 nil
_ = refl

fromToIsId : ∀{n : ℕ} → from (to n) ≡ n
fromToIsId {zero} = refl
fromToIsId {suc n} rewrite from-homomorphism (to n) | fromToIsId {n} = refl
