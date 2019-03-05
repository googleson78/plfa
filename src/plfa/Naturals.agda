module plfa.Naturals where

-- Natural numbers.
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Seven

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

eight : ℕ
eight = 8

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ (x + y)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    succ (succ zero) + succ (succ (succ zero))
  ≡⟨⟩
    succ (succ zero + succ (succ (succ zero)))
  ≡⟨⟩
    succ (succ (zero + succ (succ (succ zero))))
  ≡⟨⟩
    succ (succ (succ (succ (succ zero))))
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    succ 1 + 3
  ≡⟨⟩
    succ (succ 0 + 3)
  ≡⟨⟩
    succ (succ (zero + 3))
  ≡⟨⟩
    succ (succ 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    succ 2 + 4
  ≡⟨⟩
    succ (2 + 4)
  ≡⟨⟩
    succ (succ 1 + 4)
  ≡⟨⟩
    succ (succ (1 + 4))
  ≡⟨⟩
    succ (succ (succ zero + 4))
  ≡⟨⟩
    succ (succ (succ (zero + 4)))
  ≡⟨⟩
    (succ (succ (succ 4)))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero   * y = zero
succ x * y = y + (x * y)

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    succ 2 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (succ 1 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (succ zero * 4))
  ≡⟨⟩
    4 + (4 + (4 + (zero * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ succ y = x * (x ^ y)

_ : 2 ^ 3 ≡ 8
_ =
  begin
    2 ^ 3
  ≡⟨⟩
    2 ^ succ 2
  ≡⟨⟩
    2 * (2 ^ 2)
  ≡⟨⟩
    2 * (2 ^ succ 1)
  ≡⟨⟩
    2 * (2 * (2 ^ 1))
  ≡⟨⟩
    2 * (2 * (2 ^ succ zero))
  ≡⟨⟩
    2 * (2 * (2 * (2 ^ zero)))
  ≡⟨⟩
    2 * (2 * (2 * 1))
  ≡⟨⟩
    8
  ∎

_∸_ : ℕ → ℕ → ℕ
x      ∸ zero   = x
zero   ∸ succ y = zero
succ x ∸ succ y = x ∸ y

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    succ 4 ∸ succ 2
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    succ 3 ∸ succ 1
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    succ 2 ∸ succ 0
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩ -- pattern match
    succ 2 ∸ succ 4
  ≡⟨⟩ -- case 2
    2 ∸ 4
  ≡⟨⟩ -- pattern match
    succ 1 ∸ succ 3
  ≡⟨⟩ -- case 2
    1 ∸ 3
  ≡⟨⟩ -- pattern match
    succ 0 ∸ succ 2
  ≡⟨⟩ -- case 2
    0 ∸ 2
  ≡⟨⟩ -- case 1
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  c0_ : Bin → Bin
  c1_ : Bin → Bin

inc : Bin → Bin
inc nil    = c1 nil
inc (c0 x) = c1 x
inc (c1 x) = c0 (inc x)

_ : inc (c1 c1 nil) ≡ c0 c0 c1 nil
_ =
  begin
    inc (c1 c1 nil)
  ≡⟨⟩
    c0 (inc (c1 nil))
  ≡⟨⟩
    c0 c0 (inc nil)
  ≡⟨⟩
    c0 c0 c1 nil
  ∎

-- 0 → 1
_ : inc (c0 nil) ≡ c1 nil
_ =
  begin
    inc (c0 nil)
  ≡⟨⟩
    c1 nil
  ∎

-- 1 → 2
_ : inc (c1 nil) ≡ c0 c1 nil
_ =
  begin
    inc (c1 nil)
  ≡⟨⟩
    c0 (inc nil)
  ≡⟨⟩
    c0 c1 nil
  ∎

-- 2 → 3
_ : inc (c0 c1 nil) ≡ c1 c1 nil
_ =
  begin
    inc (c0 c1 nil)
  ≡⟨⟩
    c1 c1 nil
  ∎

-- 3 → 4
_ : inc (c1 c1 nil) ≡ c0 c0 c1 nil
_ =
  begin
    inc (c1 c1 nil)
  ≡⟨⟩
    c0 (inc (c1 nil))
  ≡⟨⟩
    c0 c0 (inc nil)
  ≡⟨⟩
    c0 c0 c1 nil
  ∎

to : ℕ → Bin
to zero        = c0 nil
to (succ x)    = inc (to x)

_ : to 0 ≡ c0 nil
_ =
  begin
    to zero
  ≡⟨⟩
    c0 nil
  ∎

_ : to 1 ≡ c1 nil
_ =
  begin
    to (succ zero)
  ≡⟨⟩
    c1 nil
  ∎

_ : to 3 ≡ c1 c1 nil
_ =
  begin
    to (succ 2)
  ≡⟨⟩
    inc (to 2)
  ≡⟨⟩
    inc (inc (to 1))
  ≡⟨⟩
    inc (inc (inc (to zero)))
  ≡⟨⟩
    inc (inc (inc (c0 nil)))
  ≡⟨⟩
    inc (inc (c1 nil))
  ≡⟨⟩
    inc (c0 c1 nil)
  ≡⟨⟩
    c1 c1 nil
  ∎

from : Bin → ℕ
from nil    = 0
from (c0 x) = 2 * from x
from (c1 x) = 1 + 2 * from x

_ : from (c0 nil) ≡ 0
_ =
  begin
    from (c0 nil)
  ≡⟨⟩
    2 * (from nil)
  ≡⟨⟩
    2 * 0
  ≡⟨⟩
    0
  ∎

_ : from (c1 nil) ≡ 1
_ =
  begin
    from (c1 nil)
  ≡⟨⟩
    1 + 2 * from nil
  ≡⟨⟩
    1 + 2 * 0
  ≡⟨⟩
    1 + 0
  ≡⟨⟩
    1
  ∎

_ : from (c0 c1 nil) ≡ 2
_ =
  begin
    from (c0 c1 nil)
  ≡⟨⟩
    2 * from (c1 nil)
  ≡⟨⟩
    2 * (1 + 2 * from nil)
  ≡⟨⟩
    2 * (1 + 2 * 0)
  ≡⟨⟩
    2 * (1 + 0)
  ≡⟨⟩
    2 * 1
  ≡⟨⟩
    2
  ∎

_ : from (c1 c1 nil) ≡ 3
_ =
  begin
    from (c1 c1 nil)
  ≡⟨⟩
    1 + 2 * from (c1 nil)
  ≡⟨⟩
    1 + 2 * (1 + 2 * from nil)
  ≡⟨⟩
    1 + 2 * (1 + 2 * 0)
  ≡⟨⟩
    1 + 2 * 1
  ≡⟨⟩
    1 + 2
  ≡⟨⟩
    3
  ∎

_ : from (c0 c0 c1 nil) ≡ 4
_ =
  begin
    from (c0 c0 c1 nil)
  ≡⟨⟩
    2 * from (c0 c1 nil)
  ≡⟨⟩
    2 * 2 * from (c1 nil)
  ≡⟨⟩
    2 * 2 * (1 + 2 * from nil)
  ≡⟨⟩
    2 * 2 * (1 + 2 * 0)
  ≡⟨⟩
    2 * 2 * (1 + 0)
  ≡⟨⟩
    2 * 2 * 1
  ≡⟨⟩
    4
  ∎
