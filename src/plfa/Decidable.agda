module plfa.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; foldr; map)
open import Function using (_∘_)
open import plfa.Relations using (_≤_; z≤n; s≤s; _<_; z<s; s<s)
open import plfa.Isomorphism using (_⇔_)

infix 4 _≤ᵇ_

data Bool : Set where
  true : Bool
  false : Bool

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
(suc _) ≤ᵇ zero = false
(suc n) ≤ᵇ (suc m) = n ≤ᵇ m

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀{b : Bool} → T b → b ≡ true
T→≡ {true} x = refl
T→≡ {false} ()

≡→T : ∀{b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀{n m : ℕ} → T (n ≤ᵇ m) → n ≤ m
≤ᵇ→≤ {zero} {m} tt = z≤n
≤ᵇ→≤ {suc n} {zero} ()
≤ᵇ→≤ {suc n} {suc m} nm = s≤s (≤ᵇ→≤ {n} {m} nm)

≤→≤ᵇ : ∀{n m : ℕ} → n ≤ m → T (n ≤ᵇ m)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s nm) = ≤→≤ᵇ nm

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀{n : ℕ} → ¬ (suc n ≤ zero)
¬s≤z ()

¬s≤s : ∀{n m : ℕ} → ¬ (n ≤ m) → ¬ (suc n ≤ suc m)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀(n m : ℕ) → Dec (n ≤ m)
zero ≤? n = yes z≤n
suc n ≤? zero = no ¬s≤z
suc n ≤? suc m
  with n ≤? m
...  | yes n≤m = yes (s≤s n≤m)
...  | no ¬n≤m = no (¬s≤s ¬n≤m)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬n<n : ∀{n : ℕ} → ¬ (n < n)
¬n<n (s<s n<n) = ¬n<n n<n

¬s<z : ∀{n : ℕ} → ¬ (suc n < zero)
¬s<z ()

¬s<s : ∀{n m : ℕ} → ¬ (n < m) → ¬ (suc n < suc m)
¬s<s ¬n<m (s<s n<m) = ¬n<m n<m

_<?_ : ∀(n m : ℕ) → Dec (n < m)
zero <? zero = no ¬n<n
zero <? suc m = yes z<s
suc n <? zero = no ¬s<z
suc n <? suc m
  with n <? m
...  | yes n<m = yes (s<s n<m)
...  | no ¬n<m = no (¬s<s ¬n<m)

¬z≡s : ∀{n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s ()

¬s≡z : ∀{n : ℕ} → ¬ (suc n ≡ zero)
¬s≡z ()

¬s≡s : ∀{n m : ℕ} → ¬ (n ≡ m) → ¬ (suc n ≡ suc m)
¬s≡s nm refl = nm refl

_≡ℕ?_ : ∀(n m : ℕ) → Dec (n ≡ m)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc m = no ¬z≡s
suc n ≡ℕ? zero = no ¬s≡z
suc n ≡ℕ? suc m
  with n ≡ℕ? m
...  | yes n≡m = yes (cong suc n≡m)
...  | no ¬n≡m = no (¬s≡s ¬n≡m)
