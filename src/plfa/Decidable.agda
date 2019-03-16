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
open _⇔_ using (to; from)

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

_≤?′_ : ∀ (n m : ℕ) → Dec (n ≤ m)
n ≤?′ m
  with n ≤ᵇ m | ≤ᵇ→≤ {n} {m} | ≤→≤ᵇ {n} {m}
...  | true  | y | _ = yes (y tt)
...  | false | _ | z = no λ n≤m → z n≤m

⌊_⌋ : ∀{A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no x ⌋ = false

_≤ᵇ'_ : ℕ → ℕ → Bool
m ≤ᵇ' n = ⌊ m ≤? n ⌋

toWitness : ∀{A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {_} {yes x} _ = x
toWitness {_} {no ¬x} ()

fromWitness : ∀{A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {_} {yes _} _ = tt
fromWitness {_} {no ¬x} x = ¬x x

≤ᵇ'→≤ : ∀{n m : ℕ} → T (n ≤ᵇ' m) → n ≤ m
≤ᵇ'→≤ = toWitness

≤→≤ᵇ' : ∀{n m : ℕ} → n ≤ m → T (n ≤ᵇ' m)
≤→≤ᵇ' = fromWitness

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true  = true
_    ∧ _     = false

infixr 6 _×-dec_

_×-dec_ : ∀{A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , _ ⟩ → ¬x x}
_     ×-dec no ¬y = no λ{ ⟨ _ , y ⟩ → ¬y y}

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
false ∨ false  = false
_     ∨ _      = true

infixr 5 _⊎-dec_

_⊎-dec_ : ∀{A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x  ⊎-dec _      = yes (inj₁ x)
_      ⊎-dec yes y  = yes (inj₂ y)
no ¬x  ⊎-dec no ¬y  = no λ{ (inj₁ x) → ¬x x
                          ; (inj₂ y) → ¬y y}

not : Bool → Bool
not true = false
not false = true

-- I think "contradiction" is more suitable than "¬¬-intro"
¬? : ∀{A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no x) = yes x

_⊃_ : Bool → Bool → Bool
true ⊃ false = false
_    ⊃ _     = true

_→-dec_ : ∀{A B : Set} → Dec A → Dec B → Dec (A → B)
yes x →-dec no ¬y = no λ A→B → ¬y (A→B x)
_     →-dec yes y = yes (λ _ → y)
no ¬x →-dec _     = yes λ x → ⊥-elim (¬x x)

∧-× : ∀{A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no y) = refl
∧-× (no x) (yes y) = refl
∧-× (no x) (no y) = refl

∨-× : ∀{A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-× (yes x) (yes y) = refl
∨-× (yes x) (no y) = refl
∨-× (no x) (yes y) = refl
∨-× (no x) (no y) = refl

not-¬ : ∀{A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no x) = refl

_⇔b_ : Bool → Bool → Bool
true  ⇔b true  = true
false ⇔b false = true
_     ⇔b _     = false

_⇔-dec_ : ∀{A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x  ⇔-dec yes y = yes (record { to = λ _ → y; from = λ _ → x })
no ¬x  ⇔-dec no ¬y = yes (record { to = λ x → ⊥-elim (¬x x) ; from = λ y → ⊥-elim (¬y y) })
no ¬x  ⇔-dec yes y = no λ A⇔B → ¬x (from A⇔B y)
yes x  ⇔-dec no ¬y = no λ A⇔B → ¬y (to A⇔B x)

⇔b-⇔ : ∀{A B : Set} → (x : Dec A) → (y : Dec B) → ⌊ x ⌋ ⇔b ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
⇔b-⇔ (yes x) (yes y) = refl
⇔b-⇔ (no x) (no y) = refl
⇔b-⇔ (yes x) (no y) = refl
⇔b-⇔ (no x) (yes y) = refl
