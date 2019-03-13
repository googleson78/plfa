module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≼_; extensionality)

open import plfa.Relations using (_<_; z<s; s<s)

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

id : ∀{A : Set} → A → A
id x = x

¬-elim : ∀{A : Set} → ¬ A → A → ⊥
¬-elim = id

¬¬-intro : ∀{A : Set} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬-elim ¬x x

¬¬¬-elim : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀{A B : Set} → (A → B) → ¬ B → ¬ A
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀{A : Set} → A → A → Set
A ≢ B = ¬ A ≡ B

_ : 1 ≢ 2
_ = λ ()

-- bogus
assimilation : ∀{A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x _ = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀{n : ℕ} → ¬ n < n
<-irreflexive (s<s n<n) = <-irreflexive n<n

<-s<s-preserves-¬ : ∀{n m : ℕ} → ¬ (n < m) → ¬ (suc n < suc m)
<-s<s-preserves-¬ ¬n<m (s<s n<m) = ¬n<m n<m

<-trichotomy : ∀{n m : ℕ}
             →   n < m × ¬ n ≡ m × ¬ m < n
             ⊎ ¬ n < m ×   n ≡ m × ¬ m < n
             ⊎ ¬ n < m × ¬ n ≡ m ×   m < n
<-trichotomy {zero} {zero} = inj₂ (inj₁ ⟨ (λ ()) , ⟨ refl , (λ ()) ⟩ ⟩)
<-trichotomy {zero} {suc m} = inj₁ ⟨ z<s , ⟨ (λ ()) , (λ ()) ⟩ ⟩
<-trichotomy {suc n} {zero} = inj₂ (inj₂ ⟨ (λ ()) , ⟨ (λ ()) , z<s ⟩ ⟩)
<-trichotomy {suc n} {suc m}
    with <-trichotomy {n} {m}
...    | inj₁ ⟨ n<m , ⟨ ¬n≡m , ¬m<n ⟩ ⟩ = inj₁ ⟨ s<s n<m , ⟨ (λ{ refl → ¬n≡m refl }) , <-s<s-preserves-¬ ¬m<n ⟩ ⟩
...    | inj₂ (inj₁ ⟨ ¬n<m , ⟨ refl , ¬m<n ⟩ ⟩) = inj₂ (inj₁ ⟨ <-irreflexive , ⟨ refl , <-irreflexive ⟩ ⟩)
...    | inj₂ (inj₂ ⟨ ¬n<m , ⟨ ¬n≡m , m<n ⟩ ⟩) = inj₂ (inj₂ ⟨ <-s<s-preserves-¬ ¬n<m , ⟨ (λ{ refl → ¬n≡m refl }) , s<s m<n ⟩ ⟩)

→-distrib-⊎ : ∀{A B C : Set} → ((A ⊎ B) → C) ≃ (A → C) × (B → C)
→-distrib-⊎ =
  record
    { to = λ f → ⟨ (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)) ⟩
    ; from = λ{ f (inj₁ x) → proj₁ f x
              ; f (inj₂ y) → proj₂ f y
              }
    ; from∘to = extensionality λ{ (inj₁ x) → refl
                                ; (inj₂ y) → refl
                                }
    ; to∘from = refl
    }

-- this is true in general, not just for ⊥ as witnessed above
⊎-dual-× : ∀{A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

-- we need stabbing for the other direction
⊎¬-implies-¬× : ∀{A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
⊎¬-implies-¬× (inj₁ ¬x) ⟨ x , _ ⟩ = ¬x x
⊎¬-implies-¬× (inj₂ ¬y) ⟨ _ , y ⟩ = ¬y y

lem-irrefutable : ∀{A : Set} → ¬ ¬ (A ⊎ ¬ A)
lem-irrefutable f = f (inj₂ λ x → f (inj₁ x))

lem-implies-stab : (∀{A : Set} → (A ⊎ ¬ A)) → ∀{A : Set} → (¬ ¬ A) → A
lem-implies-stab lem {A} ¬¬x
  with lem {A}
...  | (inj₁ x)  = x
...  | (inj₂ ¬x) = ⊥-elim (¬¬x ¬x)

-- wtf
stab-implies-peirce : (∀{A : Set} → (¬ ¬ A) → A) → ∀{A B : Set} → ((A → B) → A) → A
stab-implies-peirce stab f = stab (λ ¬A → ¬A (f λ A → ⊥-elim (¬A A)))

peirce-implies-→-as-⊎ : (∀{A B : Set} → ((A → B) → A) → A) → ∀{A B : Set} → (A → B) → ¬ A ⊎ B
peirce-implies-→-as-⊎ peirce A→B = peirce λ x → inj₁ λ A → x (inj₂ (A→B A))

⊎-elim : ∀{A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
⊎-elim f _ (inj₁ x) = f x
⊎-elim _ g (inj₂ y) = g y

→-as-⊎-implies-lem : (∀{A B : Set} → (A → B) → (¬ A) ⊎ B) → ∀{A : Set} → A ⊎ ¬ A
→-as-⊎-implies-lem →-as-⊎
  with (→-as-⊎ id)
...  | inj₁ ¬x = inj₂ ¬x
...  | inj₂ x = inj₁ x

stab-implies-de-morgan : (∀{A : Set} → ¬ ¬ A → A) → ∀{A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
stab-implies-de-morgan stab ¬¬A×¬B
  = stab λ ¬A⊎B → ¬¬A×¬B ⟨ (λ A → ¬A⊎B (inj₁ A)) , (λ B → ¬A⊎B (inj₂ B)) ⟩

-- -,-
→-as-⊎-implies-de-morgan : (∀{A B : Set} → (A → B) → (¬ A) ⊎ B) → ∀{A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
→-as-⊎-implies-de-morgan = stab-implies-de-morgan ∘ lem-implies-stab ∘ →-as-⊎-implies-lem

de-morgan-implies-→-as-⊎ : (∀{A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) → ∀{A B : Set} → (A → B) → (¬ A) ⊎ B
de-morgan-implies-→-as-⊎ de-morgan f = de-morgan (λ z → proj₁ z (λ x → proj₂ z (f x)))

de-morgan-implies-lem : (∀{A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) → ∀{A : Set} → A ⊎ ¬ A
de-morgan-implies-lem de-morgan = de-morgan λ{ ⟨ ¬A , ¬¬A ⟩ → ¬¬A ¬A }

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀{A : Set} → Stable (¬ A)
¬-stable ¬¬A A = ¬¬A (¬¬-intro A)

×-stability : ∀{A B : Set} → Stable A → Stable B → Stable (A × B)
×-stability stabA stabB ¬¬A×B
  = ⟨ stabA (λ ¬A → ¬¬A×B λ{ ⟨ A , _ ⟩ → ¬A A})
    , stabB (λ ¬B → ¬¬A×B λ{ ⟨ _ , B ⟩ → ¬B B})
    ⟩

¬A×¬B-iso-¬A⊎B : ∀{A B : Set} → ¬ A × ¬ B ≃ ¬ (A ⊎ B)
¬A×¬B-iso-¬A⊎B =
  record { to = λ{ ⟨ ¬A , ¬B ⟩ (inj₁ A) → ¬A A
                 ; ⟨ ¬A , ¬B ⟩ (inj₂ B) → ¬B B
                 }
         ; from = λ ¬A⊎B → ⟨ (λ A → ¬A⊎B (inj₁ A)) , (λ B → ¬A⊎B (inj₂ B)) ⟩
         ; from∘to = refl
         ; to∘from = extensionality λ{ (inj₁ _) → refl
                                     ; (inj₂ _) → refl}
                                     }
