module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc)
open import Function using (_∘_)
open import plfa.Isomorphism
  using ( _≃_; ≃-sym; ≃-trans; _≼_; extensionality
        ; _⇔_)
open plfa.Isomorphism.≃-Reasoning
open plfa.Isomorphism._⇔_


infixr 2 _×_

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀{A B : Set} → A × B → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀{A B : Set} → A × B → B
proj₂ ⟨ _ , y ⟩ = y

swap : ∀{A B : Set} → A × B → B × A
swap ⟨ x , y ⟩ = ⟨ y , x ⟩

η-× : ∀{A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = swap
    ; from = swap
    ; from∘to = λ { {⟨ x , y ⟩} → refl }
    ; to∘from = λ { {⟨ x , y ⟩} → refl }
    }

×-assoc : ∀{A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ {⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
    ; from = λ {⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
    ; from∘to = λ { {⟨ ⟨ x , y ⟩ , z ⟩} → refl}
    ; to∘from = λ { {⟨ x , ⟨ y , z ⟩ ⟩} → refl}
    }

⇔≃× : ∀{A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ A⇔B → ⟨ to A⇔B , from A⇔B ⟩
    ; from = λ{⟨ A→B , B→A ⟩ →
        record
          { to = A→B
          ; from = B→A
          }}
    ; from∘to = λ{ {record
                      { to = A→B
                      ; from = B→A
                      }} → refl}
    ; to∘from = λ{ {⟨ x , y ⟩} → refl}
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀(w : ⊤) → tt ≡ w
η-⊤ tt = refl

×-identity-left : ∀{A : Set} → ⊤ × A ≃ A
×-identity-left =
  record
    { to = λ{ ⟨ _ , x ⟩ → x}
    ; from = λ{ x → ⟨ tt , x ⟩}
    ; from∘to = λ{ {⟨ tt , x ⟩} → refl}
    ; to∘from = λ{ {x} → refl}
    }

×-identity-right : ∀{A : Set} → A × ⊤ ≃ A
×-identity-right {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ×-identity-left ⟩
    A
  ≃-∎
