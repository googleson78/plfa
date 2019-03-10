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
    ; from∘to = λ{ {⟨ x , y ⟩} → refl }
    ; to∘from = λ{ {⟨ x , y ⟩} → refl }
    }

×-assoc : ∀{A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
    ; from = λ{⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
    ; from∘to = λ{ {⟨ ⟨ x , y ⟩ , z ⟩} → refl}
    ; to∘from = λ{ {⟨ x , ⟨ y , z ⟩ ⟩} → refl}
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

infixr 1 _⊎_

data _⊎_ : Set → Set → Set where
  inj₁ : ∀{A B : Set} → A → A ⊎ B
  inj₂ : ∀{A B : Set} → B → A ⊎ B

case-⊎ : ∀{A B C : Set}
       → (A → C)
       → (B → C)
       → A ⊎ B
       → C
case-⊎ f _ (inj₁ x) = f x
case-⊎ _ g (inj₂ y) = g y

η-⊎ : ∀{A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ _) = refl
η-⊎ (inj₂ _) = refl

uniq-⊎ : ∀{A B C : Set} (f : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (f ∘ inj₁) (f ∘ inj₂) w ≡ f w
uniq-⊎ f (inj₁ _) = refl
uniq-⊎ f (inj₂ _) = refl

⊎-comm : ∀{A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = case-⊎ inj₂ inj₁
    ; from = case-⊎ inj₂ inj₁
    ; from∘to = λ{ {inj₁ _} → refl
                 ; {inj₂ _} → refl
                 }
    ; to∘from = λ{ {inj₁ _} → refl
                 ; {inj₂ _} → refl
                 }
    }

⊎-assoc : ∀{A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = case-⊎ (case-⊎ inj₁ (inj₂ ∘ inj₁)) (inj₂ ∘ inj₂)
    ; from = case-⊎ (inj₁ ∘ inj₁) (case-⊎ (inj₁ ∘ inj₂) inj₂)
    ; from∘to = λ{ {inj₁ (inj₁ _)} → refl
                 ; {inj₁ (inj₂ _)} → refl
                 ; {inj₂ _} → refl
                 }
    ; to∘from = λ{ {inj₁ _} → refl
                 ; {inj₂ (inj₁ _)} → refl
                 ; {inj₂ (inj₂ _)} → refl
                 }
    }

data ⊥ : Set where

efq : ∀{A : Set} → ⊥ → A
efq ()

id : ∀{A : Set} → A → A
id x = x

⊎-identity-left : ∀{A : Set} → ⊥ ⊎ A ≃ A
⊎-identity-left =
  record
    { to = case-⊎ efq id
    ; from = inj₂
    ; from∘to = λ{ {inj₁ ()}
                 ; {inj₂ y} → refl
                 }
    ; to∘from = λ {_} → refl
    }

⊎-identity-right : ∀{A : Set} → A ⊎ ⊥ ≃ A
⊎-identity-right {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊎-identity-left ⟩
    A
  ≃-∎

infixr 1 _$_

_$_ : ∀{A B : Set} → (A → B) → A → B
f $ x = f x

η-→ : ∀{A B : Set} → (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

curry : ∀{A B C : Set} → (A × B → C) → A → B → C
curry f x y = f ⟨ x , y ⟩

uncurry : ∀{A B C : Set} → (A → B → C) → A × B → C
uncurry f ⟨ x , y ⟩ = f x y

currying : ∀{A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ{ f ⟨ x , y ⟩ → f x y }
    ; from = curry
    ; from∘to = λ {f} → refl
    ; to∘from = λ {f} → extensionality λ{ ⟨ x , y ⟩ → refl }
    }

→-distrib-⊎ : ∀{A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-distrib-⊎ =
  record
    { to = λ f → ⟨ (f ∘ inj₁) , (f ∘ inj₂) ⟩
    ; from = λ{ ⟨ f , g ⟩ → case-⊎ f g }
    ; from∘to = λ{ {f} → extensionality
                          λ{ (inj₁ x) → refl
                           ; (inj₂ y) → refl
                           } }
    ; to∘from = λ{ {⟨ f , g ⟩} → refl }
    }

→-distrib-× : ∀{A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from = λ{ ⟨ f , g ⟩ x → ⟨ f x , g x ⟩ }
    ; from∘to = λ{ {f} → extensionality (η-× ∘ f) }
    ; to∘from = λ{ {⟨ f , g ⟩} → refl }
    }

×-distrib-⊎ : ∀{A B C : Set} → A × (B ⊎ C) ≃ A × B ⊎ A × C
×-distrib-⊎ =
  record
    { to = λ{ ⟨ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
            ; ⟨ x , inj₂ z ⟩ → inj₂ ⟨ x , z ⟩
            }
    ; from = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ x , inj₁ y ⟩
              ; (inj₂ ⟨ x , z ⟩) → ⟨ x , inj₂ z ⟩
              }
    ; from∘to = λ{ {⟨ x , inj₁ y ⟩} → refl
                 ; {⟨ x , inj₂ z ⟩} → refl
                 }
    ; to∘from = λ{ {(inj₁ ⟨ x , y ⟩)} → refl
                 ; {(inj₂ ⟨ x , z ⟩)} → refl
                 }
    }

-- not an iso, instead only an embedding
⊎-distrib-× : ∀{A B C : Set} → A × B ⊎ C ≼ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
            ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
            }
    ; from = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
              ; ⟨ inj₁ _ , inj₂ z ⟩ → inj₂ z
              ; ⟨ inj₂ z , inj₁ _ ⟩ → inj₂ z
              ; ⟨ inj₂ z , inj₂ _ ⟩ → inj₂ z
              }
    ; from∘to = λ{ {inj₁ ⟨ x , y ⟩} → refl
                 ; {inj₂ z} → refl
                 }
    }

-- don't know which "corresponding distributive law" this is referring to
⊎-weak-× : ∀{A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩
