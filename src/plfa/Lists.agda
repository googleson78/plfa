module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ;
   *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_; extensionality)


data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : ∀{A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

++-assoc : ∀{A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identity-left : ∀{A : Set} → {xs : List A} → [] ++ xs ≡ xs
++-identity-left = refl

++-identity-right : ∀{A : Set} → {xs : List A} → xs ++ [] ≡ xs
++-identity-right {_} {[]} = refl
++-identity-right {_} {x ∷ xs} = cong (x ∷_) ++-identity-right

length : ∀{A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀{A : Set} (xs ys : List A)→ length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀{A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-commute : ∀{A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute [] ys = sym ++-identity-right
reverse-++-commute (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀{A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute (reverse xs) [ x ] ⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

shunt : ∀{A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀{A : Set} → (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ x ∷ ys
  ≡⟨⟩
    reverse xs ++ [ x ] ++ ys
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

fast-reverse : ∀{A : Set} → List A → List A
fast-reverse xs = shunt xs []

fast-reverse-is-reverse : ∀{A : Set} → (xs : List A) → fast-reverse xs ≡ reverse xs
fast-reverse-is-reverse [] = refl
fast-reverse-is-reverse (x ∷ xs) = shunt-reverse xs [ x ]

map : ∀{A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-compose-pointful : ∀{A B C : Set}
                        (f : A → B) (g : B → C)
                        (xs : List A)
                     → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-pointful f g [] = refl
map-compose-pointful f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (map-compose-pointful f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    g (f x) ∷ map g (map f xs)
  ≡⟨⟩
    map g (f x ∷ map f xs)
  ≡⟨⟩
    map g (map f (x ∷ xs))
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

map-compose : ∀{A B C : Set}
               {f : A → B} {g : B → C}
            → map (g ∘ f) ≡ map g ∘ map f
map-compose {_} {_} {_} {f} {g} =
  begin
    map (g ∘ f)
  ≡⟨⟩
    map (λ x → g (f x))
  ≡⟨ extensionality (map-compose-pointful f g) ⟩
    (λ xs → map g (map f xs))
  ≡⟨⟩
    (map g) ∘ (map f)
  ∎

map-homomorphic-++ : ∀{A B : Set} (f : A → B) (xs ys : List A)
                    → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-homomorphic-++ f [] ys = refl
map-homomorphic-++ f (x ∷ xs) ys =
  begin
    map f (x ∷ xs ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-homomorphic-++ f xs ys) ⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    (f x ∷ map f xs) ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-tree : ∀{A B C D : Set}
         → (A → C) → (B → D)
         → Tree A B → Tree C D
map-tree f _ (leaf x) = leaf (f x)
map-tree f g (node l x r) = node (map-tree f g l) (g x) (map-tree f g r)

foldr : ∀{A B : Set} → (A → B → B) → B → List A → B
foldr _ v [] = v
foldr f v (x ∷ xs) = f x (foldr f v xs)

sum : List ℕ → ℕ
sum = foldr (_+_) 0

product : List ℕ → ℕ
product = foldr (_*_) 1

foldr-++ : ∀{A B : Set}
            (f : A → B → B) (v : B) (xs ys : List A)
         → foldr f (foldr f v ys) xs ≡ foldr f v (xs ++ ys)
foldr-++ f v [] ys = refl
foldr-++ f v (x ∷ xs) ys =
  begin
    foldr f (foldr f v ys) (x ∷ xs)
  ≡⟨⟩
    f x (foldr f (foldr f v ys) xs)
  ≡⟨ cong (f x) (foldr-++ f v xs ys) ⟩
    f x (foldr f v (xs ++ ys))
  ≡⟨⟩
    foldr f v (x ∷ xs ++ ys)
  ≡⟨⟩
    foldr f v ((x ∷ xs) ++ ys)
  ∎

map-is-foldr-pointful : ∀{A B : Set} {f : A → B} (xs : List A) → map f xs ≡ foldr (_∷_ ∘ f) [] xs
map-is-foldr-pointful {_} {_} {f} [] = refl
map-is-foldr-pointful {_} {_} {f} (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    f x ∷ map f xs
  ≡⟨ cong (f x ∷_) (map-is-foldr-pointful xs) ⟩
    f x ∷ foldr (_∷_ ∘ f) [] xs
  ≡⟨⟩
    _∷_ (f x) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    (_∷_ (f x)) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    ((_∷_ ∘ f) x) (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    (_∷_ ∘ f) x (foldr (_∷_ ∘ f) [] xs)
  ≡⟨⟩
    foldr (_∷_ ∘ f) [] (x ∷ xs)
  ∎

map-is-foldr : ∀{A B : Set} {f : A → B} → map f ≡ foldr (_∷_ ∘ f) []
map-is-foldr = extensionality map-is-foldr-pointful

fold-tree : ∀ {A B C : Set}
          → (A → C) → (C → B → C → C) → Tree A B → C
fold-tree f _ (leaf x) = f x
fold-tree f g (node l x r) = g (fold-tree f g l) x (fold-tree f g r)

map-tree-is-fold-tree : ∀{A B C D : Set}
                      → (f : A → C) → (g : B → D)
                      → (t : Tree A B)
                      → map-tree f g t ≡ fold-tree (leaf ∘ f) (λ l x r → node l (g x) r) t
map-tree-is-fold-tree f g (leaf x) = refl
map-tree-is-fold-tree {A} {B} {C} {D} f g (node l x r) =
  begin
    map-tree f g (node l x r)
  ≡⟨⟩
    node (map-tree f g l) (g x) (map-tree f g r)
  ≡⟨ cong (λ l' → node l' (g x) (map-tree f g r)) (map-tree-is-fold-tree f g l) ⟩
    node (fold-tree f' g' l) (g x) (map-tree f g r)
  ≡⟨ cong (λ r' → node (fold-tree f' g' l) (g x) r') (map-tree-is-fold-tree f g r) ⟩
    node (fold-tree f' g' l) (g x) (fold-tree f' g' r)
  ≡⟨⟩
    fold-tree f' g' (node l x r)
  ∎
    where
      f' : ∀{D' : Set} → A → Tree C D'
      f' = leaf ∘ f
      g' : ∀{C' : Set} → Tree C' D → B → Tree C' D → Tree C' D
      g'  l x r = node l (g x) r

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

sum-downFrom : ∀(n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc zero) = refl
sum-downFrom (suc (suc n)) = let n' = suc n in
  begin
    sum (downFrom (suc n')) * 2
  ≡⟨⟩
    sum (n' ∷ downFrom n') * 2
  ≡⟨⟩
    (n' + sum (downFrom n')) * 2
  ≡⟨ *-distribʳ-+ 2 n' (sum (downFrom n')) ⟩
    n' * 2 + sum (downFrom n') * 2
  ≡⟨ cong ((n' * 2) +_) (sum-downFrom n') ⟩
    n' * 2 + n' * (n' ∸ 1)
  ≡⟨ sym (*-distribˡ-+ n' 2 (n' ∸ 1)) ⟩
    n' * (2 + (n' ∸ 1))
  ≡⟨⟩
    n' * (2 + (suc n ∸ 1)) -- we use n' ≥ 1 here
  ≡⟨⟩
    n' * (2 + n)
  ≡⟨⟩
    n' * (suc (suc n))
  ≡⟨⟩
  n' * (suc n')
  ≡⟨ *-comm n' (suc n') ⟩
    suc n' * n'
  ≡⟨⟩
    suc n' * (suc n' ∸ 1)
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀(x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    left-identity : ∀(x : A) → e ⊗ x ≡ x
    right-identity : ∀(x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record { assoc = +-assoc
         ; left-identity = +-identityˡ
         ; right-identity = +-identityʳ
         }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; left-identity = *-identityˡ
    ; right-identity = *-identityʳ
    }

++-monoid : ∀{A : Set} → IsMonoid {List A} _++_ []
++-monoid {A} =
  record
    { assoc = ++-assoc
    ; left-identity = λ x → ++-identity-left {A} {x}
    ; right-identity = λ x → ++-identity-right {A} {x}
    }

foldr-monoid : ∀{A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid {A} _⊗_ e
             → (xs : List A) → (v : A)
             → foldr _⊗_ v xs ≡ foldr _⊗_ e xs ⊗ v
foldr-monoid _⊗_ e ⊗-monoid [] v = sym (left-identity ⊗-monoid v)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) v =
  begin
    x ⊗ foldr _⊗_ v xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs v) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ v)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) v) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ v
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ v
  ∎

foldl : ∀{A B : Set} → (B → A → B) → B → List A → B
foldl _ v [] = v
foldl f v (x ∷ xs) = foldl f (f v x) xs

foldl-monoid-out : ∀{A : Set}
                 → (_⊗_ : A → A → A) → (e : A) → IsMonoid {A} _⊗_ e
                 → (xs : List A) (v : A)
                 → foldl _⊗_ v xs ≡ v ⊗ foldl _⊗_ e xs
foldl-monoid-out _⊗_ e ⊗-monoid [] v = sym (right-identity ⊗-monoid v)
foldl-monoid-out _⊗_ e ⊗-monoid (x ∷ xs) v =
  begin
    foldl _⊗_ v (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (v ⊗ x) xs
  ≡⟨ foldl-monoid-out _⊗_ e ⊗-monoid xs (v ⊗ x) ⟩
    (v ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc ⊗-monoid v x (foldl _⊗_ e xs) ⟩
    v ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (v ⊗_) (sym (foldl-monoid-out _⊗_ e ⊗-monoid xs x)) ⟩
    v ⊗ foldl _⊗_ x xs
  ≡⟨ cong (v ⊗_) (cong (λ y → foldl _⊗_ y xs) (sym (left-identity ⊗-monoid x))) ⟩
    v ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    v ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl : ∀{A : Set}
                   → (_⊗_ : A → A → A) → (e : A) → IsMonoid {A} _⊗_ e
                   → (xs : List A)
                   → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e ⊗-monoid xs) ⟩
    x ⊗ foldl _⊗_ e xs
  ≡⟨ sym (foldl-monoid-out _⊗_ e ⊗-monoid xs x)  ⟩
    foldl _⊗_ x xs
  ≡⟨ sym (cong (λ y → foldl _⊗_ y xs) (left-identity ⊗-monoid x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀{x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀{x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀{x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

All-++-⇔ : ∀{A : Set} {P : A → Set} (xs ys : List A)
         → All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ [] ys =
  record { to = λ p → ⟨ [] , p ⟩
         ; from = λ{ ⟨ [] , Pys ⟩ → Pys}
         }
All-++-⇔ (x ∷ xs) ys =
  record { to = λ{ (Px ∷ p) → ⟨ Px ∷ Data.Product.proj₁ (_⇔_.to (All-++-⇔ xs ys) p) , Data.Product.proj₂ (_⇔_.to (All-++-⇔ xs ys) p)⟩}
         ; from = λ{ ⟨ Px ∷ Pxs , Pys ⟩ → Px ∷ (_⇔_.from  (All-++-⇔ xs ys) ⟨ Pxs , Pys ⟩) }
         }

Any-++-⇔ : ∀{A : Set} {P : A → Set} (xs ys : List A)
         → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P} xs ys =
  record { to = to xs ys
         ; from = from xs ys }
  where
    to : (xs ys : List A) → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
    to [] ys Pxsys = inj₂ Pxsys
    to (x ∷ xs) ys (here px) = inj₁ (here px)
    to (x ∷ xs) ys (there Pxsys)
      with to xs ys Pxsys
    ...  | inj₁ pxs = inj₁ (there pxs)
    ...  | inj₂ pys = inj₂ pys
    from : (xs ys : List A) → Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from [] ys (inj₁ ())
    from [] ys (inj₂ y) = y
    from (x ∷ xs) ys (inj₁ (here px)) = here px
    from (x ∷ xs) ys (inj₁ (there pxs)) = there (from xs ys (inj₁ pxs))
    from (x ∷ xs) ys (inj₂ pys) = there (from xs ys (inj₂ pys))

infix 4 _∈_ _∉_

_∈_ : ∀{A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀{A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

∈-++-⇔ : ∀{A : Set} (xs ys : List A) (x : A)
       → (x ∈ xs ++ ys) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++-⇔ {A} xs ys x = Any-++-⇔ {A} {x ≡_} xs ys

All-++-≃ : ∀{A : Set} {P : A → Set} (xs ys : List A)
         → All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys =
  record { to = to xs ys
         ; from = from xs ys
         ; from∘to = λ {p} → from∘to xs ys p
         ; to∘from = λ {p} → to∘from xs ys p
         }
  where
    to : (xs ys : List A) → All P (xs ++ ys) → All P xs × All P ys
    to [] ys p = ⟨ [] , p ⟩
    to (x ∷ xs) ys (Px ∷ p)
      with to xs ys p
    ...  | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩
    from : (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩
      with from xs ys ⟨ Pxs , Pys ⟩
    ...  | pr = Px ∷ pr
    from∘to : (xs ys : List A) (Pxsys : All P (xs ++ ys)) → from xs ys (to xs ys Pxsys) ≡ Pxsys
    from∘to [] ys Pxsys = refl
    from∘to (x ∷ xs) ys (Px ∷ Pxsys) = cong (Px ∷_) (from∘to xs ys Pxsys)
    to∘from : (xs ys : List A) (Pxs×Pys : All P xs × All P ys) → to xs ys (from xs ys Pxs×Pys) ≡ Pxs×Pys
    to∘from [] ys ⟨ [] , Pys ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = cong (λ{ ⟨ Pxs' , snd ⟩ → ⟨ Px ∷ Pxs' , snd ⟩}) (to∘from xs ys ⟨ Pxs , Pys ⟩)

_∘′_ : ∀{ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
     → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)

¬Any≃All¬ : ∀{A : Set} {P : A → Set}
          → (xs : List A)
          → ¬ Any P xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ {A} {P} xs =
  record { to = to xs
         ; from = from xs
         ; from∘to = from∘to xs
         ; to∘from = to∘from xs
         }
  where
    to : (xs : List A) → ¬ Any P xs → All (¬_ ∘′ P) xs
    to [] ¬AnyPxs = []
    to (x ∷ xs) ¬AnyPxs = (λ Px → ¬AnyPxs (here Px)) ∷ to xs λ AnyPxs → ¬AnyPxs (there AnyPxs)
    from : (xs : List A) → All (¬_ ∘′ P) xs → ¬ Any P xs
    from [] All¬Pxs ()
    from (x ∷ _) (¬Px ∷ _) (here Px) = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬Pxs) (there AnyPxs) = from xs All¬Pxs AnyPxs
    from∘to : (xs : List A) → {¬AnyPxs : ¬ Any P xs} → from xs (to xs ¬AnyPxs) ≡ ¬AnyPxs
    from∘to [] {¬AnyPxs} = extensionality λ()
    from∘to (x ∷ xs) {¬AnyPxs} = extensionality
      λ{ (here Px) → refl
       ; (there AnyPxs) → ⊥-elim (¬AnyPxs (there AnyPxs))
       }
    to∘from : (xs : List A) → {All¬Pxs : All (¬_ ∘′ P) xs} → to xs (from xs All¬Pxs) ≡ All¬Pxs
    to∘from [] {[]} = refl
    to∘from (x ∷ xs) {¬Px ∷ All¬Pxs} = cong (¬Px ∷_) (to∘from xs)

-- ¬All≃Any¬ requires non-constructive reasoning, however
-- we can go from Any¬ to ¬All
Any¬-implies-¬All : ∀{A : Set} {P : A → Set}
                  → (xs : List A)
                  → Any (¬_ ∘′ P) xs → ¬ All P xs
Any¬-implies-¬All [] () AllPxs
Any¬-implies-¬All (x ∷ _) (here ¬Px) (Px ∷ _) = ¬Px Px
Any¬-implies-¬All (x ∷ xs) (there Any¬Pxs) (Px ∷ AllPxs) = Any¬-implies-¬All xs Any¬Pxs AllPxs
