module Dave.Definitions where
    open import Agda.Primitive
    
    P₁ : ∀ {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
    P₁ {ℓ} A = A → Set ℓ

    P₂ : ∀ {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
    P₂ {ℓ} A = A → A → Set ℓ

    reflexiv : ∀ {ℓ} {A : Set ℓ} → P₂ A → Set ℓ
    reflexiv {ℓ} {A} prop = ∀ {m : A} → prop m m
    
    symmetry : ∀ {ℓ} {A : Set ℓ} → P₂ A → Set ℓ
    symmetry {ℓ} {A} prop = ∀ {m n : A} → prop m n → prop n m

    transitivity : ∀ {ℓ} {A : Set ℓ} → P₂ A → Set ℓ
    transitivity {ℓ} {A} prop = ∀ {m n p : A} → prop m n → prop n p → prop m p

    congruence : ∀ {ℓ} {A B : Set ℓ} → P₂ A → Set ℓ
    congruence {ℓ} {A} prop = ∀ {m n : A} → (f : A → B) → prop m n → prop (f m) (f n)