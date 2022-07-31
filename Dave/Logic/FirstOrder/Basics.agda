module Dave.Logic.FirstOrder.Basics where
    open import Agda.Primitive

    private
        variable
            A-ℓ ℓ : Level

    data Π (A : Set A-ℓ) (B : A → Set ℓ) : Set (ℓ ⊔ A-ℓ) where
        Λ : ((a : A) → B a) → Π A B        

    data Σ (A : Set A-ℓ) (B : A → Set ℓ) : Set (ℓ ⊔ A-ℓ) where
        _,_ : (a : A) → B a → Σ A B

    Σ-proj₁ : ∀ {A : Set A-ℓ} {B : A → Set ℓ} → Σ A B → A
    Σ-proj₁ (a , b) = a

    Σ-proj₂ : ∀ {A : Set A-ℓ} {B : A → Set ℓ} → (s : Σ A B) → B (Σ-proj₁ s)
    Σ-proj₂ (a , b) = b