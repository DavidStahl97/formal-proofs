module Dave.Logic.FirstOrder.Basics where
    open import Agda.Primitive

    data Π {A-ℓ ℓ} (A : Set A-ℓ) (B : A → Set ℓ) : Set (ℓ ⊔ A-ℓ) where
        Λ : ((a : A) → B a) → Π A B        

