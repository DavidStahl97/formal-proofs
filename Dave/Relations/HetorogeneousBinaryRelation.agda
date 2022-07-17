module Dave.Relations.HetorogeneousBinaryRelation where
    open import Agda.Primitive

    private
        variable
            ℓ₁ ℓ₂ ℓ₃ : Level
        
    rel : Set (lsuc (ℓ₁ ⊔ ℓ₂))
    rel {ℓ₁} {ℓ₂} = ∀ {A : Set ℓ₁} {B : Set ℓ₂} → A → B → Set (ℓ₁ ⊔ ℓ₂)            

    refl : (∀ {ℓ₁ ℓ₂} → rel {ℓ₁} {ℓ₂}) → Set (lsuc (ℓ₁))
    refl {ℓ₁} rel = ∀ {A : Set ℓ₁} {m : A} → rel m m

    sym : (∀ {ℓ₁ ℓ₂} → rel {ℓ₁} {ℓ₂}) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
    sym {ℓ₁} {ℓ₂} rel = ∀ {A : Set ℓ₁} {B : Set ℓ₂} {m : A} {n : B} → rel m n → rel n m        

    trans : (∀ {ℓ₁ ℓ₂} → rel {ℓ₁} {ℓ₂}) → Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))
    trans {ℓ₁} {ℓ₂} {ℓ₃} rel = ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {m : A} {n : B} {p : C} 
        → rel m n → rel n p → rel m p   