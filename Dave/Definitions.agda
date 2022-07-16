module Dave.Definitions where
    open import Agda.Primitive

    private
        variable
            ℓ : Level

    P₂ : ∀ {ℓ} → Set (lsuc (lsuc ℓ))
    P₂ {ℓ} = (∀ {A : Set ℓ} → A → A → Set ℓ) → Set (lsuc ℓ) 

    refl : P₂ {ℓ}
    refl {ℓ} prop = ∀ {A : Set ℓ} {m : A} → prop m m
    
    sym : P₂ {ℓ}
    sym {ℓ} prop = ∀ {A : Set ℓ} {m n : A} → prop m n → prop n m

    trans : P₂ {ℓ}
    trans {ℓ} prop = ∀ {A : Set ℓ} {m n p : A} → prop m n → prop n p → prop m p

    cong : P₂ {ℓ}
    cong {ℓ} prop = ∀ {A B : Set ℓ} {m n : A} → (f : A → B) → prop m n → prop (f m) (f n)    

    cong₂ : P₂ {ℓ}
    cong₂ {ℓ} prop = ∀ {A B C : Set ℓ} {m n : A} {o p : B} 
        → (f : A → B → C) 
        → prop m n 
        → prop o p 
        → prop (f m o) (f n p)

    cong-app : P₂ {ℓ}
    cong-app {ℓ} prop = ∀ {A B : Set ℓ} {f g : A → B}
        → prop f g
        → ∀ {x : A} → prop (f x) (g x) 

    subst : P₂ {ℓ}
    subst {ℓ} prop = ∀ {A : Set ℓ} {x y : A} {P : A → Set ℓ}
        → prop x y
        → P x → P y