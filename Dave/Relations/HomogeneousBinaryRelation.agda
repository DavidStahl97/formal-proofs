module Dave.Relations.HomogeneousBinaryRelation where
    open import Agda.Primitive
    open import Dave.Relations.HetorogeneousBinaryRelation
    
    private
        variable
            ℓ ℓ₁ ℓ₂ : Level

    homo-rel : Set (lsuc ℓ)
    homo-rel {ℓ} = ∀ {A : Set ℓ} → A → A → Set ℓ

    homo-refl : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc ℓ)
    homo-refl {ℓ} rel = ∀ {A : Set ℓ} {m : A} → rel m m

    homo-sym : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc ℓ)
    homo-sym {ℓ} rel = ∀ {A : Set ℓ} {m n : A} → rel m n → rel n m

    homo-trans : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc ℓ)
    homo-trans {ℓ} rel = ∀ {A : Set ℓ} {m n p : A} → rel m n → rel n p → rel m p

    cong : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc (ℓ ⊔ ℓ₁))
    cong {ℓ} {ℓ₁} rel = ∀ {A : Set ℓ} {B : Set ℓ₁} {m n : A}
        → (f : A → B)
        → rel m n
        → rel (f m) (f n)

    cong₂ : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc (ℓ ⊔ ℓ₁ ⊔ ℓ₂))
    cong₂ {ℓ} {ℓ₁} {ℓ₂} rel = 
        ∀ {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} {m n : A} {o p : B} 
        → (f : A → B → C) 
        → rel m n 
        → rel o p 
        → rel (f m o) (f n p)

    cong-app : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc (ℓ ⊔ ℓ₁))
    cong-app {ℓ} {ℓ₁} rel = 
        ∀ {A : Set ℓ} {B : Set ℓ₁} {f g : A → B}
        → rel f g
        → ∀ {x : A} → rel (f x) (g x)             

    subst : (∀ {ℓ} → homo-rel {ℓ}) → Set (lsuc (ℓ ⊔ ℓ₁))
    subst {ℓ} {ℓ₁} rel = ∀ {A : Set ℓ} {x y : A} {P : A → Set ℓ₁}
        → rel x y
        → P x → P y