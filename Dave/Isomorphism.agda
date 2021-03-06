module Dave.Isomorphism where
    open import Agda.Primitive
    open import Dave.Relations.Module
    open import Dave.Equality
    open import Dave.Functions

    private
        variable
            ℓ₁ ℓ₂ : Level

    infix 0 _≃_
    record _≃_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
        field
            to : A → B
            from : B → A
            from∘to : ∀ (x : A) → from (to x) ≡ x
            to∘from : ∀ (x : B) → to (from x) ≡ x
    open _≃_

    {- ≃-refl : refl {lsuc ℓ₁} _≃_
    ≃-refl = record 
        { 
            to = λ x → x; 
            from = λ y → y; 
            from∘to = λ x → ≡-refl; 
            to∘from = λ y → ≡-refl
        } -}

    ≃-sym : sym {ℓ₁} {ℓ₂} _≃_
    ≃-sym A≃B = record 
        {
            to = from A≃B ;
            from = to A≃B ;
            from∘to = to∘from A≃B ;
            to∘from = from∘to A≃B
        }

    ≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
    ≃-trans A≃B B≃C = record 
        {
            to = (to B≃C) ∘ (to A≃B);
            from = (from A≃B) ∘ (from B≃C);
            from∘to = λ x → begin
                (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x) ≡⟨⟩
                from A≃B (from B≃C (to B≃C (to A≃B x))) ≡⟨ ≡-cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                from A≃B (to A≃B x) ≡⟨ from∘to A≃B x ⟩
                x ∎;
            to∘from = λ x → begin
                (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) x) ≡⟨⟩
                to B≃C (to A≃B (from A≃B (from B≃C x))) ≡⟨ ≡-cong (to B≃C) (to∘from A≃B (from B≃C x)) ⟩
                to B≃C (from B≃C x) ≡⟨ to∘from B≃C x ⟩
                x ∎
        }
    
    {- module ≃-Reasoning where

        infix  1 ≃-begin_
        infixr 2 _≃⟨_⟩_
        infix  3 _≃-∎

        ≃-begin_ : ∀ {A B : Set}
            → A ≃ B
            -----
            → A ≃ B
        ≃-begin A≃B = A≃B

        _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≃ B
            → B ≃ C
            -----
            → A ≃ C
        A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

        _≃-∎ : ∀ (A : Set)
            -----
            → A ≃ A
        A ≃-∎ = ≃-refl

    open ≃-Reasoning public -}
        