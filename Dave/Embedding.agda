module Dave.Embedding where
    open import Dave.Functions
    open import Dave.Equality
    open import Dave.Isomorphism

    infix 0 _≲_
    record _≲_ (A B : Set) : Set where
        field
            to : A → B
            from : B → A
            from∘to : ∀ (x : A) → from (to x) ≡ x
    
    open _≲_

    ≲-refl : ∀ {A : Set} → A ≲ A
    ≲-refl = record 
        {
            to = λ a → a ;
            from = λ b → b ;
            from∘to = λ a → refl
        }

    ≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
    ≲-trans A≲B B≲C = record 
        {
            to = λ a → to B≲C (to A≲B a) ;
            from = λ c → from A≲B (from B≲C c) ;
            from∘to = λ a → begin
                (from A≲B ∘ from B≲C) ((to B≲C ∘ to A≲B) a) ≡⟨⟩
                from A≲B (from B≲C (to B≲C (to A≲B a))) ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B a)) ⟩
                from A≲B (to A≲B a) ≡⟨ from∘to A≲B a ⟩
                a ∎
        }

    ≲-antisym : ∀ {A B : Set} 
        → (A≲B : A ≲ B) 
        → (B≲A : B ≲ A) 
        → (to A≲B ≡ from B≲A)
        → (from A≲B ≡ to B≲A)
        → A ≃ B
    ≲-antisym A≲B B≲A to≡from from≡to = record 
        {
            to = λ a → to A≲B a ;
            from = λ b → from A≲B b ;
            from∘to = from∘to A≲B;
            to∘from = λ b → begin
                to A≲B (from A≲B b) ≡⟨ cong (λ x → (to A≲B (x b))) from≡to ⟩
                to A≲B (to B≲A b) ≡⟨ cong-app to≡from (to B≲A b) ⟩
                from B≲A (to B≲A b) ≡⟨ from∘to B≲A b ⟩
                b ∎
        }    

    module ≲-Reasoning where

        infix  1 ≲-begin_
        infixr 2 _≲⟨_⟩_
        infix  3 _≲-∎

        ≲-begin_ : ∀ {A B : Set}
            → A ≲ B
            -----
            → A ≲ B
        ≲-begin A≲B = A≲B

        _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
            → A ≲ B
            → B ≲ C
            -----
            → A ≲ C
        A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

        _≲-∎ : ∀ (A : Set)
            -----
            → A ≲ A
        A ≲-∎ = ≲-refl

    open ≲-Reasoning    
