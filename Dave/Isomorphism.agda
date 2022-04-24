module Dave.Isomorphism where
    open import Dave.Equality
    open import Dave.Functions

    infix 0 _≃_
    record _≃_ (A B : Set) : Set where
        field
            to : A → B
            from : B → A
            from∘to : ∀ (x : A) → from (to x) ≡ x
            to∘from : ∀ (x : B) → to (from x) ≡ x
    open _≃_

    {- Another way to define Isomporphism throug data -}
    data _≃′_ (A B : Set) : Set where
        mk-≃′ : ∀ (to : A → B) →
                ∀ (from : B → A) →
                ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
                ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
                A ≃′ B

    to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
    to′ (mk-≃′ f g g∘f f∘g) = f

    from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
    from′ (mk-≃′ f g g∘f f∘g) = g

    from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
    from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

    to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
    to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

    ≃-refl : ∀ {A : Set} → A ≃ A
    ≃-refl = record 
        { 
            to = λ x → x; 
            from = λ y → y; 
            from∘to = λ x → refl; 
            to∘from = λ y → refl
        }

    ≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
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
                  from A≃B (from B≃C (to B≃C (to A≃B x))) ≡⟨ {!   !} ⟩
                  x ∎;
            to∘from = {!   !}
        }
    
        