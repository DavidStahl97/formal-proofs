module Dave.Logic.Basics where

    data _×_ (A B : Set) : Set where
        _,_ : A → B → A × B

    proj₁ : {A B : Set} → A × B → A
    proj₁ (a , b) = a

    proj₂ : {A B : Set} → A × B → B
    proj₂ (a , b) = b

    ×-comm :  {A B : Set} → (A × B) → (B × A)
    ×-comm p = (proj₂ p) , (proj₁ p)

    record _⇔_ (A B : Set) : Set where
        field
            to   : A → B
            from : B → A

    open _⇔_

    ⇔-ref : ∀ {A : Set} → A ⇔ A
    ⇔-ref = record 
        {
            to = λ a → a;
            from = λ a → a
        }

    ⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
    ⇔-sym A⇔B = record
        {
            to = from A⇔B;
            from = to A⇔B
        }

    ⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
    ⇔-trans A⇔B B⇔C = record 
        {
            to = λ a → to B⇔C (to A⇔B a);
            from = λ c → from A⇔B (from B⇔C c)
        }
