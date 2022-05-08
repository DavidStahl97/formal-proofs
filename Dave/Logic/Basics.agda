module Dave.Logic.Basics where
    open import Dave.Equality
    open import Dave.Isomorphism
    open import Dave.Structures.Monoid

    {- True -}
    data ⊤ : Set where
        tt : ⊤

    η-⊤ : ∀ (w : ⊤) → tt ≡ w
    η-⊤ tt = refl

    {- Product (And) -}
    data _×_ (A B : Set) : Set where
        ⟨_,_⟩ : A → B → A × B

    infixr 2 _×_

    proj₁ : {A B : Set} → A × B → A
    proj₁ ⟨ a , b ⟩ = a

    proj₂ : {A B : Set} → A × B → B
    proj₂ ⟨ a , b ⟩ = b
    
    ×-comm :  {A B : Set} → (A × B) ≃ (B × A)
    ×-comm = record 
        {
            to = λ{ ⟨ a , b ⟩ → ⟨ b , a ⟩ };
            from = λ {⟨ b , a ⟩ → ⟨ a , b ⟩};
            from∘to = λ { ⟨ a , b ⟩ → refl };
            to∘from = λ { ⟨ b , a ⟩ → refl }
        }

    ×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
    ×-assoc = record 
        {
            to = λ {⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩};
            from = λ {⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩};
            from∘to = λ {⟨ ⟨ a , b ⟩ , c ⟩ → refl};
            to∘from = λ {⟨ a , ⟨ b , c ⟩ ⟩ → refl}
        }

    η-× : ∀ {A B : Set} (w : A × B) →  ⟨ proj₁ w , proj₂ w ⟩ ≡ w
    η-× ⟨ x , y ⟩ = refl   

    ⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
    ⊤-identityˡ = record
        { 
            to      = λ{ ⟨ tt , x ⟩ → x }; 
            from    = λ{ x → ⟨ tt , x ⟩ }; 
            from∘to = λ{ ⟨ tt , x ⟩ → refl }; 
            to∘from = λ{ x → refl }
        }

    ⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
    ⊤-identityʳ {A} = ≃-begin
        (A × ⊤) ≃⟨ ×-comm ⟩
        (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
        A ≃-∎
    
    {- Equality -}
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

    ⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
    ⇔≃× = record
        {
            to = λ {A⇔B → ⟨ to A⇔B , from A⇔B ⟩};
            from = λ {x → record { to = proj₁ x; from = proj₂ x } };
            from∘to = λ A⇔B → refl;
            to∘from = λ {⟨ A→B , B→A ⟩ → refl}
        }  
