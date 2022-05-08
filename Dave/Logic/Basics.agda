module Dave.Logic.Basics where
    open import Dave.Functions
    open import Dave.Equality
    open import Dave.Isomorphism
    open import Dave.Structures.Monoid

    {- True -}
    data ⊤ : Set where
        tt : ⊤

    η-⊤ : ∀ (w : ⊤) → tt ≡ w
    η-⊤ tt = refl

    {- Product (Conjunction) -}
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
    
    {- Sum (Disjunction) -}
    data _⊎_ (A B : Set) : Set where
        inj₁ : A → A ⊎ B
        inj₂ : B → A ⊎ B

    infixr 1 _⊎_

    case-⊎ : ∀ {A B C : Set}
        → (A → C)
        → (B → C)
        → A ⊎ B
        -----------
        → C
    case-⊎ f g (inj₁ x) = f x
    case-⊎ f g (inj₂ y) = g y

    uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
        case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
    uniq-⊎ h (inj₁ x) = refl
    uniq-⊎ h (inj₂ y) = refl

    η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
    η-⊎ (inj₁ x) = refl
    η-⊎ (inj₂ y) = refl

    ⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
    ⊎-comm = record 
        {
            to = λ {(inj₁ A) → inj₂ A
                  ; (inj₂ B) → inj₁ B};
            from = λ {(inj₁ B) → inj₂ B
                    ; (inj₂ A) → inj₁ A};
            from∘to = λ {(inj₁ x) → refl
                       ; (inj₂ x) → refl};
            to∘from = λ {(inj₁ x) → refl
                       ; (inj₂ x) → refl}
        }                

    ⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
    ⊎-assoc = record 
        {  
            to = λ {(inj₁ (inj₁ a)) → inj₁ a
                  ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
                  ; (inj₂ c) → inj₂ (inj₂ c)};
            from = λ {(inj₁ a) → inj₁ (inj₁ a)
                    ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
                    ; (inj₂ (inj₂ c)) → inj₂ c};
            from∘to = λ {(inj₁ (inj₁ x)) → refl
                       ; (inj₁ (inj₂ x)) → refl
                       ; (inj₂ x) → refl};
            to∘from = λ {(inj₁ x) → refl
                       ; (inj₂ (inj₁ x)) → refl
                       ; (inj₂ (inj₂ x)) → refl}
        }

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
