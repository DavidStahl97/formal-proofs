module Dave.Logic.Basics where
    open import Dave.Functions
    open import Dave.Equality
    open import Dave.Extensionality
    open import Dave.Isomorphism
    open import Dave.Embedding
    open import Dave.Structures.Monoid

    {- True -}
    data ⊤ : Set where
        tt : ⊤

    η-⊤ : ∀ (w : ⊤) → tt ≡ w
    η-⊤ tt = refl

    {- False -}
    data ⊥ : Set where
        -- no clauses!

    ⊥-elim : ∀ {A : Set} → ⊥ → A
    ⊥-elim ()

    uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
    uniq-⊥ h ()

    {- Negation -}
    ¬_ : Set → Set
    ¬ A = A → ⊥

    infix 3 ¬_

    ¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
    ¬-elim ¬x x = ¬x x   

    ¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
    ¬¬-intro x ¬x = ¬x x

    ¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
    ¬¬¬-elim ¬¬¬a a = ¬¬¬a (¬¬-intro a)

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

    ⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
    ⊥-identityˡ = record 
        {
            to = λ {(inj₂ a) → a};
            from = λ a → inj₂ a;
            from∘to = λ {(inj₂ a) → refl};
            to∘from = λ a → refl
        }

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

    ⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
    ⊥-identityʳ {A} = ≃-begin 
        (A ⊎ ⊥) ≃⟨ ⊎-comm ⟩
        (⊥ ⊎ A) ≃⟨ ⊥-identityˡ ⟩
        A ≃-∎

    ×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
    ×-distrib-⊎ = record
        { 
            to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩);
                         ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)}; 
            from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩;
                         (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩};
            from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl; 
                         ⟨ inj₂ y , z ⟩ → refl};
            to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl; 
                         (inj₂ ⟨ y , z ⟩) → refl}
        } 

    ⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
    ⊎-distrib-× = record
        { 
            to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩; 
                         (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩}; 
            from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩); 
                         ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z); 
                         ⟨ inj₂ z , _      ⟩ → (inj₂ z)}; 
            from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl; 
                         (inj₂ z)         → refl}
        }   

    ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
    ⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
    ⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩  

    ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
    ⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
    ⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩  

    {- Implication -}

    {- modus ponens-}
    →-elim : ∀ {A B : Set} → (A → B) → A → B
    →-elim A→B a = A→B a

    η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
    η-→ f = refl

    currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
    currying = record 
        { 
            to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}; 
            from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}};
            from∘to =  λ{ f → refl };
            to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
        }

    →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
    →-distrib-⊎ = record
        {
            to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩;
            from = λ{⟨ A→C , B→C ⟩ → λ{(inj₁ a) → A→C a
                                     ; (inj₂ b) → B→C b}};
            from∘to = λ f → extensionality λ{ (inj₁ a) → refl
                                            ; (inj₂ b) → refl };
            to∘from = λ{ ⟨ A→C , B→C ⟩ → refl }
        }

    →-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
    →-distrib-× = record
        { 
            to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ };
            from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ };
            from∘to = λ{ f → extensionality λ{ x → η-× (f x) } };
            to∘from = λ{ ⟨ g , h ⟩ → refl }
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
 