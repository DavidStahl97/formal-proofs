module Dave.Logic.Propositions.Basics where
    open import Dave.Functions

    {- Equality -}
    record _⇔_ (A B : Set) : Set where
        field
            to   : A → B
            from : B → A

    open _⇔_

    infixl 1 _⇔_ 

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

    {- True -}
    data ⊤ : Set where
        tt : ⊤

    {- False -}
    data ⊥ : Set where
        -- no clauses!

    ⊥-elim : ∀ {A : Set} → ⊥ → A
    ⊥-elim ()    

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

    contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
    contraposition A→B ¬B A = ¬B (A→B A)    

    {- Product (Conjunction) -}
    data _×_ (A B : Set) : Set where
        ⟨_,_⟩ : A → B → A × B

    infixl 3 _×_

    proj₁ : {A B : Set} → A × B → A
    proj₁ ⟨ a , b ⟩ = a

    proj₂ : {A B : Set} → A × B → B
    proj₂ ⟨ a , b ⟩ = b
    
    ×-comm : {A B : Set} → A × B ⇔ B × A
    ×-comm = record 
        {
            to = λ{ ⟨ a , b ⟩ → ⟨ b , a ⟩ };
            from = λ{ ⟨ b , a ⟩ → ⟨ a , b ⟩ }
        }    

    ×-assoc : ∀ {A B C : Set} → (A × B) × C ⇔ A × (B × C)
    ×-assoc = record 
        {
            to = λ{ ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ };
            from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ }
        }    

    ⊤-identityˡ : ∀ {A : Set} → ⊤ × A → A
    ⊤-identityˡ ⟨ tt , a ⟩ = a

    ⊤-identityʳ : ∀ {A : Set} → A × ⊤ → A
    ⊤-identityʳ ⟨ a , tt ⟩ = a
    
    {- Sum (Disjunction) -}
    data _⊎_ (A B : Set) : Set where
        inj₁ : A → A ⊎ B
        inj₂ : B → A ⊎ B

    infixl 3 _⊎_

    case-⊎ : ∀ {A B C : Set}
        → (A → C)
        → (B → C)
        → A ⊎ B
        -----------
        → C
    case-⊎ f g (inj₁ x) = f x
    case-⊎ f g (inj₂ y) = g y        

    ⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A → A
    ⊥-identityˡ (inj₂ x) = x        

    ⊎-comm : ∀ {A B : Set} → A ⊎ B ⇔ B ⊎ A
    ⊎-comm = record 
        {
            to = λ{ (inj₁ a) → inj₂ a
                  ; (inj₂ b) → inj₁ b };
            from = λ{ (inj₁ b) → inj₂ b
                    ; (inj₂ a) → inj₁ a }
        }     

    ⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ⇔ A ⊎ (B ⊎ C)
    ⊎-assoc = record 
        {
            to = λ{ (inj₁ (inj₁ a)) → inj₁ a
                  ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
                  ; (inj₂ c) → inj₂ (inj₂ c) };
            from = λ{ (inj₁ a) → inj₁ (inj₁ a)
                    ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
                    ; (inj₂ (inj₂ c)) → inj₂ c}
        }

    ⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ → A
    ⊥-identityʳ (inj₁ a) = a        

    ×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ⇔ (A × C) ⊎ (B × C)
    ×-distrib-⊎ = record 
        {
            to = λ{⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩
                 ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩};
            from = λ{(inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
                   ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩}
        }        

    ⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ⇔ (A ⊎ C) × (B ⊎ C)
    ⊎-distrib-× = record 
        {
            to = λ{ (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩
                  ; (inj₂ c) → ⟨ inj₂ c , inj₂ c ⟩ };
            from = λ{ ⟨ inj₁ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
                    ; ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c
                    ; ⟨ inj₂ c , _ ⟩ → inj₂ c }
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
    
    currying : ∀ {A B C : Set} → (A → B → C) ⇔ (A × B → C)
    currying = record 
        {
            to = λ{f → λ{⟨ a , b ⟩ → f a b}};
            from = λ{f → λ a → λ b → f ⟨ a , b ⟩}
        }        

    →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ⇔ (A → C) × (B → C)
    →-distrib-⊎ = record 
        {
            to = λ f → ⟨ (λ a → f (inj₁ a)) , (λ b → f (inj₂ b)) ⟩;
            from = λ{⟨ A→C , B→C ⟩ → λ{ (inj₁ a) → A→C a
                                   ; (inj₂ b) → B→C b }}
        }

    →-distrib-× : ∀ {A B C : Set} → (A → B × C) ⇔ (A → B) × (A → C)
    →-distrib-× = record 
        {
            to = λ f → ⟨ (λ a → proj₁ (f a)) , (λ a → proj₂ (f a)) ⟩;
            from = λ f → λ a → ⟨ (proj₁ f) a , (proj₂ f) a ⟩
        }