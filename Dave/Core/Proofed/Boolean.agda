module Dave.Core.Proofed.Boolean where
    open import Dave.Algebra.Naturals.Module
    open import Dave.Logic.Module
    open import Dave.Core.Boolean

    record _▸₁_ {A : Set} (f : A → Bool) (P : A → Set) : Set where
        field
            true▸ : ∀ {a} → f a ≡ true → P a
            false▸ : ∀ {a} → f a ≡ false → ¬ P a
            true◂ : ∀ {a} → P a → f a ≡ true

    record _▸₂_ {A B : Set} (f : A → B → Bool) (P : A → B → Set) : Set where
        field
            true▸ : ∀ {a b} → f a b ≡ true → P a b
            false▸ : ∀ {a b} → f a b ≡ false → ¬ P a b
            true◂ : ∀ {a b} → P a b → f a b ≡ true  

    {- ~▸¬ : ~_ ▸₁ λ a → ¬ (a ≡ true)
    ~▸¬ = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = true◂
        }
        where
        true▸ : ∀ {a} → ~ a ≡ true → ¬ a ≡ true
        true▸ {false} ~a≡t ()
        true▸ {true} () a≡true

        false▸ : ∀ {a} → ~ a ≡ false → ¬ ¬ a ≡ true
        false▸ {true} ~a≡f x = x ≡-refl

        true◂ : ∀ {a} → ¬ a ≡ true → ~ a ≡ true
        true◂ {false} ¬a≡t = ≡-refl
        true◂ {true} ¬a≡t = ⊥-elim (¬a≡t ≡-refl) -}

    {- &&▸× : _&&_ ▸₂ λ a b → (a ≡ true) × (b ≡ true)
    &&▸× = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = ◂true
        }
        where
        true▸ : ∀ {a b : Bool} → a && b ≡ true → (a ≡ true) × (b ≡ true)
        true▸ {true} {true} a&&b≡t = ⟨ ≡-refl , ≡-refl ⟩

        false▸ : ∀ {a b : Bool} → a && b ≡ false → ¬ (a ≡ true × b ≡ true)
        false▸ {a} {false} a&&b≡f ⟨ x , () ⟩
        false▸ {false} {true} a&&b≡f ⟨ () , x₁ ⟩

        ◂true : ∀ {a b : Bool} → (a ≡ true × b ≡ true) → a && b ≡ true
        ◂true {true} {true} ⟨ a≡t , b≡f ⟩ = ≡-refl -}

    -- Theorems
    true⊎false : ∀ {a} → a ≡ true ⊎ a ≡ false
    true⊎false {false} = inj₂ ≡-refl
    true⊎false {true} = inj₁ ≡-refl

    ~~-elim : ∀ {b : Bool} → ~ ~ b ≡ b
    ~~-elim {false} = ≡-refl
    ~~-elim {true} = ≡-refl

    &&-idem : ∀ {b : Bool} → b && b ≡ b
    &&-idem {false} = ≡-refl
    &&-idem {true} = ≡-refl

    ||-idem : ∀ {b : Bool} → b || b ≡ b
    ||-idem {false} = ≡-refl
    ||-idem {true} = ≡-refl

    double-neg : ∀ {b : Bool} → ~ ~ b ≡ b
    double-neg {false} = ≡-refl
    double-neg {true} = ≡-refl

    Bool-contra : false ≡ true → ∀ {P : Set} → P
    Bool-contra ()   