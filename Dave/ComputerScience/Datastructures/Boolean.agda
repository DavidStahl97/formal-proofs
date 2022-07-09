module Dave.ComputerScience.Datastructures.Boolean where
    open import Dave.Equality
    open import Dave.Logic.Basics

    data Bool : Set where
        false : Bool
        true : Bool    

    {-# BUILTIN BOOL  Bool  #-}
    {-# BUILTIN TRUE  true  #-}
    {-# BUILTIN FALSE false #-}  

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

    infix  7 ~_
    infixl 6 _xor_ _nand_
    infixl 6 _&&_
    infixl 5 _||_ 
    infix  4 if_then_else_
    infixl 4 _imp_ 

    ~_ : Bool → Bool
    ~ true = false
    ~ false = true

    ~▸¬ : ~_ ▸₁ λ a → ¬ a ≡ true
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
        false▸ {true} ~a≡f x = x refl

        true◂ : ∀ {a} → ¬ a ≡ true → ~ a ≡ true
        true◂ {false} ¬a≡t = refl
        true◂ {true} ¬a≡t = ⊥-elim (¬a≡t refl)

    _&&_ : Bool → Bool → Bool
    a && true = a
    a && false = false

    &&▸× : _&&_ ▸₂ λ a b → (a ≡ true) × (b ≡ true)
    &&▸× = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = ◂true
        }
        where
        true▸ : ∀ {a b : Bool} → a && b ≡ true → (a ≡ true) × (b ≡ true)
        true▸ {true} {true} a&&b≡t = ⟨ refl , refl ⟩

        false▸ : ∀ {a b : Bool} → a && b ≡ false → ¬ (a ≡ true × b ≡ true)
        false▸ {a} {false} a&&b≡f ⟨ x , () ⟩
        false▸ {false} {true} a&&b≡f ⟨ () , x₁ ⟩

        ◂true : ∀ {a b : Bool} → (a ≡ true × b ≡ true) → a && b ≡ true
        ◂true {true} {true} ⟨ a≡t , b≡f ⟩ = refl

    _||_ : Bool → Bool → Bool
    a || false = a
    a || true = true

    _xor_ : Bool → Bool → Bool
    false xor false = false
    false xor true = true
    true xor false = true
    true xor true = false

    if_then_else_ : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
    if false then a else b = b
    if true then a else b = a

    -- implication
    _imp_ : Bool → Bool → Bool 
    true imp b2 = b2
    false imp b2 = true

    -- also called the Sheffer stroke
    _nand_ : Bool → Bool → Bool
    true nand true = false
    true nand false = true
    false nand true = true
    false nand false = true

    _nor_ : Bool → Bool → Bool
    x nor y = ~ (x || y)

    -- Theorems
    true⊎false : ∀ {a} → a ≡ true ⊎ a ≡ false
    true⊎false {false} = inj₂ refl
    true⊎false {true} = inj₁ refl

    ~~-elim : ∀ {b : Bool} → ~ ~ b ≡ b
    ~~-elim {false} = refl
    ~~-elim {true} = refl

    &&-idem : ∀ {b : Bool} → b && b ≡ b
    &&-idem {false} = refl
    &&-idem {true} = refl

    ||-idem : ∀ {b : Bool} → b || b ≡ b
    ||-idem {false} = refl
    ||-idem {true} = refl

    double-neg : ∀ {b : Bool} → ~ ~ b ≡ b
    double-neg {false} = refl
    double-neg {true} = refl

    Bool-contra : false ≡ true → ∀ {P : Set} → P
    Bool-contra ()   