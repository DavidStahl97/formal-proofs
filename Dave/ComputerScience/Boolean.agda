module Dave.ComputerScience.Boolean where
    open import Dave.Equality

    data Bool : Set where
        false : Bool
        true : Bool    

    {-# BUILTIN BOOL  Bool  #-}
    {-# BUILTIN TRUE  true  #-}
    {-# BUILTIN FALSE false #-}

    infix  7 ~_
    infixl 6 _xor_ _nand_
    infixl 6 _&&_
    infixl 5 _||_ 
    infix  4 if_then_else_
    infixl 4 _imp_ 

    ~_ : Bool → Bool
    ~ true = false
    ~ false = true

    _&&_ : Bool → Bool → Bool
    a && true = a
    a && false = false

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
    ~~-elim : ∀ {b : Bool} → ~ ~ b ≡ b
    ~~-elim {false} = refl
    ~~-elim {true} = refl