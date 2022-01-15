module logic.simple-logic where
    
    data Bool : Set where
        false : Bool
        true : Bool    

    ¬_ : Bool → Bool
    ¬ true = false
    ¬ false = true

    _∧_ : Bool → Bool → Bool
    a ∧ true = a
    a ∧ false = false

    if_then_else_ : {A : Set} → Bool → A → A → A
    if false then a else b = b
    if true then a else b = a

    identity : {A : Set} → A → A
    identity a = a