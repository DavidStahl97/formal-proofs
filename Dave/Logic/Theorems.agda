module Dave.Logic.Theorems where

    K : {A B : Set} → A → B → A
    K a b = a

    S : {A B C : Set} → (A → B → C) → (A → B) → A → C
    S = λ f → λ g → λ a → f a (g a)    
