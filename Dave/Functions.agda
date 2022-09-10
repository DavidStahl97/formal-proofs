module Dave.Functions where

    _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
    (g ∘ f) a = g (f a)

    _∘´_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
    (g ∘´ f) = λ x → g (f x)

    identity : {A : Set} → A → A
    identity a = a    