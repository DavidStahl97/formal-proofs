module Dave.Extensionality where
    open import Dave.Equality

    postulate
        extensionality : ∀ {A B : Set} {f g : A → B} 
            → (∀ (x : A) → f x ≡ g x) 
            → f ≡ g

    postulate
        ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
            → (∀ (x : A) → f x ≡ g x)
            → f ≡ g