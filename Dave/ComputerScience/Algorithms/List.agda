module Dave.ComputerScience.Algorithms.List where
    open import Dave.Algebra.Naturals.Definition
    open import Dave.ComputerScience.Algorithms.Decidable
    open import Dave.ComputerScience.Algorithms.Boolean
    open import Dave.ComputerScience.Maybe

    data List {ℓ} (A : Set ℓ) : Set ℓ where
        [] : List A
        _::_ : (x : A) (xs : List A) → List A

    length : ∀ {ℓ}{A : Set ℓ} → List A → ℕ
    length [] = 0
    length (x :: list) = suc (length list)

    _++_ : ∀ {ℓ}{A : Set ℓ} → List A → List A → List A
    [] ++ b = b
    (x :: a) ++ b = x :: (a ++ b)

    map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → List A → List B
    map f [] = []
    map f (x :: a) = (f x) :: map f a

    filter : ∀ {ℓ} {A : Set ℓ} → (A → Bool) → List A → List A
    filter p [] = []
    filter p (x :: a) = let right = filter p a in
                        if p x then x :: right else right

    nth : ∀ {ℓ} {A : Set ℓ} → ℕ → List A → Maybe A
    nth n [] = nothing
    nth zero (x :: list) = just x
    nth (suc n) (x :: list) = nth n list
