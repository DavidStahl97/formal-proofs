module Dave.Core.Maybe where
    open import Agda.Primitive
    open import Dave.Relations.Module

    private
        variable
            ℓ-A ℓ-B : Level
            A : Set ℓ-A
            B : Set ℓ-B

    data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
        just : A → Maybe A
        nothing : Maybe A

    infixl 1 _>>=Maybe_
    _>>=Maybe_ : Maybe A → (A → Maybe B) → Maybe B
    nothing >>=Maybe f = nothing
    just a  >>=Maybe f = f a

    ≡-just : {x y : A} → just x ≡ just y → x ≡ y
    ≡-just ≡-refl = ≡-refl