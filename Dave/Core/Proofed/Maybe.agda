module Dave.Core.Proofed.Maybe where
    open import Dave.Core.Maybe public
    open import Dave.Relations.Module

    open import Agda.Primitive    

    private
        variable
            ℓ-A ℓ-B : Level
            A : Set ℓ-A
            B : Set ℓ-B

    ≡-just : {x y : A} → just x ≡ just y → x ≡ y
    ≡-just ≡-refl = ≡-refl