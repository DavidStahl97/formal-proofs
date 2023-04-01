module Dave.Core.Proofs.Boolean where
    open import Dave.Core.Maybe
    open import Dave.Relations.Module

    ≡-just : {x y : A} → just x ≡ just y → x ≡ y
    ≡-just ≡-refl = ≡-refl