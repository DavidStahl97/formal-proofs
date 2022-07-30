module Dave.Relations.LeibnizEquality where
    open import Agda.Primitive
    open import Dave.Relations.Definitions
    open import Dave.Relations.Equality

    private
        variable
            ℓ₁ ℓ₂ : Level            

    _≐_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
    _≐_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

    refl-≐ : ∀ {A : Set ℓ₁} {x : A} → x ≐ x
    refl-≐ P Px = Px

    trans-≐ : ∀ {A : Set ℓ₁ } {x y z : A} → x ≐ y → y ≐ z → x ≐ z
    trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

    {- sym-≐ : ∀ {A : Set ℓ₁} {x y : A} → x ≐ y → y ≐ x
    sym-≐ {A} {x} {y} x≐y P = Qy
        where
            Q : A → Set (lsuc ℓ₁)
            Q z = P z → P x
            Qx : Q x
            Qx = refl-≐ P
            Qy : Q y
            Qy = x≐y Q Qx

    ≡→≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
    ≡→≐ x≡y P = ≡-subst P x≡y

    ≐→≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
    ≐→≡ {A} {x} {y} x≐y = Qy
        where
            Q : A → Set
            Q z = x ≡ z
            Qx : Q x
            Qx = ≡-refl
            Qy : Q y
            Qy = x≐y Q Qx    -}