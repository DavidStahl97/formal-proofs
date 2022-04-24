module Algebra.LeibnizEquality where
    open import Algebra.Equality public

    _≐_ : ∀ {A : Set} (x y : A) → Set₁
    _≐_ {A} x y = ∀ (P : A → Set) → P x → P y

    refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
    refl-≐ P Px = Px

    trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
    trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

    sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
    sym-≐ {A} {x} {y} x≐y P = Qy
        where
            Q : A → Set
            Q z = P z → P x
            Qx : Q x
            Qx = refl-≐ P
            Qy : Q y
            Qy = x≐y Q Qx

    ≡→≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
    ≡→≐ x≡y P = subst P x≡y

    ≐→≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
    ≐→≡ {A} {x} {y} x≐y = Qy
        where
            Q : A → Set
            Q z = x ≡ z
            Qx : Q x
            Qx = refl
            Qy : Q y
            Qy = x≐y Q Qx    