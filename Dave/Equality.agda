module Dave.Equality where
  open import Agda.Primitive
  open import Dave.Relations.Module

  private
    variable
      ℓ ℓ₁ ℓ₂ : Level

  data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
    ≡-refl : x ≡ x

  infix 4 _≡_
  
  {-# BUILTIN EQUALITY _≡_ #-}

  ≡-sym : homo-sym {ℓ} _≡_
  ≡-sym ≡-refl = ≡-refl

  ≡-trans : homo-trans {ℓ} _≡_
  ≡-trans ≡-refl b = b

  ≡-cong : cong {ℓ} {ℓ₁} _≡_
  ≡-cong f ≡-refl = ≡-refl

  ≡-cong₂ : cong₂ {ℓ} {ℓ₁} {ℓ₂} _≡_
  ≡-cong₂ f ≡-refl ≡-refl = ≡-refl

  ≡-cong-app : cong-app {ℓ} {ℓ₁} _≡_
  ≡-cong-app ≡-refl = ≡-refl

  ≡-subst : subst {ℓ} {ℓ₁} _≡_
  ≡-subst ≡-refl Px = Px

  module ≡-Reasoning {A : Set} where

    infix  1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix  3 _∎

    begin_ : ∀ {x y : A}
      → x ≡ y
        -----
      → x ≡ y
    begin x≡y  =  x≡y

    _≡⟨⟩_ : ∀ (x : A) {y : A}
      → x ≡ y
        -----
      → x ≡ y
    x ≡⟨⟩ x≡y  =  x≡y

    _≡⟨_⟩_ : ∀ (x : A) {y z : A}
      → x ≡ y
      → y ≡ z
        -----
      → x ≡ z
    x ≡⟨ x≡y ⟩ y≡z  =  ≡-trans x≡y y≡z

    _∎ : ∀ (x : A)
        -----
      → x ≡ x
    x ∎  =  ≡-refl

  open ≡-Reasoning public