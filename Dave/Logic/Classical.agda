module Dave.Logic.Classical where
    open import Agda.Primitive
    open import Dave.Logic.Propositions

    private
        variable
            ℓ-A ℓ-B : Level
            A : Set ℓ-A
            B : Set ℓ-B

    {- Unprovible Propositions in Intutionistic -}
    ExcludedMiddle : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    ExcludedMiddle A = (A ⊎ (¬ A))

    DoubleNegationElimination : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    DoubleNegationElimination A = ¬ ¬ A ⇔ A

    PeircesLaw : ∀ {ℓ-A ℓ-B} (A : Set ℓ-A) (B : Set ℓ-B) → Set (ℓ-A ⊔ ℓ-B)
    PeircesLaw A B = ((A → B) → A) ⇔ A

    ImplicationAsDisjunction : ∀ {ℓ-A ℓ-B} (A : Set ℓ-A) (B : Set ℓ-B) → Set (ℓ-A ⊔ ℓ-B)
    ImplicationAsDisjunction A B = (A → B) ⇔ ¬ A ⊎ B 

    DeMorgan : ∀ {ℓ-A ℓ-B} (A : Set ℓ-A) (B : Set ℓ-B) → Set (ℓ-A ⊔ ℓ-B)
    DeMorgan A B = ¬ (¬ A × ¬ B) ⇔ A ⊎ B