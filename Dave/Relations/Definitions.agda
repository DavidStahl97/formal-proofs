module Dave.Relations.Definitions where
    open import Agda.Primitive    
    
    module HetorogeneousBinaryRelation where                

        rel : ∀ {A-ℓ B-ℓ} → Set A-ℓ → Set B-ℓ → (ℓ : Level) → Set (A-ℓ ⊔ B-ℓ ⊔ (lsuc ℓ))
        rel A B ℓ = A → B → Set ℓ        

    open HetorogeneousBinaryRelation public

    module HomogeneousBinaryRelation where    

        homo-rel : ∀ {ℓ A-ℓ} → Set A-ℓ → Set (A-ℓ ⊔ (lsuc ℓ))
        homo-rel {ℓ} A = rel A A ℓ

        homo-refl : ∀ {ℓ A-ℓ} → (A : Set A-ℓ) → homo-rel {ℓ} {A-ℓ} A → Set (ℓ ⊔ A-ℓ)
        homo-refl A rel = ∀ {m : A} → rel m m

        homo-sym : ∀ {ℓ A-ℓ} → (A : Set A-ℓ) → homo-rel {ℓ} {A-ℓ} A → Set (ℓ ⊔ A-ℓ)
        homo-sym A rel = ∀ {m n : A} → rel m n → rel n m

        homo-trans : ∀ {ℓ A-ℓ} → (A : Set A-ℓ) → homo-rel {ℓ} {A-ℓ} A → Set (ℓ ⊔ A-ℓ)
        homo-trans A rel = ∀ {m n p : A} → rel m n → rel n p → rel m p

    open HomogeneousBinaryRelation public