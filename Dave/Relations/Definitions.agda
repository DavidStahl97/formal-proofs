module Dave.Relations.Definitions where
    open import Agda.Primitive  
    open import Dave.Logic.Module      

    Rel : ∀ {A-ℓ} → Set A-ℓ 
        → ∀ {B-ℓ} → Set B-ℓ 
        → (ℓ : Level) → Set (A-ℓ ⊔ B-ℓ ⊔ (lsuc ℓ))
    Rel A B ℓ = A → B → Set ℓ

    HomoRel : ∀ {A-ℓ} → Set A-ℓ → (ℓ : Level) → Set (A-ℓ ⊔ (lsuc ℓ))
    HomoRel A ℓ = Rel A A ℓ

    {- Properties of Homogenous Relations  -}
    Reflexive : ∀ {A-ℓ} {A : Set A-ℓ} {ℓ} 
        → HomoRel A ℓ 
        → Set (ℓ ⊔ A-ℓ)
    Reflexive {A-ℓ} {A} rel = ∀ {m : A} → rel m m

    Symmetric : ∀ {A-ℓ} {A : Set A-ℓ} {ℓ}
        → HomoRel A ℓ → Set (ℓ ⊔ A-ℓ)
    Symmetric {A-ℓ} {A} rel = ∀ {m n : A} → rel m n → rel n m

    Transitive : ∀ {A-ℓ} {A : Set A-ℓ} {ℓ} 
        → HomoRel A ℓ → Set (ℓ ⊔ A-ℓ)
    Transitive {A-ℓ} {A} rel = ∀ {m n p : A} → rel m n → rel n p → rel m p            

    record EquivalenceRel {A-ℓ} (A : Set A-ℓ) : Set (lsuc A-ℓ) where
        field
            rel : HomoRel A A-ℓ
            reflive : Reflexive rel
            symmetric : Symmetric rel
            transitive : Transitive rel

    AntiSymmetric : ∀ {A-ℓ : Level} {A : Set A-ℓ} {ℓ : Level}
         → HomoRel A ℓ 
         → EquivalenceRel A
         → Set (ℓ ⊔ A-ℓ)
    AntiSymmetric {A-ℓ} {A} rel equivRel = ∀ {m n : A} 
        → rel m n 
        → rel n m 
        → EquivalenceRel.rel equivRel m n

    record PartialOrder {A-ℓ} (A : Set A-ℓ) : Set (lsuc A-ℓ) where
        field
            rel : HomoRel A A-ℓ
            equivalenceRel : EquivalenceRel A
            reflexiv : Reflexive rel
            antiSymmetric : AntiSymmetric rel equivalenceRel
            transitive : Transitive rel

    Irreflexiv : ∀ {A-ℓ} {A : Set A-ℓ} {ℓ} 
        → HomoRel A ℓ 
        → Set (ℓ ⊔ A-ℓ)
    Irreflexiv {A-ℓ} {A} rel = ∀ {m : A} → ¬ rel m m

    record StrictPartialOrder {A-ℓ} (A : Set A-ℓ) : Set (lsuc A-ℓ) where
        field
            rel : HomoRel A A-ℓ
            equivalenceRel : EquivalenceRel A
            irreflexive : Irreflexiv rel
            antiSymmetric : AntiSymmetric rel equivalenceRel
            transitive : Transitive rel            

    {- Properties of Heterogenous Relations  -}
    LeftTotal : ∀ {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ}
        → Rel A B ℓ
        → Set (ℓ ⊔ A-ℓ ⊔ B-ℓ)
    LeftTotal {A-ℓ} {A} {B-ℓ} {B} rel = ∀ {a : A} → Σ B (λ b → rel a b)

    RightTotal : ∀ {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ}
        → Rel A B ℓ
        → Set (ℓ ⊔ A-ℓ ⊔ B-ℓ)
    RightTotal {A-ℓ} {A} {B-ℓ} {B} rel = ∀ {b : B} → Σ A (λ a → rel a b)

    record Bitotal {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ} (rel : Rel A B ℓ) : Set (A-ℓ ⊔ B-ℓ ⊔ ℓ) where
        field
            leftTotal : LeftTotal rel
            rightTotal : RightTotal rel

    {- LeftUnambiguous : ∀ {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ}
        → Rel A B ℓ
        → (equivRel : ∀ {X-ℓ} (X : Set X-ℓ) → (ℓ : Level) → HomoRel X ℓ) 
        → ∀ {equiv-ℓ} → Equivalent (equivRel A equiv-ℓ)
        → Set (ℓ ⊔ A-ℓ ⊔ B-ℓ ⊔ equiv-ℓ) 
    LeftUnambiguous {A-ℓ} {A} {B-ℓ} {B} rel equivRel {equiv-ℓ} equivRelIsEquiv = 
        ∀ {b : B} {a c : A} → rel a b → rel c b → equivRel A equiv-ℓ a c

    RightUnambiguous : ∀ {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ}
        → Rel A B ℓ
        → (equivRel : ∀ {X-ℓ} (X : Set X-ℓ) → (ℓ : Level) → HomoRel X ℓ) 
        → ∀ {equiv-ℓ} → Equivalent (equivRel B equiv-ℓ)
        → Set (ℓ ⊔ A-ℓ ⊔ B-ℓ ⊔ equiv-ℓ) 
    RightUnambiguous {A-ℓ} {A} {B-ℓ} {B} rel equivRel {equiv-ℓ} equivRelIsEquiv = 
        ∀ {a : A} {b c : B} → rel a b → rel a c → equivRel B equiv-ℓ b c -}

    {- record Biunambiguous {A-ℓ} {A : Set A-ℓ} {B-ℓ} {B : Set B-ℓ} {ℓ} (rel : Rel A B ℓ) 
        (equivRel : ∀ {X-ℓ} (X : Set X-ℓ) → (ℓ : Level) → HomoRel X ℓ)
        {equiv-ℓ} : Set (A-ℓ ⊔ B-ℓ ⊔ ℓ) where
        field
            leftUnambiguous : ∀ {ℓ}  {equiv : Equivalence homoRel} → LeftUnambiguous rel equiv
            -}
            