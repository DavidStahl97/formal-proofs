module Dave.ComputerScience.Typing.SimpleLanguage where
    open import Dave.Algebra.Naturals.Module renaming (_+_ to _+ℕ_ ; _<_ to _<ℕ_)
    open import Dave.ComputerScience.Datastructures.Boolean hiding (if_then_else_)
    open import Dave.ComputerScience.Algorithms.NaturalNumbers.Ordering 

    {- see Program=Proof -}

    data Value : Set where
        VNat : ℕ → Value
        VBool : Bool → Value

    data Prog : Set where
        V : Value → Prog
        _+_ : Prog → Prog → Prog
        _<_ : Prog → Prog → Prog
        if_then_else_ : Prog → Prog → Prog → Prog

    infix 50 _+_
    infix 40 _<_
    infix 30 if_then_else_

    data _⇒_ : Prog → Prog → Set where
        ⇒-Add : (m n : ℕ) → V (VNat m) + V (VNat n) ⇒ V (VNat (m +ℕ n))
        ⇒-Add-l : {p p' : Prog} → p ⇒ p' → (q : Prog) → p + q ⇒ p' + q
        ⇒-Add-r : {q q' : Prog} → (p : Prog) → q ⇒ q' → p + q ⇒ p + q'
        ⇒-Lt : (m n : ℕ) → V (VNat m) < V (VNat n) ⇒ V (VBool (is m < n))
        ⇒-Lt-l : {p p' : Prog} → p ⇒ p' → (q : Prog) → p < q ⇒ p' < q
        ⇒-Lt-r : {q q' : Prog} → (p : Prog) → q ⇒ q' → p < q ⇒ p < q'
        ⇒-If : {p p' : Prog} → p ⇒ p' → (q r : Prog) → if p then q else r ⇒ if p' then q else r
        ⇒-If-t : (p q : Prog) → if V (VBool true) then p else q ⇒ p
        ⇒-If-f : (p q : Prog) → if V (VBool false) then p else q ⇒ q

    data Type : Set where
        TNat TBool : Type

    data ⊢_∷_ : Prog → Type → Set where
        ⊢-Nat : (n : ℕ) → ⊢ V (VNat n) ∷ TNat
        ⊢-Bool : (b : Bool) → ⊢ V (VBool b) ∷ TBool
        ⊢-Add : {p q : Prog} → ⊢ p ∷ TNat → ⊢ q ∷ TNat → ⊢ p + q ∷ TNat
        ⊢-Lt : {p q : Prog} → ⊢ p ∷ TNat → ⊢ q ∷ TNat → ⊢ p < q ∷ TBool
        ⊢-If : {p q r : Prog} {A : Type} → ⊢ p ∷ TBool → ⊢ q ∷ A → ⊢ r ∷ A → ⊢ if p then q else r ∷ A

    
    {- Theorem 1.4.3.1 : Type uniqueness -}
    tuniq : {p : Prog} {A A' : Type} → ⊢ p ∷ A → ⊢ p ∷ A' → A ≡ A'
    tuniq (⊢-Nat n) (⊢-Nat .n) = ≡-refl
    tuniq (⊢-Bool b) (⊢-Bool .b) = ≡-refl
    tuniq (⊢-Add x x₁) (⊢-Add y y₁) = ≡-refl
    tuniq (⊢-Lt x x₁) (⊢-Lt y y₁) = ≡-refl
    tuniq (⊢-If x x₁ x₂) (⊢-If y y₁ y₂) = tuniq x₂ y₂

    {- Theorem 1.4.3.2 : Subject reduction -}
    sred : {p p' : Prog} {A : Type} → (p ⇒ p') → ⊢ p ∷ A → ⊢ p' ∷ A
    sred (⇒-Add m n) (⊢-Add p∷A p∷A₁) = ⊢-Nat (m +ℕ n)
    sred (⇒-Add-l p⇒p' q) (⊢-Add p∷A q∷A) = ⊢-Add (sred p⇒p' p∷A) q∷A
    sred (⇒-Add-r p p⇒p') (⊢-Add p∷A q∷A) = ⊢-Add p∷A (sred p⇒p' q∷A)
    sred (⇒-Lt m n) (⊢-Lt p∷A q∷A) = ⊢-Bool (is m < n)
    sred (⇒-Lt-l p⇒p' q) (⊢-Lt p∷A q∷A) = ⊢-Lt (sred p⇒p' p∷A) q∷A
    sred (⇒-Lt-r p p⇒p') (⊢-Lt p∷A q∷A) = ⊢-Lt p∷A (sred p⇒p' q∷A)
    sred (⇒-If p⇒p' q r) (⊢-If p∷Bool q∷A r∷A) = ⊢-If (sred p⇒p' p∷Bool) q∷A r∷A
    sred (⇒-If-t p q) (⊢-If (⊢-Bool .true) q∷A r∷A) = q∷A
    sred (⇒-If-f p q) (⊢-If (⊢-Bool .false) q∷A r∷A) = r∷A

    {- Theorem 1.4.3.3 : Progress -}
    prgs : {p : Prog} {A : Type} 
        → ⊢ p ∷ A 
        → Σ Value (λ v → p ≡ V v) ⊎ Σ Prog (λ p' → p ⇒ p')
    prgs (⊢-Nat n) = inj₁ (VNat n , ≡-refl)
    prgs (⊢-Bool b) = inj₁ (VBool b , ≡-refl)
    prgs (⊢-Add p∷TNat q∷TNat) with prgs p∷TNat
    prgs (⊢-Add p∷TNat q∷TNat) | inj₁ (v , p≡v) with prgs q∷TNat 
    prgs (⊢-Add p∷TNat q∷TNat) | inj₁ (VNat m , ≡-refl) | inj₁ (VNat n , ≡-refl) = inj₂ (V (VNat (m +ℕ n)) , ⇒-Add m n)
    prgs (⊢-Add p∷TNat q∷TNat) | inj₁ (v , p≡v) | inj₂ (q-prog , x) = inj₂ ((_ + q-prog) , ⇒-Add-r _ x)
    prgs (⊢-Add p∷TNat q∷TNat) | inj₂ (p' , p⇒p') = inj₂ ((p' + _) , ⇒-Add-l p⇒p' _)
    prgs (⊢-Lt p∷TNat q∷TNat) with prgs p∷TNat
    prgs (⊢-Lt p∷TNat q∷TNat) | inj₁ (a , x) with prgs q∷TNat
    prgs (⊢-Lt p∷TNat q∷TNat) | inj₁ (VNat m , ≡-refl) | inj₁ (VNat n , ≡-refl) = inj₂ (V (VBool (is m < n)) , ⇒-Lt m n)
    prgs (⊢-Lt p∷TNat q∷TNat) | inj₁ (v , p≡v) | inj₂ (q , q⇒q') = inj₂ ((_ < q) , ⇒-Lt-r _ q⇒q')
    prgs (⊢-Lt p∷TNat q∷TNat) | inj₂ (p , p⇒p') = inj₂ ((p < _) , ⇒-Lt-l p⇒p' _)
    prgs (⊢-If p∷TBool q∷A r∷A) with prgs p∷TBool
    prgs (⊢-If p∷TBool q∷A r∷A) | inj₁ (VBool false , ≡-refl) = inj₂ ( _ , ⇒-If-f _ _)
    prgs (⊢-If p∷TBool q∷A r∷A) | inj₁ (VBool true , ≡-refl) = inj₂ ( _ , ⇒-If-t _ _)
    prgs (⊢-If p∷TBool q∷A r∷A) | inj₂ (p' , p⇒p') = inj₂ ((if p' then _ else _) , ⇒-If p⇒p' _ _)

