module Dave.ComputerScience.Datastructures.BinSearchTree where
    
    data BinSearchTree {ℓ} {A : Set ℓ} : A → A → Set where
        leaf : ∀ {l u : A} 
