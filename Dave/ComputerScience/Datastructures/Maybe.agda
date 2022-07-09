module Dave.ComputerScience.Datastructures.Maybe where
    data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
        nothing : Maybe A
        just : A → Maybe A