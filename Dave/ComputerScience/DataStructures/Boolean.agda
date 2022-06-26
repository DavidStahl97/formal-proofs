module Dave.ComputerScience.DataStructures.Boolean where

    data Bool : Set where
        false : Bool
        true : Bool    

    {-# BUILTIN BOOL  Bool  #-}
    {-# BUILTIN TRUE  true  #-}
    {-# BUILTIN FALSE false #-}  