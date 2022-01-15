module logic.aaa where
  data Greeting : Set where
    hello : Greeting

  greet : Greeting
  greet = hello

  test : {A : Set} → A → A
  test A = A