module logic.test123 where
  data Greeting : Set where
    hello : Greeting

  greet : Greeting
  greet = hello

  test : {A : Set} → A → A
  test A = hello