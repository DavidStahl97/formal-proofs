data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

test : {A : Set} → A → A
test A = A

test1 : {A B : Set} → B → A → A
test1 B A = B