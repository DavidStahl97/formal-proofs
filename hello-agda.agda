import logic.aaa
import logic.test123

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

greet2 : logic.aaa.Greeting
greet2 = logic.aaa.hello