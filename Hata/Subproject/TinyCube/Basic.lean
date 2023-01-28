
import Hata.Conventions


inductive UniType where
  | Int : UniType
  | Float : UniType
  | Array : UniType -> UniType

inductive Term where
  | Var : String -> Term
  | Add : Term -> Term -> Term
  | Mul : Term -> Term -> Term
  | Lambda : List String -> Term -> Term

open Term

infixl:80 " + " => Add

example : Term
  := Var "a"+Var "a"



