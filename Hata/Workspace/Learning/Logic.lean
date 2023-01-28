
-- prelude

inductive Bool' : Type where
  | true' : Bool'
  | false' : Bool'

open Bool'

def inv (x : Bool') : Bool' :=
  match x with
  | true' => false'
  | false' => true'


-----------------------------------------
-- Logic

inductive Bot

inductive Top
  | tt : Top

inductive Product (A : Type u) (B : Type v) where
  | pair : A → B → Product A B

open Product

infixl:80 " ⊗ " => Product
infixl:80 " , " => pair

def π₁ (x : A ⊗ B) : A :=
  match x with
  | a , _ => a

def π₂ : A ⊗ B -> B
  | (_ , b) => b

inductive Coproduct (A : Type u) (B : Type v) where
  | left : A -> Coproduct A B
  | right : B -> Coproduct A B

-- infixl:60 " ⊕⊕ " => Coproduct

open Coproduct

instance : Add (Type u) where
  add := Coproduct

instance : Mul (Type u) where
  mul := Product




def Biimplication (A : Type) (B : Type) : Type := 
  Product (A → B) (B → A)

infixl:50 " ↔ " => Biimplication



theorem Product_is_commutative : A ⊗ B ↔ B ⊗ A := by
  have P1 : A ⊗ B → B ⊗ A := λ (a , b) ↦ (b , a)
  have P2 : B ⊗ A → A ⊗ B := λ (b , a) ↦ (a , b)
  exact (P1 , P2)


def neg A := A -> Bot

-- prefix:100 "¬" => Negation

def Negation_triple : neg (neg (neg A)) -> neg A
  | f => λ a ↦ f (λ x ↦ x a)


def Distributive : (A ⊗ (B + C)) -> ((A ⊗ B) + (A ⊗ C))
  | a , left b  => left (a , b)
  | a , right c => right (a , c)



