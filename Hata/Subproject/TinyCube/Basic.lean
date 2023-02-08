
import Hata.Conventions
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip

open List

inductive UniType where
  | Bool : UniType
  | Int : UniType
  | Float : UniType
  | Array : UniType -> UniType

mutual
  inductive BaseTerm : 𝒰 0 where
    | mkint : ℤ -> BaseTerm
    | mkbool : Bool -> BaseTerm

    | add : Term -> Term -> BaseTerm
    | mul : Term -> Term -> BaseTerm
    | ift : Term -> Term -> Term -> BaseTerm

  inductive Term where
    | var : String -> Term
    | base : BaseTerm -> Term
    | lambda : List String -> Term -> Term
    | app : Term -> List Term -> Term
    | err : String -> Term
end

open Term
open BaseTerm

instance : Coe BaseTerm Term where
  coe := base

infixl:80 " + " => add

example : Term
  := var "a" + var "a"

structure Env where
  vars : List (String × Term)

open Env

def getFirst : List (A × Term) -> Term
  | [] => err ("could not find variable")
  | (_ , t) :: _ => t
  

mutual
  unsafe def runTerm (Γ : Env) (t : Term) : Term :=
    match t with
    | (var v) => getFirst (Γ.vars.filter (λ (v₂ , _) ↦ v₂ == v))
    | (base b) => runBaseTerm Γ b
    | (lambda vs t) => (lambda vs t)
    | (app t args) => match runTerm Γ t with
                      | (lambda vs t) =>
                        let Γ' : Env :=
                          ⟨ (zip vs args) ++ Γ.vars ⟩
                        runTerm Γ' t
                      | _ => err ""
    | (err e) => err e

  unsafe def runBaseTerm (Γ : Env) (t : BaseTerm) : Term :=
    match t with
    | (mkint n) => mkint n
    | (mkbool b) => mkbool b
    | (ift c a1 a2) => match runTerm Γ c with
                       | (mkbool b) => ite b (runTerm Γ a1) (runTerm Γ a2)
                       | _ => err "could not eval condition to boolean"

    | (add a1 a2) => match (runTerm Γ a1, runTerm Γ a2) with
                       | (mkint a1, mkint a2) => mkint (a1 + a2)
                       | _ => err "add: could not eval operand(s) to int"

    | (mul a1 a2) => match (runTerm Γ a1, runTerm Γ a2) with
                       | (mkint a1, mkint a2) => mkint (a1 * a2)
                       | _ => err "mul: could not eval operand(s) to int"
end

def Γ₀ : Env := ⟨ [] ⟩

unsafe def n : Term := runTerm Γ₀ (mkint 1)

-- open Lean.Eval

def printBaseTerm (b : BaseTerm) :=
  match b with
  | (mkint i) => repr i
  | _ => "could not eval"

def printTerm (t : Term) := 
  match t with
  | (base b) => printBaseTerm b
  | _ => "could not eval"

instance : Repr (BaseTerm) where
  reprPrec := λ t x ↦ printBaseTerm t
  -- eval (mkint i) x _ := eval i

instance : Repr Term where
  reprPrec := λ t x ↦ printTerm t
  -- eval (base a) _ _ := eval a

#eval (runTerm Γ₀ (add (mkint 1) (mkint 2)))

-- axiom a : terminates 
-- termination_by runTerm Γ t => sorry
--                runBaseTerm Γ t => sorry



