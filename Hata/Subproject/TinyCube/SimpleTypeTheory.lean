
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Option.Basic
import Hata.Conventions

----------------------------------------------
-- ## Types
--

inductive SType where
  | NN : SType
  | Prod : SType -> SType -> SType
  | Arr : SType -> SType -> SType

open SType

infixl:80 " × " => SType.Prod
infixr:80 " ⇒ " => Arr

----------------------------------------------
-- ## Context
--

abbrev SCtx := Vector SType

----------------------------------------------
-- ## Terms
--

----------------------------------------------
-- ## Typed terms
--

inductive STTerm : SCtx n -> SType -> 𝒰 0 where
  | var : (i : Fin n) -> Γ.get i = τ -> STTerm (n := n) Γ τ
  | app : STTerm Γ (A ⇒ B) -> STTerm Γ A -> STTerm Γ B
  | lam : STTerm (A ::ᵥ Γ) B -> STTerm Γ (A ⇒ B)

open STTerm

infixl:80 " $$ " => app
prefix:60 "Λ " => lam
notation:100 "V" i => var i rfl

@[reducible]
def iType : SType -> 𝒰 0
  | NN => ℕ
  | (Arr A B) => iType A -> iType B
  | (SType.Prod A B) => iType A × iType B

@[reducible]
def iCtx' : List SType -> 𝒰 0
  | [] => Unit
  | (τ :: τs) => iType τ × iCtx' τs

@[reducible]
def iCtx (Γ : SCtx n) : 𝒰 0 := iCtx' Γ.val



section

open Nat

def iVar (i : Fin n) (Γ : SCtx n) (Ts : iCtx Γ) : (iType (Γ.get i)) :=
  match n with
  | 0 => match Γ with
         | ⟨ [] , p ⟩ => match i with
                        | ⟨ i , p ⟩ => nomatch p
  | (succ n) => match Γ with
                | ⟨ (a :: as) , q ⟩ =>
                  let (T , Ts) := Ts
                  match i with
                  | ⟨ 0 , p ⟩ => T
                  | ⟨ succ i , p ⟩ => by
                      simp [*]
                      have p' : i < n := lt_of_succ_lt_succ p
                      exact iVar ⟨ i , p' ⟩ ⟨ as , (succ.inj q) ⟩ Ts
  
end

def iTerm : (t : STTerm Γ τ) -> iCtx Γ -> iType τ
  | var i p => by
      intro Γ
      have res := iVar i _ Γ
      rw [p] at res
      exact res
  | app f t =>
      let f' := iTerm f
      let t' := iTerm t
      λ Γ ↦ (f' Γ) (t' Γ)
  | lam f => λ Γ a ↦ iTerm f (a , Γ)
  


-- 
-- church numerals
--
def CN : SType := (NN ⇒ NN) ⇒ (NN ⇒ NN)

example : 0 < 1 := Nat.zero_lt_succ _

def zero : STTerm nil CN := lam (lam (var 0 rfl))
def one : STTerm nil CN := Λ (V 0)
def add : STTerm nil (CN ⇒ CN ⇒ CN) :=
  lam (lam (lam (lam (
    (app (app (var 3 rfl) (var 1 rfl))
    (app (app (var 2 rfl) (var 1 rfl))
       (var 0 rfl))
    )))))
def mul : STTerm nil (CN ⇒ CN ⇒ CN) := Λ Λ Λ (var 2 rfl $$ (var 1 rfl $$ V 0))

def two : STTerm nil CN := add $$ one $$ one
def three : STTerm nil CN := add $$ two $$ one

def run (x : STTerm Vector.nil CN) := iTerm (Γ := Vector.nil) x () (λ x ↦ x + 1) 0

#eval run (mul $$ three $$ three) 


