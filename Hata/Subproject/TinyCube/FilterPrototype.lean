
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic
import Hata.Conventions

open Vector

--
-- This file describes the filtering type system and syntax,
-- as originally invented by @undefdev and @MxmUrw on 2023-02-10.
--
-- 
-- # Type system
--
-- We concern ourselves with *table types*, denoted by `T I A` where `I` is a _finite_ index type,
-- and `A` is (any) content type. The tables have named dimensions and named indices. This is done
-- by having the names included in the index types.
-- 
-- The index types are as follows:

inductive Name where
  | mkName : String -> Name

open Name
instance : Coe String Name := ⟨ mkName ⟩

inductive IndexType : 𝒰 0 where
  | Idx : Name -> ℕ -> IndexType
  | Prod : List IndexType -> IndexType
  | Sum : List IndexType -> IndexType

open IndexType


--
-- For example, the index type for the m×n table, with indices called "row" and "col" would be:
example (m n : ℕ) : IndexType := Prod [Idx "row" m, Idx "col" n]
--
-- We can add another, single "err" row by writing: 
example (m n : ℕ) : IndexType := Prod [(Sum [Idx "row" m, Idx "err" 1]), Idx "col" n]
--

--
-- TODO: We need to typecheck auto-lambdas for index types,
--       this means that: given a term (a : b : c), it is a
--       case distinction, but we only know the cases by
--       looking at the variables that are used in the sub-
--       terms.
--       Similarly, but with a distinct mechanism, given
--       terms (x , y, z), we search for assignments
--       (u := x, v := y, w := z)
--
-- Given an index type, we can compute the list of indices
--
def projIndex : IndexType -> Name -> List Name
  | Idx n size, m => sorry
  | IndexType.Prod Is, m => sorry
  | IndexType.Sum Is, m => sorry

--
-- ## More complex types
--

inductive Inv? : 𝒰 0 where
  | inv : Inv?
  | notInv : Inv?

mutual

  inductive FilterKind : 𝒰 0 where
    | pure : Inv? -> FilterKind
    | aff : FType -> FilterKind

  inductive FType : 𝒰 0 where
    | Index : IndexType -> FType
    | Filter : IndexType -> FilterKind -> IndexType ->FType
    | Fun : FType -> FType -> FType
    | Table : IndexType -> FType -> FType
end

open Inv?
open FilterKind
open FType

infixl:80 " × " => FType.Prod
infixr:80 " ⇒ " => Fun
notation:80 A " ⊸[" X "]" B => Filter A X B
notation:120 I " |⇒ " A => Table I A

--
-- # Deps
--
-- inductive ListD : (A : )


--
-- # Typed terms
-- 
@[reducible]
def FCtx := Vector FType

mutual

  inductive ITerm : FCtx n -> IndexType -> FilterKind -> IndexType -> 𝒰 0 where
    | fcases : (∀ I, I ∈ Is -> ITerm Γ I any J) -> ITerm Γ (Sum Is) any J
    | ftuple : (∀ J, J ∈ Js -> ITerm Γ I any J) -> ITerm Γ I any (IndexType.Prod Js)
    | fproj : ITerm Γ I any (IndexType.Prod Js) -> J ∈ Js -> ITerm Γ I any J
    | finj : ITerm Γ I any J -> J ∈ Js -> ITerm Γ I any (IndexType.Sum Js)
    | fid: ITerm Γ I any I
    | fassign : (n1 n2 : String) -> ITerm Γ (Idx n1 k) any (Idx n2 k)
    -- | fterm : FTerm (Index I ::ᵥ nil) (Index J) -> ITerm Γ I any J

  inductive FTerm : FCtx n -> FType -> 𝒰 0 where
    -- basic type theory
    | var : (i : Fin n) -> Γ.get i = τ -> FTerm (n := n) Γ τ
    | app : FTerm Γ (A ⇒ B) -> FTerm Γ A -> FTerm Γ B
    | lam : FTerm (A ::ᵥ Γ) B -> FTerm Γ (A ⇒ B)
 
    -- filters
    -- | fproj : (Is : List IndexType) -> I -> I ∈ Is -> FTerm Γ (Index (Prod Is)) -> FTerm Γ I
 
    -- tables
    | filter : FTerm Γ (I ⊸[aff A] J) -> FTerm Γ ((I |⇒ A) ⇒ (J |⇒ A))
    | invf : FTerm Γ (I ⊸[pure inv] J) -> FTerm Γ (J ⊸[pure notInv] (Sum [I , Idx "else" 1]))

end

open ITerm
open FTerm

infixl:80 " $$ " => app
prefix:60 "Λ " => lam
notation:100 "V" i => var i rfl
notation:50 Γ "⊢" τ => FTerm Γ τ

--------------------------------------------------------------------------------------------------
--
-- ## Examples
--

example (m n : ℕ): ITerm nil (Prod [Idx "row" m , Idx "col" n]) (pure inv) (Prod [Idx "row" m , Idx "c" n]) :=
  ftuple sorry

