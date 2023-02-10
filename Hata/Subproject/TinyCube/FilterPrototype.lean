
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Hata.Conventions

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
-- The types of our type system are constructed from index types; we have a special filter function type.
--

inductive FTType : 𝒰 0 where
  | Filter : IndexType -> IndexType -> Option FTType -> FTType
  | Fun : FTType -> FTType -> FTType

