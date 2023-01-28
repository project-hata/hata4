
import Hata.Conventions

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.BooleanAlgebra
import Mathlib.Data.Real.Basic

structure TopologicalSpace (α : Type u) where
  (is_open        : Set α → Prop)
  (is_open_univ   : is_open ⊤)
  (is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
  (is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))


-- example (A : 𝒰 𝓁) : (∅ : Set A) = (λ x => False)
--   := rfl

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.of_closed {α : Type u}
  (T : Set (Set α))
  (empty_mem : ∅ ∈ T)
  (sInter_mem : ∀ A ≤ T, ⋂₀ A ∈ T)
  (union_mem : ∀ A B, A ∈ T → B ∈ T → A ∪ B ∈ T) :
  TopologicalSpace α
  :=
  {
    is_open := λ X => Xᶜ ∈ T
    is_open_univ := by simp [empty_mem]
    is_open_inter := by
      intros A B Ap Bp
      have := Set.compl_inter A B
      simp [*]
    is_open_sUnion := sorry
  }

-- #align topological_space TopologicalSpace

