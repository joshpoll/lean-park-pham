import Mathlib

namespace ParkPham

abbrev SetFamily (α : Type*) := Finset (Finset α)

section FiniteGroundSet

-- α is a finite set with a decidable equality
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev 𝒳 : Finset α := Finset.univ

-- Override set comprehensions to return Finset instead of Set
local notation "{ " T " | " P " }" =>
  𝒳.powerset.filter fun T => P

def SetFamily.upperClosure (ℱ : SetFamily α) : SetFamily α :=
  { T | ∃ S ∈ ℱ, S ⊆ T }

notation "⟪" ℱ "⟫" => SetFamily.upperClosure ℱ

@[simp]
theorem SetFamily.coe_upperClosure (ℱ : SetFamily α) :
    (↑(SetFamily.upperClosure ℱ) : Set (Finset α)) =
      ↑(_root_.upperClosure (↑ℱ : Set (Finset α))) := by
  ext T
  simp [SetFamily.upperClosure, _root_.mem_upperClosure]

/-- Membership in the upward closure means containing one of its generators. -/
@[simp]
theorem SetFamily.mem_upperClosure {ℱ : SetFamily α} {T : Finset α} :
    T ∈ SetFamily.upperClosure ℱ ↔ ∃ S ∈ ℱ, S ⊆ T := by
  simp [SetFamily.upperClosure]

-- Correspondence with MathLib UpperSet
theorem upperClosure_isUpperSet (ℱ : SetFamily α) :
    IsUpperSet (⟪ℱ⟫ : Set (Finset α)) := by
  rw [SetFamily.coe_upperClosure]
  exact UpperSet.upper _

def Covers (𝒢 ℋ : SetFamily α) : Prop :=
  ℋ ⊆ ⟪𝒢⟫

namespace UpperClosureExample

/-- On the ground set `Fin 3`, start with the single generator `{0, 1}`. -/
def generators : SetFamily (Fin 3) :=
  {{0, 1}}

/-- Its upward closure consists of `{0, 1}` and `{0, 1, 2}`. -/
def closure : SetFamily (Fin 3) :=
  ⟪generators⟫

example : ({0, 1} : Finset (Fin 3)) ∈ closure := by
  simp [closure, generators, SetFamily.upperClosure]

example : ({0, 1, 2} : Finset (Fin 3)) ∈ closure := by
  simp [closure, generators, SetFamily.upperClosure]

example : ({0} : Finset (Fin 3)) ∉ closure := by
  native_decide

end UpperClosureExample

end FiniteGroundSet

end ParkPham
