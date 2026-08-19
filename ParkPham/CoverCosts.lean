import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Powerset
import ParkPham.FiniteSetSystems

namespace ParkPham

section FiniteGroundSet

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {p : ℝ}
variable {ℱ 𝒢 𝒢₁ 𝒢₂ ℋ ℋ₁ ℋ₂ : SetFamily α}

def Covers (𝒢 ℋ : SetFamily α) : Prop :=
  ℋ ⊆ ⟪𝒢⟫

def pCost (p : ℝ) (ℱ : SetFamily α) : ℝ :=
  ∑ S ∈ ℱ, p ^ S.card

def IsPCheap (p : ℝ) (ℱ : SetFamily α) : Prop :=
  pCost p ℱ <= 1 / 2

def IsPSmall (p : ℝ) (ℱ : SetFamily α) : Prop :=
  ∃ 𝒢, Covers 𝒢 ℱ ∧ IsPCheap p 𝒢


instance decidableCovers (𝒢 ℋ : SetFamily α) : Decidable (Covers 𝒢 ℋ) := by
  unfold Covers
  infer_instance

theorem covers_self (ℋ : SetFamily α) : Covers ℋ ℋ := by
  intro S hS
  exact SetFamily.mem_upperClosure.mpr
    ⟨S, hS, fun _ h => h⟩

lemma Covers.of_subset {C : SetFamily α}
    (hC_covers_ℋ : Covers C ℋ) (h : 𝒢 ⊆ ℋ) : Covers C 𝒢 := by
  intro S hS_in_𝒢
  exact hC_covers_ℋ (h hS_in_𝒢)

def coveringFamilies (ℋ : SetFamily α) : Finset (SetFamily α) :=
  Finset.univ.filter fun 𝒢 => Covers 𝒢 ℋ

@[simp]
theorem mem_coveringFamilies : 𝒢 ∈ coveringFamilies ℋ ↔ Covers 𝒢 ℋ := by
  simp [coveringFamilies]

theorem coveringFamilies_nonempty (ℋ : SetFamily α) : (coveringFamilies ℋ).Nonempty := by
  exact ⟨ℋ, mem_coveringFamilies.mpr (covers_self ℋ)⟩

-- cover cost is the cost of the cheapest cover of ℋ
def coverCost (p : ℝ) (ℋ : SetFamily α) : ℝ :=
  (coveringFamilies ℋ).inf'
    (coveringFamilies_nonempty ℋ)
    (pCost p)

theorem exists_optimal_cover (p : ℝ) (ℋ : SetFamily α) :
    ∃ 𝒢, Covers 𝒢 ℋ ∧ coverCost p ℋ = pCost p 𝒢 := by
  obtain ⟨𝒢, h𝒢_mem, h𝒢_cost⟩ :=
    Finset.exists_mem_eq_inf' (coveringFamilies_nonempty ℋ) (pCost p)
  refine ⟨𝒢, ?_, ?_⟩
  · exact mem_coveringFamilies.mp h𝒢_mem
  · simpa only [coverCost] using h𝒢_cost

/- coverCost is (roughly) an outer measure -/
lemma coverCost_le_pCost_of_covers (h : Covers 𝒢 ℋ) : coverCost p ℋ ≤ pCost p 𝒢 := by
  unfold coverCost
  exact Finset.inf'_le _ (mem_coveringFamilies.mpr h)

lemma pCost_nonneg (hp : 0 ≤ p) : 0 ≤ pCost p 𝒢 := by
  unfold pCost
  apply Finset.sum_nonneg
  intro S hS
  exact pow_nonneg hp S.card

lemma coverCost_nonneg (hp: 0 ≤ p) : 0 ≤ coverCost p 𝒢 := by
  unfold coverCost
  apply Finset.le_inf'
  intro ℋ hℋ
  exact pCost_nonneg hp

theorem coverCost_empty (hp : 0 ≤ p) : coverCost p (∅ : SetFamily α) = 0 := by
  apply le_antisymm
  exact coverCost_le_pCost_of_covers (covers_self ∅)
  exact coverCost_nonneg hp

theorem coverCost_mono (h : 𝒢 ⊆ ℋ) : coverCost p 𝒢 ≤ coverCost p ℋ := by
  apply Finset.le_inf'
  intro 𝒞 h𝒞
  have h𝒞_covers_ℋ : Covers 𝒞 ℋ :=
    mem_coveringFamilies.mp h𝒞
  have h𝒞_covers_𝒢 : Covers 𝒞 𝒢 := h𝒞_covers_ℋ.of_subset h
  exact coverCost_le_pCost_of_covers h𝒞_covers_𝒢

lemma covers_union (h₁ : Covers 𝒢₁ ℋ₁) (h₂ : Covers 𝒢₂ ℋ₂) :
    Covers (𝒢₁ ∪ 𝒢₂) (ℋ₁ ∪ ℋ₂) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS_in_ℋ₁ | hS_in_ℋ₂
  · obtain ⟨T, hT_in_𝒢₁, hT_subset_S⟩ := SetFamily.mem_upperClosure.mp (h₁ hS_in_ℋ₁)
    exact SetFamily.mem_upperClosure.mpr
      ⟨T, Finset.mem_union_left 𝒢₂ hT_in_𝒢₁, hT_subset_S⟩
  · obtain ⟨T, hT_in_𝒢₂, hT_subset_S⟩ := SetFamily.mem_upperClosure.mp (h₂ hS_in_ℋ₂)
    exact SetFamily.mem_upperClosure.mpr
      ⟨T, Finset.mem_union_right 𝒢₁ hT_in_𝒢₂, hT_subset_S⟩

lemma pCost_union_le (hp : 0 ≤ p) :
    pCost p (𝒢₁ ∪ 𝒢₂) ≤ pCost p 𝒢₁ + pCost p 𝒢₂ := by
  unfold pCost
  rw [← Finset.sum_union_inter]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro S hS
  exact pow_nonneg hp S.card

theorem coverCost_union_le (hp : 0 ≤ p) :
    coverCost p (ℋ₁ ∪ ℋ₂) ≤ coverCost p ℋ₁ + coverCost p ℋ₂ := by
  obtain ⟨𝒢₁, h𝒢₁_covers, h𝒢₁_cost⟩ :=
    exists_optimal_cover p ℋ₁
  obtain ⟨𝒢₂, h𝒢₂_covers, h𝒢₂_cost⟩ :=
    exists_optimal_cover p ℋ₂

  calc
    coverCost p (ℋ₁ ∪ ℋ₂)
        ≤ pCost p (𝒢₁ ∪ 𝒢₂) :=
          coverCost_le_pCost_of_covers
            (covers_union h𝒢₁_covers h𝒢₂_covers)
    _ ≤ pCost p 𝒢₁ + pCost p 𝒢₂ :=
          pCost_union_le hp
    _ = coverCost p ℋ₁ + coverCost p ℋ₂ := by
          rw [h𝒢₁_cost, h𝒢₂_cost]

/- end outer measure properties -/



end FiniteGroundSet

end ParkPham
