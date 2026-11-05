module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ShiftLaw.Probability
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Translated lattice integration

The exact Lebesgue expectation used in `app:ch_waves:thm:sampling`
(paper.tex, lines 5924–5926), obtained by partitioning space into half-open cells.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling

/-- A translated lattice cell in the expectation argument of
`app:ch_waves:thm:sampling`. -/
def latticeCell (h : ℝ) (a : Point) (m : Lattice) : Set Point :=
  Set.univ.pi fun i ↦ Set.Ico (a i + h * (m i : ℝ)) (a i + h * (m i : ℝ) + h)

/-- The cells in `app:ch_waves:thm:sampling` are measurable. -/
theorem measurableSet_latticeCell (h : ℝ) (a : Point) (m : Lattice) :
    MeasurableSet (latticeCell h a m) := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

/-- Integer floors identify the unique lattice cell in
`app:ch_waves:thm:sampling`. -/
theorem mem_latticeCell_iff {h : ℝ} (hh : 0 < h) (a x : Point) (m : Lattice) :
    x ∈ latticeCell h a m ↔ ∀ i, ⌊(x i - a i) / h⌋ = m i := by
  simp only [latticeCell, Set.mem_univ_pi, Set.mem_Ico, Int.floor_eq_iff]
  apply forall_congr'
  intro i
  rw [le_div_iff₀ hh, div_lt_iff₀ hh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

/-- The half-open lattice cells cover space (`app:ch_waves:thm:sampling`). -/
theorem iUnion_latticeCell {h : ℝ} (hh : 0 < h) (a : Point) :
    (⋃ m : Lattice, latticeCell h a m) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨fun i ↦ ⌊(x i - a i) / h⌋,
    (mem_latticeCell_iff hh a x _).mpr fun _ ↦ rfl⟩

/-- Distinct half-open cells are disjoint (`app:ch_waves:thm:sampling`). -/
theorem pairwiseDisjoint_latticeCell {h : ℝ} (hh : 0 < h) (a : Point) :
    Pairwise (fun m n ↦ Disjoint (latticeCell h a m) (latticeCell h a n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hm hn
  apply hmn
  exact funext fun i ↦ ((mem_latticeCell_iff hh a x m).mp hm i).symm.trans
    ((mem_latticeCell_iff hh a x n).mp hn i)

/-- Each cell is a translate of the shift cube (`app:ch_waves:thm:sampling`). -/
theorem latticeCell_eq_image (h : ℝ) (a : Point) (m : Lattice) :
    latticeCell h a m = (fun u : Point ↦ (a + fun i ↦ h * (m i : ℝ)) + u) ''
      shiftCube h := by
  ext x
  simp only [latticeCell, Set.mem_univ_pi, Set.mem_Ico, Set.mem_image]
  constructor
  · intro hx
    refine ⟨x - (a + fun i ↦ h * (m i : ℝ)), mem_shiftCube.mpr ?_, by abel⟩
    intro i
    have hi := hx i
    dsimp
    constructor <;> linarith
  · rintro ⟨u, hu, rfl⟩
    intro i
    have hi := mem_shiftCube.mp hu i
    dsimp
    constructor <;> linarith

/-- Translation preserves the cell integral (`app:ch_waves:thm:sampling`). -/
theorem integral_latticeCell {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ) (a : Point) (m : Lattice) (f : Point → F) :
    ∫ x in latticeCell h a m, f x =
      ∫ u in shiftCube h, f ((a + fun i ↦ h * (m i : ℝ)) + u) := by
  rw [latticeCell_eq_image]
  exact (measurePreserving_add_left volume (a + fun i ↦ h * (m i : ℝ))).setIntegral_image_emb
    (Homeomorph.addLeft (a + fun i ↦ h * (m i : ℝ))).measurableEmbedding _ _

/-- The sum of all translated cell integrals is the full integral
(`app:ch_waves:thm:sampling`). -/
theorem integral_eq_tsum_shiftCube {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ} (hh : 0 < h) (a : Point) (f : Point → F) (hf : Integrable f) :
    ∫ x, f x = ∑' m : Lattice,
      ∫ u in shiftCube h, f ((a + fun i ↦ h * (m i : ℝ)) + u) := by
  have he := integral_iUnion (measurableSet_latticeCell h a)
    (pairwiseDisjoint_latticeCell hh a) (f := f)
    (by simpa only [iUnion_latticeCell hh a, IntegrableOn, Measure.restrict_univ] using hf)
  simpa only [iUnion_latticeCell hh a, Measure.restrict_univ, integral_latticeCell] using he

/-- A continuous function is integrable under the uniform shift law, without a
global bound (`app:ch_waves:thm:sampling`). -/
theorem integrable_uniformShift_of_continuous {F : Type*} [NormedAddCommGroup F]
    {h : ℝ} (hh : 0 < h) {f : Point → F} (hf : Continuous f) :
    Integrable f (uniformShift h) := by
  have hi : IntegrableOn f (shiftCube h) :=
    (hf.integrableOn_Icc (a := (0 : Point)) (b := fun _ ↦ h)).mono_set (by
      intro u hu
      exact ⟨fun i ↦ (mem_shiftCube.mp hu i).1, fun i ↦ (mem_shiftCube.mp hu i).2.le⟩)
  exact hi.smul_measure (by
    rw [ENNReal.inv_ne_top, volume_shiftCube]
    exact pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hh)))

/-- Finite truncation of translated lattice averaging, when all omitted terms
vanish on the shift cube (`app:ch_waves:thm:sampling`). This support condition is
verified for the literal blocks using `offset_bound`. -/
theorem integral_uniformShift_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ} (hh : 0 < h) (a : Point) (f : Point → F) (hf : Continuous f)
    (hfi : Integrable f) (s : Finset Lattice)
    (hs : ∀ m ∉ s, ∀ u ∈ shiftCube h, f ((a + fun i ↦ h * (m i : ℝ)) + u) = 0) :
    ∫ u, (h ^ 3) • (∑ m ∈ s, f ((a + fun i ↦ h * (m i : ℝ)) + u)) ∂uniformShift h =
      ∫ x, f x := by
  rw [integral_uniformShift hh, integral_smul, integral_finsetSum]
  · rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hh.ne'), one_smul]
    rw [integral_eq_tsum_shiftCube hh a f hfi]
    exact (tsum_eq_sum fun m hm ↦ setIntegral_eq_zero_of_forall_eq_zero (hs m hm)).symm
  · intro m _
    exact ((hf.comp (continuous_const.add continuous_id)).integrableOn_Icc
      (a := (0 : Point)) (b := fun _ ↦ h)).mono_set (by
        intro u hu
        exact ⟨fun i ↦ (mem_shiftCube.mp hu i).1, fun i ↦ (mem_shiftCube.mp hu i).2.le⟩)

/-- Compact support gives a single finite offset set valid for every admissible
shift (`app:ch_waves:thm:sampling`). -/
theorem exists_finite_lattice_truncation {F : Type*} [Zero F] {f : Point → F}
    (hfc : HasCompactSupport f) {h : ℝ} (hh : 0 < h) (a : Point) :
    ∃ s : Finset Lattice, ∀ m ∉ s, ∀ u ∈ shiftCube h,
      f ((a + fun i ↦ h * (m i : ℝ)) + u) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
    hfc.isCompact.isBounded
  refine ⟨integerCube ⌈(R + ‖a‖ + h) / h⌉₊, ?_⟩
  intro m hm u hu
  by_contra hn
  apply hm
  apply mem_integerCube.mpr
  have hz := hR (subset_tsupport f hn)
  have hz' : ‖(a + fun i ↦ h * (m i : ℝ)) + u‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  intro i
  have hzi : |a i + h * (m i : ℝ) + u i| ≤ R :=
    (norm_le_pi_norm ((a + fun i ↦ h * (m i : ℝ)) + u) i).trans hz'
  have hai : |a i| ≤ ‖a‖ := norm_le_pi_norm a i
  have hui := mem_shiftCube.mp hu i
  have hmi : |(m i : ℝ)| ≤ (R + ‖a‖ + h) / h := by
    rw [le_div_iff₀ hh]
    have hzabs := abs_le.mp hzi
    have haabs := abs_le.mp hai
    rcases le_total 0 (m i : ℝ) with hi | hi
    · rw [abs_of_nonneg hi]
      nlinarith
    · rw [abs_of_nonpos hi]
      nlinarith
  have hc := hmi.trans (Nat.le_ceil ((R + ‖a‖ + h) / h))
  exact_mod_cast hc

/-- The translated lattice sum is Bochner integrable under the uniform law
for a continuous compactly supported integrand (`app:ch_waves:thm:sampling`). -/
theorem integrable_uniformShift_tsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ} (hh : 0 < h) (a : Point) (f : Point → F)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun u ↦ (h ^ 3) • (∑' m : Lattice,
      f ((a + fun i ↦ h * (m i : ℝ)) + u))) (uniformShift h) := by
  obtain ⟨s, hs⟩ := exists_finite_lattice_truncation hfc hh a
  have hi : Integrable (fun u ↦ (h ^ 3) • (∑ m ∈ s,
      f ((a + fun i ↦ h * (m i : ℝ)) + u))) (uniformShift h) := by
    apply integrable_uniformShift_of_continuous hh
    apply Continuous.const_smul
    apply continuous_finsetSum
    intro m _
    exact hf.comp (continuous_const.add continuous_id)
  apply hi.congr
  filter_upwards [ae_mem_shiftCube h] with u hu
  rw [tsum_eq_sum fun m hm ↦ hs m hm u hu]

/-- Uniformly translating a lattice has exactly Lebesgue expectation for every
continuous compactly supported Banach-valued integrand
(`app:ch_waves:thm:sampling`, paper.tex, lines 5924–5926). -/
theorem integral_uniformShift_tsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {h : ℝ} (hh : 0 < h) (a : Point) (f : Point → F)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ u, (h ^ 3) • (∑' m : Lattice, f ((a + fun i ↦ h * (m i : ℝ)) + u))
      ∂uniformShift h = ∫ x, f x := by
  obtain ⟨s, hs⟩ := exists_finite_lattice_truncation hfc hh a
  calc
    _ = ∫ u, (h ^ 3) • (∑ m ∈ s, f ((a + fun i ↦ h * (m i : ℝ)) + u))
        ∂uniformShift h := by
      apply integral_congr_ae
      filter_upwards [ae_mem_shiftCube h] with u hu
      rw [tsum_eq_sum fun m hm ↦ hs m hm u hu]
    _ = _ := integral_uniformShift_sum hh a f hf (hf.integrable_of_hasCompactSupport hfc) s hs

end JanetCartan.Sampling
