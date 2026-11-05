module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Jets
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# A genuine compact cutoff extension

For the local restriction norm in `app:ch_background:prop:bg-mixed-physical`,
the extension is literally a fixed scalar cutoff times the periodic lift.
Its weak jets and all L² bounds are proved, rather than assumed as extension
operator data. The cutoff is independent of the output and derivative order.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem cutoff_derivative_bound {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s j : ℕ) (hj : j ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j χ x‖ ≤ cNorm (tsupport χ) s χ := by
  by_cases hx : x ∈ tsupport χ
  · exact norm_iteratedFDeriv_le_cNorm hc (hχ.of_le (by simp)) hx hj
  · have hz : iteratedFDeriv ℝ j χ x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (tsupport_iteratedFDeriv_subset j (subset_tsupport _ hx'))
    rw [hz, norm_zero]
    exact cNorm_nonneg _ _ _

/-- An explicit fixed cutoff constant, using its actual compact-support jets
and dimension/order comparison (`app:ch_background:eq:bg-Vaux-raw-band`). -/
def localCutoffConstant (s : ℕ) (χ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (s + 1), ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * cNorm (tsupport χ) s χ) *
    Real.sqrt ((s + 1) * BallExtension.frechetEnergyComparisonConstant n s)

/-- Nonnegativity of the explicit cutoff constant (`app:not:fourier`). -/
theorem localCutoffConstant_nonneg (s : ℕ) (χ : EuclideanSpace ℝ (Fin n) → ℝ) :
    0 ≤ localCutoffConstant s χ := by
  apply mul_nonneg _ (Real.sqrt_nonneg _)
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)

private theorem cutoff_jet_lpNorm_le
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (s j : ℕ) (hj : j ≤ s) :
    (eLpNorm (iteratedFDeriv ℝ j (fun x ↦ χ x • periodicLift f x)) 2 volume).toReal ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * cNorm (tsupport χ) s χ) *
        jetL2Norm (halfOpenCell n) s (fun k ↦ iteratedFDeriv ℝ k (periodicLift f)) := by
  let A := cNorm (tsupport χ) s χ
  let J := fun k ↦ iteratedFDeriv ℝ k (periodicLift f)
  let μ := volume.restrict (halfOpenCell n)
  have hm (i : ℕ) : MemLp (fun x ↦ ((j.choose i : ℝ) * A) * ‖J (j-i) x‖) 2 μ := by
    exact (memLp_iteratedFDeriv_periodicLift_cell hf (j-i)).norm.const_mul _
  have hprod : ContDiff ℝ ∞ (fun x ↦ χ x • periodicLift f x) := hχ.smul hf.2
  have he : Function.support (iteratedFDeriv ℝ j (fun x ↦ χ x • periodicLift f x)) ⊆
      halfOpenCell n :=
    (subset_tsupport _).trans ((tsupport_iteratedFDeriv_subset j).trans
      ((tsupport_smul_subset_left χ (periodicLift f)).trans hs))
  rw [← eLpNorm_restrict_eq_of_support_subset (p := 2) (μ := volume)
    (hprod.continuous_iteratedFDeriv (m := j) (by simp)).aestronglyMeasurable he]
  change lpNorm _ 2 μ ≤ _
  calc
    _ ≤ lpNorm (∑ i ∈ Finset.range (j+1),
        fun x ↦ ((j.choose i : ℝ) * A) * ‖J (j-i) x‖) 2 μ := by
      apply lpNorm_mono_real (memLp_finsetSum' _ (fun i _ ↦ hm i))
      intro x
      apply (norm_iteratedFDeriv_smul_le hχ hf.2 x (by simp : (j : ℕ∞ω) ≤ ∞)).trans
      simp only [Finset.sum_apply]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (cutoff_derivative_bound hχ hc s i (by have := Finset.mem_range.mp hi; omega) x)
        (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ Finset.range (j+1),
        lpNorm (fun x ↦ ((j.choose i : ℝ) * A) * ‖J (j-i) x‖) 2 μ :=
      lpNorm_sum_le (fun i _ ↦ hm i) (by norm_num)
    _ = ∑ i ∈ Finset.range (j+1),
        ((j.choose i : ℝ) * A) * (eLpNorm (J (j-i)) 2 μ).toReal := by
      apply Finset.sum_congr rfl
      intro i _
      have hA : 0 ≤ (j.choose i : ℝ) * A := mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
      change lpNorm (((j.choose i : ℝ) * A) • (fun x ↦ ‖J (j-i) x‖)) 2 μ = _
      rw [lpNorm_const_smul, lpNorm_norm
        (memLp_iteratedFDeriv_periodicLift_cell hf (j-i)).aestronglyMeasurable]
      simp only [Real.nnnorm_of_nonneg hA, NNReal.coe_mk, toReal_eLpNorm]
      rfl
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      exact Finset.single_le_sum (f := fun k ↦ (eLpNorm (J k) 2 μ).toReal)
        (fun _ _ ↦ ENNReal.toReal_nonneg) (Finset.mem_range.mpr (by omega))

end JanetCartan.AuxiliaryRawBand

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The literal cutoff of the periodic lift is a whole-space weak Sobolev
extension of the physical L² class, with an explicit bound at every order
(`app:ch_background:prop:bg-mixed-physical`). The premises specify only the
fixed cutoff's geometry, smoothness and plateau, not an extension estimate. -/
theorem exists_cutoff_sobolevExtension_of_eqOn
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)
    (hplateau : EqOn χ (fun _ ↦ 1) W)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W)
    (u : LocalL2 W F) (hu : g =ᵐ[volume.restrict W] u) (s : ℕ) :
    ∃ e : SobolevExtension W s u,
      e.toFun = (fun x ↦ χ x • periodicLift f x) ∧
      e.jetNorm ≤ localCutoffConstant s χ * periodicSobolevNorm s f := by
  have hprod : ContDiff ℝ ∞ (fun x ↦ χ x • periodicLift f x) := hχ.smul hf.2
  have hcomp : HasCompactSupport (fun x ↦ χ x • periodicLift f x) := hc.smul_right
  let e : SobolevExtension W s u := {
    toFun := fun x ↦ χ x • periodicLift f x
    jet := fun j ↦ iteratedFDeriv ℝ j (fun x ↦ χ x • periodicLift f x)
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hprod.of_le (by simp)) univ
    memLp_fun := hprod.continuous.memLp_of_hasCompactSupport hcomp
    memLp_jet := fun j _ ↦ memLp_iteratedFDeriv_of_contDiff_hasCompactSupport hprod hcomp j
    restrict_eq := by
      filter_upwards [ae_restrict_mem hW.measurableSet, hu] with x hx hx'
      rw [hplateau hx, one_smul, ← heq hx]
      exact hx' }
  refine ⟨e, rfl, ?_⟩
  calc
    e.jetNorm ≤ (∑ j ∈ Finset.range (s+1), ∑ i ∈ Finset.range (j+1),
        (j.choose i : ℝ) * cNorm (tsupport χ) s χ) *
        jetL2Norm (halfOpenCell n) s (fun k ↦ iteratedFDeriv ℝ k (periodicLift f)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj ↦ cutoff_jet_lpNorm_le hχ hc hs hf s j
        (by have := Finset.mem_range.mp hj; omega)
    _ ≤ (∑ j ∈ Finset.range (s+1), ∑ i ∈ Finset.range (j+1),
        (j.choose i : ℝ) * cNorm (tsupport χ) s χ) *
        (Real.sqrt ((s+1) * BallExtension.frechetEnergyComparisonConstant n s) *
          periodicSobolevNorm s f) := by
      apply mul_le_mul_of_nonneg_left (jetL2Norm_periodicLift_cell_le hf s)
      exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
        mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
    _ = _ := by rw [localCutoffConstant, mul_assoc]

/-- The actual physical L² class lies in the restriction Sobolev space and
satisfies the fixed-cutoff comparison (`app:ch_background:eq:bg-Vaux-raw-band`).
This is obtained from the constructed weak extension, not from its infimum
being zero off the Sobolev domain. -/
theorem restrictionSobolevNorm_le_periodicSobolevNorm_of_eqOn
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)
    (hplateau : EqOn χ (fun _ ↦ 1) W)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W)
    (u : LocalL2 W F) (hu : g =ᵐ[volume.restrict W] u) (s : ℕ) :
    MemRestrictionSobolev W s u ∧
      restrictionSobolevNorm W s u ≤ localCutoffConstant s χ * periodicSobolevNorm s f := by
  obtain ⟨e, _, hb⟩ := exists_cutoff_sobolevExtension_of_eqOn hW hχ hc hs hplateau hf heq u hu s
  exact ⟨⟨e⟩, (restrictionSobolevNorm_le e).trans hb⟩

end JanetCartan.AuxiliaryRawBand
