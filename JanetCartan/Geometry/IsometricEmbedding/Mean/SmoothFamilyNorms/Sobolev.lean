module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevProduct

/-!
# Weighted L² and integer Sobolev seminorms of smooth families

Exact square-sum conventions for `main:lem:mean-recurrence`. Smoothness proves
all integrability and Fourier summability obligations. No canonical update or
recurrence estimate is an input to these constructions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean.SmoothPeriodicFamily

variable {d : ℕ} {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]

section Normed
variable [NormedSpace ℝ F]

omit [Fintype ι] in
/-- `main:lem:mean-recurrence`: an L² class has exactly the integral norm of
its smooth component representative. -/
theorem norm_componentL2 (i : ι) (D : SmoothPeriodicFamily d ι F) :
    ‖componentL2 i D‖ = periodicL2Norm (fun x ↦ D.val x i) := by
  change ‖(memLp D i).toLp (fun x ↦ D.val x i)‖ = _
  rw [Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (memLp D i)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, periodicL2Norm]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- `main:lem:mean-recurrence`: the weighted L² seminorm on actual smooth families. -/
def l2Seminorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    Seminorm ℝ (SmoothPeriodicFamily d ι F) :=
  weightedSquareSeminorm μ hμ (fun i ↦ (normSeminorm ℝ (PeriodicL2 d F)).comp (componentL2 i))

/-- `main:lem:mean-recurrence`: exact agreement with the existing weighted L² size. -/
theorem l2Seminorm_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D : SmoothPeriodicFamily d ι F) :
    l2Seminorm μ hμ D = weightedPeriodicL2Norm μ D.val := by
  rw [l2Seminorm, weightedSquareSeminorm_eq]
  simp only [Seminorm.comp_apply, coe_normSeminorm, norm_componentL2, weightedPeriodicL2Norm]

/-- `main:lem:mean-recurrence`: weighted Cʳ triangle inequality, with constant one. -/
theorem weightedCNorm_add_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (r : ℕ)
    (D E : SmoothPeriodicFamily d ι F) :
    weightedPeriodicCNorm μ r (D + E).val ≤
      weightedPeriodicCNorm μ r D.val + weightedPeriodicCNorm μ r E.val := by
  simpa only [cSeminorm_eq] using map_add_le_add (cSeminorm μ hμ r) D E

/-- `main:lem:mean-recurrence`: real homogeneity in the weighted Cʳ convention. -/
theorem weightedCNorm_smul (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (r : ℕ)
    (c : ℝ) (D : SmoothPeriodicFamily d ι F) :
    weightedPeriodicCNorm μ r (c • D).val = ‖c‖ * weightedPeriodicCNorm μ r D.val := by
  simpa only [cSeminorm_eq] using map_smul_eq_mul (cSeminorm μ hμ r) c D

/-- `main:lem:mean-recurrence`: weighted L² triangle inequality, with constant one. -/
theorem weightedL2Norm_add_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D E : SmoothPeriodicFamily d ι F) :
    weightedPeriodicL2Norm μ (D + E).val ≤
      weightedPeriodicL2Norm μ D.val + weightedPeriodicL2Norm μ E.val := by
  simpa only [l2Seminorm_eq] using map_add_le_add (l2Seminorm μ hμ) D E

/-- `main:lem:mean-recurrence`: real homogeneity in the weighted L² convention. -/
theorem weightedL2Norm_smul (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (c : ℝ) (D : SmoothPeriodicFamily d ι F) :
    weightedPeriodicL2Norm μ (c • D).val = ‖c‖ * weightedPeriodicL2Norm μ D.val := by
  simpa only [l2Seminorm_eq] using map_smul_eq_mul (l2Seminorm μ hμ) c D

end Normed

section Hilbert
variable [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `main:lem:mean-recurrence`: smoothness places every component in the actual
integer Fourier Sobolev subspace of L². -/
def componentSobolev (s : ℕ) (i : ι) :
    SmoothPeriodicFamily d ι F →ₗ[ℝ] periodicSobolevLevel d F s :=
  (componentL2 i).codRestrict _ (fun D ↦
    (smooth D i).toLp_mem_periodicSobolevLevel s (memLp D i))

omit [Fintype ι] in
/-- `main:lem:mean-recurrence`: Sobolev realization retains the L² component. -/
@[simp] theorem componentSobolev_val (s : ℕ) (i : ι)
    (D : SmoothPeriodicFamily d ι F) :
    (componentSobolev s i D).val = componentL2 i D := rfl

/-- `main:lem:mean-recurrence`: the weighted integer Sobolev seminorm, using
the existing convergent Fourier analysis map. -/
def sobolevSeminorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ) :
    Seminorm ℝ (SmoothPeriodicFamily d ι F) :=
  weightedSquareSeminorm μ hμ (fun i ↦
    (periodicSobolevSeminorm s).comp (componentSobolev s i))

/-- `main:lem:mean-recurrence`: exact agreement with the existing square-sum
Fourier Sobolev norm; no norm-equivalence constants are introduced. -/
theorem sobolevSeminorm_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ)
    (D : SmoothPeriodicFamily d ι F) :
    sobolevSeminorm μ hμ s D = weightedPeriodicSobolevNorm μ s D.val := by
  rw [sobolevSeminorm, weightedSquareSeminorm_eq]
  simp only [Seminorm.comp_apply, periodicSobolevSeminorm_eq, componentSobolev_val, weightedPeriodicSobolevNorm, periodicSobolevNorm,
    periodicFourierCoeff_congr_ae (componentL2_coe_ae _ D)]

/-- `main:lem:mean-recurrence`: Parseval identifies the zeroth weighted
Sobolev seminorm with the weighted L² seminorm. -/
theorem sobolevSeminorm_zero (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    sobolevSeminorm (d := d) (F := F) μ hμ 0 = l2Seminorm μ hμ := by
  ext D
  simp only [sobolevSeminorm, l2Seminorm, weightedSquareSeminorm_eq,
    Seminorm.comp_apply, periodicSobolevSeminorm_zero, componentSobolev_val, coe_normSeminorm]

/-- `main:lem:mean-recurrence`: weighted Sobolev triangle inequality, with constant one. -/
theorem weightedSobolevNorm_add_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ)
    (D E : SmoothPeriodicFamily d ι F) :
    weightedPeriodicSobolevNorm μ s (D + E).val ≤
      weightedPeriodicSobolevNorm μ s D.val + weightedPeriodicSobolevNorm μ s E.val := by
  simpa only [sobolevSeminorm_eq] using map_add_le_add (sobolevSeminorm μ hμ s) D E

/-- `main:lem:mean-recurrence`: real homogeneity in the weighted Sobolev convention. -/
theorem weightedSobolevNorm_smul (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ)
    (c : ℝ) (D : SmoothPeriodicFamily d ι F) :
    weightedPeriodicSobolevNorm μ s (c • D).val =
      ‖c‖ * weightedPeriodicSobolevNorm μ s D.val := by
  simpa only [sobolevSeminorm_eq] using map_smul_eq_mul (sobolevSeminorm μ hμ s) c D

end Hilbert

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `main:lem:mean-recurrence`: the concrete complex Frobenius-matrix
Sobolev seminorm. The local Hilbert realization preserves this norm exactly. -/
def matrixSobolevSeminorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ) :
    Seminorm ℝ (SmoothPeriodicFamily d ι (Matrix m n ℂ)) :=
  letI := matrixFrobeniusInnerProductSpace (m := m) (n := n) (E := ℂ)
  sobolevSeminorm μ hμ s

/-- `main:lem:mean-recurrence`: exact agreement for the actual derivative matrices. -/
theorem matrixSobolevSeminorm_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s : ℕ)
    (D : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    matrixSobolevSeminorm μ hμ s D = weightedPeriodicSobolevNorm μ s D.val := by
  let := matrixFrobeniusInnerProductSpace (m := m) (n := n) (E := ℂ)
  exact sobolevSeminorm_eq μ hμ s D

end JanetCartan.CurrentMean.SmoothPeriodicFamily
