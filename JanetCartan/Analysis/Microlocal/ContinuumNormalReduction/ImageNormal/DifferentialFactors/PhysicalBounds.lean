module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.Amplitude

/-!
# Physical coefficients in the differential-factor remainder

The remainder in `app:ch_background:prop:bg-frame`, Step 1, is affine in the
physical covector before division by the Bessel denominator. This separates
the physical derivatives from frequency decay without dropping any coefficient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.Pseudodifferential
open scoped ContDiff
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-- The physical coefficient array of the affine remainder: `none` is its
constant term, `some a` its coefficient of `kₐ`
(`app:ch_background:prop:bg-frame`, Step 1). -/
def differentialRemainderCoefficients (A : E → Fin d → Mat) (Z : E → Mat)
    (C μ : E → ℝ) (i l : Fin d) (p : E × E) : Option (Fin d) → ℂ
  | none => (μ p.1 * μ p.2 : ℝ) *
      ∑ j, (sourceProductCoefficient A Z C p.1 i j : ℂ) * Z p.2 l j
  | some a => (μ p.1 * μ p.2 : ℝ) * ∑ j,
      Complex.I * ((C p.1 * A p.1 a i j * Z p.2 l j : ℝ) -
        sourceProductCoefficient A Z C p.1 i j * A p.2 a l j)

/-- Exact affine-in-frequency expression of the coefficient remainder,
used to bound its physical derivatives
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem differentialRemainderAmplitude_eq_affine
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (x y ξ : E) (i l : Fin d) :
    differentialRemainderAmplitude A Z C μ x y ξ i l =
      ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ : ℝ) •
        ((∑ a, (((2 * Real.pi) • ξ) a : ℝ) •
          differentialRemainderCoefficients A Z C μ i l (x, y) (some a)) +
        differentialRemainderCoefficients A Z C μ i l (x, y) none) := by
  simp only [differentialRemainderAmplitude, differentialRemainderCoefficients,
    differentialPencil, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun a j ↦ _)]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_add, mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · ring

/-- The denominator times one physical frequency gains one full order;
this is the frequency estimate needed by the actual affine remainder
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem inverseDenominator_mul_norm_le_imageBesselSymbol (ξ : E) :
    (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ * ‖(2 * Real.pi) • ξ‖ ≤ imageBesselSymbol ξ := by
  let k := (2 * Real.pi) • ξ
  have hp : 0 < 1 + ‖k‖ ^ 2 := by positivity
  have hn : ‖k‖ ≤ (1 + ‖k‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  calc
    _ ≤ (1 + ‖k‖ ^ 2)⁻¹ * (1 + ‖k‖ ^ 2) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = imageBesselSymbol ξ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hp]
      norm_num [imageBesselSymbol, euclideanSobolevWeight, k]

/-- The constant-in-frequency remainder term has at least one order of
decay, including frequency zero (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem inverseDenominator_le_imageBesselSymbol (ξ : E) :
    (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ ≤ imageBesselSymbol ξ := by
  unfold imageBesselSymbol euclideanSobolevWeight
  rw [← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le
  · nlinarith [sq_nonneg ‖(2 * Real.pi) • ξ‖]
  · norm_num

/-- Fixed-frequency contraction of the actual affine coefficient array,
for the physical derivative estimate in `app:ch_background:prop:bg-frame`. -/
def differentialRemainderContraction (ξ : E) :
    (Option (Fin d) → ℂ) →L[ℝ] ℂ :=
  (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ •
    ((∑ a, (((2 * Real.pi) • ξ) a : ℝ) • ContinuousLinearMap.proj (some a)) +
      ContinuousLinearMap.proj none)

/-- Order-minus-one norm of the contraction, including frequency zero
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_differentialRemainderContraction_le (ξ : E) :
    ‖differentialRemainderContraction ξ‖ ≤ (d + 1) * imageBesselSymbol ξ := by
  have hw : 0 ≤ imageBesselSymbol ξ := by
    unfold imageBesselSymbol euclideanSobolevWeight
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv (a : Option (Fin d)) : ‖v a‖ ≤ ‖v‖ := norm_le_pi_norm v a
  have hk (a : Fin d) : ‖(((2 * Real.pi) • ξ) a : ℝ)‖ ≤ ‖(2 * Real.pi) • ξ‖ :=
    PiLp.norm_apply_le _ a
  have hden : 0 ≤ (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by positivity
  simp only [differentialRemainderContraction, smul_apply,
    add_apply, sum_apply, ContinuousLinearMap.proj_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hden]
  calc
    _ ≤ (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ *
        ((∑ a, ‖(((2 * Real.pi) • ξ) a : ℝ)‖ * ‖v (some a)‖) + ‖v none‖) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add
        (by simpa only [norm_smul] using norm_sum_le Finset.univ (fun a ↦ (((2 * Real.pi) • ξ) a : ℝ) • v (some a))) le_rfl)
    _ ≤ (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ *
        ((∑ _a : Fin d, ‖(2 * Real.pi) • ξ‖ * ‖v‖) + ‖v‖) := by
      gcongr with a
      · exact hk a
      · exact hv (some a)
      · exact hv none
    _ = (d * ((1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ * ‖(2 * Real.pi) • ξ‖) +
        (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹) * ‖v‖ := by simp; ring
    _ ≤ (d * imageBesselSymbol ξ + imageBesselSymbol ξ) * ‖v‖ := by
      gcongr
      · exact inverseDenominator_mul_norm_le_imageBesselSymbol ξ
      · exact inverseDenominator_le_imageBesselSymbol ξ
    _ = _ := by ring

/-- The affine contraction is the actual remainder, not an assumed error
operator (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem differentialRemainderAmplitude_eq_contraction
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (ξ : E) (i l : Fin d) :
    (fun p : E × E ↦ differentialRemainderAmplitude A Z C μ p.1 p.2 ξ i l) =
      differentialRemainderContraction ξ ∘ differentialRemainderCoefficients A Z C μ i l := by
  funext p
  rw [differentialRemainderAmplitude_eq_affine]
  simp [differentialRemainderContraction]

/-- Smoothness of `Q = A dC + ZC` follows from the actual primitive fields
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_sourceProductCoefficient (A : E → Fin d → Mat) (Z : E → Mat)
    (C : E → ℝ) (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j)) (hC : ContDiff ℝ ∞ C)
    (i j : Fin d) : ContDiff ℝ ∞ (fun x ↦ sourceProductCoefficient A Z C x i j) := by
  apply ContDiff.add _ ((hZ i j).mul hC)
  exact ContDiff.sum (fun a _ ↦ (hA a i j).mul
    ((hC.fderiv_right (by simp)).clm_apply contDiff_const))

/-- Joint physical smoothness of the actual affine coefficients follows
from primitive coefficient and cutoff smoothness
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_differentialRemainderCoefficients
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hC : ContDiff ℝ ∞ C) (hμ : ContDiff ℝ ∞ μ) (i l : Fin d) :
    ContDiff ℝ ∞ (differentialRemainderCoefficients A Z C μ i l) := by
  have hQ j := contDiff_sourceProductCoefficient A Z C hA hZ hC i j
  have hr (f : E × E → ℝ) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun p ↦ (f p : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  apply contDiff_pi.mpr
  intro a
  cases a with
  | none =>
    apply (hr _ ((hμ.comp contDiff_fst).mul (hμ.comp contDiff_snd))).mul
    exact ContDiff.sum (fun j _ ↦ (hr _ ((hQ j).comp contDiff_fst)).mul
      (hr _ ((hZ l j).comp contDiff_snd)))
  | some a =>
    apply (hr _ ((hμ.comp contDiff_fst).mul (hμ.comp contDiff_snd))).mul
    apply ContDiff.sum
    intro j _
    exact contDiff_const.mul ((hr _ (((hC.comp contDiff_fst).mul
      ((hA a i j).comp contDiff_fst)).mul ((hZ l j).comp contDiff_snd))).sub
        ((hr _ ((hQ j).comp contDiff_fst)).mul (hr _ ((hA a l j).comp contDiff_snd))))

/-- Both measurement masks localize every physical coefficient to the
fixed chart (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_differentialRemainderCoefficients
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (hμ : HasCompactSupport μ) (i l : Fin d) :
    HasCompactSupport (differentialRemainderCoefficients A Z C μ i l) := by
  apply HasCompactSupport.intro (hμ.isCompact.prod hμ.isCompact)
  intro p hp
  have hz : μ p.1 * μ p.2 = 0 := by
    by_cases hx : p.1 ∈ tsupport μ
    · have hy : p.2 ∉ tsupport μ := fun hy ↦ hp ⟨hx, hy⟩
      simp [image_eq_zero_of_notMem_tsupport hy]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  funext a
  cases a <;> simp [differentialRemainderCoefficients, hz]

/-- Every physical derivative of the actual coefficient remainder has
order minus one, from primitive smooth fields and a fixed compact measurement
cutoff. This is an existence bound for a fixed chart, not a uniform tame
bound over a family of geometries (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_differentialRemainder_physical_jet_bound
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hC : ContDiff ℝ ∞ C) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (i l : Fin d) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ p,
      ‖iteratedFDeriv ℝ n
        (fun p : E × E ↦ differentialRemainderAmplitude A Z C μ p.1 p.2 ξ i l) p‖ ≤
        K * imageBesselSymbol ξ := by
  have hs := contDiff_differentialRemainderCoefficients A Z C μ hA hZ hC hμ i l
  have hc := hasCompactSupport_differentialRemainderCoefficients A Z C μ hμc i l
  obtain ⟨K, hK⟩ := (hc.iteratedFDeriv n).exists_bound_of_continuous
    (hs.continuous_iteratedFDeriv (by simp))
  have hK₀ : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨(d + 1) * K, by positivity, ?_⟩
  intro ξ p
  rw [differentialRemainderAmplitude_eq_contraction]
  apply ((differentialRemainderContraction ξ).norm_iteratedFDeriv_comp_left
    hs.contDiffAt (by simp)).trans
  have hw : 0 ≤ imageBesselSymbol ξ := by
    unfold imageBesselSymbol euclideanSobolevWeight
    positivity
  exact (mul_le_mul (norm_differentialRemainderContraction_le ξ) (hK p)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- One constant controls any prescribed finite physical derivative
reserve on the fixed chart (`app:ch_background:prop:bg-frame`, Step 1).
The constant is obtained from the actual primitive fields and compact cutoff. -/
theorem exists_differentialRemainder_physical_budget
    (A : E → Fin d → Mat) (Z : E → Mat) (C μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hC : ContDiff ℝ ∞ C) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (i l : Fin d) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≤ N, ∀ ξ p,
      ‖iteratedFDeriv ℝ n
        (fun p : E × E ↦ differentialRemainderAmplitude A Z C μ p.1 p.2 ξ i l) p‖ ≤
        K * imageBesselSymbol ξ := by
  have h (n : ℕ) := exists_differentialRemainder_physical_jet_bound
    A Z C μ hA hZ hC hμ hμc i l n
  choose K hK₀ hK using h
  refine ⟨∑ n ∈ Finset.range (N + 1), K n, Finset.sum_nonneg (fun n _ ↦ hK₀ n), ?_⟩
  intro n hn ξ p
  apply (hK n ξ p).trans
  apply mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ ↦ hK₀ j) (Finset.mem_range.mpr (by omega)))
  unfold imageBesselSymbol euclideanSobolevWeight
  positivity

end JanetCartan.ContinuumNormalReduction.ImageNormal
