module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.Operator.Complex
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Real action and paired H¹ bounds of the one-factor remainder

For `app:ch_background:prop:bg-frame`, Step 1, the real one-factor remainder
integrates its concrete real matrix kernel. Its literal real Hilbert adjoint
integrates the spatially reversed, transposed kernel. Complex inclusion
intertwines both operators with the corresponding complex realizations, so
their proved paired Sobolev bounds give exactly the remainder input `hD` of
`normalCrossTerms_sobolev_one_bounds`. Kernel support gives the measurement
support of the remainder and the original source support of its adjoint.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

open Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)
local notation "R²" => PeriodicLocalL2.EuclideanL2 d E

private theorem realCompression_adjoint (T : C² →L[ℂ] C²) :
    (realOutputCompression T).adjoint = realOutputCompression (T).adjoint := by
  have hi : (l2ComplexInclusion (ι := Fin d) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [realOutputCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictScalars_complex, l2RealPart_adjoint, hi, ContinuousLinearMap.comp_assoc]

private theorem realMatrixIntegral_inclusion
    (K : Fin d → Fin d → E × E → ℝ) (f : R²) (x : E) (i : Fin d) :
    (∑ j, ∫ y, (K i j (x, y) : ℂ) * l2ComplexInclusion volume f y j) =
      ((∑ j, ∫ y, K i j (x, y) * f y j : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL f] with y hy
  change l2ComplexInclusion volume f y = euclideanComplexInclusion (f y) at hy
  simp only [hy, euclideanComplexInclusion_apply, Complex.ofReal_mul]

private theorem realCompression_ae_integral
    (T : C² →L[ℂ] C²) (K : Fin d → Fin d → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, (K i j (x, y) : ℂ) * f y j)) (f : R²) :
    realOutputCompression T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, K i j (x, y) * f y j) := by
  filter_upwards [euclideanRealPart.coeFn_compLpL (T (l2ComplexInclusion volume f)),
    hT (l2ComplexInclusion volume f)] with x hx hT
  change realOutputCompression T f x = euclideanRealPart _ at hx
  rw [hx, hT]
  ext i
  change (∑ j, ∫ y, (K i j (x, y) : ℂ) * l2ComplexInclusion volume f y j).re = _
  rw [realMatrixIntegral_inclusion]
  rfl

private theorem inclusion_realCompression
    (T : C² →L[ℂ] C²) (K : Fin d → Fin d → E × E → ℝ)
    (hT : ∀ f : C², T f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, (K i j (x, y) : ℂ) * f y j)) (f : R²) :
    l2ComplexInclusion volume (realOutputCompression T f) = T (l2ComplexInclusion volume f) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (realOutputCompression T f),
    realCompression_ae_integral T K hT f, hT (l2ComplexInclusion volume f)] with x hx hy hz
  change l2ComplexInclusion volume (realOutputCompression T f) x = euclideanComplexInclusion _ at hx
  rw [hx, hy, hz]
  ext i
  exact (realMatrixIntegral_inclusion K f x i).symm

variable {r : ℝ} (hr : r < 1 / 2) (ρ χ μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρs : ∀ x, ρ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hχs : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ r)
    (hμs : ∀ x, μ x ≠ 0 → ∀ a, |x a| ≤ r)
    (A : EuclideanSpace ℝ (Fin d) → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))

local notation "K" => oneFactorRemainderKernel (d := d) ρ χ μ A Z
local notation "T" => complexOneFactorRemainderOperator (d := d) (r := r) hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ
local notation "D" => realOneFactorRemainderOperator (d := d) (r := r) hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ

/-- The literal real adjoint is the compression of the complex adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_adjoint :
    (D).adjoint = realOutputCompression (T).adjoint :=
  realCompression_adjoint T

/-- The actual real one-factor remainder integrates the differentiated
matrix kernel on all of L² (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_ae_integral (f : R²) :
    D f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, K i j (x, y) * f y j) :=
  realCompression_ae_integral T K
    (complexOneFactorRemainderOperator_ae_integral
      hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ) f

/-- The literal real Hilbert adjoint integrates the spatially reversed,
transposed kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_adjoint_ae_integral (f : R²) :
    (D).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun j ↦ ∑ i, ∫ x, K i j (x, y) * f x i) := by
  rw [realOneFactorRemainderOperator_adjoint]
  exact realCompression_ae_integral (T).adjoint (fun j i p ↦ K i j p.swap)
    (complexOneFactorRemainderOperator_adjoint_ae_integral
      hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ) f

/-- Complex inclusion intertwines the concrete real and complex one-factor
remainders, by their real integral kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realOneFactorRemainderOperator (f : R²) :
    l2ComplexInclusion volume (D f) = T (l2ComplexInclusion volume f) :=
  inclusion_realCompression T K
    (complexOneFactorRemainderOperator_ae_integral
      hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ) f

/-- Complex inclusion also intertwines the literal real and complex Hilbert
adjoints (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem l2ComplexInclusion_realOneFactorRemainderOperator_adjoint (f : R²) :
    l2ComplexInclusion volume ((D).adjoint f) = (T).adjoint (l2ComplexInclusion volume f) := by
  rw [realOneFactorRemainderOperator_adjoint]
  exact inclusion_realCompression (T).adjoint (fun j i p ↦ K i j p.swap)
    (complexOneFactorRemainderOperator_adjoint_ae_integral
      hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ) f

/-- The actual remainder retains the measurement support, as required by
`normalCrossTerms_periodic_endpoints` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_support (f : R²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ → D f x = 0 := by
  filter_upwards [realOneFactorRemainderOperator_ae_integral
    hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ f] with x hx
  intro hxs
  have hk (i j : Fin d) (y : E) : K i j (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h ↦ hxs ((tsupport_oneFactorRemainderKernel_subset ρ χ μ A Z i j h).1))
  rw [hx]
  ext i
  simp [hk]

/-- The literal adjoint retains the original source cutoff support
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_adjoint_support (f : R²) :
    ∀ᵐ y ∂volume, y ∉ tsupport χ → (D).adjoint f y = 0 := by
  filter_upwards [realOneFactorRemainderOperator_adjoint_ae_integral
    hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ f] with y hy
  intro hys
  have hk (i j : Fin d) (x : E) : K i j (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h ↦ hys ((tsupport_oneFactorRemainderKernel_subset ρ χ μ A Z i j h).2))
  rw [hy]
  ext j
  simp [hk]

/-- The concrete real one-factor remainder and its literal Hilbert adjoint
gain one Fourier Sobolev derivative with a common finite constant for the
fixed data. This is exactly `hD` of `normalCrossTerms_sobolev_one_bounds`,
derived from the kernel without extra analytic premises
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem realOneFactorRemainderOperator_sobolev_one_bounds :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ f : R²,
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume (D f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (D f)) ≤ CD * ‖f‖ ∧
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume ((D).adjoint f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume ((D).adjoint f)) ≤ CD * ‖f‖ := by
  obtain ⟨C, hC, hT⟩ := complexOneFactorRemainderOperator_sobolev_one_bounds
    hr ρ χ μ hρ hχ hμ hρs hχs hμs A Z hA hZ
  refine ⟨C, hC, fun f ↦ ?_⟩
  rw [l2ComplexInclusion_realOneFactorRemainderOperator,
    l2ComplexInclusion_realOneFactorRemainderOperator_adjoint]
  have hb : ‖l2ComplexInclusion volume f‖ ≤ ‖f‖ := by
    simpa using (l2ComplexInclusion volume).le_of_opNorm_le
      (l2ComplexInclusion_norm_le volume) f
  exact ⟨(hT _).1, (hT _).2.1.trans (mul_le_mul_of_nonneg_left hb hC),
    (hT _).2.2.1, (hT _).2.2.2.trans (mul_le_mul_of_nonneg_left hb hC)⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
