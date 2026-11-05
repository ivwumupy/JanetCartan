module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.ExtensionEnergy
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison

/-!
# Sobolev bounds for the fixed ball extension

The actual Cartesian derivative norm in
`app:ch_regular_base:eq:ball-extension-sobolev` is bounded at every order for
one fixed Seeley extension formula. The proof integrates the local jet bounds
using the radial Jacobian, sums the series, and compares Cartesian and Fréchet
energies. Closed-ball smoothness of the input suffices in all dimensions,
including zero and one.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {n : ℕ} (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- Squared Cartesian derivative Sobolev bound for the actual fixed Seeley
extension, as in `app:ch_regular_base:eq:ball-extension-sobolev`. The constant
is independent of the input; all auxiliary integrability and norm comparisons
are discharged. -/
theorem exists_cartesianSobolevEnergy_extend_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cartesianSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
        C * cartesianSobolevEnergy (ball p.center p.radius) m f := by
  obtain ⟨C, hC, hb⟩ := p.exists_frechetSobolevEnergy_extend_bound m
  refine ⟨cartesianEnergyComparisonConstant n m * C * frechetEnergyComparisonConstant n m,
    mul_pos (mul_pos (cartesianEnergyComparisonConstant_pos n m) hC)
      (frechetEnergyComparisonConstant_pos n m), ?_⟩
  intro f hf
  calc
    _ ≤ cartesianEnergyComparisonConstant n m *
        frechetSobolevEnergy univ m (p.extend Seeley.coeff f) :=
      p.cartesianSobolevEnergy_extend_le_mul_frechetSobolevEnergy hf m
    _ ≤ cartesianEnergyComparisonConstant n m *
        (C * frechetSobolevEnergy (ball p.center p.radius) m f) :=
      mul_le_mul_of_nonneg_left (hb f hf) (cartesianEnergyComparisonConstant_pos n m).le
    _ ≤ cartesianEnergyComparisonConstant n m *
        (C * (frechetEnergyComparisonConstant n m *
          cartesianSobolevEnergy (ball p.center p.radius) m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (p.frechetSobolevEnergy_ball_le_mul_cartesianSobolevEnergy hf m)
          hC.le) (cartesianEnergyComparisonConstant_pos n m).le
    _ = _ := by ring

/-- The all-order derivative `H^m` bound in
`app:ch_regular_base:eq:ball-extension-sobolev`, for one fixed operator and the
finite sum of squared Cartesian multiindex derivatives specified in the paper.
Only smoothness on the closed input ball is assumed. The theorem includes
`n = 0` and `n = 1`. -/
theorem exists_cartesianSobolevNorm_extend_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cartesianSobolevNorm univ m (p.extend Seeley.coeff f) ≤
        C * cartesianSobolevNorm (ball p.center p.radius) m f := by
  obtain ⟨C, hC, hb⟩ := p.exists_cartesianSobolevEnergy_extend_bound m
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro f hf
  simpa only [cartesianSobolevNorm, Real.sqrt_mul hC.le] using Real.sqrt_le_sqrt (hb f hf)

end JanetCartan.BallExtension.Parameters
