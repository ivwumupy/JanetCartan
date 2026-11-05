module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Symbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.GraphConvergence

/-!
# The exact cutoff in the cross-normal symbol

The compact cross-normal in `app:ch_regular_base:eq:actual-normal-amplitude`
contains the square of the original frequency cutoff at the inverse covector.
Both positions and the zero extension are retained. These identities supply the
pointwise input to removal of compact regularization in `UncutNormal`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.UncutNormal

open LowBounds LowBounds.FrequencyCutoff NormalComparison AmplitudeBound

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Both compact graph cutoffs survive the full inverse-Jacobian substitution
in `app:ch_regular_base:eq:actual-normal-amplitude`. The inverse covector depends
on both physical positions. -/
theorem cycleCrossNormalAmplitude_cutAmplitude
    (D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (m : ℕ) (x y ξ : E) :
    cycleCrossNormalAmplitude D S (cutAmplitude A m) (cutAmplitude B m) η J x y ξ =
      ((physicalCutoff m (η x y ((2 * Real.pi) • ξ))) ^ 2 : ℂ) •
        cycleCrossNormalAmplitude D S A B η J x y ξ := by
  classical
  unfold cycleCrossNormalAmplitude extendedCrossNormalAmplitude
  by_cases h : (x, y, (2 * Real.pi) • ξ) ∈
      {q : NormalVariables n | q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D}
  · simp only [indicator_of_mem h, crossNormalAmplitude,
      crossNormalNumerator, cutAmplitude, Matrix.conjTranspose_smul,
      complexPhysicalCutoff, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul (↑(physicalCutoff m (η x y ((2 * Real.pi) • ξ))) : ℂ)
      (↑(physicalCutoff m (η x y ((2 * Real.pi) • ξ))) : ℂ), ← pow_two]
    exact smul_comm _ _ _
  · simp only [indicator_of_notMem h, smul_zero]

/-- The exact cutoff formula in the paired coordinates of the existing matrix
PDO (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem cycleCrossNormalSymbol_cutAmplitude
    (D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (m : ℕ) (ξ : E) (z : Euclidean (2 * n)) :
    cycleCrossNormalSymbol D S (cutAmplitude A m) (cutAmplitude B m) η J ξ z =
      ((physicalCutoff m (η (splitPhysicalPositions z).1 (splitPhysicalPositions z).2
        ((2 * Real.pi) • ξ))) ^ 2 : ℂ) • cycleCrossNormalSymbol D S A B η J ξ z :=
  cycleCrossNormalAmplitude_cutAmplitude D S A B η J m _ _ ξ

/-- At each pair of positions and each frequency, the compact symbol eventually
agrees exactly with the full zero extension. This supplies pointwise convergence
without a transformed-cutoff hypothesis, for
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cycleCrossNormalSymbol_cutAmplitude_eventually_eq
    (D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (ξ : E) (z : Euclidean (2 * n)) :
    ∀ᶠ m : ℕ in atTop,
      cycleCrossNormalSymbol D S (cutAmplitude A m) (cutAmplitude B m) η J ξ z =
        cycleCrossNormalSymbol D S A B η J ξ z := by
  filter_upwards [physicalCutoff_eventually_eq_one
    (η (splitPhysicalPositions z).1 (splitPhysicalPositions z).2
      ((2 * Real.pi) • ξ))] with m hm
  rw [cycleCrossNormalSymbol_cutAmplitude, hm]
  simp

/-- The zeroth-order domination is inherited from the original full symbol,
not from a hypothesized dominating oscillatory kernel. Higher derivative bounds
come separately from the primitive shell estimates. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_cycleCrossNormalSymbol_cutAmplitude_le
    (D : Set E) (S : E → E → ℝ) (A B : E → E → Mat)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (m : ℕ) (ξ : E) (z : Euclidean (2 * n)) :
    ‖cycleCrossNormalSymbol D S (cutAmplitude A m) (cutAmplitude B m) η J ξ z‖ ≤
      ‖cycleCrossNormalSymbol D S A B η J ξ z‖ := by
  rw [cycleCrossNormalSymbol_cutAmplitude, norm_smul, norm_pow]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact pow_le_one₀ (norm_nonneg _) (complexPhysicalCutoff_norm_le m _)

end JanetCartan.FourierIntegral.UncutNormal
