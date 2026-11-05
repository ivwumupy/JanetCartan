module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Derivatives
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Periodization
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# L¹ masses for the fixed cutoff derivative kernels

For `main:lem:smoothing` and `main:eq:smoothing-low`, the derivative
periodization identity and the L¹ inequality for periodization transfer the
Euclidean derivative mass estimate to the normalized unit torus. The constant
is the mass of a derivative of the fixed Euclidean profile, independent of the
cutoff scale.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: the exact fixed cutoff's
order-`j` derivative kernel has L¹ mass bounded by a constant times `R ^ j`,
uniformly for `R ≥ 1` on the normalized unit torus. -/
theorem exists_periodicCutoffDerivKernel_mass_bound (n j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ y : Torus n,
        ‖periodicCutoffDerivKernel j R (0 : EuclideanSpace ℝ (Fin n)) y‖) ≤
        C * R ^ j := by
  let : Measure.IsNegInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isNegInvariant _
  refine ⟨cutoffEuclideanDerivMass n j, cutoffEuclideanDerivMass_nonneg n j, ?_⟩
  intro R hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb := integral_norm_torus_periodization_le _
    (integrable_iteratedFDeriv_re_cutoffEuclideanKernel n j hR0)
    (fun y ↦ periodicCutoffDerivKernel j R 0 (-y))
    ((continuous_periodicCutoffDerivKernel j R 0).comp continuous_neg)
    (periodicCutoffDerivKernel_eq_tsum_iteratedFDeriv_re_cutoffEuclideanKernel n j hR0)
  rw [integral_neg_eq_self (fun y : Torus n ↦ ‖periodicCutoffDerivKernel j R 0 y‖)] at hb
  exact hb.trans (integral_norm_iteratedFDeriv_re_cutoffEuclideanKernel_le n j hR0)

end JanetCartan
