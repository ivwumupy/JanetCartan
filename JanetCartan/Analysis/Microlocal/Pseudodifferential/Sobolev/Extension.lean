module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Sequence
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.DensityZero
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Density

/-!
# Extension of compact-test Sobolev estimates

For `app:ch_regular_base:eq:fio-input`, proved compact smooth density at every
natural input order and lower semicontinuity pass compact-test estimates to
all Sobolev inputs of an actual bounded L² operator. The exact constant is
preserved, and output Sobolev membership is proved. Only the compact-test
operator estimate remains an explicit premise for the consuming PDO results.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Extend a compact smooth test estimate to every input of natural Fourier
Sobolev order, including output membership and the unchanged constant in
`app:ch_regular_base:eq:fio-input`. The producers of the test premise are
`exists_twoPositionL2Operator_integer_tame_constant` and
`exists_twoPositionL2Operator_integer_gain_tame_constant`. The output order
may be any real number, in particular either `n` or `n + 1`. Density and limit
membership are proved, including dimension zero and input order zero. -/
theorem fourierSobolev_operator_bound_of_compactSmooth_nat
    (T : L² →L[ℂ] L²) (n : ℕ) (t C H : ℝ)
    (htest : ∀ (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g),
      let f := (hg.continuous.memLp_of_hasCompactSupport hc).toLp g
      MemFourierSobolev t (T f) ∧
        fourierSobolevNorm t (T f) ≤ C * (fourierSobolevNorm (n : ℝ) f + H * ‖f‖))
    (v : L²) (hv : MemFourierSobolev (n : ℝ) v) :
    MemFourierSobolev t (T v) ∧
      fourierSobolevNorm t (T v) ≤ C * (fourierSobolevNorm (n : ℝ) v + H * ‖v‖) := by
  obtain ⟨g, hg, hc, hu, hlim, _⟩ := exists_compactSmooth_fourierSobolev_nat_tendsto n v hv
  exact fourierSobolev_operator_bound_of_approximating_sequence T (Nat.cast_nonneg n)
    hu hv hlim (fun k ↦ htest (g k) (hg k) (hc k))

/-- Extend the compact-test estimate to every L² input, including output
Sobolev membership. This proves the zero-input-order endpoint needed by the
gain-one estimate `app:ch_regular_base:eq:fio-input`. Only the actual test
estimate is a premise; compact smooth density and limit membership are proved. -/
theorem fourierSobolev_operator_bound_of_compactSmooth_zero
    (T : L² →L[ℂ] L²) (t C H : ℝ)
    (htest : ∀ (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g),
      let f := (hg.continuous.memLp_of_hasCompactSupport hc).toLp g
      MemFourierSobolev t (T f) ∧
        fourierSobolevNorm t (T f) ≤ C * (fourierSobolevNorm 0 f + H * ‖f‖))
    (v : L²) :
    MemFourierSobolev t (T v) ∧
      fourierSobolevNorm t (T v) ≤ C * (fourierSobolevNorm 0 v + H * ‖v‖) := by
  obtain ⟨g, hg, hc, hlim⟩ := exists_compactSmooth_L2_tendsto v
  apply fourierSobolev_operator_bound_of_approximating_sequence T (s := 0) le_rfl
    (fun k ↦ memFourierSobolev_zero _) (memFourierSobolev_zero v) _
    (fun k ↦ htest (g k) (hg k) (hc k))
  simpa only [fourierSobolevNorm_zero, dist_eq_norm] using
    tendsto_iff_dist_tendsto_zero.mp hlim

end JanetCartan.Pseudodifferential
