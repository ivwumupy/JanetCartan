module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Limits

/-!
# Passing an actual operator estimate along Sobolev approximations

The assembly step for `app:ch_regular_base:eq:fio-input` retains the same
constant and gains output membership. This module proves the limit argument
for a supplied approximating sequence; construction of compact smooth
approximations is a separate obligation.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The sequence assembly step for
`exists_twoPositionL2Operator_integer_tame_constant` and
`exists_twoPositionL2Operator_integer_gain_tame_constant`, implementing
`app:ch_regular_base:eq:fio-input`. The approximations are supplied explicitly;
this theorem does not assert compact smooth density. -/
theorem fourierSobolev_operator_bound_of_approximating_sequence
    (T : L² →L[ℂ] L²) {s t C H : ℝ} (hs : 0 ≤ s)
    {u : ℕ → L²} {v : L²} (hu : ∀ k, MemFourierSobolev s (u k))
    (hv : MemFourierSobolev s v)
    (hlim : Tendsto (fun k ↦ fourierSobolevNorm s (u k - v)) atTop (𝓝 0))
    (hbound : ∀ k, MemFourierSobolev t (T (u k)) ∧
      fourierSobolevNorm t (T (u k)) ≤
        C * (fourierSobolevNorm s (u k) + H * ‖u k‖)) :
    MemFourierSobolev t (T v) ∧
      fourierSobolevNorm t (T v) ≤ C * (fourierSobolevNorm s v + H * ‖v‖) := by
  have hL2 := tendsto_L2_of_fourierSobolevNorm_sub hs hu hv hlim
  apply memFourierSobolev_and_norm_le_of_tendsto t
    (T.continuous.continuousAt.tendsto.comp hL2) (fun k ↦ (hbound k).1)
    ((tendsto_fourierSobolevNorm_of_sub hu hv hlim).add
      (hL2.norm.const_mul H) |>.const_mul C)
  exact fun k ↦ (hbound k).2

end JanetCartan.Pseudodifferential
