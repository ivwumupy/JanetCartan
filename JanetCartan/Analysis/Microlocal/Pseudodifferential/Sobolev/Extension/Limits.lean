module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Passing Fourier Sobolev bounds through L² limits

For `app:ch_regular_base:eq:fio-input`, a bound on the weighted Fourier norms
passes to an L² limit, including membership. This is the closedness step used
when extending the actual compact-test PDO estimates. The extended norm is
used before establishing finiteness; `ENNReal.toReal` alone cannot detect
failure of Sobolev membership.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The extended Fourier Sobolev norm inherits convergent bounds under L²
limits (`app:ch_regular_base:eq:fio-input`). No membership of the limit is
assumed. The proof uses an a.e. convergent Fourier subsequence and Fatou. -/
theorem eLpNorm_weightedL2Fourier_le_of_tendsto (s : ℝ)
    {u : ℕ → L²} {v : L²} (hu : Tendsto u atTop (𝓝 v))
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ k, eLpNorm (weightedL2Fourier s (u k)) 2 volume ≤ b k) :
    eLpNorm (weightedL2Fourier s v) 2 volume ≤ B := by
  have hF : Tendsto (fun k ↦ 𝓕 (u k)) atTop (𝓝 (𝓕 v)) :=
    continuous_fourier.continuousAt.tendsto.comp hu
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hw : ∀ᵐ ξ ∂volume, Tendsto (fun k ↦ weightedL2Fourier s (u (φ k)) ξ)
      atTop (𝓝 (weightedL2Fourier s v ξ)) := by
    filter_upwards [hae] with ξ hξ
    exact tendsto_const_nhds.smul hξ
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun k ↦ aestronglyMeasurable_weightedL2Fourier s (u (φ k)))
    (weightedL2Fourier s v) (aestronglyMeasurable_weightedL2Fourier s v) hw
  exact hfat.trans ((liminf_le_liminf (Eventually.of_forall (fun k ↦ hbound (φ k)))).trans_eq
    (hb.comp hφ.tendsto_atTop).liminf_eq)

/-- Extended Sobolev sublevel sets are closed in L². This is the closedness
behind passing the output bound in `app:ch_regular_base:eq:fio-input`. -/
theorem isClosed_eLpNorm_weightedL2Fourier_sublevel (s : ℝ) (B : ℝ≥0∞) :
    IsClosed {u : L² | eLpNorm (weightedL2Fourier s u) 2 volume ≤ B} := by
  apply IsSeqClosed.isClosed
  intro u v hbound hu
  exact eLpNorm_weightedL2Fourier_le_of_tendsto s hu tendsto_const_nhds hbound

/-- The extended Sobolev norm is lower semicontinuous on actual L² classes,
as used in the density argument for `app:ch_regular_base:eq:fio-input`.
This statement retains the value `∞` outside Sobolev space. -/
theorem lowerSemicontinuous_eLpNorm_weightedL2Fourier (s : ℝ) :
    LowerSemicontinuous (fun u : L² ↦ eLpNorm (weightedL2Fourier s u) 2 volume) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  exact isClosed_eLpNorm_weightedL2Fourier_sublevel s

/-- Sobolev membership and the sharp bound both pass through an L² limit
when the bounds converge, for `app:ch_regular_base:eq:fio-input`. This is the
limit step for both the order-zero and gain-one compact-test estimates. -/
theorem memFourierSobolev_and_norm_le_of_tendsto (s : ℝ)
    {u : ℕ → L²} {v : L²} (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, MemFourierSobolev s (u k))
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ k, fourierSobolevNorm s (u k) ≤ b k) :
    MemFourierSobolev s v ∧ fourierSobolevNorm s v ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hb (Eventually.of_forall fun k ↦
    (fourierSobolevNorm_nonneg s (u k)).trans (hbound k))
  have he : eLpNorm (weightedL2Fourier s v) 2 volume ≤ ENNReal.ofReal B := by
    apply eLpNorm_weightedL2Fourier_le_of_tendsto s hu
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb)
    intro k
    rw [← ENNReal.ofReal_toReal (hmem k).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hbound k)
  refine ⟨he.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal hB)

end JanetCartan.Pseudodifferential
