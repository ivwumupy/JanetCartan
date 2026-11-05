module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.LocalInterpolation

/-!
# Primitive interpolation for the normal-amplitude one-high estimate

The consumer is `exists_crossNormalAmplitude_oneHigh_bound`. This helper derives
its pointwise primitive profiles on fixed working balls from the buffered
interpolation API of `app:ch_regular_base:lem:buffered-interpolation`.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral.NormalOneHigh

/-- Primitive joint C¹ bounds and a linear Cˢ bound give the exact profiles
required by the normal-amplitude theorem. The constant is independent of H and
of the primitive map. A coefficient estimate at s + β can therefore be inserted
as H = 1 + its Sobolev norm, with the same fixed β and no extra derivative loss.
Source: `app:ch_regular_base:lem:buffered-interpolation`. -/
theorem exists_primitiveJet_profile_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {U : Set E} (hU : IsOpen U)
    (hball : Metric.closedBall x ρ ⊆ U) {s : ℕ} (hs : 2 ≤ s)
    {M T : ℝ} (hM : 0 ≤ M) (hT : 1 ≤ T) :
    ∃ K ≥ 1, ∀ (f : E → F) (H : ℝ),
      ContDiffOn ℝ ∞ f U → 1 ≤ H → cNorm (Metric.closedBall x ρ) 1 f ≤ M →
      1 + cNorm (Metric.closedBall x ρ) s f ≤ T * H →
      (∀ z ∈ Metric.closedBall x ρ, ‖f z‖ ≤ M) ∧
      ∀ z ∈ Metric.closedBall x ρ, ∀ i, 1 ≤ i → i ≤ s →
        ‖iteratedFDeriv ℝ i f z‖ ≤ K * H ^ (((i : ℝ) - 1) / (s - 1)) := by
  obtain ⟨K, hK, hp⟩ := FlowForcing.exists_uniform_cNorm_baseline_one_profile_closedBall_on
    (F := F) x hρ hU hball hs hM
  refine ⟨K * T, one_le_mul_of_one_le_of_one_le hK hT, ?_⟩
  intro f H hf hH hlow hhigh
  have hlocal (j : ℕ) (z) (hz : z ∈ Metric.closedBall x ρ) : ContDiffAt ℝ j f z :=
    (hf.contDiffAt (hU.mem_nhds (hball hz))).of_le (by simp)
  constructor
  · intro z hz
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall x ρ) (hlocal 1) hz (Nat.zero_le 1)
    simpa only [norm_iteratedFDeriv_zero] using hb.trans hlow
  · intro z hz i hi his
    have hn := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall x ρ) (hlocal i) hz (le_refl i)
    apply (hn.trans (hp f hf hlow i hi his)).trans
    have hspos : (0 : ℝ) < s - 1 := by
      have : (2 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    have hθ : 0 ≤ ((i : ℝ) - 1) / (s - 1) :=
      div_nonneg (sub_nonneg.mpr (by exact_mod_cast hi)) hspos.le
    have hθ' : ((i : ℝ) - 1) / (s - 1) ≤ 1 :=
      (div_le_one hspos).mpr (sub_le_sub_right (by exact_mod_cast his) 1)
    have hpow : (1 + cNorm (Metric.closedBall x ρ) s f) ^ (((i : ℝ) - 1) / (s - 1)) ≤
        T * H ^ (((i : ℝ) - 1) / (s - 1)) := by
      calc
        _ ≤ (T * H) ^ (((i : ℝ) - 1) / (s - 1)) :=
          Real.rpow_le_rpow (by linarith [CompositionBounds.cNorm_nonneg (Metric.closedBall x ρ) s f]) hhigh hθ
        _ = T ^ (((i : ℝ) - 1) / (s - 1)) * H ^ (((i : ℝ) - 1) / (s - 1)) :=
          Real.mul_rpow (zero_le_one.trans hT) (zero_le_one.trans hH)
        _ ≤ T * H ^ (((i : ℝ) - 1) / (s - 1)) :=
          mul_le_mul_of_nonneg_right
            ((Real.rpow_le_rpow_of_exponent_le hT hθ').trans_eq (Real.rpow_one T))
            (Real.rpow_nonneg (zero_le_one.trans hH) _)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hK)

end JanetCartan.FourierIntegral.NormalOneHigh
