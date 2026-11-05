module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.ParameterSupport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension

/-!
# Exhaustion by the original radial carrier masks

The masks used in `app:ch_background:eq:bg-T` exhaust every compact initial
test. Their parameter truncations construct the actual finite operators, while
`ParameterSupport` identifies their action with these original radial masks.
Consumer: the uniform full-normal construction and `exists_carrierL2Extension`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
variable {n N : ℕ}

/-- The original radial carrier mask before compact parameter truncation;
it is squared only by taking the normal (`app:ch_background:eq:bg-T`). -/
def radialCarrierMask (κ : ℝ → ℝ) (Q : ℝ) (z : CarrierVariable n) : ℝ :=
  κ (‖z.2‖ / Q)

/-- The original radial masks at radii `k + 1` equal one on each compact
initial set eventually. Parameter truncation is deliberately absent here:
the angular kernel support justifies it separately
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem radialCarrierMask_eventually_eq_one (κ : ℝ → ℝ)
    (hκ : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    (K : Set (CarrierVariable n)) (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, radialCarrierMask κ (k + 1) z = 1 := by
  obtain ⟨L, _, hL⟩ := (hK.image continuous_snd).isBounded.exists_pos_norm_le
  have ht : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop L)] with k hk z hz
  apply hκ
  exact ⟨div_nonneg (norm_nonneg _) (by positivity),
    (div_le_one (by positivity : (0 : ℝ) < k + 1)).mpr ((hL _ ⟨z, hz, rfl⟩).trans hk)⟩

/-- The compact radial profile and primitive kernel hypotheses construct all
finite `MaskHypotheses`; there is no operator bound in the inputs. Constants
for mask size and frequency support precede the radius
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_radialCarrierMask_hypotheses
    (d : CarrierData n N) (Z : Set CarrierParameter) (hZ : IsCompact Z)
    {κ : ℝ → ℝ} (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : StronglyMeasurable (Function.uncurry (carrierKernel d)))
    (ha : ∀ x z, ‖carrierAmplitude d x z‖ ≤ C * Real.sqrt ‖z.2‖) :
    ∃ L > 0, ∃ M ≥ 0, ∀ Q : ℝ, 0 < Q →
      CarrierRegularization.MaskHypotheses d
        (parameterTruncatedMask Z (radialCarrierMask κ Q)) Z (L * Q) M C := by
  obtain ⟨L, hL, hzero⟩ := hcκ.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hκ.norm.bddAbove_range_of_hasCompactSupport hcκ.norm
  have hM₀ : 0 ≤ M := (norm_nonneg (κ 0)).trans (hM ⟨0, rfl⟩)
  refine ⟨L, hL, M, hM₀, fun Q hQ ↦ ?_⟩
  apply maskHypotheses_parameterTruncatedMask d Z (radialCarrierMask κ Q)
    hZ (mul_nonneg hL.le hQ.le) hM₀ hC hk
  · exact (hκ.comp (continuous_snd.norm.div_const Q)).stronglyMeasurable
  · intro z hz
    apply hzero
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hQ.le)]
    exact ((le_div_iff₀ hQ).mpr hz.le)
  · intro z
    exact hM ⟨‖z.2‖ / Q, rfl⟩
  · exact ha

end JanetCartan.ContinuumRow.CarrierNormalRealization
