module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.SourceComplement
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedProtectedTail

/-!
# The corrected complete source mask on the original signed directions

The characteristic-plus-elliptic source supplies its own normalized plateau.
Compactness of the supplied symmetric terminal set turns that plateau into the
angular buffer needed by the signed source tail. The original low collar at
`2*L₀` is retained, and its frequency threshold is chosen before accuracy.
Consumer: `app:ch_pairs:prop:pairs-lag-sum`, Fourier localization in Step 2.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory FourierTransform
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ResponseTransfer.Complement.InactiveSource
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure E)

/-- The actual complete normalized complement, with bound one and all its
radial and angular shoulders, in the existing mask API (`resolved-angular-tail`). -/
def normalizedComplementBoundedMask (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hK : IsCompact K) (L₀ : ℝ) : BoundedMask (d+1) where
  symbol ξ := (normalizedComplementMask f hK L₀ ξ : ℂ)
  measurable := (Complex.continuous_ofReal.comp
    (normalizedComplementMask_properties f hK L₀).1.continuous).stronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le ξ := by
    rw [Complex.norm_real, Real.norm_of_nonneg ((normalizedComplementMask_properties f hK L₀).2.1 ξ).1]
    exact ((normalizedComplementMask_properties f hK L₀).2.1 ξ).2

/-- Identify the same supplied-family Fourier operator on all L² data.
The `2π` conversion is identical in both existing realizations
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedComplementBoundedMask_fourierMultiplier
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ) (u : H) :
    (normalizedComplementBoundedMask f hK L₀).fourierMultiplier u =
      complementFourierOperator f hK L₀ u := by
  apply (Lp.fourierTransformₗᵢ E (EuclideanSpace ℂ (Fin (d+1)))).injective
  apply Lp.ext
  exact ((normalizedComplementBoundedMask f hK L₀).fourierMultiplier_fourier_ae u).trans
    (complementFourierOperator_fourier_ae f hK L₀ u).symm

/-- The producer's normalized plateau gives a uniform angular gap on the
FULL nonzero complementary mask above the original `4*L₀` threshold.
`T ⊆ K` is the same terminal-coverage input owned by the fixed-response radius
selection; no plateau or decay estimate is assumed (`pairs-lag-sum`, Step 2). -/
theorem exists_normalizedComplement_angular_buffer
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    {T : Set E} (hT : IsCompact T) (hTK : T ⊆ K) (hTneg : ∀ v ∈ T, -v ∈ T) :
    ∃ δ > (0 : ℝ), ∀ L₀ > (0 : ℝ), ∀ η : E,
      (normalizedComplementBoundedMask f hK L₀).symbol η ≠ 0 →
      4*L₀ ≤ ‖η‖ → ∀ v ∈ T, δ ≤ dist v (NormedSpace.normalize η) := by
  obtain ⟨V, hV, hTV, _, hplateau⟩ := exists_normalizedSourceMask_partition_near f hK hTK hTneg
  obtain ⟨δ, hδ, hbuffer⟩ := hT.exists_cthickening_subset_open hV hTV
  refine ⟨δ, hδ, ?_⟩
  intro L₀ hL₀ η hη hhigh v hv
  by_contra hdist
  have hn : NormedSpace.normalize η ∈ V := hbuffer
    (mem_cthickening_of_dist_le _ v δ T hv (by rw [dist_comm]; exact (lt_of_not_ge hdist).le))
  have hp := (hplateau L₀ hL₀ η hn).2 hhigh
  exact hη (by simp [normalizedComplementBoundedMask, normalizedComplementMask, hp])

/-- One fixed stage threshold clears the retained physical low collar at
all later original separated frequencies. It precedes the accuracy, samples,
targets and histories (`main:eq:all-pair-scales`, `resolved-angular-tail`). -/
theorem exists_normalizedComplement_radial_threshold {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (L₀ : ℝ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin, ∀ ρ : ℝ,
      c * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      4*L₀ ≤ a*ρ/2 := by
  have he : 0 < carrierExponent - separationExponent := by
    norm_num [carrierExponent, separationExponent]
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt (8*L₀/(a*c)) he)
  refine ⟨max 2 R₁, le_max_left _ _, ?_⟩
  intro R hR ρ hρ
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hR)
  have hpow : 8*L₀/(a*c) ≤ R ^ (carrierExponent - separationExponent) := by
    simpa only [Real.rpow_zero, mul_one] using hR₁ R ((le_max_right _ _).trans hR)
  have hfreq : R ^ carrierExponent * R ^ (-separationExponent) =
      R ^ (carrierExponent - separationExponent) := by
    rw [← Real.rpow_add hRp]; rfl
  rw [hfreq] at hρ
  have hlow := (div_le_iff₀ (mul_pos ha hc)).mp hpow
  have hu := mul_le_mul_of_nonneg_left hρ ha.le
  nlinarith

end JanetCartan.SignedProductEstimates
