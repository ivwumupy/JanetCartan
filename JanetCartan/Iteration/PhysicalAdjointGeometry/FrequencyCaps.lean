module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.ActualGeometry
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.ModulationScales
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LebesgueData

/-!
# The original fine input band stays in the same phase buffer

The original source uses `cutoffCount (R ^ fineExponent)`, whose literal
Lebesgue Fourier density has support in the closed ball of radius `2^J ≤ 4K`.
The final displacement Fourier exponent is larger than the carrier exponent
and is deliberately NOT used here. The existing original-scale threshold
places every source displacement in the fixed buffer before histories.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric

namespace JanetCartan.PhysicalAdjointGeometry
open RawInputPartition RawPrimary

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

omit [NormedSpace ℝ X] in
/-- The complete original dyadic Fourier ceiling, not just its nominal cutoff,
lies in the fixed displacement buffer after one pre-history threshold
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_originalFineBand_shiftDomain_threshold
    {r ε : ℝ} (hε : 0 < ε) (ξ : Euclidean m) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S, ∀ stage : ℕ,
      let R := historyScale R₀ growthExponent stage
      ∀ radial : ℝ, 1 ≤ radial →
      ∀ (x : X), ‖x‖ < r → ∀ ζ : Euclidean m, dist ζ ξ + ε < r →
      ∀ η ∈ closedBall (0 : Euclidean m) ((2 : ℝ) ^ cutoffCount (R ^ fineExponent)),
        (x, ζ, (radial * R ^ carrierExponent)⁻¹ • η) ∈ shiftDomain ξ r := by
  obtain ⟨S, hS, hshift⟩ := InitialSourceLocalization.exists_originalScale_source_shift_threshold hε 4
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ stage R radial hradial x hx ζ hζ η hη
  have hR₀one : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR₀)
  have hR : 1 ≤ R := hR₀one.trans (le_historyScale hR₀one stage)
  have hK : 1 ≤ R ^ fineExponent := Real.one_le_rpow hR (by norm_num [fineExponent, meanSlack])
  have hηnorm : ‖η‖ ≤ (2 : ℝ) ^ cutoffCount (R ^ fineExponent) := by simpa using hη
  have hb := hshift R₀ hR₀ stage radial hradial ((2 : ℝ) ^ cutoffCount (R ^ fineExponent))
    (by positivity) (cutoffCount_ceiling hK)
  refine ⟨hx, ?_⟩
  calc
    _ = dist ζ ξ + |(radial * R ^ carrierExponent)⁻¹| * ‖η‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ dist ζ ξ + |(radial * R ^ carrierExponent)⁻¹| *
        (2 : ℝ) ^ cutoffCount (R ^ fineExponent) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hηnorm (abs_nonneg _))
    _ ≤ dist ζ ξ + ε := add_le_add le_rfl hb
    _ < r := hζ

/-- The literal representative of the unchanged wide Fourier density only
uses the frequency ball for which the preceding actual displacement theorem
applies. The spatial initial cutoff is not confused with a frequency cutoff
(`app:ch_waves:eq:individual-representation`). -/
theorem originalWideDensity_support_subset {n J : ℕ}
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    Function.support (weightedWideDensity d v) ⊆
      closedBall (0 : Euclidean (n - 1)) ((2 : ℝ) ^ J) := by
  intro η hη
  by_contra hn
  have hb : (2 : ℝ) ^ J ≤ ‖η‖ := le_of_lt (by simpa using hn)
  exact hη (wideDensity_eq_zero_of_ceiling_le d v hb)

end JanetCartan.PhysicalAdjointGeometry
