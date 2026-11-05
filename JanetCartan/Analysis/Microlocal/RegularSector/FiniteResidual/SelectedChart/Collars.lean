module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Source
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension

/-!
# Matching the two actual spatial collars

The spatial collar in the selected evolution and the collar in the finite
algebraic family are separately constructed. Both are one on the same right
multiplier after a fixed radial enlargement. Their source and algebraic
symbols, including the entire physical derivative of the latter, therefore
agree. No equality of the two collars is used. Consumer: the four PDOs of
the selected-chart equation in `energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FinitePdo
open CompatibleResponse
open FourierIntegral.LowBounds.FrequencyCutoff
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

private theorem dilated_mask_factor (mask : E → ℝ) {L₀ L : ℝ}
    (hL₀ : 0 < L₀) (hL : 2 * L₀ ≤ L) (ζ : E) :
    dilatedConicMask mask L ζ =
      (1 - physicalCutoff 0 (L⁻¹ • ζ)) * dilatedConicMask mask L₀ ζ := by
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  by_cases hz : ‖ζ‖ ≤ L
  · have hb : ‖L⁻¹ • ζ‖ ≤ radius 0 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      simp only [radius, Nat.cast_zero, zero_add]
      exact (inv_mul_le_iff₀ hLp).mpr (by simpa using hz)
    simp only [dilatedConicMask, conicMask, physicalCutoff_eq_one 0 hb, sub_self, zero_mul]
  · have hn : 2 ≤ ‖L₀⁻¹ • ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL₀.le)]
      exact (le_inv_mul_iff₀ hL₀).mpr (by linarith)
    change (1 - physicalCutoff 0 (L⁻¹ • ζ)) * radialSourceCutoff mask (L⁻¹ • ζ) =
      (1 - physicalCutoff 0 (L⁻¹ • ζ)) * conicMask mask (L₀⁻¹ • ζ)
    rw [conicMask_eq_radial hn]
    simp only [radialSourceCutoff,
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr hLp),
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr hL₀)]

variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The original finite-family collar is one on every full pulled-back right
support above twice its threshold. This factor-of-two margin uses only the
actual bump's inner and outer plateaux, without assuming radial monotonicity.
`SelectedChartEvolutionAt` allows choosing such a larger threshold.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selected_spatialMask_plateau_enlarged
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {L : ℝ}
    (hL : 2 * f.radialThreshold ≤ L) {ζ : E}
    (hζ : ζ ∈ tsupport (fun η ↦ (dilatedConicMask (f.angularMask p) L
      (physicalCoordinates (f.chart p).index η) : ℂ))) :
    conicMask (f.spatialMask p) =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ) := by
  let e := physicalCoordinates (f.chart p).index
  have he : (fun η ↦ dilatedConicMask (f.angularMask p) L (e η)) =
      (fun η ↦ 1 - physicalCutoff 0 (L⁻¹ • e η)) *
        (dilatedConicMask (f.angularMask p) f.radialThreshold ∘ e) := by
    funext η
    exact dilated_mask_factor _ (zero_lt_one.trans_le f.radialThreshold_ge_one) hL (e η)
  have hs : ζ ∈ tsupport (fun η ↦ dilatedConicMask (f.angularMask p) L (e η)) :=
    tsupport_comp_subset Complex.ofReal_zero _ hζ
  rw [he] at hs
  exact f.spatialMask_plateau p ζ (tsupport_mul_subset_right hs)

/-- Indices zero, one, and three use exactly the source/algebraic symbols
constructed by `FiniteAlgebraic.Construction` and `FinitePdo.Source`.
The endpoint keeps the retained `W₁`; the two collars are matched only after
their common right multiplier. Equality of the full algebraic symbol also
preserves every term of `P_x(b₋₁ α)` (`energy-complete-residual`). -/
theorem selected_directPDOSymbols_collar
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {L : ℝ}
    (hL : 2 * f.radialThreshold ≤ L)
    (angular : Euclidean d → ℝ)
    (hangular : ∀ ζ ∈ tsupport (fun η ↦ (dilatedConicMask (f.angularMask p) L
      (physicalCoordinates (f.chart p).index η) : ℂ)),
      conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ))
    (A : E → Fin (d + 1) → CMat) (B : E → CMat)
    (W₁ : TwoTimeAmplitude d (d + 1)) (bminus : E → E → CMat) :
    let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L
      (physicalCoordinates (f.chart p).index ζ) : ℂ)
    directPDOSymbols A B W₁ bminus
        (conicSourceSymbol (f.chart p).radialSection (conicMask angular) (f.chart p).sourceMask) β =
      directPDOSymbols A B W₁ bminus
        (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
          (f.chart p).sourceMask) β := by
  intro β
  have ha ζ (hζ : β ζ ≠ 0) := (hangular ζ (subset_tsupport β hζ)).eq_of_nhds
  have hf ζ (hζ : β ζ ≠ 0) :=
    (selected_spatialMask_plateau_enlarged f p hL (subset_tsupport β hζ)).eq_of_nhds
  have hb := (conicAlgebraicSymbol_eq_on_frequency_plateau (f.chart p).radialSection
    (conicMask angular) (f.chart p).sourceMask β bminus ha).trans
      (conicAlgebraicSymbol_eq_on_frequency_plateau (f.chart p).radialSection
        (conicMask (f.spatialMask p)) (f.chart p).sourceMask β bminus hf).symm
  have hs : (fun y ζ ↦ (conicSourceSymbol (f.chart p).radialSection
        (conicMask angular) (f.chart p).sourceMask y (spatialPart ζ) * β ζ) • (1 : CMat)) =
      fun y ζ ↦ (conicSourceSymbol (f.chart p).radialSection
        (conicMask (f.spatialMask p)) (f.chart p).sourceMask y (spatialPart ζ) * β ζ) •
          (1 : CMat) := by
    funext y ζ
    rw [conicSourceSymbol_mul_right_multiplier _ _ _ _ ha,
      conicSourceSymbol_mul_right_multiplier _ _ _ _ hf]
  simp only [directPDOSymbols, hb, hs]

/-- The source component of the direct residual is the actual finite-family
source PDO symbol at the same physical threshold, including its low-frequency
shoulder (`energy-complete-residual`). -/
theorem selected_directPDOSymbols_source
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (A : E → Fin (d + 1) → CMat) (B : E → CMat)
    (W₁ : TwoTimeAmplitude d (d + 1)) (bminus : E → E → CMat) :
    directPDOSymbols A B W₁ bminus
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask)
      (fun ζ ↦ (dilatedConicMask (f.angularMask p) L
        (physicalCoordinates (f.chart p).index ζ) : ℂ)) 1 = selectedSourceSymbol f p L := rfl

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
