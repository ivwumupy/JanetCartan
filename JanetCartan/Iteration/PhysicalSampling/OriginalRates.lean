module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMargins
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedOriginalScaleMargins

/-!
# Fine-ceiling rate admission on the actual original family

The existing stronger original rate theorem is restricted to the literal
revised fine ceiling; its larger `1 + meanSlack` ceiling is NOT identified with
`fineExponent`. The same original finite family and common rate margin are used.
The radial labels remain the parent's labels, with only their positive numeric
lower bound supplied; no colors, rates, source or samples are reselected.

Consumers: `OriginalScalarHistory.current_bounds` and the corrected measured
continuations in the ONE original event (`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalRates
open PhysicalSeed PhysicalNormalInverse RawInputPartition

variable {m : ℕ} (hn : 5 ≤ m + 1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (m + 1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean (m + 1))
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (m + 1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (userExtra : StrongExtraCaps hn)

local notation "merged" => samplingCappedExtra hn pOrder userExtra
local notation "capped" => strongCappedExtra hn merged
set_option quotPrecheck false in
local notation "selected(" f ")" =>
  f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "actual(" f ")" =>
  f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra

/-- A numerical threshold before histories gives the exact fine-ceiling scalar
and measured rate admission at every stage, without changing the parent's
radial/color labels. The event threshold is reached by the COARSE parameter. -/
theorem exists_fine_threshold {Rmin : ℝ} (hRmin : 0 < Rmin) (eventThreshold : ℝ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ Rinit ≥ S, ∀ stage : ℕ,
      let T := historyScale Rinit growthExponent stage
      let Λ := T ^ fineExponent
      let lam := T ^ carrierExponent
      eventThreshold ≤ T ∧ 1 ≤ Λ ∧ 0 < lam ∧
      (∀ _i : actual(OriginalWeights.Index),
        2 * Λ / (Rmin * lam) ≤ actual(OriginalMargins.ε)) ∧
      ∀ (radial : actual(OriginalWeights.Index) → (Fin 3 → Fin (pOrder + 1)) → ℝ),
        (∀ i color, Rmin ≤ radial i color) → ∀ i color,
        0 < (radial i color * lam)⁻¹ ∧ (radial i color * lam)⁻¹ ≤ 1 ∧
        ∀ j : Fin (cutoffCount Λ),
          (radial i color * lam)⁻¹ * (2 : ℝ) ^ j.val ≤ actual(OriginalMargins.ε) := by
  let Trow := fun i : actual(OriginalWeights.Index) ↦
    OriginalBoundary.T hn ⟨i.1.1.1.1, i.2⟩
  let ρ := fun i : actual(OriginalWeights.Index) ↦
    originalSamplingRadius hn i.1.1 i.2 (selected(SelectedBoundary.cell) i.1.1 i.2)
  have hP := fun i : actual(OriginalWeights.Index) ↦
    ((OriginalBoundary.hD hn).2.2.2.2.1 i.1.1.1.1 i.2).1
  obtain ⟨S, hS, hwide⟩ := Sampling.exists_corrected_sampling_originalScale_threshold
    Trow hP (ρ := fun i ↦ (ρ i).1) (e := fun _ ↦ actual(OriginalMargins.ε))
    (fun i ↦ (ρ i).2) (fun _ ↦ actual(OriginalMargins.hε)) hRmin eventThreshold
  refine ⟨max S eventThreshold, hS.trans (le_max_left _ _), ?_⟩
  intro Rinit hRinit stage T Λ lam
  have hRold : S ≤ Rinit := (le_max_left _ _).trans hRinit
  have hRone : 1 ≤ Rinit := (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hRold)
  have hstage : Rinit ≤ T := le_historyScale hRone stage
  have hTone : 1 ≤ T := hRone.trans hstage
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hTone (by norm_num [fineExponent, meanSlack])
  have hceiling : Λ ≤ T ^ (1 + meanSlack) :=
    Real.rpow_le_rpow_of_exponent_le hTone (by norm_num [fineExponent, meanSlack])
  obtain ⟨_, _, hlam, hbuffer, hrates⟩ := hwide Rinit hRold stage
  refine ⟨((le_max_right S eventThreshold).trans hRinit).trans hstage, hΛ, hlam, ?_, ?_⟩
  · intro i
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hceiling (by norm_num : (0 : ℝ) ≤ 2))
      (mul_pos hRmin hlam).le).trans (hbuffer i)
  · intro radial hradial i color
    obtain ⟨hτ, hτone, hband⟩ := hrates pOrder radial hradial i color
    refine ⟨hτ, hτone, ?_⟩
    intro j
    let wide : Fin (cutoffCount (T ^ (1 + meanSlack))) :=
      ⟨j.val, j.isLt.trans_le (cutoffCount_mono hΛ hceiling)⟩
    exact (hband wide).trans (min_le_left _ _)

/-- The current coefficient scale fits both the literal fine ceiling and the
inverse of every genuine original rate whose radial label is at least one.
This supplies the scale-window input of the actual measured mean/band factories;
the compatible colored radial producer must still supply `hradial`. -/
theorem current_scale_bounds_for_radial_rate {Rinit radial : ℝ}
    (hRinit : 1 ≤ Rinit) (hradial : 1 ≤ radial) (stage : ℕ) :
    1 ≤ currentCoefficientScale Rinit stage ∧
      currentCoefficientScale Rinit stage ≤
        historyScale Rinit growthExponent stage ^ fineExponent ∧
      currentCoefficientScale Rinit stage ≤
        ((radial * historyScale Rinit growthExponent stage ^ carrierExponent)⁻¹)⁻¹ := by
  have hT : 1 ≤ historyScale Rinit growthExponent stage :=
    hRinit.trans (le_historyScale hRinit stage)
  refine ⟨one_le_currentCoefficientScale hRinit stage, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hT
      (show coefficientExponent ≤ fineExponent by
        norm_num [coefficientExponent, fineExponent, meanSlack])
  · simp only [inv_inv]
    exact (Real.rpow_le_rpow_of_exponent_le hT
      (show coefficientExponent ≤ carrierExponent by
        norm_num [coefficientExponent, carrierExponent])).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hT) _) hradial)

end JanetCartan.PhysicalSampling.OriginalRates
