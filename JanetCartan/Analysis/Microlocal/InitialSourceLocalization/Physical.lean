module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Realization
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers.Schwartz

/-!
# Physical Hilbert realization of the initial defect

The finite-channel quantization is transferred to its original Euclidean
fiber. The source and mask are unchanged, and the physical-to-unit-period
frequency conversion is exactly `xi = 2*pi*eta`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set MeasureTheory FourierTransform Filter
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph FiniteChain.Graph.KernelLimits JanetCartan.Localization
open FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The literal right quantization respects almost-everywhere equality of
the source, through its original two integrals
(`app:ch_regular:lem:finite-chain`). -/
theorem rightLocalizer_congr_ae (ρ : ℝ) (m : LocalizerSymbol n)
    {f g : E → Fin r → ℂ} (hfg : f =ᵐ[volume] g) (x : E) :
    rightLocalizer ρ m f x = rightLocalizer ρ m g x := by
  unfold rightLocalizer FourierIntegral.graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Changing only the finite-fiber representation commutes with the literal
complementary Fourier kernel, with no norm or Fourier-normalization change
(`app:ch_regular:eq:source-tail`). -/
theorem complementarySourceFourierKernel_toEuclidean
    (m : LocalizerSymbol n) (φ : E → ℝ) (a : E → V) (ρ : ℝ) (ξ : E) :
    WithLp.toLp 2 (complementarySourceFourierKernel m φ (fun y ↦ (a y).ofLp) ρ ξ) =
      complementarySourceFourierKernel m φ a ρ ξ := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm
  change e (∫ y, phaseOscillation (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) y •
    complementarySourceAmplitude m (fun y ↦ (a y).ofLp) (ρ⁻¹ • ξ) y) = _
  rw [← e.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [complementarySourceAmplitude, map_smul]
  rfl

/-- The original Hilbert-valued source minus the literal right quantization
has a Schwartz representative whose ordinary Fourier transform is the
proved complementary kernel at the EXACT physical frequency `2*pi*xi`
(`app:ch_regular:eq:source-tail`). -/
theorem exists_initialSource_defect_euclidean_schwartz
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → V) {U : Set E} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∃ g : SchwartzMap E V,
      (∀ x, g x = phaseOscillation (fun y ↦ ρ * φ y) x • a x -
        WithLp.toLp 2 (rightLocalizer ρ m
          (fun y ↦ (phaseOscillation (fun z ↦ ρ * φ z) y • a y).ofLp) x)) ∧
      ∀ ξ, (𝓕 g) ξ = complementarySourceFourierKernel m φ a ρ ((2 * Real.pi) • ξ) := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  have ha' : ContDiffOn ℝ ∞ (fun y ↦ (a y).ofLp) U :=
    (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn ha
  have hs' : tsupport (fun y ↦ (a y).ofLp) ⊆ tsupport a :=
    tsupport_comp_subset e.map_zero a
  obtain ⟨g, hg, hgF⟩ := exists_initialSource_defect_schwartz m hm hmc φ
    (fun y ↦ (a y).ofLp) hU hφ ha' (hs'.trans hs)
      (hc.of_isClosed_subset (isClosed_tsupport _) hs') hρ
  refine ⟨toEuclideanSchwartz g, fun x ↦ ?_, fun ξ ↦ ?_⟩
  · rw [toEuclideanSchwartz_apply, hg]
    rfl
  · have hnorm := hgF ((2 * Real.pi) • ξ)
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    change ((2 * Real.pi) ^ n : ℝ)⁻¹ •
      (𝓕 g) ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ)) = _ at hnorm
    rw [inv_smul_smul₀ hπ] at hnorm
    have hnorm' : (((2 * Real.pi) ^ n : ℂ)⁻¹) • (𝓕 g) ξ =
        (((2 * Real.pi) ^ n : ℂ)⁻¹) •
          complementarySourceFourierKernel m φ (fun y ↦ (a y).ofLp) ρ
            ((2 * Real.pi) • ξ) := by
      convert hnorm using 1
      norm_cast
    have heq := (smul_right_injective (M := Fin r → ℂ)
      (show (((2 * Real.pi) ^ n : ℂ)⁻¹) ≠ 0 by exact inv_ne_zero (pow_ne_zero _
        (by exact_mod_cast hπ)))) hnorm'
    rw [← toEuclideanSchwartz_fourier, toEuclideanSchwartz_apply, heq]
    exact complementarySourceFourierKernel_toEuclidean m φ a ρ _

/-- The actual bounded right localizer has the initial complementary kernel
as its Fourier representative on the ORIGINAL L² source. All representatives
are identified almost everywhere; no independent operator is selected
(`app:ch_regular:eq:source-tail`). -/
theorem bounded_initialSource_defect_fourier_ae
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → V) {U : Set E} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a) {ρ : ℝ} (hρ : ρ ≠ 0)
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (hu : u =ᵐ[volume] fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y) :
    (𝓕 (u - M u) : H) =ᵐ[volume]
      fun ξ ↦ complementarySourceFourierKernel m φ a ρ ((2 * Real.pi) • ξ) := by
  obtain ⟨g, hg, hgF⟩ := exists_initialSource_defect_euclidean_schwartz
    m hm hmc φ a hU hφ ha hs hc hρ
  have hinput : (fun y ↦ (u y).ofLp) =ᵐ[volume]
      fun y ↦ (phaseOscillation (fun z ↦ ρ * φ z) y • a y).ofLp :=
    hu.fun_comp WithLp.ofLp
  have he : u - M u = g.toLp 2 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub u (M u), hu, hM u, g.coeFn_toLp 2] with x hsub hu' hm' hg'
    rw [hsub, Pi.sub_apply, hu', hm', hg', hg, rightLocalizer_congr_ae ρ m hinput x]
  rw [he, SchwartzMap.toLp_fourier_eq]
  exact ((𝓕 g).coeFn_toLp 2).trans (Eventually.of_forall hgF)

end JanetCartan.InitialSourceLocalization
