module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks

/-!
# The actual sampling colors on the preparation carrier space

For `app:ch_mean_pairs:prop:mean-coarse`, finite lattice colors partition the
original carrier support. Complete them measurably only where the external
carrier cutoff is zero, to instantiate the global partition used by finite
preparation. Prove exact equality of every weighted term and of the literal
Lebesgue integral. No sample, active weight, or mask derivative is changed.
-/

open MeasureTheory Set
open scoped ContDiff

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow SeparatedSampling LatticeQuadrature
open Sampling.BackgroundQuadrature Sampling.ColoredNormalComparison

/-- A fixed continuous compact carrier cutoff supplies the actual squared
sampling patch bounds before the mesh or shifts are chosen
(`app:ch_waves:thm:sampling`). -/
theorem exists_preparationCarrier_patchBounds
    (χ : CarrierParameter → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B P : ℝ, 0 ≤ P ∧
      PatchBounds (fun z : Point ↦ χ (carrierSamplingEquiv.symm z) ^ 2) B P := by
  have he : Continuous carrierSamplingEquiv :=
    carrierSamplingLinearEquiv.toContinuousLinearEquiv.continuous
  obtain ⟨B, hB⟩ := (hc.image he).isBounded.exists_norm_le
  obtain ⟨P, hP⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  refine ⟨max B 0, P ^ 2, sq_nonneg P, le_max_right _ _, fun _ ↦ sq_nonneg _, ?_, ?_⟩
  · intro z
    have hb := hP _ (mem_range_self (carrierSamplingEquiv.symm z))
    rw [Real.norm_eq_abs] at hb
    exact sq_le_sq.mpr (hb.trans (le_abs_self _))
  · intro z hz j
    have hχz : χ (carrierSamplingEquiv.symm z) ≠ 0 := by
      intro hh
      exact hz (by simp [hh])
    have hb : ‖z‖ ≤ B := hB z ⟨carrierSamplingEquiv.symm z,
      subset_tsupport χ hχz, carrierSamplingEquiv.apply_symm_apply z⟩
    have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j
    exact hj.trans (hb.trans (le_max_left _ _))

/-- The original finite lattice color, completed by one color where the
external carrier weight vanishes. This choice precedes the random shifts
(`app:ch_mean_pairs:prop:mean-coarse`). -/
def preparationCarrierColorMask (p : ℕ) (B : ℝ) (w : ℝ → ℝ) (h : ℝ)
    (χ : CarrierParameter → ℝ) (c : Fin 3 → Fin (p + 1)) (z : CarrierParameter) : ℝ :=
  if χ z = 0 then if c = (fun _ ↦ 0) then 1 else 0
  else coloredBlockMask p (integerCube (blockCutoff p B h)) w h c (carrierSamplingEquiv z)

/-- The completion requires only measurability; preparation never
differentiates these masks (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem measurable_preparationCarrierColorMask {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (p : ℕ) (B h : ℝ) {χ : CarrierParameter → ℝ} (hχ : Measurable χ)
    (c : Fin 3 → Fin (p + 1)) :
    Measurable (preparationCarrierColorMask p B (convolvedBoxWindow κ p) h χ c) := by
  classical
  apply Measurable.ite (measurableSet_eq_fun hχ measurable_const) measurable_const
  exact (contDiff_coloredBlockMask hc hs p _ h c).continuous.measurable.comp
    carrierSamplingEquiv.measurable

/-- All completed colors are nonnegative, uniformly in the mesh
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationCarrierColorMask_nonneg {p : ℕ} (B h : ℝ)
    {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t) (χ : CarrierParameter → ℝ)
    (c : Fin 3 → Fin (p + 1)) (z : CarrierParameter) :
    0 ≤ preparationCarrierColorMask p B w h χ c z := by
  classical
  unfold preparationCarrierColorMask
  split_ifs <;> first | positivity | exact coloredBlockMask_nonneg _ hw h c _

/-- The literal support partition supplies the global partition required by
the preparation recurrence. Its only patch hypothesis is the original
squared external carrier weight (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem sum_preparationCarrierColorMask {κ : ℝ → ℝ} (hi : Integrable κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {χ : CarrierParameter → ℝ} {B P : ℝ}
    (hχ : PatchBounds (fun z ↦ χ (carrierSamplingEquiv.symm z) ^ 2) B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : CarrierParameter) :
    ∑ c, preparationCarrierColorMask p B (convolvedBoxWindow κ p) h χ c z = 1 := by
  classical
  by_cases hz : χ z = 0
  · simp [preparationCarrierColorMask, hz]
  · simp only [preparationCarrierColorMask, ite_eq_right hz]
    exact sum_coloredBlockMask_eq_one hi hm hn hk hp hχ hh hh₁
      (by simpa only [Function.mem_support, carrierSamplingEquiv.symm_apply_apply,
        ne_eq, sq_eq_zero_iff] using hz)

/-- Each weighted color is exactly the original finite lattice color.
In particular the preparation completion cannot alter any active row or
current integral (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem preparationCarrierColorMask_mul_sq (p : ℕ) (B : ℝ) (w : ℝ → ℝ) (h : ℝ)
    (χ : CarrierParameter → ℝ) (c : Fin 3 → Fin (p + 1)) (z : CarrierParameter) :
    preparationCarrierColorMask p B w h χ c z * χ z ^ 2 =
      coloredBlockMask p (integerCube (blockCutoff p B h)) w h c
        (carrierSamplingEquiv z) * χ z ^ 2 := by
  classical
  by_cases hz : χ z = 0 <;> simp [preparationCarrierColorMask, hz]

/-- Exact change to the sampling coordinates for the SAME completed-color
integral. The carrier product measure is proved to be Lebesgue with no
normalization factor (`app:ch_mean_pairs:eq:mean-prepared-residual`). -/
theorem integral_preparationCarrierColorMask {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ℕ) (B : ℝ) (w : ℝ → ℝ) (h : ℝ)
    (χ : CarrierParameter → ℝ) (F : (Fin 3 → Fin (p + 1)) → CarrierParameter → E) :
    (∫ z, ∑ c, preparationCarrierColorMask p B w h χ c z • (χ z ^ 2 • F c z)
      ∂(volume.prod volume)) =
      ∫ z : Point, ∑ c, coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
        (χ (carrierSamplingEquiv.symm z) ^ 2 • F c (carrierSamplingEquiv.symm z)) := by
  rw [← integral_carrierSamplingEquiv]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [carrierSamplingEquiv.symm_apply_apply, smul_smul,
    preparationCarrierColorMask_mul_sq]

/-- The deterministic quadrature bound now applies to the original carrier
integral used by preparation. Its inputs are primitive carrier derivatives
of the weighted integrand, not a quadrature-error premise. The finite sample
labels, weights, colors and nodes are unchanged
(`app:ch_waves:eq:background-quadrature`). -/
theorem norm_preparationCarrierQuadrature_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {χ : CarrierParameter → ℝ} {B P : ℝ}
    (hχ : PatchBounds (fun z ↦ χ (carrierSamplingEquiv.symm z) ^ 2) B P)
    (F : (Fin 3 → Fin (p + 1)) → CarrierParameter → E)
    (hF : ∀ c, ContDiff ℝ p (fun z : Point ↦
      χ (carrierSamplingEquiv.symm z) ^ 2 • F c (carrierSamplingEquiv.symm z)))
    {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ c z, ‖iteratedFDeriv ℝ p (fun z : Point ↦
      χ (carrierSamplingEquiv.symm z) ^ 2 • F c (carrierSamplingEquiv.symm z)) z‖ ≤ A)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    ‖(∑ a ∈ samples p B (fun z ↦ χ (carrierSamplingEquiv.symm z) ^ 2)
        (convolvedBoxWindow κ p) h U,
      weight (fun z ↦ χ (carrierSamplingEquiv.symm z) ^ 2) (convolvedBoxWindow κ p) h U a •
        F (color p a.1) (carrierSamplingEquiv.symm (node h U a))) -
      ∫ z, ∑ c, preparationCarrierColorMask p B (convolvedBoxWindow κ p) h χ c z •
        (χ z ^ 2 • F c z) ∂(volume.prod volume)‖ ≤
      backgroundQuadratureConstant p B * A * h ^ p := by
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hw := convolvedBoxWindow_bounds hi hm hn hk hp
  rw [integral_preparationCarrierColorMask]
  rw [← sum_blockIntegrals_eq_integral_colored_masks]
  · exact norm_background_quadrature_le hc hs hm hn hk hp hχ
      (fun c z ↦ F c (carrierSamplingEquiv.symm z)) hF hA hD hh hh₁ U hU
  · intro q _
    exact integrable_blockWeight_smul hw (contDiff_convolvedBoxWindow hc hs p).continuous
      hh.ne' q (hF (color p q)).continuous

end JanetCartan.CurrentMean
