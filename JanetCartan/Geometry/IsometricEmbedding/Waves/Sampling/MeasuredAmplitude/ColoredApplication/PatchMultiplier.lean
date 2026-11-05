module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.MaskDerivative

/-!
# The original patch weight in the colored multiplier

The actual retained normal amplitude contains the smooth auxiliary carrier
cutoff from `FullNormalData`. The original patch weight instead belongs in
the input multiplier. The consumer is the retained application of
`app:ch_waves:eq:colored-normal-comparison`. Only the patch weight itself is
differentiated; no smooth square root is required.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open SeparatedSampling LatticeQuadrature BackgroundQuadrature ColoredNormalComparison

/-- The original patch-weighted color partition is exact everywhere, including
outside the patch. This is the multiplier identity at the transport endpoint
of `app:ch_waves:eq:colored-normal-comparison`. -/
theorem sum_patch_mul_coloredBlockMask
    {κ : ℝ → ℝ} (hi : Integrable κ) (hm : ∫ t, κ t = 1)
    (hn : ∀ t, 0 ≤ κ t) (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : Point) :
    ∑ c, φ z * coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c z = φ z := by
  rw [← Finset.mul_sum]
  by_cases hz : φ z = 0
  · simp only [hz, zero_mul]
  · rw [sum_coloredBlockMask_eq_one hi hm hn hk hp hφ hh hh₁ hz, mul_one]

/-- The first derivative of the original smooth patch weight is bounded by a
fixed constant, as required for its product with the color mask in
`app:ch_waves:eq:colored-normal-comparison`. The compact support is proved
from the original `PatchBounds`, rather than added as an analytic premise. -/
theorem exists_patch_fderiv_bound {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) (hs : ContDiff ℝ ∞ φ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z, ‖fderiv ℝ φ z‖ ≤ L := by
  have hc : HasCompactSupport φ := by
    apply HasCompactSupport.intro
      (isCompact_Icc (a := fun _ : Fin 3 ↦ -B) (b := fun _ ↦ B))
    intro z hz
    by_contra hn
    apply hz
    exact ⟨fun i ↦ (abs_le.mp (hφ.support z hn i)).1,
      fun i ↦ (abs_le.mp (hφ.support z hn i)).2⟩
  obtain ⟨L, hL⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hs.continuous_fderiv (by simp))
  exact ⟨L, (norm_nonneg _).trans (hL 0), hL⟩

/-- The literal patch-weighted color multiplier has range `[0,P]` and first
derivative at most `L/h`, with `L` chosen before the spectator, mesh, colors
and frequencies. This supplies the multiplier input of the retained normal
comparison without differentiating a square root
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_patch_coloredBlockMask_pullback_bounds
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {φ : Point → ℝ} {B P : ℝ}
    (hφ : PatchBounds φ B P) (hφs : ContDiff ℝ ∞ φ)
    {n : ℕ} (Z : EuclideanSpace ℝ (Fin n) →L[ℝ] Point) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z₀ : Point, ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ c : Fin 3 → Fin (p + 1),
        let m := fun u ↦ φ (z₀ + Z u) *
          coloredBlockMask p (integerCube (blockCutoff p B h))
            (convolvedBoxWindow κ p) h c (z₀ + Z u)
        ContDiff ℝ ∞ m ∧ (∀ u, 0 ≤ m u ∧ m u ≤ P) ∧
          ∀ u, ‖fderiv ℝ m u‖ ≤ L / h := by
  obtain ⟨Lφ, hLφ, hφd⟩ := exists_patch_fderiv_bound hφ hφs
  obtain ⟨Lc, hLc, hcd⟩ := exists_coloredBlockMask_pullback_fderiv_bound hc hs hm hn hk hp
  have hP : 0 ≤ P := (hφ.nonneg 0).trans (hφ.le_bound 0)
  refine ⟨Lφ * ‖Z‖ + P * (Lc * ‖Z‖), by positivity, ?_⟩
  intro z₀ h hh hh₁ c
  let a := fun u ↦ z₀ + Z u
  let b := fun u ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h c (a u)
  have ha : ContDiff ℝ ∞ a := contDiff_const.add Z.contDiff
  have hb : ContDiff ℝ ∞ b :=
    (contDiff_coloredBlockMask hc hs p _ h c).comp ha
  have hb₀ (u) : 0 ≤ b u :=
    coloredBlockMask_nonneg _ (convolvedBoxWindow_nonneg hn p) h c (a u)
  have hb₁ (u) : b u ≤ 1 := coloredBlockMask_le_one
    (hs.continuous.integrable_of_hasCompactSupport hc) hm hn hp _ h c (a u)
  refine ⟨(hφs.comp ha).mul hb, fun u ↦ ⟨mul_nonneg (hφ.nonneg _) (hb₀ u),
    (mul_le_mul_of_nonneg_left (hb₁ u) (hφ.nonneg _)).trans
      (by simpa only [mul_one] using hφ.le_bound (a u))⟩, ?_⟩
  intro u
  have hφa : ‖fderiv ℝ (φ ∘ a) u‖ ≤ Lφ * ‖Z‖ := by
    rw [fderiv_comp u (hφs.differentiable (by simp) _) (ha.differentiable (by simp) _),
      (Z.hasFDerivAt.const_add z₀).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hφd _) (norm_nonneg _))
  change ‖fderiv ℝ (fun u ↦ (φ ∘ a) u * b u) u‖ ≤ _
  rw [fderiv_fun_mul ((hφs.comp ha).differentiable (by simp) u)
    (hb.differentiable (by simp) u)]
  calc
    _ ≤ ‖(φ ∘ a) u • fderiv ℝ b u‖ + ‖b u • fderiv ℝ (φ ∘ a) u‖ := norm_add_le _ _
    _ = φ (a u) * ‖fderiv ℝ b u‖ + b u * ‖fderiv ℝ (φ ∘ a) u‖ := by
      rw [norm_smul, norm_smul, Function.comp_apply, Real.norm_of_nonneg (hφ.nonneg _),
        Real.norm_of_nonneg (hb₀ u)]
    _ ≤ P * (Lc * ‖Z‖ / h) + 1 * (Lφ * ‖Z‖) :=
      add_le_add (mul_le_mul (hφ.le_bound _) (hcd n Z B h hh c z₀ u)
        (norm_nonneg _) hP)
        (mul_le_mul (hb₁ u) hφa (norm_nonneg _) zero_le_one)
    _ ≤ (Lφ * ‖Z‖ + P * (Lc * ‖Z‖)) / h := by
      apply (le_div_iff₀ hh).mpr
      have hd : Lφ * ‖Z‖ * h ≤ Lφ * ‖Z‖ :=
        mul_le_of_le_one_right (by positivity) hh₁
      field_simp
      nlinarith

/-- Exact `L∞` realizations of the original patch-weighted masks. This is
valid for the actual open input domain; no Cartesian-product domain is needed
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_patch_coloredBlockMask_symbols
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t) {p : ℕ} (hp : 0 < p)
    {φ : Point → ℝ} {B P : ℝ} (hφ : PatchBounds φ B P) (hφc : Continuous φ)
    {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) (h : ℝ) (z : EuclideanSpace ℝ (Fin n) → Point)
    (hz : Continuous z) :
    ∃ g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict D),
      (∀ c, g c =ᵐ[volume.restrict D] fun u ↦
        (φ (z u) * coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z u) : ℂ)) ∧
      ∀ c, ‖g c‖ ≤ P := by
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hP : 0 ≤ P := (hφ.nonneg 0).trans (hφ.le_bound 0)
  let m := fun c u ↦ φ (z u) *
    coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c (z u)
  have hmc (c) : Continuous (fun u ↦ (m c u : ℂ)) :=
    Complex.continuous_ofReal.comp ((hφc.comp hz).mul
      ((contDiff_coloredBlockMask hc hs p _ h c).continuous.comp hz))
  have hmb (c) : ∀ᵐ u ∂volume.restrict D, ‖(m c u : ℂ)‖ ≤ P := by
    filter_upwards [] with u
    have hm₀ := coloredBlockMask_nonneg (p := p)
      (integerCube (blockCutoff p B h)) (convolvedBoxWindow_nonneg hn p) h c (z u)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ.nonneg _) hm₀)]
    exact (mul_le_mul_of_nonneg_left (coloredBlockMask_le_one hi hm hn hp _ h c (z u))
      (hφ.nonneg _)).trans (by simpa only [mul_one] using hφ.le_bound (z u))
  refine ⟨fun c ↦ AmplitudeBound.boundedSymbol _ (hmc c).aestronglyMeasurable P (hmb c),
    ?_, fun c ↦ AmplitudeBound.norm_boundedSymbol_le _ (hmc c).aestronglyMeasurable P (hmb c) hP⟩
  intro c
  simpa only [m, Complex.ofReal_mul] using
    AmplitudeBound.boundedSymbol_coeFn _ (hmc c).aestronglyMeasurable P (hmb c)

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
