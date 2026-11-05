module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Enumeration

/-!
# Banach-valued background quadrature

The generic deterministic estimate in `app:ch_waves:eq:background-quadrature`
of paper.tex. The window is the actual mollified convolution of `p` unit boxes.
Taylor's integral remainder, proved polynomial exactness, the two block masses,
and the existing block count give a constant independent of mesh and shifts.

The application to the manuscript's background tensors must establish the
stated `C^p` regularity and uniform derivative bounds for `ψ • H_c`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.BackgroundQuadrature
open SeparatedSampling LatticeQuadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact nonzero-sample enumeration identity for the weighted background
sum in `app:ch_waves:eq:background-quadrature`. -/
theorem sum_carrierBlock_eq_samples (p : ℕ) (B : ℝ) (ψ : Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (H : (Fin 3 → Fin (p + 1)) → Point → V)
    (U : Lattice → Point) :
    (∑ q ∈ integerCube (blockCutoff p B h),
      carrierBlock p w h (fun z ↦ ψ z • H (color p q) z) U q) =
      ∑ a ∈ samples p B ψ w h U,
        weight ψ w h U a • H (color p a.1) (node h U a) := by
  classical
  unfold samples
  rw [Finset.sum_filter]
  simp only [Finset.sum_product, carrierBlock, smul_smul]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro m _
  have he : h ^ 3 * blockWeight w h q (node h U (q, m)) * ψ (node h U (q, m)) =
      weight ψ w h U (q, m) := by unfold weight; ring
  rw [he]
  by_cases hz : weight ψ w h U (q, m) = 0 <;> simp [hz]

/-- Explicit uniform quadrature coefficient from block counting and the
support radius (`app:ch_waves:eq:background-quadrature`). -/
def backgroundQuadratureConstant (p : ℕ) (B : ℝ) : ℝ :=
  2 * blockCountConstant p B * windowRadius p ^ p

/-- The generic deterministic background quadrature estimate for the actual
convolved-box product window. All hypotheses concern the smoothing kernel,
the fixed patch, and actual carrier derivatives; no quadrature error or
cancellation premise is assumed. The constant is independent of `h`, `U`, and
any frequency entering `H` (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_background_quadrature_le [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (H : (Fin 3 → Fin (p + 1)) → Point → V)
    (hH : ∀ c, ContDiff ℝ p (fun z ↦ ψ z • H c z))
    {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ z • H c z) z‖ ≤ A)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    ‖(∑ a ∈ samples p B ψ (convolvedBoxWindow κ p) h U,
        weight ψ (convolvedBoxWindow κ p) h U a • H (color p a.1) (node h U a)) -
      ∑ q ∈ integerCube (blockCutoff p B h),
        ∫ z : Point, blockWeight (convolvedBoxWindow κ p) h q z •
          (ψ z • H (color p q) z)‖ ≤ backgroundQuadratureConstant p B * A * h ^ p := by
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hw := convolvedBoxWindow_bounds hi hm hn hk hp
  rw [← sum_carrierBlock_eq_samples, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _q ∈ integerCube (blockCutoff p B h),
        h ^ 3 * (2 * A * (h * windowRadius p) ^ p) :=
      Finset.sum_le_sum fun q _ ↦ norm_carrierBlock_error_le hc hs hm hp hw
        (hH (color p q)) hA (hD (color p q)) hh U q (hU q)
    _ = (((integerCube (blockCutoff p B h)).card : ℝ) * h ^ 3) *
        (2 * A * (h * windowRadius p) ^ p) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ blockCountConstant p B * (2 * A * (h * windowRadius p) ^ p) :=
      mul_le_mul_of_nonneg_right (card_blocks_mul_cube_le hψ.radius_nonneg hh hh₁)
        (by dsimp [windowRadius]; positivity)
    _ = backgroundQuadratureConstant p B * A * h ^ p := by
      unfold backgroundQuadratureConstant
      rw [mul_pow]
      ring

/-- The constant in the background estimate is positive and fixed before the
mesh and shifts (`app:ch_waves:eq:background-quadrature`). -/
theorem backgroundQuadratureConstant_pos (p : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 < backgroundQuadratureConstant p B := by
  dsimp [backgroundQuadratureConstant, blockCountConstant, windowRadius]
  positivity

/-- Colored masks on a finite block enumeration, in the convention of
`app:ch_waves:thm:sampling`. -/
def coloredBlockMask (p : ℕ) (s : Finset Lattice) (w : ℝ → ℝ) (h : ℝ)
    (c : Fin 3 → Fin (p + 1)) (z : Point) : ℝ :=
  ∑ q ∈ s with color p q = c, blockWeight w h q z

/-- Exact pointwise regrouping by colored masks, for the background integrand
in `app:ch_waves:eq:background-quadrature`. -/
theorem sum_blockWeight_eq_colored_masks (p : ℕ) (s : Finset Lattice)
    (w : ℝ → ℝ) (h : ℝ) (F : (Fin 3 → Fin (p + 1)) → Point → V) (z : Point) :
    (∑ q ∈ s, blockWeight w h q z • F (color p q) z) =
      ∑ c, coloredBlockMask p s w h c z • F c z := by
  classical
  unfold coloredBlockMask
  simp only [Finset.sum_smul]
  rw [← Finset.sum_fiberwise s (color p) (fun q ↦ blockWeight w h q z • F (color p q) z)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro q hq
  rw [(Finset.mem_filter.mp hq).2]

/-- Exact integral identification with the colored masks whenever the literal
block integrands are integrable (`app:ch_waves:eq:background-quadrature`). -/
theorem sum_blockIntegrals_eq_integral_colored_masks (p : ℕ) (s : Finset Lattice)
    (w : ℝ → ℝ) (h : ℝ) (F : (Fin 3 → Fin (p + 1)) → Point → V)
    (hI : ∀ q ∈ s, Integrable (fun z ↦ blockWeight w h q z • F (color p q) z)) :
    (∑ q ∈ s, ∫ z : Point, blockWeight w h q z • F (color p q) z) =
      ∫ z : Point, ∑ c, coloredBlockMask p s w h c z • F c z := by
  rw [← integral_finsetSum _ hI]
  congr 1
  funext z
  exact sum_blockWeight_eq_colored_masks p s w h F z

/-- The source's sum of colored-mask integrals equals the literal block-integral
sum. Continuity supplies every integrability requirement
(`app:ch_waves:eq:background-quadrature`). -/
theorem sum_blockIntegrals_eq_sum_coloredMask_integrals {p : ℕ} (s : Finset Lattice)
    {w : ℝ → ℝ} {M : ℝ} (hw : WindowBounds p w M) (hwc : Continuous w)
    {h : ℝ} (hh : h ≠ 0) (F : (Fin 3 → Fin (p + 1)) → Point → V)
    (hF : ∀ c, Continuous (F c)) :
    (∑ q ∈ s, ∫ z : Point, blockWeight w h q z • F (color p q) z) =
      ∑ c, ∫ z : Point, coloredBlockMask p s w h c z • F c z := by
  classical
  rw [← Finset.sum_fiberwise s (color p)
    (fun q ↦ ∫ z : Point, blockWeight w h q z • F (color p q) z)]
  apply Finset.sum_congr rfl
  intro c _
  simp only [coloredBlockMask, Finset.sum_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2]
  · intro q _
    exact integrable_blockWeight_smul hw hwc hh q (hF c)

/-- The deterministic estimate in colored-mask form, with all block
integrability and Taylor cancellation obligations discharged
(`app:ch_waves:eq:background-quadrature`). -/
theorem norm_background_quadrature_colored_le [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (H : (Fin 3 → Fin (p + 1)) → Point → V)
    (hH : ∀ c, ContDiff ℝ p (fun z ↦ ψ z • H c z))
    {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ z • H c z) z‖ ≤ A)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    ‖(∑ a ∈ samples p B ψ (convolvedBoxWindow κ p) h U,
        weight ψ (convolvedBoxWindow κ p) h U a • H (color p a.1) (node h U a)) -
      ∑ c, ∫ z : Point,
        coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c z •
          (ψ z • H c z)‖ ≤ backgroundQuadratureConstant p B * A * h ^ p := by
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  rw [← sum_blockIntegrals_eq_sum_coloredMask_integrals _
    (convolvedBoxWindow_bounds hi hm hn hk hp)
    (contDiff_convolvedBoxWindow hc hs p).continuous hh.ne' _ (fun c ↦ (hH c).continuous)]
  exact norm_background_quadrature_le hc hs hm hn hk hp hψ H hH hA hD hh hh₁ U hU

end JanetCartan.Sampling.BackgroundQuadrature
