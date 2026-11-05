module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.BlockEstimate

/-!
# Physical carrier blocks

Change of variables and the literal sampled block of
`app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.BackgroundQuadrature
open SeparatedSampling LatticeQuadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Center of the carrier block in `app:ch_waves:thm:sampling`. -/
def blockCenter (h : ℝ) (q : Lattice) : Point := fun i ↦ h * (q i : ℝ)

/-- Literal block sum, with the patch weight absorbed into the Banach-valued
carrier function, in `app:ch_waves:eq:background-quadrature`. -/
def carrierBlock (p : ℕ) (w : ℝ → ℝ) (h : ℝ) (f : Point → V)
    (U : Lattice → Point) (q : Lattice) : V :=
  ∑ m ∈ integerCube (p + 2),
    (h ^ 3 * blockWeight w h q (node h U (q, m))) • f (node h U (q, m))

/-- The window in block coordinates is the product window
(`app:ch_waves:eq:background-quadrature`). -/
theorem blockWeight_rescale (w : ℝ → ℝ) {h : ℝ} (hh : h ≠ 0)
    (q : Lattice) (y : Point) :
    blockWeight w h q (blockCenter h q + h • y) = productWindow w y := by
  unfold blockWeight productWindow
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, blockCenter]
  field_simp
  ring

/-- The physical block integral is exactly `h³` times its normalized integral,
including for Banach-valued functions (`app:ch_waves:eq:background-quadrature`). -/
theorem integral_blockWeight_rescale (w : ℝ → ℝ) {h : ℝ} (hh : 0 < h)
    (q : Lattice) (f : Point → V) :
    (∫ z : Point, blockWeight w h q z • f z) =
      h ^ 3 • ∫ y : Point, productWindow w y • f (blockCenter h q + h • y) := by
  have he : (∫ y : Point, blockWeight w h q (blockCenter h q + h • y) •
      f (blockCenter h q + h • y)) =
      (h ^ 3)⁻¹ • ∫ z : Point, blockWeight w h q z • f z := by
    rw [volume.integral_comp_smul
      (fun z ↦ blockWeight w h q (blockCenter h q + z) • f (blockCenter h q + z)) h,
      integral_add_left_eq_self (fun z : Point ↦ blockWeight w h q z • f z) (blockCenter h q)]
    simp [abs_of_pos hh]
  simp_rw [blockWeight_rescale w hh.ne'] at he
  rw [he, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hh.ne'), one_smul]

/-- Continuous carrier functions give integrable physical block integrands;
this discharges the integrability input in the colored-mask identity
(`app:ch_waves:eq:background-quadrature`). -/
theorem integrable_blockWeight_smul {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) (hwc : Continuous w) {h : ℝ} (hh : h ≠ 0)
    (q : Lattice) {f : Point → V} (hf : Continuous f) :
    Integrable (fun z : Point ↦ blockWeight w h q z • f z) := by
  have hi : Integrable (fun y : Point ↦ productWindow w y •
      f (blockCenter h q + h • y)) :=
    integrable_productWindow_smul hw hwc (hf.comp (by fun_prop))
  have hi' : Integrable (fun y : Point ↦ blockWeight w h q (blockCenter h q + h • y) •
      f (blockCenter h q + h • y)) := by
    simpa only [blockWeight_rescale w hh] using hi
  have ht := (integrable_comp_smul_iff volume
    (fun z : Point ↦ blockWeight w h q (blockCenter h q + z) •
      f (blockCenter h q + z)) hh).mp hi'
  simpa only [add_neg_cancel_left] using ht.comp_add_left (-blockCenter h q)

/-- The literal sample node is the normalized lattice node rescaled about its
block center (`app:ch_waves:thm:sampling`). -/
theorem node_rescale {h : ℝ} (hh : h ≠ 0) (U : Lattice → Point) (q m : Lattice) :
    node h U (q, m) = blockCenter h q + h • (fun i ↦ U q i / h + m i) := by
  ext i
  simp only [node, blockCenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The finite literal block is the normalized sample sum times `h³`
(`app:ch_waves:eq:background-quadrature`). -/
theorem carrierBlock_rescale (p : ℕ) (w : ℝ → ℝ) {h : ℝ} (hh : h ≠ 0)
    (f : Point → V) (U : Lattice → Point) (q : Lattice) :
    carrierBlock p w h f U q = h ^ 3 •
      ∑ m ∈ integerCube (p + 2), productWindow w (fun i ↦ U q i / h + m i) •
        f (blockCenter h q + h • (fun i ↦ U q i / h + m i)) := by
  simp only [carrierBlock, node_rescale hh, blockWeight_rescale w hh,
    Finset.smul_sum, smul_smul]

/-- Physical block error `2 A R^p h^(p+3)` with no hypothesis asserting an error
estimate or remainder cancellation (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_carrierBlock_error_le [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) {p : ℕ} (hp : 0 < p) {M : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) M)
    {f : Point → V} (hf : ContDiff ℝ p f) {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ z, ‖iteratedFDeriv ℝ p f z‖ ≤ A) {h : ℝ} (hh : 0 < h)
    (U : Lattice → Point) (q : Lattice) (hU : ∀ i, 0 ≤ U q i ∧ U q i < h) :
    ‖carrierBlock p (convolvedBoxWindow κ p) h f U q -
      ∫ z : Point, blockWeight (convolvedBoxWindow κ p) h q z • f z‖ ≤
        h ^ 3 * (2 * A * (h * windowRadius p) ^ p) := by
  rw [carrierBlock_rescale p _ hh.ne', integral_blockWeight_rescale _ hh,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg hh.le 3)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le 3)
  apply norm_normalized_block_error_le hc hs hm hp hw hf hA hD hh.le
  intro i
  exact ⟨div_nonneg (hU i).1 hh.le, (div_lt_one hh).mpr (hU i).2⟩

end JanetCartan.Sampling.BackgroundQuadrature
