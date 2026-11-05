module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.TransportComparison.Pointwise
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks

/-!
# The colored-to-transport integral comparison

The first inverse-frequency jet and the exact original colored partition give
the comparison following `app:ch_waves:eq:background-quadrature`. The constant
uses the mass of the original carrier measurement, and is independent of the
mesh, shifts, radial labels and amplitude scale. This Banach-valued deduction
applies to physical tensors and, after the compact lift, to their L2 classes.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling LatticeQuadrature BackgroundQuadrature ColoredNormalComparison

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The unchanged compact patch weight is compactly supported. Consumer:
the transport comparison following `app:ch_waves:eq:background-quadrature`. -/
theorem hasCompactSupport_backgroundPatch {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) : HasCompactSupport ψ := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Icc (fun _ : Fin 3 ↦ -B) (fun _ : Fin 3 ↦ B)))
  intro z hz
  by_contra hn
  exact hz ⟨fun i ↦ (abs_le.mp (hψ.support z hn i)).1,
    fun i ↦ (abs_le.mp (hψ.support z hn i)).2⟩

/-- The original color masks and radial labels give the `O(λ⁻¹)` integral
comparison directly from the first joint jet. At the actual polynomial's
zero endpoint, `backgroundPolynomial_zero` identifies the original transport
tensor; no prepared scalar or altered measurement enters
(`app:ch_waves:eq:background-quadrature`, adjacent comparison). -/
theorem norm_colored_integral_sub_transport_le
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ)
    {H : ℝ × Point → V} (hH : ContDiff ℝ ∞ H)
    {A : ℕ → ℝ} (hA : 0 ≤ A 1) {L : ℝ} {rpar : ℕ} (hrpar : 1 ≤ rpar)
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z, ∀ j,
      ‖iteratedFDeriv ℝ j H (τ, z)‖ ≤ A j * L ^ (j - rpar))
    (R : (Fin 3 → Fin (p + 1)) → ℝ) (hR : ∀ c, 1 ≤ R c)
    {lam : ℝ} (hlam : 1 ≤ lam) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    ‖(∑ c, ∫ z : Point,
        coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c z •
          (ψ z • H ((R c * lam)⁻¹, z))) -
      ∫ z : Point, ψ z • H (0, z)‖ ≤ ((∫ z, ψ z) * A 1) * lam⁻¹ := by
  classical
  let m := coloredBlockMask p (integerCube (blockCutoff p B h))
    (convolvedBoxWindow κ p) h
  let w := fun c z ↦ m c z * ψ z
  let C := A 1 * lam⁻¹
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hψs := hasCompactSupport_backgroundPatch hψ
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hmn (c) (z) : 0 ≤ m c z :=
    coloredBlockMask_nonneg _ (convolvedBoxWindow_nonneg hn p) h c z
  have hwn (c) (z) : 0 ≤ w c z := mul_nonneg (hmn c z) (hψ.nonneg z)
  have hwc (c) : Continuous (w c) :=
    (contDiff_coloredBlockMask hc hs p _ h c).continuous.mul hψc
  have hws (c) : HasCompactSupport (w c) := hψs.mul_left
  have hI (c) (t : ℝ) : Integrable (fun z ↦ w c z • H (t, z)) :=
    ((hwc c).smul (hH.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport ((hws c).smul_right)
  have hwSum (z : Point) : ∑ c, w c z = ψ z := by
    dsimp [w]
    rw [← Finset.sum_mul]
    by_cases hz : ψ z = 0
    · simp [hz]
    · rw [sum_coloredBlockMask_eq_one hi hm hn hk hp hψ hh hh₁ hz, one_mul]
  have hzero (z : Point) : ∑ c, w c z • H (0, z) = ψ z • H (0, z) := by
    rw [← Finset.sum_smul, hwSum]
  have hbound (z : Point) :
      ‖∑ c, w c z • (H ((R c * lam)⁻¹, z) - H (0, z))‖ ≤ ψ z * C := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ c, w c z * C := by
        apply Finset.sum_le_sum
        intro c _
        rw [norm_smul, Real.norm_of_nonneg (hwn c z)]
        exact mul_le_mul_of_nonneg_left
          (norm_radial_inverseFrequency_sub_zero_le hH hA hrpar hj (hR c) hlam z)
          (hwn c z)
      _ = _ := by rw [← Finset.sum_mul, hwSum]
  have he :
      (∑ c, ∫ z, m c z • (ψ z • H ((R c * lam)⁻¹, z))) -
        (∫ z, ψ z • H (0, z)) =
      ∫ z, ∑ c, w c z • (H ((R c * lam)⁻¹, z) - H (0, z)) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    rw [integral_sub (integrable_finsetSum _ fun c _ ↦ hI c _)
      (integrable_finsetSum _ fun c _ ↦ hI c 0),
      integral_finsetSum _ (fun c _ ↦ hI c _)]
    simp_rw [hzero]
    simp only [w, smul_smul]
  rw [he]
  exact (norm_integral_le_of_norm_le (hψi.mul_const C)
    (Eventually.of_forall hbound)).trans_eq (by rw [integral_mul_const]; dsimp [C]; ring)

end JanetCartan.Sampling.RetainedBackground
