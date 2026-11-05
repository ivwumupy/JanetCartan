module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.Reassembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Coordinates

/-!
# Original sampling weights in carrier coordinates

The unmasked mean in `app:ch_waves:eq:sampling-prefix-normal` is a finite sum
of wide-band normals, followed by the literal spectator integral. Bochner
integrability follows from compact patch bounds and kernel continuity.
The weight is the original `ψ`; no regularity of its square root is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.MeanNormalBound
open RawInputPartition SamplingKernelBounds SeparatedSampling BackgroundQuadrature ContinuumRow

variable {n J : ℕ} {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
  [LocallyCompactSpace Q]

/-- Bochner integrability of one reassembled weighted band in the original
sampling coordinates (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_wideBand_patch_normal
    (D : BandKernelData (Fin J × Q) n) (j : Fin J) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    Integrable (fun z ↦ ψ z • atomNormal (wideBandKernelOperator D j.val (j, q z))) :=
  integrable_patch_normal hψ hc _
    ((continuous_wideBandKernelOperator D j.val).comp
      (continuous_const.prodMk hq))

/-- Exact integration of the reassembled normals, on the same full Euclidean
output (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_refinedKernelPrefix_normal_eq_wide
    (D : BandKernelData (Fin J × Q) n) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D J (q z))) =
      ∑ j : Fin J, ∫ z : Point,
        ψ z • atomNormal (wideBandKernelOperator D j.val (j, q z)) := by
  simp_rw [refinedKernelPrefix_normal_eq_wide, Finset.smul_sum]
  exact integral_finsetSum _ (fun j _ ↦ integrable_wideBand_patch_normal D j q hq hψ hc)

/-- Fubini for one literal wide band, with spectator `v` outside and slice
parameter `s` inside. Both measures are Lebesgue, with no density or Jacobian
introduced by the carrier coordinates (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_wideBand_normal_eq_spectator
    (D : BandKernelData (Fin J × Q) n) (j : Fin J) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    (∫ z : Point, ψ z • atomNormal (wideBandKernelOperator D j.val (j, q z))) =
      ∫ v : Euclidean 2, ∫ s : ℝ,
        ψ (carrierSamplingEquiv (s, v)) •
          atomNormal (wideBandKernelOperator D j.val (j, q (carrierSamplingEquiv (s, v)))) := by
  rw [← integral_carrierSamplingEquiv]
  exact integral_prod_symm _
    (carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable
      (integrable_wideBand_patch_normal D j q hq hψ hc))

/-- The largest unmasked prefix, with the original weight and all original
wide bands, equals its spectator/slice integral
(`app:ch_waves:eq:sampling-prefix-normal`). The remaining full-phase bridge
must identify the inner integral from forward kernels. -/
theorem integral_refinedKernelPrefix_normal_eq_spectator
    (D : BandKernelData (Fin J × Q) n) (q : Point → Q) (hq : Continuous q)
    {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D J (q z))) =
      ∑ j : Fin J, ∫ v : Euclidean 2, ∫ s : ℝ,
        ψ (carrierSamplingEquiv (s, v)) •
          atomNormal (wideBandKernelOperator D j.val (j, q (carrierSamplingEquiv (s, v)))) := by
  rw [integral_refinedKernelPrefix_normal_eq_wide D q hq hψ hc]
  exact Finset.sum_congr rfl (fun j _ ↦ integral_wideBand_normal_eq_spectator D j q hq hψ hc)

/-- All original charts and radial colors remain in the exact unmasked mean.
This is the literal right side of `norm_refinedKernelPrefix_mean_le_unmasked`,
after reassembly and the measure-preserving carrier change
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_integral_refinedKernelPrefix_normal_eq_spectator
    {A : Type*} [Fintype A] {p : ℕ}
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ : A → Point → ℝ} {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hc : ∀ a, Continuous (ψ a)) :
    (∑ a, ∑ c, ∫ z : Point, ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) =
      ∑ a, ∑ c, ∑ j : Fin J, ∫ v : Euclidean 2, ∫ s : ℝ,
        ψ a (carrierSamplingEquiv (s, v)) •
          atomNormal (wideBandKernelOperator (D a) j.val
            (j, (c, carrierSamplingEquiv (s, v)))) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact integral_refinedKernelPrefix_normal_eq_spectator (D a) (fun z ↦ (c, z))
    (continuous_const.prodMk continuous_id) (hψ a) (hc a)

/-- Domination by a smooth cutoff square uses only `ψ ≤ P` and its support,
without asserting that `sqrt ψ` is smooth. The cutoff can therefore be used
in a full forward amplitude (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem patchWeight_le_cutoff_sq {ψ χ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hP : 0 ≤ P)
    (hχ : ∀ z, ψ z ≠ 0 → χ z = 1) (z : Point) : ψ z ≤ P * χ z ^ 2 := by
  by_cases hz : ψ z = 0
  · rw [hz]
    exact mul_nonneg hP (sq_nonneg _)
  · simpa only [hχ z hz, one_pow, mul_one] using hψ.le_bound z

end JanetCartan.Sampling.MeanNormalBound
