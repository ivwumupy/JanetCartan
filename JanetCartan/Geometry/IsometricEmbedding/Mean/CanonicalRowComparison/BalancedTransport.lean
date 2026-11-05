module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundPreservingMasks

/-!
# The balanced detector copies retain the original transport density

The sampling refinement shares each subset's background weight among its
labels and compensates in its angular masks. Apply that actual construction
to the literal transport kernel, including detector dependence on the carrier
parameter. No plateau is required of an individual copied weight, and no
equality of independently chosen fields is used.

Consumer: the transport endpoint in `app:ch_waves:eq:colored-normal-comparison`
before the original continuum raw-square identification.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Classical

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow RawInputPartition Sampling SeparatedSampling

variable {n N : ℕ}

/-- The square root of the SAME nonnegative sampling weight enters the
literal normal density as that weight, with the Fourier scalar and original
band still inside the base kernel (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transportBand_normalDensity_eq_weight (d : CarrierData n N)
    (j : ℕ) (ψ : Point → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (x y : Torus n) (i k : Fin n) (u : CarrierVariable n) :
    carrierNormalDensity d (transportBandMask n j ψ) x y i k u =
      (ψ (carrierSamplingEquiv u.1) : ℂ) * carrierNormalDensity d
        (fun v ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j v) x y i k u := by
  have he : transportBandMask n j ψ = fun v : CarrierVariable n ↦
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j v) *
        Real.sqrt (ψ (carrierSamplingEquiv v.1)) := by
    funext v
    dsimp only [transportBandMask]
    ring
  rw [he, carrierNormalDensity_mul_mask, ← Complex.ofReal_pow, Real.sq_sqrt (hψ _)]

/-- The actual balanced carrier/detector copies reassemble each original
transport normal density on its full support, including zero weights and
zero detector/high-pass values. The cover is needed only where the original
kernel can be nonzero; no new detector is selected
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:background-quadrature`). -/
theorem sum_balanced_transportBand_normalDensity
    {I : Type*} [Fintype I] [DecidableEq I]
    (d : CarrierData n N) (j : ℕ)
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ a, ηb a ≠ 0) (hr : ∀ a, 0 < r a)
    (ψ : Point → ℝ) (b : I → Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P)
    (hb : ∀ a z, b a z ∈ Set.Icc (0 : ℝ) 1)
    (hcover : ∀ z η, ψ z ≠ 0 →
      d.angularCutoff (carrierSamplingEquiv.symm z) (‖η‖⁻¹ • η) ≠ 0 →
      d.highCutoff ‖η‖ ≠ 0 →
      ∃ a, b a z = 1 ∧ NormedSpace.normalize η ∈
        Metric.ball (NormedSpace.normalize (ηb a))
          (ContinuumRow.CanonicalConic.angularWidth (ηb a) (r a) / 4))
    (x y : Torus n) (i k : Fin n) (u : CarrierVariable n) :
    (∑ s : Finset I, ∑ a : s, carrierNormalDensity d
      (fun v ↦ transportBandMask n j (balancedCarrierSubsetWeight ψ b s) v *
        balancedSubsetAngularMask ηb r hηb hr s a v.2) x y i k u) =
      carrierNormalDensity d (transportBandMask n j ψ) x y i k u := by
  let m := fun v : CarrierVariable n ↦
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j v
  have he (s : Finset I) (a : s) : carrierNormalDensity d
      (fun v ↦ transportBandMask n j (balancedCarrierSubsetWeight ψ b s) v *
        balancedSubsetAngularMask ηb r hηb hr s a v.2) x y i k u =
      ((balancedCarrierSubsetWeight ψ b s (carrierSamplingEquiv u.1) *
        balancedSubsetAngularMask ηb r hηb hr s a u.2 ^ 2 : ℝ) : ℂ) *
          carrierNormalDensity d m x y i k u := by
    rw [carrierNormalDensity_mul_mask, transportBand_normalDensity_eq_weight d j
      (balancedCarrierSubsetWeight ψ b s)
      (balancedCarrierSubsetWeight_patchBounds ψ b hψ hb s).nonneg]
    push_cast
    ring
  simp_rw [he]
  rw [transportBand_normalDensity_eq_weight d j ψ hψ.nonneg]
  by_cases ha : d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) = 0
  · have hz (z : Torus n) : carrierKernel d z u = 0 := by
      by_cases hx : z ∈ d.outputChart <;>
        simp [carrierKernel, carrierAmplitude, hx, ha]
    simp [carrierNormalDensity, maskedCarrierKernel, hz]
  · by_cases hh : d.highCutoff ‖u.2‖ = 0
    · simp [carrierNormalDensity, maskedCarrierKernel, carrierKernel_eq_zero_of_highCutoff d _ _ hh]
    · have hp := sum_carrierSubsetWeight_mul_subsetAngularMask_sq ηb r hηb hr ψ b
        (carrierSamplingEquiv u.1) u.2 (fun hz ↦ hcover _ _ hz
          (by simpa only [MeasurableEquiv.symm_apply_apply] using ha) hh)
      simp_rw [balancedCarrierSubsetWeight_mul_angularMask_sq, ← Finset.sum_mul]
      congr 1
      exact_mod_cast hp

end JanetCartan.CanonicalRowComparison
