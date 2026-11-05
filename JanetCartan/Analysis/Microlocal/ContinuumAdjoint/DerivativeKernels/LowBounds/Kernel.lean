module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Expansion
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Substitution

/-!
# Normal kernels for arbitrary modified adjoint amplitudes

The amplitudes in `app:ch_background:prop:bg-adjoint` may be complex after
derivative trades. They include every measurement and angular cutoff. The
adjoint uses `a`, so the forward kernel uses `conj a`. These definitions retain
both positions and the literal carrier measure; no torus or graph input is
substituted for the carrier space.

Consumers: the compact regularization and primitive jet estimates in `LowBounds`.
The conic chart hypotheses below are geometric inputs, to be instantiated from
`ContinuumNormalReduction.ConicChart` by the parent construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow ContinuumRow.TransportKernel NormalComparison

variable {n : ℕ}

/-- Forward scalar kernel whose adjoint is `chartAdjoint`, including an arbitrary
real frequency regularization (`app:ch_background:prop:bg-adjoint`). -/
def modifiedCarrierKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x : Euclidean n) (u : CarrierVariable n) : ℂ :=
  (m u : ℂ) * oscillatoryFactor 1 (Φ u.1 x u.2) * star (a u.1 x u.2)

/-- Complete two-position density of a modified amplitude, retaining the square
of regularization (`app:ch_background:prop:bg-adjoint`). -/
def modifiedNormalDensity (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (u : CarrierVariable n) : ℂ :=
  (m u : ℂ) ^ 2 * (star (a u.1 x u.2) * a u.1 y u.2)

/-- Literal paired kernel, on `dz dη`, for a modified amplitude in
`app:ch_background:prop:bg-adjoint`. Its operator realization is a separate proof. -/
def modifiedNormalKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) : ℂ :=
  ∫ u, modifiedCarrierKernel Φ a m x u * star (modifiedCarrierKernel Φ a m y u)
    ∂carrierMeasure n

/-- Exact phase subtraction for the full complex amplitude, as needed in
`app:ch_background:prop:bg-adjoint`. -/
theorem modifiedCarrierKernel_mul_star
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (u : CarrierVariable n) :
    modifiedCarrierKernel Φ a m x u * star (modifiedCarrierKernel Φ a m y u) =
      oscillatoryFactor 1 (Φ u.1 x u.2 - Φ u.1 y u.2) *
        modifiedNormalDensity a m x y u := by
  rw [← oscillatoryFactor_mul_star]
  simp only [modifiedCarrierKernel, modifiedNormalDensity, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The exact density formula before substitution, with no discarded cutoff
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedNormalKernel_eq_phase_density
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n) :
    modifiedNormalKernel Φ a m x y = ∫ u,
      oscillatoryFactor 1 (Φ u.1 x u.2 - Φ u.1 y u.2) *
        modifiedNormalDensity a m x y u ∂carrierMeasure n := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (modifiedCarrierKernel_mul_star Φ a m x y)

/-- Full inverse-Jacobian density for an arbitrary modified amplitude. The
spectator is retained, and the inverse is allowed to depend on both positions
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def modifiedInverseDensity (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (k : Euclidean n) : ℂ :=
  (Ψ v '' D v).indicator (fun k ↦ |(J v (U v k)).det|⁻¹ •
    modifiedNormalDensity a m x y (chartCarrierVariable e v (U v k))) k

/-- The spectator integral in the full modified normal, in physical frequency
(`app:ch_background:prop:bg-adjoint`). The literal carrier has no Fourier
prefactor; the normalized PDO amplitude is `(2π)^n` times this integral. -/
def modifiedNormalAmplitude (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (x y : Euclidean n) (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n) : ℂ :=
  ∫ v, modifiedInverseDensity a m x y e D Ψ U J v k

/-- Conic substitution at fixed spectator for a modified complex amplitude,
reusing the general Jacobian theorem (`app:ch_background:prop:bg-adjoint`). -/
theorem integral_modified_slice_eq_inverseDensity
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (hD : MeasurableSet (D v))
    (hΨ : ∀ t ∈ D v, HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : InjOn (Ψ v) (D v)) (hU : ∀ t ∈ D v, U v (Ψ v t) = t)
    (hJ : ∀ t ∈ D v, (J v t).det ≠ 0)
    (hsupp : ∀ t ∉ D v, modifiedNormalDensity a m x y (chartCarrierVariable e v t) = 0)
    (hphase : ∀ t ∈ D v,
      Φ (chartCarrierVariable e v t).1 x (chartCarrierVariable e v t).2 -
        Φ (chartCarrierVariable e v t).1 y (chartCarrierVariable e v t).2 =
          inner ℝ (x - y) (Ψ v t)) :
    (∫ t : SliceVariable n, oscillatoryFactor 1 (Φ (t.1, v) x t.2 - Φ (t.1, v) y t.2) *
      modifiedNormalDensity a m x y ((t.1, v), t.2) ∂(volume.prod volume)) =
      ∫ k, oscillatoryFactor 1 (inner ℝ (x - y) k) *
        modifiedInverseDensity a m x y e D Ψ U J v k := by
  rw [← he.integral_comp']
  change (∫ t, oscillatoryFactor 1
    (Φ (chartCarrierVariable e v t).1 x (chartCarrierVariable e v t).2 -
      Φ (chartCarrierVariable e v t).1 y (chartCarrierVariable e v t).2) *
      modifiedNormalDensity a m x y (chartCarrierVariable e v t)) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := D v) (fun t ht ↦ by simp [hsupp t ht])]
  rw [integral_eq_inverse_jacobian_integral (D v) hD (Ψ v) (U v) (J v) hΨ hinj hU hJ]
  rw [← integral_indicator (measurable_image_of_fderivWithin hD hΨ hinj)]
  apply integral_congr_ae
  filter_upwards [] with k
  by_cases hk : k ∈ Ψ v '' D v
  · obtain ⟨t, ht, rfl⟩ := hk
    simp only [modifiedInverseDensity, indicator_of_mem (mem_image_of_mem (Ψ v) ht),
      hU t ht, hphase t ht, Complex.real_smul]
    ring
  · simp [modifiedInverseDensity, hk]

/-- Exact full two-position normal for modified amplitudes. The displayed
absolute integrability conditions are precisely the two Fubini obligations;
they are not operator estimates (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedNormalKernel_eq_fullAmplitude
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v)) (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ v t, t ∉ D v → modifiedNormalDensity a m x y (chartCarrierVariable e v t) = 0)
    (hphase : ∀ v t, t ∈ D v →
      Φ (chartCarrierVariable e v t).1 x (chartCarrierVariable e v t).2 -
        Φ (chartCarrierVariable e v t).1 y (chartCarrierVariable e v t).2 =
          inner ℝ (x - y) (Ψ v t))
    (hint : Integrable (fun u ↦ oscillatoryFactor 1 (Φ u.1 x u.2 - Φ u.1 y u.2) *
      modifiedNormalDensity a m x y u) (carrierMeasure n))
    (htrans : Integrable (fun p : Euclidean 2 × Euclidean n ↦
      oscillatoryFactor 1 (inner ℝ (x - y) p.2) *
        modifiedInverseDensity a m x y e D Ψ U J p.1 p.2) (volume.prod volume)) :
    modifiedNormalKernel Φ a m x y = ∫ k,
      oscillatoryFactor 1 (inner ℝ (x - y) k) *
        modifiedNormalAmplitude a m x y e D Ψ U J k := by
  rw [modifiedNormalKernel_eq_phase_density, integral_carrier_eq_spectator _ hint]
  simp_rw [integral_modified_slice_eq_inverseDensity Φ a m x y e he D Ψ U J _
    (hD _) (hΨ _) (hinj _) (hU _) (hJ _) (hsupp _) (hphase _)]
  rw [integral_integral_swap htrans]
  apply integral_congr_ae
  filter_upwards [] with k
  exact integral_const_mul _ _

end JanetCartan.ContinuumAdjoint.DerivativeKernels
