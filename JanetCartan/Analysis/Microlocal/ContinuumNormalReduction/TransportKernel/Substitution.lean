module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Entries
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Spectator
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables

/-!
# Conic substitution with a spectator

Conditional kernel calculation for `app:ch_background:eq:bg-full-complex-amplitude`.
The coordinate identification of `(s,η)` with Euclidean space has an explicit
measure-preservation premise. The conic map itself is supplied with its genuine
derivative, injectivity, left inverse and nonzero determinant, never with a
postulated integral identity. Geometric producers must instantiate these inputs.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ}

/-- Put Euclidean chart coordinates back into the literal initial variables,
retaining the spectator (`app:ch_background:eq:bg-Psi`). -/
def chartCarrierVariable (e : Euclidean n ≃ᵐ SliceVariable n)
    (v : Euclidean 2) (t : Euclidean n) : CarrierVariable n :=
  (((e t).1, v), (e t).2)

/-- The full two-position entry after inverse substitution and zero extension
outside the conic image (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def inverseDensityEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (k : Euclidean n) (i j : Fin n) : ℝ :=
  (Ψ v '' D v).indicator (fun k ↦ |(J v (U v k)).det|⁻¹ *
    normalDensityEntry d m x y (chartCarrierVariable e v (U v k)) i j) k

/-- The actual spectator integral defining the full two-position amplitude,
with regularization squared (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def fullAmplitudeEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n) (i j : Fin n) : ℝ :=
  ∫ v, inverseDensityEntry d m x y e D Ψ U J v k i j

/-- Exact change of variables at fixed spectator, with the absolute Jacobian
and both positions. This reuses the checked generic inverse-Jacobian theorem
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integral_slice_eq_inverseDensity (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x y : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (i j : Fin n)
    (hD : MeasurableSet (D v))
    (hΨ : ∀ t ∈ D v, HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : InjOn (Ψ v) (D v)) (hU : ∀ t ∈ D v, U v (Ψ v t) = t)
    (hJ : ∀ t ∈ D v, (J v t).det ≠ 0)
    (hsupp : ∀ t ∉ D v, normalDensityEntry d m x y (chartCarrierVariable e v t) i j = 0)
    (hphase : ∀ t ∈ D v,
      carrierPhase d x (chartCarrierVariable e v t) -
        carrierPhase d y (chartCarrierVariable e v t) =
          inner ℝ (d.chartPoint x - d.chartPoint y) (Ψ v t)) :
    (∫ t : SliceVariable n, NormalComparison.oscillatoryFactor 1
      (carrierPhase d x ((t.1, v), t.2) - carrierPhase d y ((t.1, v), t.2)) *
        (normalDensityEntry d m x y ((t.1, v), t.2) i j : ℂ)
          ∂(volume.prod volume)) =
      ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (inverseDensityEntry d m x y e D Ψ U J v k i j : ℂ) := by
  rw [← he.integral_comp']
  change (∫ t, NormalComparison.oscillatoryFactor 1
    (carrierPhase d x (chartCarrierVariable e v t) -
      carrierPhase d y (chartCarrierVariable e v t)) *
        (normalDensityEntry d m x y (chartCarrierVariable e v t) i j : ℂ)) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := D v) (fun t ht ↦ by simp [hsupp t ht])]
  rw [NormalComparison.integral_eq_inverse_jacobian_integral
    (D v) hD (Ψ v) (U v) (J v) hΨ hinj hU hJ]
  rw [← integral_indicator (measurable_image_of_fderivWithin hD hΨ hinj)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  by_cases hk : k ∈ Ψ v '' D v
  · obtain ⟨t, ht, rfl⟩ := hk
    simp only [Set.indicator_of_mem (mem_image_of_mem (Ψ v) ht),
      inverseDensityEntry, hU t ht, hphase t ht, Complex.real_smul,
      Complex.ofReal_mul]
    ring
  · simp [inverseDensityEntry, hk]

/-- The full regularized kernel equals the oscillatory integral of the
spectator amplitude. The two explicit integrability premises justify exactly
the two Fubini steps; no unregularized carrier bound is assumed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedNormalEntry_eq_fullAmplitude (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) {x y : Torus n}
    (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (i j : Fin n)
    (hD : ∀ v, MeasurableSet (D v))
    (hΨ : ∀ v t, t ∈ D v → HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : ∀ v, InjOn (Ψ v) (D v)) (hU : ∀ v t, t ∈ D v → U v (Ψ v t) = t)
    (hJ : ∀ v t, t ∈ D v → (J v t).det ≠ 0)
    (hsupp : ∀ v t, t ∉ D v →
      normalDensityEntry d m x y (chartCarrierVariable e v t) i j = 0)
    (hphase : ∀ v t, t ∈ D v →
      carrierPhase d x (chartCarrierVariable e v t) -
        carrierPhase d y (chartCarrierVariable e v t) =
          inner ℝ (d.chartPoint x - d.chartPoint y) (Ψ v t))
    (hint : Integrable (fun u ↦ NormalComparison.oscillatoryFactor 1
      (carrierPhase d x u - carrierPhase d y u) *
        (normalDensityEntry d m x y u i j : ℂ)) (carrierMeasure n))
    (htrans : Integrable (fun p : Euclidean 2 × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (d.chartPoint x - d.chartPoint y) p.2) *
        (inverseDensityEntry d m x y e D Ψ U J p.1 p.2 i j : ℂ)) (volume.prod volume)) :
    regularizedNormalEntry d m x y i j =
      ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (fullAmplitudeEntry d m x y e D Ψ U J k i j : ℂ) := by
  rw [regularizedNormalEntry_eq_phase_density d m hx hy,
    integral_carrier_eq_spectator _ hint]
  simp_rw [integral_slice_eq_inverseDensity d m x y e he D Ψ U J _ i j
    (hD _) (hΨ _) (hinj _) (hU _) (hJ _) (hsupp _) (hphase _)]
  rw [integral_integral_swap htrans]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  dsimp only
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

/-- Expanded manuscript formula: the measurement cutoffs are outside the
spectator integral, and the squared half-weight is divided by the absolute
conic Jacobian (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeEntry_eq_spectator_formula (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x y : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (k : Euclidean n) (i j : Fin n) :
    fullAmplitudeEntry d m x y e D Ψ U J k i j =
      d.measurementCutoff x * d.measurementCutoff y * ∫ v : Euclidean 2,
        (Ψ v '' D v).indicator (fun k ↦
          let u := chartCarrierVariable e v (U v k)
          (m u ^ 2 * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) ^ 2 *
            d.highCutoff ‖u.2‖ ^ 2 * ‖u.2‖ / |(J v (U v k)).det|) *
            ‖d.normalField (d.chartPoint x) u.1‖ ^ 2 *
            ‖d.normalField (d.chartPoint y) u.1‖ ^ 2 *
            reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1) i *
            reducedCovector d (d.chartPoint y) (d.covector (d.chartPoint y) u.1) j) k := by
  rw [fullAmplitudeEntry, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hk : k ∈ Ψ v '' D v
  · simp only [inverseDensityEntry, Set.indicator_of_mem hk, normalDensityEntry]
    ring
  · simp [inverseDensityEntry, hk]

/-- The literal carrier has no Fourier prefactor. With the normalized PDO
prefactor `(2π)⁻ⁿ`, its amplitude is therefore `(2π)ⁿ` times the spectator
integral (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integral_normalized_amplitude (a : Euclidean n → ℂ)
    (z : Euclidean n) :
    (((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k,
      NormalComparison.oscillatoryFactor 1 (inner ℝ z k) *
        (((2 * Real.pi) ^ n : ℂ) * a k)) =
      ∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ z k) * a k := by
  simp_rw [mul_left_comm (NormalComparison.oscillatoryFactor 1 _) ((2 * Real.pi) ^ n : ℂ)]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

end JanetCartan.ContinuumRow.TransportKernel
