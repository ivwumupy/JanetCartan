module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.CompactKernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.Conic
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.Cutoff

/-!
# Actual compact modified carrier operators

The scalar operator for each derivative-expansion term of
`app:ch_background:prop:bg-adjoint`, on Euclidean measurement L² and the
literal shared carrier L² space. Continuity and compact support construct the
operator, its Hilbert adjoint, and its normal; no operator estimate is assumed.
Consumer: the modified-amplitude bound in `LowBounds`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow

variable {n : ℕ}
  (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
  (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
  (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
  (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
  (hm : Continuous m) (hms : HasCompactSupport m)
  {K : Set (Euclidean n)} (hK : IsCompact K)
  (has : ∀ u : CarrierVariable n, ∀ x, x ∉ K → a u.1 x u.2 = 0)

/-- The constructed compact regularization for an arbitrary complex modified
amplitude (`app:ch_background:prop:bg-adjoint`). -/
def modifiedCarrierOperator : CarrierL2 n →L[ℂ] Lp (α := Euclidean n) ℂ 2 :=
  CompactCarrierKernel.compactKernelOperator
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has)

/-- The regularization acts by its actual forward kernel on every carrier L²
input (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierOperator_ae (f : CarrierL2 n) :
    modifiedCarrierOperator Φ a m hΦ ha hm hms hK has f =ᵐ[volume]
      fun x ↦ ∫ u, modifiedCarrierKernel Φ a m x u * f u ∂carrierMeasure n :=
  CompactCarrierKernel.compactKernelOperator_ae_integral _ _ f

include hΦ ha hm hms hK has

/-- Every forward integral converges absolutely
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedCarrierOperator (f : CarrierL2 n) (x : Euclidean n) :
    Integrable (fun u ↦ modifiedCarrierKernel Φ a m x u * f u) (carrierMeasure n) :=
  CompactCarrierKernel.integrable_compactKernel_mul_L2
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f x

/-- Every adjoint integral converges absolutely
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedCarrierOperator_adjoint
    (f : Lp (α := Euclidean n) ℂ 2) (u : CarrierVariable n) :
    Integrable (fun x ↦ star (modifiedCarrierKernel Φ a m x u) * f x) :=
  CompactCarrierKernel.integrable_compactKernel_adjoint_L2
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f u

/-- The actual Hilbert adjoint is the regularized `chartAdjoint` on all
measurement L² data (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierOperator_adjoint_ae (f : Lp (α := Euclidean n) ℂ 2) :
    (modifiedCarrierOperator Φ a m hΦ ha hm hms hK has).adjoint f =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) *
        chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) f := by
  have h := CompactCarrierKernel.compactKernelOperator_adjoint_ae_integral
    (μ := carrierMeasure n) (ν := volume)
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f
  simpa only [modifiedCarrierOperator, integral_star_modifiedCarrierKernel] using h

/-- Absolute joint integrability justifies normal-kernel Fubini on every L²
input (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedCarrierOperator_normal_weight
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    Integrable (fun p : Euclidean n × CarrierVariable n ↦
      modifiedCarrierKernel Φ a m x p.2 * star (modifiedCarrierKernel Φ a m p.1 p.2) *
        f p.1) (volume.prod (carrierMeasure n)) :=
  CompactCarrierKernel.integrable_compactKernel_normal_weight
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f x

/-- Absolute convergence of the literal normal on all measurement L² data
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedNormalKernel_action
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    Integrable (fun y ↦ modifiedNormalKernel Φ a m x y * f y) :=
  CompactCarrierKernel.integrable_compactKernel_normal_action
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f x

/-- The composed normal has the literal `modifiedNormalKernel` on every
measurement L² datum (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierOperator_normal_ae (f : Lp (α := Euclidean n) ℂ 2) :
    modifiedCarrierOperator Φ a m hΦ ha hm hms hK has
      ((modifiedCarrierOperator Φ a m hΦ ha hm hms hK has).adjoint f) =ᵐ[volume]
        fun x ↦ ∫ y, modifiedNormalKernel Φ a m x y * f y :=
  CompactCarrierKernel.compactKernelOperator_normal_ae
    (continuous_modifiedCarrierKernel Φ a m hΦ ha hm)
    (hasCompactSupport_modifiedCarrierKernel Φ a m hK hms has) f

/-- On all measurement L² data, the actual normal is the physical-frequency
integral of the full spectator amplitude. Every change-of-variables and Fubini
premise is supplied by primitive chart data and compact support
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-adjoint`). The normalized PDO amplitude is `(2π)^n`
times the displayed amplitude, as in `TransportKernel.integral_normalized_amplitude`.
The output is exactly the scalar Euclidean L² space of the scalar PDO API. -/
theorem modifiedCarrierOperator_normal_fullAmplitude_ae
    (e : Euclidean n ≃ᵐ TransportKernel.SliceVariable n) (hec : Continuous e)
    (he : MeasurePreserving e volume (volume.prod volume))
    (D : Euclidean n → Euclidean n → Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean n → Euclidean n → Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean 2 → Euclidean n →
      Euclidean n →L[ℝ] Euclidean n)
    (C : Euclidean n → Euclidean n → Set (Euclidean 2 × Euclidean n))
    (hC : ∀ x y, IsCompact (C x y))
    (hCD : ∀ x y p, p ∈ C x y → p.2 ∈ D x y p.1)
    (hΨc : ∀ x y, ContinuousOn
      (fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ x y p.1 p.2)) (C x y))
    (hUc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ U x y p.1 p.2)
      ((fun p : Euclidean 2 × Euclidean n ↦ (p.1, Ψ x y p.1 p.2)) '' C x y))
    (hJc : ∀ x y, ContinuousOn (fun p : Euclidean 2 × Euclidean n ↦ J x y p.1 p.2)
      (C x y))
    (hD : ∀ x y v, MeasurableSet (D x y v))
    (hΨ : ∀ x y v t, t ∈ D x y v →
      HasFDerivWithinAt (Ψ x y v) (J x y v t) (D x y v) t)
    (hinj : ∀ x y v, InjOn (Ψ x y v) (D x y v))
    (hU : ∀ x y v t, t ∈ D x y v → U x y v (Ψ x y v t) = t)
    (hJ : ∀ x y v t, t ∈ D x y v → (J x y v t).det ≠ 0)
    (hsupp : ∀ x y p, p ∉ C x y → modifiedNormalDensity a m x y
      (TransportKernel.chartCarrierVariable e p.1 p.2) = 0)
    (hphase : ∀ x y v t, t ∈ D x y v →
      Φ (TransportKernel.chartCarrierVariable e v t).1 x
          (TransportKernel.chartCarrierVariable e v t).2 -
        Φ (TransportKernel.chartCarrierVariable e v t).1 y
          (TransportKernel.chartCarrierVariable e v t).2 =
          inner ℝ (x - y) (Ψ x y v t))
    (f : Lp (α := Euclidean n) ℂ 2) :
    modifiedCarrierOperator Φ a m hΦ ha hm hms hK has
      ((modifiedCarrierOperator Φ a m hΦ ha hm hms hK has).adjoint f) =ᵐ[volume]
        fun x ↦ ∫ y, (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
          modifiedNormalAmplitude a m x y e (D x y) (Ψ x y) (U x y) (J x y) k) * f y := by
  filter_upwards [modifiedCarrierOperator_normal_ae Φ a m hΦ ha hm hms hK has f]
    with x hx
  rw [hx]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [modifiedNormalKernel_eq_fullAmplitude_of_compactChart Φ a m x y hΦ ha hm hms
    e hec he (D x y) (Ψ x y) (U x y) (J x y) (C x y) (hC x y) (hCD x y)
    (hΨc x y) (hUc x y) (hJc x y) (hD x y) (hΨ x y) (hinj x y) (hU x y)
    (hJ x y) (hsupp x y) (hphase x y)]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
