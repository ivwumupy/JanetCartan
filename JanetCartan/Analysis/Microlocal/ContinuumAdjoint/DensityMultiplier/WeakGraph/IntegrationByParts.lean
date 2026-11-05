module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.MixedJetClosure
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Weighted carrier integration by parts

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the strong jets on compact smooth
tests satisfy the actual weak identity on literal product Lebesgue measure.
The transverse weight is constant during fiberwise integration by parts.
These identities and integrability lemmas are consumed by `WeakGraph` when
passing to the strong limits constructed in `MixedJetClosure`.
-/

open MeasureTheory LineDeriv
open scoped ContDiff

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem schwartz_direction_commute (f : SchwartzMap E ℂ) (v w : E) :
    ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v =
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w
  have hd := ((f.smooth ⊤).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    zero_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add]
  exact (f.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by simp) v w

private theorem schwartz_iterated_direction_commute (k : ℕ) (w : Fin k → E)
    (f : SchwartzMap E ℂ) (v : E) : ∂^{w} (∂_{v} f) = ∂_{v} (∂^{w} f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, ih, schwartz_direction_commute,
      ← iteratedLineDerivOp_succ_left]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem integral_schwartz_iterated (k : ℕ) (w : Fin k → E)
    (f φ : SchwartzMap E ℂ) :
    (∫ x, φ x * iteratedFDeriv ℝ k f x w ∂μ) =
      (-1 : ℂ)^k * ∫ x, f x * iteratedFDeriv ℝ k φ x w ∂μ := by
  simp only [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  induction k generalizing f φ with
  | zero => simp [mul_comm]
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left,
      SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left]
    rw [ih, schwartz_iterated_direction_commute, ← iteratedLineDerivOp_succ_left,
      pow_succ]
    ring

open ContinuumRow
variable {n k : ℕ}

/-- Evaluating the weighted test jet gives an L² coefficient for the weak
pairing in `app:ch_background:eq:bg-density-adjoint`. -/
theorem memLp_weightedCarrierJet_apply (k t : ℕ)
    {φ : CarrierVariable n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (w : Fin k → CarrierParameter) :
    MemLp (fun x ↦ weightedCarrierJet k t φ x w) 2 (carrierMeasure n) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ CarrierParameter) ℂ w).comp_memLp'
    (memLp_weightedCarrierJet_of_compactSupport k t hφ hcφ)

/-- Integrability of the jet side of the weak identity for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem integrable_test_mul_carrierJet (J : Lp (CarrierParameter [×k]→L[ℝ] ℂ)
    2 (carrierMeasure n)) {φ : CarrierVariable n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (w : Fin k → CarrierParameter) :
    Integrable (fun x ↦ φ x * J x w) (carrierMeasure n) := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure; infer_instance
  exact (hφ.continuous.memLp_of_hasCompactSupport hcφ (p := 2)).integrable_mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ CarrierParameter) ℂ w).comp_memLp J)

/-- Integrability of the transposed weighted test against any literal carrier
L² datum (`app:ch_background:eq:bg-density-adjoint`). -/
theorem integrable_weighted_test_derivative (t : ℕ) (g : CarrierL2 n)
    {φ : CarrierVariable n → ℂ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (w : Fin k → CarrierParameter) :
    Integrable (fun x ↦ (etaBesselWeight t x : ℂ) * g x *
      iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w) (carrierMeasure n) := by
  convert (Lp.memLp g).integrable_mul (memLp_weightedCarrierJet_apply k t hφ hcφ w) using 1
  ext x
  simp only [Pi.mul_apply, weightedCarrierJet, smul_apply,
    Complex.real_smul]
  ring

private theorem hasCompactSupport_carrier_slice {f : CarrierVariable n → ℂ}
    (hc : HasCompactSupport f) (η : Euclidean (n - 1)) :
    HasCompactSupport (fun z ↦ f (z, η)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
  intro z hz
  exact ⟨(z, η), subset_tsupport f hz, rfl⟩

/-- Repeated carrier integration by parts on compact smooth tests, with the
transverse weight constant on each carrier fiber. Used to identify the strong
jet limits in `app:ch_background:eq:bg-density-adjoint`. -/
theorem integral_test_mul_weightedCarrierJet (k t : ℕ)
    {f φ : CarrierVariable n → ℂ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (w : Fin k → CarrierParameter) :
    (∫ x, φ x * weightedCarrierJet k t f x w ∂carrierMeasure n) =
      (-1 : ℂ)^k * ∫ x, (etaBesselWeight t x : ℂ) * f x *
        iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure; infer_instance
  have hi := (hφ.continuous.memLp_of_hasCompactSupport hcφ (p := 2)).integrable_mul
    (memLp_weightedCarrierJet_apply k t hf hcf w)
  have hj := (hf.continuous.memLp_of_hasCompactSupport hcf (p := 2)).integrable_mul
    (memLp_weightedCarrierJet_apply k t hφ hcφ w)
  change Integrable (fun x ↦ φ x * weightedCarrierJet k t f x w) _ at hi
  change Integrable (fun x ↦ f x * weightedCarrierJet k t φ x w) _ at hj
  have he x : (etaBesselWeight t x : ℂ) * f x *
      iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w =
      f x * weightedCarrierJet k t φ x w := by
    simp only [weightedCarrierJet, smul_apply, Complex.real_smul]
    ring
  simp_rw [he]
  rw [carrierMeasure, integral_prod_symm _ hi, integral_prod_symm _ hj,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with η
  have h := integral_schwartz_iterated (μ := volume.prod volume) k w
    ((hasCompactSupport_carrier_slice hcf η).toSchwartzMap
      (hf.comp (contDiff_id.prodMk contDiff_const)))
    ((hasCompactSupport_carrier_slice hcφ η).toSchwartzMap
      (hφ.comp (contDiff_id.prodMk contDiff_const)))
  simp only [weightedCarrierJet, smul_apply, Complex.real_smul]
  change (∫ z, φ (z, η) * ((etaBesselWeight t (0, η) : ℂ) *
      iteratedFDeriv ℝ k (fun z ↦ f (z, η)) z w) ∂volume.prod volume) =
    (-1 : ℂ)^k * ∫ z, f (z, η) * ((etaBesselWeight t (0, η) : ℂ) *
      iteratedFDeriv ℝ k (fun z ↦ φ (z, η)) z w) ∂volume.prod volume
  simp_rw [mul_left_comm _ (etaBesselWeight t (0, η) : ℂ), integral_const_mul]
  change (etaBesselWeight t (0, η) : ℂ) * _ = _
  change (∫ z, φ (z, η) * iteratedFDeriv ℝ k (fun z ↦ f (z, η)) z w
    ∂volume.prod volume) = (-1 : ℂ)^k * ∫ z, f (z, η) *
      iteratedFDeriv ℝ k (fun z ↦ φ (z, η)) z w ∂volume.prod volume at h
  rw [h]
  ring

end JanetCartan.ContinuumAdjoint.DensityMultiplier
