module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Output.CompactKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Output integration by parts for the regularized literal adjoint

The output step of `app:ch_regular_base:eq:graph-derivative-transfer`, independent
of homogeneity and the source phase trade. The full physical amplitude, original
coordinates, normalization, Lebesgue measure, and complex Euclidean output fiber
are retained. The separate source-transfer proof must still identify the first
output amplitude integral with its remainder and datum branches.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
variable {K : Set (Euclidean n × Euclidean n)} {C : FullAmplitude n r}
  {S : Euclidean n → Euclidean n → ℝ} {χ : Euclidean n → ℂ}

private theorem reverseGraphOperator_output_weak_pairing_coordinates
    (hC : ReverseAmplitudeAdmissible K C) (hK : IsCompact K)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (u : E → Fin r → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    (∫ y, partialDeriv φ y i • reverseGraphOperator S (frequencyCutFullAmplitude χ C) u y) =
      -(∫ y, φ y • reverseGraphOperator S
        (frequencyCutFullAmplitude χ (reverseFirstOutputAmplitude C i)) u y) := by
  have hg := ReverseRegularized.Output.smooth_reverseGraphOperator hC hS hχ hχs hχ0 hu hus
  have hgs := ReverseRegularized.Output.compactSupport_reverseGraphOperator
    (S := S) (χ := χ) (u := u) hC hK
  have hi : Integrable (fun y ↦ φ y • reverseGraphOperator S (frequencyCutFullAmplitude χ C) u y) :=
    (hφ.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hiφ : Integrable (fun y ↦ partialDeriv φ y i •
      reverseGraphOperator S (frequencyCutFullAmplitude χ C) u y) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hig : Integrable (fun y ↦ φ y •
      partialDeriv (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) y i) :=
    (hφ.continuous.smul ((hg.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hgs.fderiv_apply ℝ (EuclideanSpace.single i 1)).smul_left
  have hb := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hiφ hig hi
    (fun y _ ↦ hφ.differentiable (by simp) y) (fun y _ ↦ hg.differentiable (by simp) y)
  have hw : (∫ y, partialDeriv φ y i •
      reverseGraphOperator S (frequencyCutFullAmplitude χ C) u y) =
      -(∫ y, φ y • partialDeriv (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) y i) := by
    simpa only [partialDeriv, neg_neg] using congrArg Neg.neg hb.symm
  simpa only [ReverseRegularized.Output.partialDeriv_reverseGraphOperator
    hC hS hχ hχs hχ0 hu hus] using hw

/-- Integrability of the undifferentiated regularized reverse pairing in the
complex Hilbert fiber. Apply to every admissible remainder or datum amplitude
before integrating the separate source-transfer identity.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_frequencyCut_integrable_pairing
    (hC : ReverseAmplitudeAdmissible K C) (hK : IsCompact K)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    Integrable (fun y ↦ φ y • WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun x ↦ (u.val x).ofLp) := Lr.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun x ↦ (u.val x).ofLp) :=
    u.property.2.comp_left Lr.map_zero
  have hg := ReverseRegularized.Output.smooth_reverseGraphOperator hC hS hχ hχs hχ0 hu hus
  have hgs := ReverseRegularized.Output.compactSupport_reverseGraphOperator
    (S := S) (χ := χ) (u := fun x ↦ (u.val x).ofLp) hC hK
  have hi := (φ.continuous.smul hg.continuous).integrable_of_hasCompactSupport
    (μ := (volume : Measure E)) hgs.smul_left
  have ht : Integrable (fun y ↦ L.symm (φ y •
      reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) :=
    L.symm.toContinuousLinearMap.integrable_comp hi
  simpa only [map_smul, L, PiLp.coe_symm_continuousLinearEquiv] using ht

/-- Output weak integration by parts for the literal compact-frequency reverse
operator. The first output amplitude is explicit, and all integration and
domination premises have been discharged from smoothness and compact support.
No homogeneity, mixed inverse, source-transfer identity, or recurrence is assumed.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraphOperator_frequencyCut_output_weak_pairing
    (hC : ReverseAmplitudeAdmissible K C) (hK : IsCompact K)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    (∫ y, partialDeriv φ y i • WithLp.toLp 2
      (reverseGraphOperator S (frequencyCutFullAmplitude χ C) (fun x ↦ (u.val x).ofLp) y)) =
      -(∫ y, φ y • WithLp.toLp 2
        (reverseGraphOperator S (frequencyCutFullAmplitude χ (reverseFirstOutputAmplitude C i))
          (fun x ↦ (u.val x).ofLp) y)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun x ↦ (u.val x).ofLp) := Lr.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun x ↦ (u.val x).ofLp) :=
    u.property.2.comp_left Lr.map_zero
  have hw := reverseGraphOperator_output_weak_pairing_coordinates hC hK hS hχ hχs hχ0
    _ hu hus φ (φ.smooth ⊤) i
  have he := congrArg L.symm hw
  simp only [map_neg] at he
  simp_rw [← L.symm.integral_comp_comm] at he
  simp only [map_smul] at he
  simpa only [L, PiLp.coe_symm_continuousLinearEquiv] using he

end JanetCartan.FourierIntegral
