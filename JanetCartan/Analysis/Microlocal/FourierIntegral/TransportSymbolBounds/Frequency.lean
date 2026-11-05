module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Homogeneity

/-!
# Frequency weights in normalized joint charts

For `app:ch_regular_base:eq:direct-graph-amplitudes`, a fixed positive frequency
radius rescales the two covector jets by degrees -1 and -2 and the phase Hessian
by degree 1. This module proves the resulting degree -1 identity for every joint
jet of the literal correction. Physical differentiation preserves that degree
in the complete remainder, including its zeroth-order coefficient term.

The domain `E` consists of physical and normalized covector variables. The
producer must identify the displayed rescaled primitives with its actual
primitives on each radial slice. These are homogeneous high-frequency estimates;
no smooth extension through the zero covector is asserted.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral
variable {E R ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℂ R] [Fintype ι]
local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- The fixed physical and angle masks preserve the radial amplitude degree
in `app:ch_regular_base:eq:actual-global-cutoff`. They may depend on every
normalized chart variable. -/
theorem maskedTransportAmplitude_rescale (χt χs χg t : ℂ) (b : R) :
    maskedTransportAmplitude χt χs χg (t • b) =
      t • maskedTransportAmplitude χt χs χg b := by
  simp only [maskedTransportAmplitude]
  rw [smul_comm χg t, smul_comm χs t, smul_comm χt t]

/-- Radial multiplication commutes with the actual spatial derivative in the
complete expression `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem completeTransportRemainder_rescale (A : ι → E → R) (B b : E → R)
    (v : ι → E) (t : ℂ) (x : E) :
    transportRemainder (fun j ↦ A j x)
      (fun j ↦ fderiv ℝ (fun y ↦ t • b y) x (v j)) (B x) (t • b x) =
      t • transportRemainder (fun j ↦ A j x)
        (fun j ↦ fderiv ℝ b x (v j)) (B x) (b x) := by
  have hd (j : ι) : fderiv ℝ (fun y ↦ t • b y) x (v j) =
      t • fderiv ℝ b x (v j) := by
    change fderiv ℝ (t • b) x (v j) = _
    rw [fderiv_const_smul_field]
    rfl
  simp_rw [hd]
  exact transportRemainder_rescale _ _ _ _ _

/-- All normalized mixed joint jets of the displayed correction have the
same radial weight. This supplies the order-minus-one weight in
`app:ch_regular_base:eq:direct-graph-amplitudes`; its unit-radius bound is
`norm_iteratedFDeriv_correctionAmplitude_le`. -/
theorem norm_iteratedFDeriv_rescaled_correctionAmplitude
    (n : ℕ) {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ n (c1 j)) (hdU : ∀ j, ContDiff ℝ n (dU j))
    (hc2 : ∀ j l, ContDiff ℝ n (c2 j l))
    (hS : ∀ j l, ContDiff ℝ n (S j l)) (hU : ContDiff ℝ n U)
    {r : ℝ} (hr : 0 < r) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ correctionAmplitude
      (fun j ↦ (r : ℂ)⁻¹ • c1 j y) (fun j ↦ dU j y)
      (fun j l ↦ ((r : ℂ)⁻¹ ^ 2) • c2 j l y)
      (fun j l ↦ (r : ℂ) * S j l y) (U y)) x‖ =
      r⁻¹ * ‖iteratedFDeriv ℝ n (fun y ↦ correctionAmplitude
        (fun j ↦ c1 j y) (fun j ↦ dU j y)
        (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)) x‖ := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simp_rw [correctionAmplitude_rescale _ _ _ _ _ hr']
  rw [iteratedFDeriv_const_smul_apply'
    (contDiff_correctionAmplitude hc1 hdU hc2 hS hU).contDiffAt, norm_smul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- Joint regularity needed when applying normalized weights to the complete
remainder of `app:ch_regular_base:eq:direct-graph-identity`. The extra derivative
is on the actual correction, not an independently supplied remainder jet. -/
theorem contDiff_completeTransportRemainder (n : ℕ)
    {A : ι → E → R} {B b : E → R} (v : ι → E)
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hb : ContDiff ℝ (n + 1) b) :
    ContDiff ℝ n (fun x ↦ transportRemainder (fun j ↦ A j x)
      (fun j ↦ fderiv ℝ b x (v j)) (B x) (b x)) := by
  have hdb (j : ι) : ContDiff ℝ n (fun x ↦ fderiv ℝ b x (v j)) :=
    (hb.fderiv_right (m := n) (by simp)).clm_apply contDiff_const
  exact ((ContDiff.sum fun j _ ↦ (hA j).mul (hdb j)).add
    (hB.mul (hb.of_le (by exact_mod_cast Nat.le_succ n)))).const_smul _

/-- Every normalized joint jet of the complete remainder retains the radial
weight of the correction (`app:ch_regular_base:eq:direct-graph-identity`).
Combine with `correctionAmplitude_rescale` to use the literal correction and
with `norm_iteratedFDeriv_completeTransportRemainder_le` for its primitive bound. -/
theorem norm_iteratedFDeriv_rescaled_completeTransportRemainder (n : ℕ)
    {A : ι → E → R} {B b : E → R} (v : ι → E)
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hb : ContDiff ℝ (n + 1) b) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
      (fun j ↦ fderiv ℝ (fun z ↦ (r : ℂ)⁻¹ • b z) y (v j))
      (B y) ((r : ℂ)⁻¹ • b y)) x‖ =
      r⁻¹ * ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
        (fun j ↦ fderiv ℝ b y (v j)) (B y) (b y)) x‖ := by
  simp_rw [completeTransportRemainder_rescale]
  rw [iteratedFDeriv_const_smul_apply'
    (contDiff_completeTransportRemainder n v hA hB hb).contDiffAt, norm_smul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- Fixed source, target and angle masks retain the same normalized radial
weight, including all their joint derivatives
(`app:ch_regular_base:eq:actual-global-cutoff`). Literal adjoint and conjugate
amplitudes have identical norms by the theorems in `Masks`. -/
theorem norm_iteratedFDeriv_rescaled_maskedTransportAmplitude (n : ℕ)
    {χt χs χg : E → ℂ} {b : E → R}
    (ht : ContDiff ℝ n χt) (hs : ContDiff ℝ n χs)
    (hg : ContDiff ℝ n χg) (hb : ContDiff ℝ n b) (t : ℂ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude
      (χt y) (χs y) (χg y) (t • b y)) x‖ =
      ‖t‖ * ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude
        (χt y) (χs y) (χg y) (b y)) x‖ := by
  simp_rw [maskedTransportAmplitude_rescale]
  have hmask : ContDiff ℝ n (fun y ↦ maskedTransportAmplitude
      (χt y) (χs y) (χg y) (b y)) := ht.smul (hs.smul (hg.smul hb))
  rw [iteratedFDeriv_const_smul_apply' hmask.contDiffAt, norm_smul]

end JanetCartan.FourierIntegral
