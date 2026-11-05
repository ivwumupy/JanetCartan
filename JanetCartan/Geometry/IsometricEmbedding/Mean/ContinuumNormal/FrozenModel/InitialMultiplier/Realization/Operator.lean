module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.Representative
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Complex multiplication on the original carrier input

The bounded input multiplier for `app:ch_background:eq:bg-T`, on the literal
Lebesgue carrier measure. Its real restriction is the existing raw cutoff
multiplier. The consumer is the realization of the nonconstant frozen carrier
from the same unit-initial operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff ENNReal
namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
open ContinuumRow

variable {n : ℕ}

/-- Complex-linear multiplication by a real L∞ coefficient, retaining both
quadratures (`app:ch_background:eq:bg-realification`). -/
def complexCarrierMultiplier (m : Lp ℝ ∞ (carrierMeasure n)) :
    CarrierL2 n →L[ℂ] CarrierL2 n :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL (carrierMeasure n) ∞ 2 2
    (Complex.ofRealCLM.compLpL ∞ (carrierMeasure n) m)

/-- Literal almost-everywhere action (`app:ch_background:eq:bg-T`). -/
theorem complexCarrierMultiplier_coeFn (m : Lp ℝ ∞ (carrierMeasure n)) (f : CarrierL2 n) :
    complexCarrierMultiplier m f =ᵐ[carrierMeasure n] fun u ↦ m u • f u := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
    (Complex.ofRealCLM.compLpL ∞ (carrierMeasure n) m) f,
    Complex.ofRealCLM.coeFn_compLpL m] with u hu hm
  change complexCarrierMultiplier m f u = _ at hu
  rw [hu, hm]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (m u) (f u) |>.symm

/-- This specialization agrees with the existing real carrier multiplier;
no second real input operator is introduced (`app:ch_background:defn:bg-mixed`). -/
theorem complexCarrierMultiplier_restrictScalars (m : Lp ℝ ∞ (carrierMeasure n)) :
    (complexCarrierMultiplier m).restrictScalars ℝ = RawCutoffBounds.carrierMultiplier m := by
  ext1 f
  exact Lp.ext ((complexCarrierMultiplier_coeFn m f).trans
    (RawCutoffBounds.carrierMultiplier_coeFn m f).symm)

/-- Real multiplication is self-adjoint also for the complex Hilbert inner
product (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem complexCarrierMultiplier_adjoint (m : Lp ℝ ∞ (carrierMeasure n)) :
    (complexCarrierMultiplier m).adjoint = complexCarrierMultiplier m := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexCarrierMultiplier_coeFn m f,
    complexCarrierMultiplier_coeFn m g] with u hf hg
  rw [hf, hg, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal]

/-- A bounded continuous label representative gives an actual coefficient on
`dz dη`, despite being constant in the unbounded frequency variable
(`app:ch_background:eq:bg-T`). -/
def labelCoefficient (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) : Lp ℝ ∞ (carrierMeasure n) :=
  (memLp_top_of_bound (hb.comp continuous_fst).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun u ↦ hbound u.1)).toLp (fun u ↦ b u.1)

/-- The coefficient retains its original label action (`app:ch_background:eq:bg-T`). -/
theorem labelCoefficient_coeFn (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) :
    labelCoefficient (n := n) b hb hbound =ᵐ[carrierMeasure n] fun u ↦ b u.1 :=
  MemLp.coeFn_toLp _

/-- The bounded complex input multiplier used in the frozen construction
(`app:ch_background:prop:bg-frame`, Step 1). -/
def labelMultiplier (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) : CarrierL2 n →L[ℂ] CarrierL2 n :=
  complexCarrierMultiplier (labelCoefficient b hb hbound)

/-- Literal label action on the entire carrier L² space (`app:ch_background:eq:bg-T`). -/
theorem labelMultiplier_coeFn (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (f : CarrierL2 n) :
    labelMultiplier b hb hbound f =ᵐ[carrierMeasure n] fun u ↦ b u.1 • f u := by
  filter_upwards [complexCarrierMultiplier_coeFn (labelCoefficient b hb hbound) f,
    labelCoefficient_coeFn (n := n) b hb hbound] with u hu hb
  simpa only [labelMultiplier, hb] using hu

/-- The bound uses only the fixed local C⁰ budget of the representative,
not any derivatives (`app:ch_background:prop:bg-frame`). -/
theorem labelMultiplier_norm_le (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z, ‖b z‖ ≤ B) :
    ‖labelMultiplier (n := n) b hb hbound‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [labelMultiplier_coeFn b hb hbound f] with u hu
  rw [hu, norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound u.1) (norm_nonneg _)

/-- The constructed label multiplier is self-adjoint (`bg-full-complex-amplitude`). -/
theorem labelMultiplier_adjoint (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) :
    (labelMultiplier (n := n) b hb hbound).adjoint = labelMultiplier b hb hbound :=
  complexCarrierMultiplier_adjoint _

/-- The operator agrees with multiplication on the ORIGINAL dense test
space (`app:ch_background:eq:bg-T`). -/
theorem labelMultiplier_initialTest (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (f : carrierInitialTestSpace n) :
    labelMultiplier b hb.continuous hbound (carrierInitialTestToLp f) =
      carrierInitialTestToLp (multiplyInitialTest b hb f) := by
  apply Lp.ext
  filter_upwards [labelMultiplier_coeFn b hb.continuous hbound (carrierInitialTestToLp f),
    (carrierInitialTest_memLp f).coeFn_toLp,
    (carrierInitialTest_memLp (multiplyInitialTest b hb f)).coeFn_toLp] with u hu hf hg
  change carrierInitialTestToLp f u = f.val u at hf
  change carrierInitialTestToLp (multiplyInitialTest b hb f) u = _ at hg
  rw [hu, hf, hg]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (b u.1) (f.val u)

/-- Only a lower bound on the support of the input is needed. In the actual
application the input is the unit adjoint, whose support follows from the
original angular mask (`app:ch_background:prop:bg-frame`). -/
theorem labelMultiplier_norm_sq_ge_of_supported
    (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) {Z : Set CarrierParameter}
    (hlower : ∀ z ∈ Z, (1 / 4 : ℝ) ≤ b z) (f : CarrierL2 n)
    (hsupport : ∀ᵐ u ∂carrierMeasure n, u.1 ∉ Z → f u = 0) :
    (1 / 16 : ℝ) * ‖f‖ ^ 2 ≤ ‖labelMultiplier b hb hbound f‖ ^ 2 := by
  have hnorm : ‖f‖ ≤ 4 * ‖labelMultiplier b hb hbound f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [labelMultiplier_coeFn b hb hbound f, hsupport] with u hu hs
    rw [hu, norm_smul]
    by_cases hz : u.1 ∈ Z
    · have h := hlower u.1 hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b u.1)]
      nlinarith [norm_nonneg (f u)]
    · rw [hs hz, norm_zero, mul_zero, mul_zero]
  have hsquare := pow_le_pow_left₀ (norm_nonneg f) hnorm 2
  nlinarith

/-- The bounded complex normal is exactly `V M² V*`, with the SAME unit
operator `V` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem labelMultiplier_complex_normal (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    let M := labelMultiplier (n := n) b hb hbound
    (V ∘L M) ∘L (V ∘L M).adjoint = V ∘L (M ∘L M) ∘L V.adjoint := by
  dsimp only
  rw [ContinuousLinearMap.adjoint_comp, labelMultiplier_adjoint]
  ext1 f
  rfl

/-- The real normal retains the established factor four and both input
quadratures (`app:ch_background:eq:bg-realification`). -/
theorem labelMultiplier_real_normal (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    let M := labelMultiplier (n := n) b hb hbound
    realQuadratureChannel (V ∘L M) ∘L (realQuadratureChannel (V ∘L M)).adjoint =
      (4 : ℝ) • realOutputCompression (V ∘L (M ∘L M) ∘L V.adjoint) := by
  dsimp only
  rw [realQuadratureChannel_normal_eq_four_realPart, labelMultiplier_complex_normal]

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
