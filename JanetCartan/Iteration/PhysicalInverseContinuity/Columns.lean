module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Retained
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel

/-!
# Column membership for the literal retained raw adjoint integral

The actual original normal and reduced-covector regularity, common retained
buffers, and original masks imply that every fixed column belongs to torus L².
This discharges the measurability/integrability input of the compact-frequency
adjoint comparison without an extra analytic kernel hypothesis.
Consumer: `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInverseContinuity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol

/-- Each actual original carrier column has the required torus L² membership,
from its primitive retained geometry. Its auxiliary column bound is used only
for measurability/integrability and need not be uniform over histories. -/
theorem memLp_retained_carrierKernel_column
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hRc : 0 < Rc) (hτ : 0 < τ) (hKΩ : K ⊆ Ω) (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (him : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (D : CoefficientNormCharts n)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.region K)
    (hSflow : MapsTo (densityCoordinates T) D.field.region
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    (hSphase : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot : MapsTo (densityFootpoint T c.inverse) D.field.region
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hang : ContDiff ℝ ∞ (Function.uncurry angular)) {Z : Set CarrierParameter} (hZ : IsCompact Z)
    (hzero : ∀ z ∉ Z, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical hr 1) ×ˢ Z ⊆ D.field.carrier)
    (u : CarrierVariable n) :
    MemLp (fun x ↦ carrierKernel (data T c.Q F row col c.forward c.inverse initial hr hcell
      angular FixedCutoffs.highFrequency) x u) 2 (volume : Measure (Torus n)) := by
  obtain ⟨hν, hred⟩ := retained_originalScalar_coefficients_contDiffOn c hP hRc hτ hKΩ hKU
    hF him hrank hSK hSflow hR initial hi hipos hfoot
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (c.Q.1 p.1) (T.carrierGradient c.Q p.1 (parameter p.2))
  let Lq := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  have hq : ContDiffOn ℝ ∞ q D.field.region := Lq.contDiff.comp_contDiffOn hred
  have hmeas := stronglyMeasurable_carrierKernel_of_local_primitives T c.Q F row col
    c.forward c.inverse initial hr hcell angular D.field.isOpen_region
    ((transportPosition_smooth T c.Q hP).mono hSphase).continuousOn
    hν.continuousOn hq.continuousOn hang.continuous hzero (hsupport.trans D.field.ball_subset)
  let Bν := cNorm D.field.carrier 1 (c.normal initial)
  let Bq := cNorm D.field.carrier 1 q
  let Cmask := cNorm (Z ×ˢ closedBall (0 : Euclidean (n - 1)) 1) 0 (Function.uncurry angular) *
    Bν ^ 2 * Bq
  have hBq : 0 ≤ Bq := cNorm_nonneg ..
  have hC : 0 ≤ Cmask := mul_nonneg (mul_nonneg (cNorm_nonneg ..) (sq_nonneg Bν)) hBq
  have hb := norm_carrierAmplitude_le_of_primitive_norms T c.Q F row col c.forward c.inverse
    initial hr hcell angular D.field hZ hzero hang hsupport hν hq
    (cNorm_nonneg D.field.carrier 1 (c.normal initial)) hBq le_rfl le_rfl
  apply MemLp.of_bound hmeas.of_uncurry_right.aestronglyMeasurable (Cmask * Real.sqrt ‖u.2‖)
  apply Filter.Eventually.of_forall
  intro x
  let d := data T c.Q F row col c.forward c.inverse initial hr hcell angular FixedCutoffs.highFrequency
  change ‖carrierKernel d x u‖ ≤ _
  by_cases hx : x ∈ d.outputChart
  · simpa only [carrierKernel, Set.indicator_of_mem hx, norm_smul, Complex.norm_exp_I_mul_ofReal,
      euclideanComplexInclusion_norm, one_mul] using (hb x u)
  · rw [carrierKernel_eq_zero_outside d hx, norm_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)

end JanetCartan.PhysicalInverseContinuity
