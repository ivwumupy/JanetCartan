module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.Realization.Operator
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Realization

/-!
# Identify multiplication with the literal normalized carrier

The phase, physical chart, angular mask, high cutoff, and carrier measure are
unchanged. These lemmas consume the test and adjoint outputs for the SAME unit
operator from `FrozenIncidencePatchData.exists_common_measurement_realization`.
The local-input endpoint constructs their representative in `Realization.lean`.
Sources: `app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-realification`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
open ActualCarriers FrozenMenu CurrentFullPhase
open ContinuumRow CanonicalCarrier CanonicalConic

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hcell : 4 * ρ < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

local notation "ei" => normalizedCarrierData T Q F row col Φ Y initial hρ hcell angular high 0
local notation "e₁" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hρ hcell angular high 0

/-- Multiplication on the original dense initial tests gives exactly the
nonconstant normalized carrier, without changing masks (`app:ch_background:eq:bg-T`). -/
theorem labelMultiplier_test_action
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (heq : EqOn b (labelWeight Y initial) Z)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVtest : ∀ f : carrierInitialTestSpace n,
      V (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e₁ f.val)
    (f : carrierInitialTestSpace n) :
    (V ∘L labelMultiplier b hb.continuous hbound) (carrierInitialTestToLp f) =ᵐ[volume]
      carrierTestIntegral ei f.val := by
  change V (labelMultiplier b hb.continuous hbound (carrierInitialTestToLp f)) =ᵐ[volume] _
  rw [labelMultiplier_initialTest b hb hbound f]
  filter_upwards [hVtest (multiplyInitialTest b hb f)] with x hx
  rw [hx, carrierTestIntegral_initial_of_eqOn T Q F row col Φ Y initial hρ hcell
    angular high hang b heq]
  rfl

/-- The adjoint of `V ∘ M` is the literal adjoint for the nonconstant
normalized data (`app:ch_background:eq:bg-realification`). The only adjoint
input is the unit constructor's already proved action. -/
theorem labelMultiplier_adjoint_action
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (heq : EqOn b (labelWeight Y initial) Z)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w)
    (w : ComplexOutputL2 n) :
    (V ∘L labelMultiplier b hb hbound).adjoint w =ᵐ[carrierMeasure n]
      carrierAdjointIntegral ei w := by
  rw [ContinuousLinearMap.adjoint_comp, labelMultiplier_adjoint]
  filter_upwards [labelMultiplier_coeFn b hb hbound (V.adjoint w), hVadj w] with u hu hv
  change labelMultiplier b hb hbound (V.adjoint w) u = _
  rw [hu, hv, carrierAdjointIntegral_initial_of_eqOn T Q F row col Φ Y initial
    hρ hcell angular high hang b heq]

/-- Membership of the actual nonconstant adjoint follows from its identified
bounded Hilbert realization (`app:ch_background:eq:bg-realification`). -/
theorem labelMultiplier_adjoint_memLp
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (heq : EqOn b (labelWeight Y initial) Z)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w)
    (w : ComplexOutputL2 n) :
    MemLp (carrierAdjointIntegral ei w) 2 (carrierMeasure n) :=
  (memLp_congr_ae (labelMultiplier_adjoint_action T Q F row col Φ Y initial hρ hcell
    angular high hang b hb hbound heq V hVadj w)).mp (Lp.memLp _)

/-- The real adjoint comparison is on the SAME unit realization and all real
outputs. The lower bound is required only at retained footpoints, since the
unit adjoint vanishes on the complement by the original angular mask.
No global positivity of the cutoff representative is used
(`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-realification`). -/
theorem labelMultiplier_real_adjoint_comparison
    {Z : Set CarrierParameter} (hang : ∀ z ∉ Z, ∀ θ, angular z θ = 0)
    (b : CarrierParameter → ℝ) (hb : Continuous b)
    {B : ℝ} (hbound : ∀ z, ‖b z‖ ≤ B) (heq : EqOn b (labelWeight Y initial) Z)
    (hlower : ∀ z ∈ Z, (1 / 2 : ℝ) ≤ initial (Y (0, (0, parameter z))))
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w)
    (w : OutputL2 n) :
    (1 / 16 : ℝ) * ‖(realQuadratureChannel V).adjoint w‖ ^ 2 ≤
      ‖(realQuadratureChannel (V ∘L labelMultiplier b hb hbound)).adjoint w‖ ^ 2 := by
  have hlo : ∀ z ∈ Z, (1 / 4 : ℝ) ≤ b z := by
    intro z hz
    rw [heq hz]
    dsimp only [labelWeight]
    nlinarith [hlower z hz]
  have h := labelMultiplier_norm_sq_ge_of_supported b hb hbound hlo
    (V.adjoint (l2ComplexInclusion volume w))
    (unit_adjoint_supported T Q F row col Φ Y hρ hcell angular high hang V hVadj
      (l2ComplexInclusion volume w))
  simp only [realQuadratureChannel_adjoint_apply, ContinuousLinearMap.adjoint_comp,
    labelMultiplier_adjoint, ContinuousLinearMap.comp_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
