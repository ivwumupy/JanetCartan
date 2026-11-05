module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.Realization.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.Basic

/-!
# Realize nonconstant frozen initial data on the same carrier

Construct the bounded complex input multiplier from LOCAL scalar and flow data,
and compose it with the supplied unit-initial realization. This gives the literal
normalized carrier with unchanged phase, chart, angular mask and high cutoff,
its unique bounded extension, full output support, literal adjoint and a `1/16`
comparison on all real outputs. The complex normal is `V M² V*`; realification
retains the existing factor four.

The primitive producer is `ActualAmplitude.exists_projected_local_positive_amplitude`:
its retained inverse flow supplies smoothness and range. Containment of the
entire label buffer in its flow domain is the explicit `hseed` obligation; the
range into the scalar domain is `hYrange`. Neither is replaced by a global
smoothness or positivity assumption. The SAME `V` and its unit test/adjoint
identities come from `FrozenIncidencePatchData.exists_common_measurement_realization`
or `FrozenCoercivity.exists_finite_realized_frozen_row_gap`.

Consumer: the parent task's finite-family assembly for
`app:ch_background:prop:bg-frame`. Instantiating these local geometric inputs
and transferring the original unit-row gap remain with that parent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {a δ r ρ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (har : 6 * a ≤ 3 * r)
    (hρ : 0 < ρ) (hcell : 4 * ρ < 1 / 2) (high : ℝ → ℝ)

local notation "angular₀" => angularMask z₀ θ₀ ha hδ
local notation "ei" => normalizedCarrierData T Q F row col Φ Y initial hρ hcell angular₀ high 0
local notation "e₁" => normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) hρ hcell angular₀ high 0

include har

/-- Construct the literal nonconstant frozen carrier from a local scalar C⁰
budget and the actual retained inverse flow (`new:lem:scaling`,
`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-T`).
The measurement radius `ρ`, label radius `a`, and angular width `δ` are distinct.
The only lower bound is at the original retained footpoints. In particular the
constructed coefficient may vanish outside its compact cutoff. -/
theorem exists_initial_multiplier_realization
    (B : ℝ) (hB : 0 ≤ B)
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hi : ContDiffOn ℝ ∞ initial D) (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D) (hbound : ∀ q ∈ D, ‖initial q‖ ≤ B)
    (hlower : ∀ z ∈ carrierSupport z₀ (r := a),
      (1 / 2 : ℝ) ≤ initial (Y (0, (0, parameter z))))
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVtest : ∀ f : carrierInitialTestSpace n,
      V (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e₁ f.val)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w) :
    ∃ (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b)
      (hbb : ∀ z, ‖b z‖ ≤ B ^ 2),
      HasCompactSupport b ∧ (∀ z, 0 ≤ b z) ∧
      EqOn b (labelWeight Y initial) (carrierSupport z₀ (r := a)) ∧
      let M := labelMultiplier (n := n) b hb.continuous hbb
      let Vi := V ∘L M
      ‖M‖ ≤ B ^ 2 ∧ M.adjoint = M ∧
      ‖Vi‖ ≤ ‖V‖ * B ^ 2 ∧
      (∀ f : carrierInitialTestSpace n,
        Vi (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (ei).outputChart → Vi f x = 0) ∧
      (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          W (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val) → W = Vi) ∧
      (∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral ei w) 2 (carrierMeasure n) ∧
        Vi.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral ei w) ∧
      (∀ w : OutputL2 n, (1 / 16 : ℝ) * ‖(realQuadratureChannel V).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel Vi).adjoint w‖ ^ 2) ∧
      Vi ∘L Vi.adjoint = V ∘L (M ∘L M) ∘L V.adjoint ∧
      realQuadratureChannel Vi ∘L (realQuadratureChannel Vi).adjoint =
        (4 : ℝ) • realOutputCompression (V ∘L (M ∘L M) ∘L V.adjoint) := by
  obtain ⟨b, hb, hc, hn, hbb, heq⟩ := exists_bounded_smooth_labelWeight z₀ ha har
    B hB Y initial hi hY hseed hYrange hbound
  have hang : ∀ z ∉ carrierSupport z₀ (r := a), ∀ θ, angular₀ z θ = 0 :=
    fun _ hz θ ↦ angularMask_zero_outside z₀ θ₀ ha hδ hz θ
  let M := labelMultiplier (n := n) b hb.continuous hbb
  let Vi := V ∘L M
  have hM : ‖M‖ ≤ B ^ 2 := labelMultiplier_norm_le b hb.continuous (sq_nonneg B) hbb
  have ht : ∀ f : carrierInitialTestSpace n,
      Vi (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val :=
    labelMultiplier_test_action T Q F row col Φ Y initial hρ hcell angular₀ high
      hang b hb hbb heq V hVtest
  refine ⟨b, hb, hbb, hc, hn, heq, hM, labelMultiplier_adjoint b hb.continuous hbb,
    (ContinuousLinearMap.opNorm_comp_le V M).trans
      (mul_le_mul_of_nonneg_left hM (norm_nonneg V)), ht,
    carrierRealization_eq_zero_outside ei Vi ht, ?_, ?_, ?_,
    labelMultiplier_complex_normal b hb.continuous hbb V,
    labelMultiplier_real_normal b hb.continuous hbb V⟩
  · exact fun W hW ↦ carrierExtensions_eq_of_initialTests ei Vi W ht hW
  · intro w
    exact ⟨labelMultiplier_adjoint_memLp T Q F row col Φ Y initial hρ hcell angular₀ high
      hang b hb.continuous hbb heq V hVadj w,
      labelMultiplier_adjoint_action T Q F row col Φ Y initial hρ hcell angular₀ high
        hang b hb.continuous hbb heq V hVadj w⟩
  · exact labelMultiplier_real_adjoint_comparison T Q F row col Φ Y initial hρ hcell
      angular₀ high hang b hb.continuous hbb heq hlower V hVadj

omit initial in
/-- The full original density interval gives a fixed multiplier bound `4`
and the same `1/16` adjoint comparison, with no higher-derivative smallness
assumed. This instantiates the local representative and bounded realization
for `sqrt (1+v)` (`app:ch_background:prop:bg-frame`). The finite-family unit-gap
instantiation remains the parent's obligation. -/
theorem exists_sqrt_initial_multiplier_realization
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    {Dflow : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hv : ContDiffOn ℝ ∞ v D)
    (hden : ∀ q ∈ D, (1 / 2 : ℝ) ≤ 1 + v q ∧ 1 + v q ≤ 3 / 2)
    (hY : ContDiffOn ℝ ∞ Y Dflow)
    (hseed : MapsTo (fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z)))
      (ball (z₀ 0) r ×ˢ ball (spectatorCenter z₀) (6 * a)) Dflow)
    (hYrange : MapsTo Y Dflow D)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVtest : ∀ f : carrierInitialTestSpace n,
      V (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e₁ f.val)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e₁ w) :
    let initial := fun q ↦ Real.sqrt (1 + v q)
    let e := normalizedCarrierData T Q F row col Φ Y initial hρ hcell angular₀ high 0
    ∃ (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b)
      (hbb : ∀ z, ‖b z‖ ≤ 4),
      HasCompactSupport b ∧ (∀ z, 0 ≤ b z) ∧
      EqOn b (labelWeight Y initial) (carrierSupport z₀ (r := a)) ∧
      let M := labelMultiplier (n := n) b hb.continuous hbb
      let Vi := V ∘L M
      ‖M‖ ≤ 4 ∧ M.adjoint = M ∧
      ‖Vi‖ ≤ ‖V‖ * 4 ∧
      (∀ f : carrierInitialTestSpace n,
        Vi (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vi f x = 0) ∧
      (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          W (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → W = Vi) ∧
      (∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
        Vi.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
      (∀ w : OutputL2 n, (1 / 16 : ℝ) * ‖(realQuadratureChannel V).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel Vi).adjoint w‖ ^ 2) ∧
      Vi ∘L Vi.adjoint = V ∘L (M ∘L M) ∘L V.adjoint ∧
      realQuadratureChannel Vi ∘L (realQuadratureChannel Vi).adjoint =
        (4 : ℝ) • realOutputCompression (V ∘L (M ∘L M) ∘L V.adjoint) := by
  obtain ⟨hi, hlo, hup⟩ := sqrt_initial_properties_of_density_range hv hden
  have hlower : ∀ z ∈ carrierSupport z₀ (r := a),
      (1 / 2 : ℝ) ≤ Real.sqrt (1 + v (Y (0, (0, parameter z)))) := by
    intro z hz
    apply hlo _ (hYrange (hseed ?_))
    exact ⟨closedBall_subset_ball (by linarith) hz.1,
      closedBall_subset_ball (by linarith) hz.2⟩
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
    exists_initial_multiplier_realization T Q F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
      z₀ θ₀ ha hδ har hρ hcell high 2 (by norm_num) hi hY hseed hYrange hup hlower
      V hVtest hVadj

end JanetCartan.ContinuumNormal.FrozenModel.InitialMultiplier
