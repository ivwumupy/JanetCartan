module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Noncomparable.OriginalPhase

/-!
# Uniform covector comparison on the selected elapsed carriers

One pair of positive constants works for the fixed finite family before
the coefficient field, slow scale, accuracy, or shell scale is chosen.
The supported phase is used only through its original conic germ on the
same `Ua` supplied by `exists_selected_elapsed_physical_carriers`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open Characteristic.UniformEvolution Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.ResidualCoordinates EvolutionLocalization FourierIntegral
open FiniteMasks FiniteMasks.ActualFamily
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

/-- The original order-three coefficient profile and the retained phase
estimates give positive, uniform full covector constants. The same arbitrary
`Vphase` and `Ua` from `exists_selected_elapsed_physical_carriers` are kept;
no new chart, cutoff, or carrier is selected. All analytic chart hypotheses
are literal outputs of `exists_finite_direct_operator_bounds`. The auxiliary
germ premise is produced by `jc-selected-elapsed-quantitative-phase` and must
be instantiated by `jc-selected-elapsed-carrier-geometry`.

Consumers: `hSphase`, `hg`, and `hcomp` of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_covector_comparison
    (f : ActualMaskFamily Ω x RQ A₀ K M) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ Q : E → Fin (d+1) → MetricTensor (d+1),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
      ∀ p : f.centers,
      let c := f.chart p
      let e := coordinateSplit c.index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      let ε := retainedRadius c.targetRadius c.bufferRadius
      let Δ := 3*c.maskRadius/4
      c.bufferRadius ≤ c.targetRadius → c.maskRadius ≤ c.bufferRadius/4 →
      ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
      closedBall (z.1, z) c.targetRadius ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      (∀ q ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C q - 1‖ ≤ 1/2) →
      (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
        c.phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) →
      ∀ (Ψ : TwoTimePhase d) (Vphase : Set (E × E)) (Ua : Set (SymbolBudgets.TwoTimePoint d)),
      Vphase ⊆ elapsedPhysicalBox z ε ×ˢ (spatialPart ⁻¹' angularCone c.radialSection z.2.2 ε) →
      Ua ⊆ bufferedBase z ε ×ˢ angularCone c.radialSection z.2.2 ε →
      (∀ r ∈ Icc 0 Δ, ∀ w ∈ Vphase, elapsedPhasePoint r w ∈ Ua) →
      (∀ w ∈ Ua, jointPhase Ψ =ᶠ[𝓝 w] jointPhase (curriedPhase c.radialSection C)) →
      ∃ g : ℝ → E → E → E,
        (∀ r ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) Vphase) ∧
        (∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase →
          fderiv ℝ (fun v ↦ elapsedPhase Ψ r v ξ) u = innerSL ℝ (g r u ξ)) ∧
        (∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase →
          c₀*‖ξ‖ ≤ ‖g r u ξ‖ ∧ ‖g r u ξ‖ ≤ C₀*‖ξ‖) := by
  classical
  let B : f.centers → ℝ := fun p ↦
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
    retainedPhaseCost c.radialSection z (2*retainedRadius c.targetRadius c.bufferRadius)
      (1/2) 2 c.phaseCost 2 * (1+A 3)
  have hB p : 0 ≤ B p := mul_nonneg
    (retainedPhaseCost_pos _ _ _ _ _ (f.chart p).phaseCost_pos _).le (by linarith [hA 3])
  let Bsum := ∑ p, B p
  have hBsum : 0 ≤ Bsum := Finset.sum_nonneg (fun p _ ↦ hB p)
  refine ⟨(3+2*Bsum)⁻¹, 3+2*Bsum, by positivity, by positivity, ?_⟩
  intro Rstar hRstar L _hL Q hQ p c e z ε Δ hρb hsrcρ h Φ C hbuffer hs hdiff hnear hphase
    Ψ Vphase Ua hV hUa hmap heq
  have hε : 0 < ε := (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).1
  have hεb : 4*ε ≤ c.targetRadius := four_mul_retainedRadius_le _ _
  have hΔε : Δ < ε := (UniformAmplitudes.retained_source_slab_bounds
    c.maskRadius_pos hρb hsrcρ).2
  have hQ3 : cNorm (closedBall x RQ) 3 Q ≤ A 3 := by
    simpa only [Nat.sub_eq_zero_of_le (by omega : 3 ≤ Rstar), pow_zero, mul_one] using hQ 3
  have hreg := selected_supported_elapsed_phase_regular c.radialSection hε
    (show 2*ε ≤ c.targetRadius by linarith) hbuffer hs Ψ Vphase Ua hUa hmap heq
  refine ⟨fun r ↦ phaseCovectorMap (curriedPhase c.radialSection C) r,
    fun r hr ↦ (hreg r hr).1, fun r hr ↦ (hreg r hr).2, ?_⟩
  intro r hr u ξ hu
  have hcomparison := selected_original_phaseCovectorMap_comparison c.radialSection
    hε hεb hbuffer hs hdiff hnear (closedBall x RQ) Q c.phaseCost (c.phaseCost_pos 2).le
    hphase (hA 3) hQ3 (show r ∈ Icc 0 ε from ⟨hr.1, hr.2.trans hΔε.le⟩)
    (hV hu).1 (hV hu).2
  change (3+2*B p)⁻¹*‖ξ‖ ≤ ‖phaseCovectorMap (curriedPhase c.radialSection C) r u ξ‖ ∧
    ‖phaseCovectorMap (curriedPhase c.radialSection C) r u ξ‖ ≤ (3+2*B p)*‖ξ‖ at hcomparison
  have hp : B p ≤ Bsum := Finset.single_le_sum (fun q _ ↦ hB q) (Finset.mem_univ p)
  have hi : (3+2*Bsum)⁻¹ ≤ (3+2*B p)⁻¹ :=
    inv_anti₀ (by linarith [hB p]) (by linarith)
  exact ⟨(mul_le_mul_of_nonneg_right hi (norm_nonneg ξ)).trans hcomparison.1,
    hcomparison.2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg ξ))⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
