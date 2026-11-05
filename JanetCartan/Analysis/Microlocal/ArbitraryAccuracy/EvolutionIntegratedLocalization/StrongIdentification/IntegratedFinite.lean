module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.LocalizedFinite
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.FiniteContinuity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.IntegralRepresentatives
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.StrongIntegral

/-! # Bounded L² realization of the finite elapsed shells

Elapsed integration commutes with both fixed localizers and the independent
Fourier output cutoff. The finite physical integral is its representative;
all integrability comes from the primitive LOW bound.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The independently regularized bounded elapsed operator has exactly the
published physical shell kernel as its test representative. Both localizers,
the regularized identity, and the endpoints `0, Δ` are retained. The sole
operator bound is the primitive LOW bound, not the desired integrated
Sobolev estimate (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem bounded_elapsed_outputMultiplier_realization
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo) (hos : HasCompactSupport mo)
    (Mi Mo : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (hS : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hA : Continuous (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hSs : ∀ r ∈ Icc 0 Δ, ∀ x ξ, ξ ≠ 0 →
      ContDiffAt ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (x, ξ))
    (hAs : ∀ r ∈ Icc 0 Δ, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (χA : E → ℝ) (j : ℕ) (hχ : ContDiff ℝ ∞ χA) (hχ0 : (0 : E) ∉ tsupport χA)
    (c : ∀ r, RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) χA (physicalCutoff j))
    (hcommon : ∀ r, (c r).jointCarrier = (c 0).jointCarrier)
    (hinput : ∀ r, (c r).inputBase = (c 0).inputBase)
    (T : ℝ → H →L[ℂ] H)
    (hreal : ∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
      T r (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
          (fun x y ξ ↦ (χA ξ : ℂ) • orientedElapsedAmplitude backward b χout χsource β r x y ξ)
          (fun y ↦ (u.val y).ofLp)) x))
    (hm : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    {C : ℝ} (hb : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C) (u : graphTestSpace (d + 1) q) :
    (1 - Mo) (multiplier j (∫ r in Icc 0 Δ, T r (Mi (graphTestToLp u)))) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (∫ y,
        (elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
          χA (physicalCutoff j) x y).mulVec (u.val y).ofLp) := by
  let L : H →L[ℂ] H := (1 - Mo).comp (multiplier j)
  have hint := integrableOn_apply_of_uniform_bound hm hb (Mi (graphTestToLp u))
  have hc := continuous_finiteJointKernel_test backward (elapsedPhase Ψ)
    (orientedElapsedAmplitude backward b χout χsource β) _ _ χA (physicalCutoff j)
    hS hA (hi.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
    (ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))) hχ.continuous
    (physicalCutoff_contDiff j).continuous c hcommon hinput (fun y ↦ (u.val y).ofLp)
    ((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous)
  have he := integral_L2_eq_continuous_representative
    (fun r ↦ L (T r (Mi (graphTestToLp u))))
    (fun r x ↦ WithLp.toLp 2 (∫ y,
      (regularizedJointKernel backward (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        χA (physicalCutoff j) x y).mulVec (u.val y).ofLp))
    Δ (L.integrable_comp hint) hc (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact bounded_finiteGraph_outputMultiplier_realization hρ mi mo hi ho hos Mi Mo hMi hMo
        backward (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
        (hS.comp (continuous_const.prodMk continuous_id)) (hSs r hr) (hAs r hr)
        χA j hχ hχ0 (c r) (T r) (hreal r hr) u)
  rw [L.integral_comp_comm hint] at he
  refine he.trans (Eventually.of_forall ?_)
  intro x
  dsimp only
  rw [elapsedPhysicalShellKernel_test_fubini backward ρ Δ Ψ b χout χsource β mi mo
    χA (physicalCutoff j) hS hA hi.continuous ho hχ.continuous
    (physicalCutoff_contDiff j).continuous c hcommon hinput (fun y ↦ (u.val y).ofLp)
    ((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous) x]
  exact ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).symm.integral_comp_comm _)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
