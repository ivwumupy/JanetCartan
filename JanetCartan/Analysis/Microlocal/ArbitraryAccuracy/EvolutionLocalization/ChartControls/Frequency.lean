module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.ChartControls.PhaseFields

/-!
# Full covector comparison for the literal elapsed phase

Local radial homogeneity and the original spatial mixed/temporal derivative
budgets imply comparison at every temporal covector. In particular, no cone
condition on the temporal component is imposed. Consumer:
`FiniteChain.Graph.exists_graph_factor_sobolev_bound_of_primitive_grades`,
for `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ}

/-- Euler's identity for an original degree-one phase derivative, proved by
differentiating radial scaling. Consumer: full elapsed frequency comparison
(`app:ch_regular:eq:high-phase`). -/
theorem phaseField_euler {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclidean d → F} {η : Euclidean d} (hd : DifferentiableAt ℝ f η)
    (hh : ∀ᶠ c : ℝ in 𝓝 1, f (c • η) = c • f η) :
    fderiv ℝ f η η = f η := by
  have hc : HasDerivAt (fun c : ℝ => c • η) η 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const η
  have hf : HasFDerivAt f (fderiv ℝ f η) ((1 : ℝ) • η) := by
    simpa using hd.hasFDerivAt
  have hh' : (fun c : ℝ => f (c • η)) =ᶠ[𝓝 1] (fun c => c • f η) := hh
  have he := (hf.comp_hasDerivAt 1 hc).congr_of_eventuallyEq hh'.symm
  exact he.unique (by simpa using (hasDerivAt_id (1 : ℝ)).smul_const (f η))

/-- Radial homogeneity turns the original spatial mixed half-gap into
control of the spatial covector itself. This supplies, rather than assumes,
the spatial part of full frequency comparison
(`app:ch_regular:lem:finite-chain`). -/
theorem phaseMomentum_radial_error {F : Euclidean d → Euclidean d}
    {η : Euclidean d} (hd : DifferentiableAt ℝ F η)
    (hh : ∀ᶠ c : ℝ in 𝓝 1, F (c • η) = c • F η)
    (hg : ‖fderiv ℝ F η-ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 1/2) :
    ‖F η-η‖ ≤ (1/2 : ℝ)*‖η‖ := by
  have he := phaseField_euler hd hh
  calc
    ‖F η-η‖ = ‖(fderiv ℝ F η-ContinuousLinearMap.id ℝ (Euclidean d)) η‖ := by rw [← he]; rfl
    _ ≤ ‖fderiv ℝ F η-ContinuousLinearMap.id ℝ (Euclidean d)‖*‖η‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)

/-- Full triangular frequency comparison at arbitrary temporal covector.
The constant is fixed by the original temporal derivative budget before
scale or elapsed time; spatial near-identity alone would not suffice.
Consumer: the graph-factor frequency-comparison premise
(`app:ch_regular:lem:finite-chain`). -/
theorem triangular_covector_comparison
    {F : Euclidean d → Euclidean d} {a : Euclidean d → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (ξ : Euclidean (d+1))
    (hd : DifferentiableAt ℝ F (spatialPart ξ))
    (hh : ∀ᶠ c : ℝ in 𝓝 1, F (c • spatialPart ξ) = c • F (spatialPart ξ))
    (hg : ‖fderiv ℝ F (spatialPart ξ)-ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 1/2)
    (ha : DifferentiableAt ℝ a (spatialPart ξ))
    (hah : ∀ᶠ c : ℝ in 𝓝 1, a (c • spatialPart ξ) = c • a (spatialPart ξ))
    (hb : ‖fderiv ℝ a (spatialPart ξ)‖ ≤ L) :
    (3+2*L)⁻¹ * ‖ξ‖ ≤
        ‖timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ))‖ ∧
      ‖timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ))‖ ≤
        (3+2*L)*‖ξ‖ := by
  let v := timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ))
  have he := phaseMomentum_radial_error hd hh hg
  have hlo : ‖spatialPart ξ‖ ≤ 2*‖F (spatialPart ξ)‖ := by
    have ht := norm_sub_le (F (spatialPart ξ)) (F (spatialPart ξ)-spatialPart ξ)
    rw [sub_sub_cancel] at ht
    linarith only [he, ht]
  have hup : ‖F (spatialPart ξ)‖ ≤ (3/2 : ℝ)*‖spatialPart ξ‖ := by
    have ht := norm_sub_le (F (spatialPart ξ)-spatialPart ξ) (-spatialPart ξ)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
    linarith only [he, ht]
  have hs : |a (spatialPart ξ)| ≤ L*‖spatialPart ξ‖ := by
    rw [← phaseField_euler ha hah]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hp : ‖F (spatialPart ξ)‖ ≤ ‖v‖ := by
    simpa only [v, spatialPart_timeSpacePoint] using norm_spatialPart_le v
  have ht : |ξ 0+a (spatialPart ξ)| ≤ ‖v‖ := PiLp.norm_apply_le v 0
  have hx : |ξ 0| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ 0
  have hη := norm_spatialPart_le ξ
  have hn := norm_le_time_add_spatial ξ
  have htime : |ξ 0| ≤ |ξ 0+a (spatialPart ξ)|+|a (spatialPart ξ)| := by
    have hh' := abs_sub (ξ 0+a (spatialPart ξ)) (a (spatialPart ξ))
    simpa only [add_sub_cancel_right] using hh'
  have hc : 0 < 3+2*L := by positivity
  constructor
  · rw [inv_mul_eq_div, div_le_iff₀ hc]
    change ‖ξ‖ ≤ ‖v‖*(3+2*L)
    have hηv : ‖spatialPart ξ‖ ≤ 2*‖v‖ := hlo.trans (by gcongr)
    nlinarith only [hn, htime, ht, hs, hηv, mul_le_mul_of_nonneg_left hηv hL]
  · have hv := norm_timeSpacePoint_le (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ))
    have hh' := abs_add_le (ξ 0) (a (spatialPart ξ))
    change ‖v‖ ≤ (3+2*L)*‖ξ‖
    nlinarith only [hv, hh', hx, hs, hup, hη,
      mul_le_mul_of_nonneg_left hη hL, mul_nonneg hL (norm_nonneg ξ), norm_nonneg ξ]

/-- Uniform full frequency constants precede the phase, elapsed time, and
physical frequency. Primitive radial homogeneity and derivative budgets of
the original two-time phase maps are the only analytic premises. Their
finite coefficient-family realization remains the regular-sector producer's
obligation (`app:ch_regular:eq:high-phase`). -/
theorem exists_phaseCovectorMap_comparison_constants (L : ℝ) (hL : 0 ≤ L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : Euclidean (d+1)),
      let F := fun η => phaseMomentum Ψ r ((x 0, spatialPart x), η)
      let a := fun η => phaseShear Ψ r ((x 0, spatialPart x), η)
      DifferentiableAt ℝ F (spatialPart ξ) →
      (∀ᶠ k : ℝ in 𝓝 1, F (k • spatialPart ξ) = k • F (spatialPart ξ)) →
      ‖fderiv ℝ F (spatialPart ξ)-ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ 1/2 →
      DifferentiableAt ℝ a (spatialPart ξ) →
      (∀ᶠ k : ℝ in 𝓝 1, a (k • spatialPart ξ) = k • a (spatialPart ξ)) →
      ‖fderiv ℝ a (spatialPart ξ)‖ ≤ L →
      c*‖ξ‖ ≤ ‖phaseCovectorMap Ψ r x ξ‖ ∧
        ‖phaseCovectorMap Ψ r x ξ‖ ≤ C*‖ξ‖ := by
  refine ⟨(3+2*L)⁻¹, 3+2*L, by positivity, by positivity, ?_⟩
  intro Ψ r x ξ F a hd hh hg ha hah hb
  exact triangular_covector_comparison (F := F) (a := a) hL ξ hd hh hg ha hah hb

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
