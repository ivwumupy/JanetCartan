module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryCoordinates

/-!
# Common physical masks in the actual elapsed factors

The selected inverse's input and output multipliers are absorbed into the
existing elapsed graph using the original plateau identities. The literal
adjoint reverses their order. Both datum-wise integrals keep the entire
original elapsed interval and the original low operator constant.

The actual finite family's masks, together with the inverse's smaller output
cutoff, have support inside the stationary physical box returned by the
full-source selector. This supplies the physical-domain input for the same
solver and complete residual factors in the full-source envelope application.
The original graph realization and integral construction remain the producers
of the displayed test-action and integrability inputs.

Sources: `app:ch_response:eq:fixed-factor-transfer` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic EvolutionIntegral FourierIntegral LowBounds FullLowBounds
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- The common physical masks give exactly the same elapsed graph operator.
The source multiplication stays on the right. The plateau identities are
actual outputs of the selected inverse, and the graph test realization comes
from the original primitive graph construction
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsedGraph_common_physical_masks_of_realizes
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (t : ℝ)
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hs : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hout : ∀ x, (ψout x : ℂ) * χout x = (ψout x : ℂ))
    (hsource : ∀ x, χsource x * (ψsource x : ℂ) = (ψsource x : ℂ))
    (hreal : ∀ u : graphTestSpace (d + 1) q,
      elapsedGraph Ψ W χout χsource β t (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t) (elapsedAmplitude W χout χsource β t) u) :
    (sourceCutMultiplier ψout ho hob).comp
      ((elapsedGraph Ψ W χout χsource β t).comp
        (sourceCutMultiplier ψsource hs.continuous hsb)) =
      elapsedGraph Ψ W (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) β t := by
  symm
  apply fullGraphOperator_eq_of_realizes
  intro u
  change sourceCutMultiplier ψout ho hob
    (elapsedGraph Ψ W χout χsource β t
      (sourceCutMultiplier ψsource hs.continuous hsb (graphTestToLp u))) =ᵐ[volume] _
  rw [sourceCutMultiplier_graphTestToLp ψsource hs hsb u]
  filter_upwards [sourceCutMultiplier_coeFn ψout ho hob
    (elapsedGraph Ψ W χout χsource β t (graphTestToLp (sourceCutTest ψsource hs u))),
    hreal (sourceCutTest ψsource hs u)] with x hx hu
  rw [hx, hu]
  change WithLp.toLp 2 ((ψout x : ℂ) • graphOperator (elapsedPhase Ψ t)
      (elapsedAmplitude W χout χsource β t)
      (fun y ↦ (ψsource y : ℂ) • (u.val y).ofLp) x) = _
  rw [graphOperator_source_mul]
  rw [← graphOperator_target_mul (elapsedPhase Ψ t)
    (fun x y η ↦ (ψsource y : ℂ) • elapsedAmplitude W χout χsource β t x y η)
    (fun y ↦ (ψout y : ℂ)) (fun y ↦ (u.val y).ofLp) x]
  congr 2
  funext y z ξ
  simp only [elapsedAmplitude, smul_smul]
  congr 1
  calc
    (ψout y : ℂ) * ((ψsource z : ℂ) * (χout y * χsource z * β ξ)) =
      ((ψout y : ℂ) * χout y) * (χsource z * (ψsource z : ℂ)) * β ξ := by ring
    _ = _ := by rw [hout, hsource]

/-- The common-mask graph keeps the original low operator constant: both
physical multipliers are contractions. No new graph budget is selected
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem norm_elapsedGraph_common_physical_masks_le
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (t : ℝ)
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hs : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hout : ∀ x, (ψout x : ℂ) * χout x = (ψout x : ℂ))
    (hsource : ∀ x, χsource x * (ψsource x : ℂ) = (ψsource x : ℂ))
    (hreal : ∀ u : graphTestSpace (d + 1) q,
      elapsedGraph Ψ W χout χsource β t (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t) (elapsedAmplitude W χout χsource β t) u) :
    ‖elapsedGraph Ψ W (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) β t‖ ≤
      ‖elapsedGraph Ψ W χout χsource β t‖ := by
  rw [← elapsedGraph_common_physical_masks_of_realizes Ψ W χout χsource β t
    ψout ψsource ho hs hob hsb hout hsource hreal]
  calc
    _ ≤ ‖sourceCutMultiplier (r := q) ψout ho hob‖ *
        ‖(elapsedGraph Ψ W χout χsource β t).comp
          (sourceCutMultiplier ψsource hs.continuous hsb)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖elapsedGraph Ψ W χout χsource β t‖ * 1) :=
      mul_le_mul (norm_sourceCutMultiplier_le (r := q) ψout ho hob)
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_sourceCutMultiplier_le (r := q) ψsource hs.continuous hsb)
            (norm_nonneg _))) (norm_nonneg _) (by norm_num)
    _ = _ := by ring



/-- Both datum-wise integrals on the whole original elapsed interval retain
exactly the common-mask graph and its literal adjoint. Integrability is the
output of the original strong-integral construction; neither endpoint nor
phase is changed (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsed_integrals_common_physical_masks_of_realizes
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (Δ : ℝ)
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hs : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hout : ∀ x, (ψout x : ℂ) * χout x = (ψout x : ℂ))
    (hsource : ∀ x, χsource x * (ψsource x : ℂ) = (ψsource x : ℂ))
    (hreal : ∀ t ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
      elapsedGraph Ψ W χout χsource β t (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t) (elapsedAmplitude W χout χsource β t) u)
    (hi : ∀ u : H, IntegrableOn (fun t ↦ elapsedGraph Ψ W χout χsource β t u) (Icc 0 Δ))
    (hiAdj : ∀ u : H, IntegrableOn
      (fun t ↦ (elapsedGraph Ψ W χout χsource β t).adjoint u) (Icc 0 Δ)) :
    ∀ u : H,
      sourceCutMultiplier ψout ho hob
        (elapsedGraphIntegral Δ Ψ W χout χsource β
          (sourceCutMultiplier ψsource hs.continuous hsb u)) =
        elapsedGraphIntegral Δ Ψ W (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) β u ∧
      sourceCutMultiplier ψsource hs.continuous hsb
        (∫ t in Icc 0 Δ, (elapsedGraph Ψ W χout χsource β t).adjoint
          (sourceCutMultiplier ψout ho hob u)) =
        ∫ t in Icc 0 Δ,
          (elapsedGraph Ψ W (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) β t).adjoint u := by
  have hm t (ht : t ∈ Icc 0 Δ) := elapsedGraph_common_physical_masks_of_realizes
    Ψ W χout χsource β t ψout ψsource ho hs hob hsb hout hsource (hreal t ht)
  intro u
  constructor
  · unfold elapsedGraphIntegral
    rw [← (sourceCutMultiplier ψout ho hob).integral_comp_comm (hi _)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact DFunLike.congr_fun (hm t ht) u
  · rw [← (sourceCutMultiplier ψsource hs.continuous hsb).integral_comp_comm (hiAdj _)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have h := congrArg ContinuousLinearMap.adjoint (hm t ht)
    simpa only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint,
      ContinuousLinearMap.comp_apply] using DFunLike.congr_fun h u


open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic

/-- The actual common input and the inverse's smaller output cutoff lie in
the selector's SAME stationary physical box. The output plateau is used only
for support containment; no equality of the original and smaller masks is
asserted (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_common_physical_masks_subset_stationary_box
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (z : RootState (Euclidean d)) (ε : ℝ)
    (hbox : MapsTo (CompatibleResponse.primaryCoordinateChange (f.chart p).index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z (ε / 2)))
    (output : E → ℝ) (hout : tsupport output ⊆ Metric.ball x f.physicalRadius) :
    tsupport (fun y ↦ (output (physicalCoordinates (f.chart p).index y) : ℂ)) ∪
      tsupport (chartInputMask f p) ⊆ elapsedPhysicalBox z (ε / 2) := by
  intro y hy
  have hphys : physicalCoordinates (f.chart p).index y ∈
      tsupport f.inputMask ∪ tsupport f.outputMask := by
    rcases hy with hy | hy
    · have houtput : physicalCoordinates (f.chart p).index y ∈ tsupport output :=
        tsupport_comp_subset Complex.ofReal_zero output
          (tsupport_comp_subset_preimage (fun z ↦ (output z : ℂ))
            (physicalCoordinates (f.chart p).index).continuous hy)
      have hp := f.outputMask_plateau (Metric.ball_subset_closedBall (hout houtput))
      have he : f.outputMask (physicalCoordinates (f.chart p).index y) = 1 :=
        interior_subset (s := {y : E | f.outputMask y = 1}) hp
      exact Or.inr (subset_tsupport _ (by
        change f.outputMask (physicalCoordinates (f.chart p).index y) ≠ 0
        rw [he]
        exact one_ne_zero))
    · exact Or.inl (tsupport_comp_subset Complex.ofReal_zero f.inputMask
        (tsupport_comp_subset_preimage (fun z ↦ (f.inputMask z : ℂ))
          (physicalCoordinates (f.chart p).index).continuous hy))
  simpa only [CompatibleResponse.primaryCoordinateChange, physicalCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hbox hphys

end JanetCartan.ResponseTransfer.RetainedFactors
