module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# Actual integrands of the ordered compact transfer branches

The algebraic product rule for the actual transferred integrand in
`paper-v2.tex`, `new:eq:carrier-ibp`. The input remains an ordered derivative
of the original datum, and the full amplitude is always the first argument
of the bilinear action. Consumer: the finite compact integral expansion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential IsometricEmbedding.Response.NearCarrier

variable {n : ℕ} {P M V F ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- The literal integrand of one branch, acting in the original matrix order
on a derivative of the original input (`new:eq:carrier-ibp`). -/
def jointTransferTermValue (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (B : M →L[ℝ] V →L[ℝ] F)
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → M) (a : Euclidean n × P → V)
    (t : JointTransferTerm n P M ι) (q : Euclidean n × P) (w : CarrierVariables n) : F :=
  B (t.amplitude.evaluate (jointAmplitudeFields b f w₀ α) (q, w)).1
    (sourceDatum (originalDatumDerivative t.datumWord a) q w)

/-- Local smoothness of each literal branch integrand is derived from the
primitive amplitude and coefficient fields and the original datum. No output
identity or output norm is assumed (`new:eq:carrier-ibp`). -/
theorem contDiffOn_jointTransferTermValue
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    {U : Set (Euclidean n × P)} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ha : ContDiff ℝ ∞ a) (t : JointTransferTerm n P M ι) :
    ContDiffOn ℝ ∞ (Function.uncurry (jointTransferTermValue b B f w₀ α a t)) (U ×ˢ D) := by
  have hv := contDiffOn_amplitudeExpression (hU.prod hD) _
    (contDiffOn_jointAmplitudeFields b hα hA) t.amplitude
  apply (B.contDiff.comp_contDiffOn hv.fst).clm_apply
  exact (contDiff_originalDatumDerivative ha t.datumWord).comp_contDiffOn
    (((WithLp.fstL 2 ℝ (Euclidean n) (Euclidean n)).contDiff.comp_contDiffOn
      contDiffOn_snd).prodMk contDiffOn_fst.snd)

/-- One complete integrand transfer is exactly the sum of its constructed
children. The signed source coefficients and the zero output/covector datum
derivatives are proved, rather than assumed. Source: `new:eq:carrier-ibp`. -/
theorem transferredIntegrand_jointTransferTermValue
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    {U : Set (Euclidean n × P)} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ha : ContDiff ℝ ∞ a) (t : JointTransferTerm n P M ι) (e : Euclidean n × P)
    {q : Euclidean n × P} {w : CarrierVariables n} (hq : q ∈ U) (hw : w ∈ D) :
    transferredIntegrand b f w₀ e (jointTransferTermValue b B f w₀ α a t) q w =
      ((jointTransferChildren b e t).map fun u => jointTransferTermValue b B f w₀ α a u q w).sum := by
  classical
  let fields := jointAmplitudeFields b f w₀ α
  let v := t.amplitude.evaluate fields
  let u := originalDatumDerivative t.datumWord a
  let B' : (M × ℝ) →L[ℝ] V →L[ℝ] F := B.comp (ContinuousLinearMap.fst ℝ M ℝ)
  have hv := contDiffOn_amplitudeExpression (hU.prod hD) fields
    (contDiffOn_jointAmplitudeFields b hα hA) t.amplitude
  have hvj := hv.contDiffAt ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))
  have hve : DifferentiableAt ℝ (fun p => v (p, w)) q :=
    (hvj.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hvw : DifferentiableAt ℝ (fun z => v (q, z)) w :=
    (hvj.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hu := contDiff_originalDatumDerivative ha t.datumWord
  have hue : DifferentiableAt ℝ (fun p => sourceDatum u p w) q :=
    (hu.comp (contDiff_const.prodMk contDiff_snd)).differentiable (by simp) q
  have huw : DifferentiableAt ℝ (sourceDatum u q) w :=
    (hu.comp ((WithLp.fstL 2 ℝ (Euclidean n) (Euclidean n)).contDiff.prodMk
      contDiff_const)).differentiable (by simp) w
  have hAw : DifferentiableAt ℝ (transferCoefficient f w₀ e q) w :=
    (((hA e).contDiffAt ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))).comp w
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hder : fderiv ℝ (fun p => B' (v (p, w)) (sourceDatum u p w)) q e =
      B' (fderiv ℝ (fun p => v (p, w)) q e) (sourceDatum u q w) +
      B' (v (q, w)) (fderiv ℝ (fun p => sourceDatum u p w) q e) := by
    simpa [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, add_comm] using
      congrArg (fun L : (Euclidean n × P) →L[ℝ] F => L e) (B'.fderiv_of_bilinear hve hue)
  have hsum := congrArg (fun z => B' (v (q, w)) (fderiv ℝ (sourceDatum u q) w z))
    (b.sum_repr' (transferCoefficient f w₀ e q w))
  simp only [map_sum, map_smul] at hsum
  change fderiv ℝ (fun p => B' (v (p, w)) (sourceDatum u p w)) q e -
    weightedDivergence b (transferCoefficient f w₀ e q)
      (fun z => B' (v (q, z)) (sourceDatum u q z)) w = _
  rw [hder, weightedDivergence_bilinear b B' hAw hvw huw, ← hsum]
  simp only [jointTransferChildren, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def, Finset.sum_map_toList, jointTransferTermValue]
  rw [evaluate_jointDivergenceTransfer b hU hD hα hA t.amplitude e hq hw]
  simp_rw [evaluate_jointCoefficientProduct]
  change _ = B' (transferredIntegrand b f w₀ e (fun p z => v (p, z)) q w)
      (sourceDatum u q w) +
    (B' (v (q, w)) (sourceDatum (fun z => fderiv ℝ u z (0, e.2)) q w) +
      ∑ i, B' (-inner ℝ (b i) (transferCoefficient f w₀ e q w) • v (q, w))
        (sourceDatum (fun z => fderiv ℝ u z ((b i).fst, 0)) q w))
  rw [fderiv_sourceDatum_external q e w (hu.differentiable (by simp) _)]
  simp_rw [fderiv_sourceDatum_integration (a := u) q w _ (hu.differentiable (by simp) _)]
  simp only [transferredIntegrand, map_sub, sub_apply, sourceDatum]
  have hmul (c : ℝ) (z : M × ℝ) (y : V) : B' (c • z) y = c • B' z y := by
    exact congrArg (fun L : V →L[ℝ] F => L y) (B'.map_smul c z)
  simp_rw [hmul]
  simp only [neg_smul, Finset.sum_neg_distrib]
  dsimp only [u]
  abel

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
