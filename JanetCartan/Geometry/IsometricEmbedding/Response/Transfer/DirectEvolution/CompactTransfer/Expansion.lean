module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.BranchIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.BranchSupport

/-!
# Finite expansion of actual compact carrier integrals

The finite iteration following `paper-v2.tex`, `new:eq:carrier-ibp`, with
literal amplitude expressions and original datum derivatives. Primitive critical
geometry supplies the oscillation trade; compact support supplies every analytic
integrability and differentiation hypothesis. Consumer:
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential IsometricEmbedding.Response.NearCarrier

variable {n : ℕ} {E F J ι : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

private theorem contDiffOn_list_sum {S : Set E} (l : List J) (g : J → E → F)
    (hg : ∀ i ∈ l, ContDiffOn ℝ ∞ (g i) S) :
    ContDiffOn ℝ ∞ (fun p => (l.map fun i => g i p).sum) S := by
  induction l with
  | nil => simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : F)) S)
  | cons i is ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hg i (by simp)).add (ih (fun j hj => hg j (by simp [hj])))

private theorem transferredIntegrand_add
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    {g h : E → CarrierVariables n → F} {q : E} {w : CarrierVariables n}
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (q, w))
    (hh : ContDiffAt ℝ ∞ (Function.uncurry h) (q, w))
    (e : E) (hA : DifferentiableAt ℝ (transferCoefficient f w₀ e q) w) :
    transferredIntegrand b f w₀ e (fun p z => g p z + h p z) q w =
      transferredIntegrand b f w₀ e g q w + transferredIntegrand b f w₀ e h q w := by
  have hge : DifferentiableAt ℝ (fun p => g p w) q := (hg.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hhe : DifferentiableAt ℝ (fun p => h p w) q := (hh.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hgw : DifferentiableAt ℝ (g q) w := (hg.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hhw : DifferentiableAt ℝ (h q) w := (hh.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hi (i : ι) := ((differentiableAt_const (b i)).inner ℝ hA)
  simp only [transferredIntegrand, weightedDivergence, smul_add,
    fderiv_fun_add hge hhe, add_apply]
  have hiadd (i : ι) :
      fderiv ℝ (fun z => inner ℝ (b i) (transferCoefficient f w₀ e q z) • g q z +
        inner ℝ (b i) (transferCoefficient f w₀ e q z) • h q z) w =
      fderiv ℝ (fun z => inner ℝ (b i) (transferCoefficient f w₀ e q z) • g q z) w +
        fderiv ℝ (fun z => inner ℝ (b i) (transferCoefficient f w₀ e q z) • h q z) w :=
    fderiv_fun_add ((hi i).smul hgw) ((hi i).smul hhw)
  simp_rw [hiadd, add_apply]
  rw [Finset.sum_add_distrib]
  abel

private theorem transferredIntegrand_list_sum
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    {U : Set E} {D : Set (CarrierVariables n)} (hU : IsOpen U) (hD : IsOpen D)
    (l : List J) (g : J → E → CarrierVariables n → F)
    (hg : ∀ i ∈ l, ContDiffOn ℝ ∞ (Function.uncurry (g i)) (U ×ˢ D))
    (e : E) {q : E} {w : CarrierVariables n} (hq : q ∈ U) (hw : w ∈ D)
    (hA : DifferentiableAt ℝ (transferCoefficient f w₀ e q) w) :
    transferredIntegrand b f w₀ e (fun p z => (l.map fun i => g i p z).sum) q w =
      (l.map fun i => transferredIntegrand b f w₀ e (g i) q w).sum := by
  induction l with
  | nil => simp [transferredIntegrand, weightedDivergence]
  | cons i is ih =>
    have hi := (hg i (by simp)).contDiffAt
      ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))
    have hs := (contDiffOn_list_sum is (fun i => Function.uncurry (g i))
      (fun j hj => hg j (by simp [hj]))).contDiffAt
        ((hU.prod hD).mem_nhds (show (q, w) ∈ U ×ˢ D from ⟨hq, hw⟩))
    simp only [List.map_cons, List.sum_cons]
    rw [transferredIntegrand_add b f w₀ (g := g i)
      (h := fun p w => (is.map fun j => g j p w).sum) hi hs e hA, ih (fun j hj => hg j (by simp [hj]))]

private theorem sum_map_flatMap {A C G : Type*} [AddCommMonoid G]
    (l : List A) (children : A → List C) (v : C → G) :
    ((l.flatMap children).map v).sum = (l.map fun t => ((children t).map v).sum).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

variable {P M V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The original compact box supports every actual branch integrand, although
no compact support is required of the original datum (`new:eq:carrier-ibp`). -/
theorem support_jointTransferTermValue
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    {α : (Euclidean n × P) → CarrierVariables n → M} (a : Euclidean n × P → V)
    {U : Set (Euclidean n × P)} {K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hK : IsClosed K)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) :
    ∀ q ∈ U, Function.support (jointTransferTermValue b B f w₀ α a t q) ⊆ K := by
  intro q hq w hw
  by_contra hn
  have hz := Function.notMem_support.mp (fun h => hn
    (support_jointTransferTerms_amplitude b f w₀ hU hK hs es t ht q hq h))
  exact hw (by simp only [jointTransferTermValue, hz, Prod.fst_zero, map_zero, zero_apply])

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem support_list_sum {U : Set E} {K : Set (CarrierVariables n)}
    (l : List J) (g : J → E → CarrierVariables n → F)
    (hs : ∀ i ∈ l, ∀ q ∈ U, Function.support (g i q) ⊆ K) :
    ∀ q ∈ U, Function.support (fun w => (l.map fun i => g i q w).sum) ⊆ K := by
  intro q hq w hw
  by_contra hn
  apply hw
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  exact Function.notMem_support.mp (fun h => hn (hs i hi q hq h))

variable [FiniteDimensional ℝ P] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

set_option maxHeartbeats 400000 in
/-- Actual finite ordered differentiation equals the compact integral of the
constructed amplitude/input branches. The only coefficient premise is local
smoothness of the literal `transferCoefficient`, produced by coefficient jets.
Critical geometry, the same convex box, and the original compact support yield
every oscillation trade and every differentiation under the integral.
Source: iteration of `new:eq:carrier-ibp`. -/
theorem orderedTransferAction_integral_eq_jointTransferTerms
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {U : Set (Euclidean n × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ∀ q ∈ U, DifferentiableAt ℝ w₀ q)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0)
    (h₀ : ∀ q ∈ U, w₀ q ∈ D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (hA : ∀ e, ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D))
    (ρ : ℝ) (es : List (Euclidean n × P)) {q : Euclidean n × P} (hq : q ∈ U) :
    orderedTransferAction (fun e h p => fderiv ℝ h p e) es
        (fun p => ∫ w, oscillation f ρ p w • B (α p w) (sourceDatum a p w)) q =
      ∫ w, oscillation f ρ q w •
        ((jointTransferTerms b es).map fun t => jointTransferTermValue b B f w₀ α a t q w).sum := by
  let value := jointTransferTermValue b B f w₀ α a
  have hv (t : JointTransferTerm n P M ι) := contDiffOn_jointTransferTermValue b B hU hD hα hA ha t
  have hvs (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b es) :=
    support_jointTransferTermValue b B f w₀ a hU hK.isClosed hs es t ht
  have hg (es : List (Euclidean n × P)) : ContDiffOn ℝ ∞
      (Function.uncurry (fun p w => ((jointTransferTerms b es).map fun t => value t p w).sum))
      (U ×ˢ D) := contDiffOn_list_sum _ _ (fun t _ => hv t)
  have hgs (es : List (Euclidean n × P)) := support_list_sum (jointTransferTerms b es) value (hvs es)
  induction es generalizing q with
  | nil =>
    simp only [jointTransferTerms, orderedTransferAction, List.map_singleton, List.sum_singleton,
      jointTransferTermValue, initialJointTransferTerm, AmplitudeExpression.evaluate,
      jointAmplitudeFields, originalDatumDerivative]
  | cons e es ih =>
    have heq : orderedTransferAction (fun e h p => fderiv ℝ h p e) es
        (fun p => ∫ w, oscillation f ρ p w • B (α p w) (sourceDatum a p w)) =ᶠ[𝓝 q]
        (fun p => ∫ w, oscillation f ρ p w •
          ((jointTransferTerms b es).map fun t => value t p w).sum) := by
      filter_upwards [hU.mem_nhds hq] with p hp
      exact ih hp
    change fderiv ℝ _ q e = _
    rw [heq.fderiv_eq]
    have hAs : ContDiffOn ℝ ∞ (transferCoefficient f w₀ e q) D := by
      have hcomp := (hA e).comp (f := fun w : CarrierVariables n => (q, w))
        (s := D) (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw => ⟨hq, hw⟩)
      simpa only [Function.comp_def, Function.uncurry_def] using hcomp
    rw [fderiv_integral_oscillation_smul b hU hD hcD hK hKD hf (hg es) (hgs es)
      hq (hw₀ q hq) (hcritical q hq)
      (by filter_upwards [hU.mem_nhds hq] with p hp; exact hvalue p hp)
      (h₀ q hq) (hinv q hq) ρ e hAs]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w ∈ D
    · congr 1
      change transferredIntegrand b f w₀ e
        (fun p z => ((jointTransferTerms b es).map fun t => value t p z).sum) q w = _
      rw [transferredIntegrand_list_sum b f w₀ hU hD (jointTransferTerms b es) value
        (fun t _ => hv t) e hq hw ((hAs.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp))]
      change _ = (((jointTransferTerms b es).flatMap (jointTransferChildren b e)).map
        fun t => value t q w).sum
      rw [sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      exact transferredIntegrand_jointTransferTermValue b B hU hD hα hA ha t e hq hw
    · have hn : w ∉ K := fun h => hw (hKD h)
      have hl := Function.notMem_support.mp (fun h => hn
        (support_transferredIntegrand_subset b f w₀ hU hK.isClosed (hgs es) e q hq h))
      have hr := Function.notMem_support.mp (fun h => hn (hgs (e :: es) q hq h))
      change oscillation f ρ q w • transferredIntegrand b f w₀ e
        (fun p z => ((jointTransferTerms b es).map fun t => value t p z).sum) q w = _
      rw [hl]
      change _ = _ • (((jointTransferTerms b (e :: es)).map fun t => value t q w).sum)
      rw [hr]

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
