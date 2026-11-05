module
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketEquation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-! # A size-only local representative of the unmodified signed datum

χsrc need not be supported inside the phase chart. On the compact support of
the *output* cutoff choose an auxiliary scalar equal to χsrc and supported in
the chart. It equals χsrc also on the actual measurement support. Thus the
once-measured input of the Neumann inverse, and the exterior Schwartz field,
are unchanged; no cutoff is inserted into the genuine solution or the PDE.
`app:ch_pairs:eq:pairs-lag-sum-size`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius NNReal ENNReal
namespace JanetCartan.PhysicalPairs.OriginalSizeSupport
open CompatibleResponse AmbientResponse UniformStep SmallSupport LocalSobolev FixedDomainInverse
open ResponseSourceExtension PrimarySourceAdmission CorrectedAtoms
variable {n N : ℕ}
local notation "E" => Euclidean n
local instance : Fact (1 ≤ ((2:ℝ≥0):ℝ≥0∞)) := ⟨by norm_num⟩

theorem exists_factor {c : E} (χ₂ χ₃ : ContDiffBump c) {U : Set E} (η : E → ℝ) (hU : IsOpen U)
    (hs : tsupport (χ₃ : E → ℝ) ⊆ U) (hc : HasCompactSupport (χ₃ : E → ℝ)) (hη : ContDiff ℝ ∞ η)
    (hn : ∀ x ∈ tsupport (χ₂ : E → ℝ), χ₃ x = 1) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ U ∧
      EqOn θ η (tsupport (χ₂ : E → ℝ)) ∧ EqOn θ η (tsupport (χ₃ : E → ℝ)) := by
  obtain ⟨a,ha,_,hac,haU,hplateau⟩ := exists_compact_family_cutoff hc hU hs
  have hts : tsupport (a*η) ⊆ tsupport a := tsupport_mul_subset_left
  have he : EqOn (a*η) η (tsupport (χ₃ : E → ℝ)) := by
    intro x hx
    have hm : x ∈ {t | a t = 1} := interior_subset (hplateau hx)
    have hh : a x = 1 := hm
    simp only [Pi.mul_apply,hh,one_mul]
  exact ⟨a*η,ha.mul hη,hac.of_isClosed_subset (isClosed_tsupport _) hts,hts.trans haU,
    fun x hx ↦ he (subset_tsupport (χ₃ : E → ℝ) (show χ₃ x ≠ 0 by rw [hn x hx]; exact one_ne_zero)),he⟩

def jetCost (b : ℝ) (f : E → ℝ) (j : ℕ) : ℝ := cNorm (closedBall (0 : E) b) j f

theorem jetCost_nonneg (b : ℝ) (f : E → ℝ) (j : ℕ) : 0 ≤ jetCost b f j := cNorm_nonneg _ _ _

theorem jet_bound {G : Set E} {b : ℝ} (hG : G ⊆ ball 0 b) (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    {L : ℝ} (hL : 1 ≤ L) : ∀ x ∈ G, ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ jetCost b f j * L^j :=
  fun x hx j ↦ (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) (hf.of_le (by simp)) (ball_subset_closedBall (hG hx)) le_rfl).trans
    (le_mul_of_one_le_right (jetCost_nonneg b f j) (one_le_pow₀ hL))

theorem original_class {I : Type} (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ) (minus : Bool) (i j : I)
    {U W : Set E} {η : E → ℝ} (ho : IsOpen U) (Q : E → Fin n → MetricTensor n) (hQ : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ Q x k) U)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ((SampledInput.uncut (W := W) Z θ minus i j ho Q hQ hη hc hηU).val : E → E) =ᵐ[volume.restrict W]
      fun y ↦ (WithLp.toLp 2 (stressSource Q (OriginalSignedPackets.originalTensor Z θ minus i j η) y) : E) := by
  have hh := cutoffStressSmoothSource_coeFn (W := W) Q (fun _ ↦ 1) ho hQ contDiff_const hηU
    ⟨_,SampledInput.tensor_admitted Z θ minus i j hη hc⟩
  unfold OriginalSignedPackets.originalTensor
  simpa only [SampledInput.uncut,euclideanCutoffStressSource,cutoffSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul] using hh

theorem same_measurement {W : Set E} {c : E} (χ : ContDiffBump c) (Q : E → Fin n → MetricTensor n) (H : MetricField n)
    (η α : E → ℝ) (hα : EqOn α η (tsupport (χ : E → ℝ))) (v : LocalL2 W E)
    (hv : (v : E → E) =ᵐ[volume.restrict W] fun x ↦ (WithLp.toLp 2 (stressSource Q (fun y ↦ η y • H y) x) : E)) :
    let f := fun x ↦ (WithLp.toLp 2 (cutoffSource (fun _ ↦ 1) (stressSource Q (fun y ↦ α y • H y)) x) : E)
    ∀ hf : MemLp f 2 volume, bumpL2 (p := 2) le_rfl χ ((hf.restrict W).toLp f) = bumpL2 (p := 2) le_rfl χ v := by
  intro f hf
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ ((hf.restrict W).toLp f),bumpL2_coeFn (p := 2) le_rfl χ v,(hf.restrict W).coeFn_toLp,hv] with x he he' hnew hold
  rw [he,he',hnew,hold]
  by_cases h : χ x = 0
  · simp only [h,zero_smul]
  · have h' := hα (subset_tsupport (χ : E → ℝ) (show χ x ≠ 0 from h))
    simp only [f,cutoffSource,stressSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul,h']

theorem same_field (ψ η α : E → ℝ) (hα : EqOn α η (tsupport ψ)) (F : E → Euclidean N) (u : E → E) (H : MetricField n) (x : E) :
    ψ x • completedVariation F u (fun y ↦ η y • H y) x = ψ x • completedVariation F u (fun y ↦ α y • H y) x := by
  by_cases hx : ψ x = 0
  · simp only [hx,zero_smul]
  · simp only [completedVariation,Pi.add_apply, hα (subset_tsupport ψ (show ψ x ≠ 0 from hx))]
end JanetCartan.PhysicalPairs.OriginalSizeSupport
end
public meta section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSizeSupport
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSizeSupport
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (h : Expr) : Nat → Expr | 0 => h | k+1 => down (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (down h k)
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (reg ++ `χ₂)).type (some 23) fun p _ => do
    let m (k : Name) := a (mask ++ k) p
    let hs := m `χsrc_smooth
    let ex ← mkAppM (ns ++ `exists_factor) #[a (reg ++ `χ₂) p,a (reg ++ `χ₃) p,(← inferType hs).appArg!,m `chart_open,m `χ₃_support_chart,m `χ₃_compact,hs,m `χ₃_on_χ₂]
    let ω ← store (ns ++ `factor) p (← mkAppM ``Classical.choose #[ex]) true
    let spec ← store (ns ++ `factor_spec) p (← mkAppM ``Classical.choose_spec #[ex]) false (some ((← inferType ex).appArg!.beta #[ω]))
    for (k,h) in [(`smooth,part spec 0),(`compact,part spec 1),(`support_chart,part spec 2),(`same_input,part spec 3),(`same_output,down spec 4)] do
      discard <| store (ns ++ k) p h
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo `JanetCartan.PhysicalPairs.OriginalSignedData.uncut).type (some 50) fun p _ => do
    let old := `JanetCartan.PhysicalPairs.OriginalSignedData.uncut
    let raw := ((← getConstInfo old).value! (allowOpaque := true)).beta p
    unless raw.isAppOf `JanetCartan.PhysicalPairs.SampledInput.uncut do throwError "lost actual broad signed input"
    let pf := a (ns ++ `original_class) raw.getAppArgs
    discard <| store (ns ++ `original_input_ae) p pf false (some ((← inferType pf).replace fun e => if e == raw then some (a old p) else none))
end JanetCartan.PhysicalPairs.OriginalSizeSupport
end
