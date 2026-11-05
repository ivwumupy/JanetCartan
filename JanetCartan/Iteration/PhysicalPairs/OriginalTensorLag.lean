module
public import JanetCartan.Iteration.PhysicalPairs.OriginalResidualEmbedding
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.DirectResidualTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedPhysicalEquation
public import JanetCartan.Geometry.IsometricEmbedding.Normal.ReducedEquation.Completion

/-! # From the true smooth signed solver to its full metric error

The frame comes from the proved original graph margin, with the numerical
width chosen no larger than the raw-primary frame threshold *before* σ.
The complete normal column is recovered from the germ of the same Schwartz
packet. No inclusion of the support of the broad physical tensor in W is used.
`app:ch_response:eq:response-full-identity`, `app:ch_pairs:eq:pairs-lag-one-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius BigOperators SchwartzMap
namespace JanetCartan.PhysicalPairs.OriginalTensorLag
open AmbientResponse UniformStep ProjectedStressFrame CharacteristicTransport.CompleteResidual GeometricProfile CorrectedAtoms
open ProtectedFlow ResponseTransfer.RetainedFactors CanonicalAtomRealization RawPrimary PhysicalSeed NullTransport
variable {d : ℕ}
local notation "n" => d+1
local notation "E" => Euclidean (d+1)
local notation "V" => Euclidean (embeddingDimension (d+1))

theorem actual_tensor_symmetric {m N : ℕ} {I : Type} (Z : I → SchwartzMap (Euclidean m) (EuclideanSpace ℂ (Fin N)))
    (θ : I → Euclidean m → ℝ) (minus : Bool) (i j : I) (η : Euclidean m → ℝ) : ∀ x, (OriginalSignedPackets.originalTensor Z θ minus i j η x).IsSymm := by
  intro x
  unfold OriginalSignedPackets.originalTensor
  rw [SampledInput.tensor_formula]
  exact ((symmetricBilinearTensor_isSymm _ _).map Complex.re).smul _

theorem original_inner {m : ℕ} {c : Euclidean m} (χ : ContDiffBump c) : closedBall c (χ.rIn/2) ⊆ ball c χ.rIn := closedBall_subset_ball (half_lt_self χ.rIn_pos)

theorem original_frame_ball {m : ℕ} {c : Euclidean m} (χ : ContDiffBump c) {U : Set (Euclidean m)} {b : ℝ}
    (hs : tsupport (χ : Euclidean m → ℝ) ⊆ U) (hu : U ⊆ ball 0 b) : closedBall c (χ.rIn/2) ⊆ ball 0 b :=
  ((original_inner χ).trans (OriginalPacketEquation.inner_subset χ hs)).trans hu

theorem row_of_local_margin (ext : BallExtension.Parameters E) (F : E → V) (γ : ℝ)
    (hQ : ContDiff ℝ ∞ (extendedProjectedStress ext F))
    (hm : ∀ K : Set E, cNorm K 6 (extendedProjectedStress ext F - fun _ ↦ cubeStress n) < γ)
    (x : E) (hx : x ∈ ball ext.center ext.radius) (i : Fin n) :
    cNorm {x} 6 (fun y ↦ projectedStress F y i - cubeStress n i) < γ := by
  let G := extendedProjectedStress ext F - fun _ ↦ cubeStress n
  let L : (Fin n → MetricTensor n) →L[ℝ] MetricTensor n := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖A i‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using norm_le_pi_norm A i
  have hg : cNorm {x} 6 (L ∘ G) = cNorm {x} 6 (fun y ↦ projectedStress F y i - cubeStress n i) := by
    apply cNorm_eq_of_eventuallyEq _ 6
    intro y hy
    obtain rfl : y = x := mem_singleton_iff.mp hy
    filter_upwards [isOpen_ball.mem_nhds hx] with t ht
    change extendedProjectedStress ext F t i - cubeStress n i = _
    rw [show extendedProjectedStress ext F t = projectedStress F t from affineFrameExtension_eqOn ext _ (ball_subset_closedBall ht)]
  rw [← hg]
  have hG : ContDiff ℝ ∞ G := hQ.sub contDiff_const
  have hnorm : cNorm {x} 6 (L ∘ G) ≤ ‖L‖ * cNorm {x} 6 G := FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on
    isCompact_singleton 6 L (fun y _ ↦ (hG.contDiffAt (x := y)).of_le (by simp))
  calc
    _ ≤ ‖L‖ * cNorm {x} 6 G := hnorm
    _ ≤ 1 * cNorm {x} 6 G := mul_le_mul_of_nonneg_right hL (cNorm_nonneg {x} 6 G)
    _ = cNorm {x} 6 G := one_mul _
    _ < γ := hm {x}

theorem from_true_pencil (hn : 5 ≤ n) (ext : BallExtension.Parameters E) (hc : ext.center = 0) (hb : ext.radius = OriginalBoundary.b hn)
    (F : E → V) (hF : ContDiffOn ℝ ∞ F (ball 0 (OriginalBoundary.R hn))) (hi : IsImmersionOn F (ball 0 (OriginalBoundary.R hn)))
    (hr : HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn))) (γ : ℝ) (hγ : γ ≤ ambientStrainFrameThreshold hn)
    (hQ : ContDiff ℝ ∞ (extendedProjectedStress ext F))
    (hmargin : ∀ K : Set E, cNorm K 6 (extendedProjectedStress ext F - fun _ ↦ cubeStress n) < γ)
    (D O : Set E) (hDO : D ⊆ O) (hDb : D ⊆ ball 0 (OriginalBoundary.b hn))
    (u r : E → E) (H : MetricField n) (packet : E → V) (hu : ContDiff ℝ ∞ u) (hH : ContDiff ℝ ∞ H) (hsym : ∀ x, (H x).IsSymm)
    (hg : ∀ x ∈ D, packet =ᶠ[𝓝 x] completedVariation F u H)
    (hp : EqOn (physicalWeakApply (fun y a ↦ ActualCarriers.pencil (extendedProjectedStress ext F y) (EuclideanSpace.single a 1))
      (reducedZerothProjection n ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F)
      (fun y ↦ (euclideanComplexInclusion (u y)).ofLp) (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (u y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (r y)).ofLp) O) :
    ∀ x ∈ D, ‖linearizedMetric F packet x - H x‖ ≤ projectedStressResidualConstant hn *
      ‖r x - (WithLp.toLp 2 (stressSource (projectedStress F) H x) : E)‖ := by
  intro x hx
  let z : E := r x - WithLp.toLp 2 (stressSource (projectedStress F) H x)
  have hxR : x ∈ ball 0 (OriginalBoundary.R hn) := ball_subset_ball (OriginalBoundary.b_lt_R hn).le (hDb hx)
  have hxeOpen : x ∈ ball ext.center ext.radius := by simpa only [hc,hb] using hDb hx
  have hxe := ball_subset_closedBall hxeOpen
  have hclose (i : Fin n) := (row_of_local_margin ext F γ hQ hmargin x hxeOpen i).trans_le hγ
  have hKs : ({x} : Set E) ⊆ ball 0 (OriginalBoundary.R hn) := singleton_subset_iff.mpr hxR
  have frameX := projectedStress_tensorFrame_of_cNorm_closeness hn isOpen_ball isCompact_singleton hKs hF hi hr hclose (mem_singleton x)
  have bound := projectedStress_residual_coefficient_le hn isOpen_ball isCompact_singleton hKs hF hi hr hclose (mem_singleton x)
  have hF₂ : ContDiffAt ℝ 2 F x := (hF.contDiffAt (isOpen_ball.mem_nhds hxR)).of_le (by simp)
  have red (j : Fin n) : reducedOperator F (projectedStress F) u x j = r x j := by
    apply Complex.ofReal_injective
    exact (physicalWeakApply_extendedProjectedStress_eq_reducedOperator ext F hxe hF₂ (hr x hxR) (hu.differentiable (by simp) x) j).symm.trans (congrFun (hp (hDO hx)) j)
  have hcoord (j : Fin n) : reducedOperator F (projectedStress F) u x j - (1/2:ℝ) * tensorPairing (projectedStress F x j) (H x) = z j := by rw [red]; rfl
  have hg' : linearizedMetric F packet x = linearizedMetric F (completedVariation F u H) x := by
    funext i j
    simp only [linearizedMetric,partialDeriv,(hg x hx).fderiv_eq]
  rw [hg',completedVariation_error_eq_inverseGram isOpen_ball hF hu.contDiffOn hi hr hH.contDiffOn hxR (hsym x) (projectedStress F) frameX.2.1 frameX.2.2]
  simp_rw [hcoord]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hp' := CurrentMean.norm_inverseGramReconstruction_le (projectedStress F x) (fun j ↦ z j)
  rw [inverseGramReconstruction_eq_sum] at hp'
  calc
    _ ≤ 2 * (∑ i, ∑ j, |(stressGram (projectedStress F x))⁻¹ i j| * |z j| * ‖projectedStress F x i‖) := mul_le_mul_of_nonneg_left hp' (by norm_num)
    _ ≤ 2 * (∑ i, ∑ j, |(stressGram (projectedStress F x))⁻¹ i j| * ‖z‖ * ‖projectedStress F x i‖) := by
      gcongr with i j
      exact PiLp.norm_apply_le z j
    _ = (2 * (∑ i, ∑ j, |(stressGram (projectedStress F x))⁻¹ i j| * ‖projectedStress F x i‖)) * ‖z‖ := by
      simp only [Finset.sum_mul,mul_assoc]
      congr 1; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right bound (norm_nonneg z)
end JanetCartan.PhysicalPairs.OriginalTensorLag
end
public meta section
set_option maxHeartbeats 1300000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalTensorLag
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalTensorLag
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (h : Expr) : Nat → Expr | 0 => h | j+1 => down (.proj ``And 1 h) j
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
elab "transfer_original_tensor_lag " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (pkt ++ `packet)).type (some 50) fun p _ => do
    let pt := p[:49].toArray
    let b := pt[:37].toArray
    let gf ← inferType (a (hist ++ `index) pt)
    let g := gf.getAppArgs
    let fix := g[:23].toArray
    let d := pt[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := pt[1]!
    let γ := g[23]!
    let hγType ← mkAppM ``LE.le #[γ,a `JanetCartan.RawPrimary.ambientStrainFrameThreshold #[n,hn]]
    let hg := part (a (hist ++ `measured_history) pt) 0
    let dyn := #[pt[37]!,hg] ++ pt[39:43].toArray
    let now := pt[:36].toArray ++ dyn
    let current := a `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected now
    let prop := Expr.proj ``Subtype 1 current
    let F := Expr.proj ``Subtype 0 current
    let tensor := a (pkt ++ `tensor) p
    if piece.getNat == 0 then
      let raw := ((← getConstInfo (pkt ++ `tensor)).value! (allowOpaque := true)).beta p
      let pf := a (ns ++ `actual_tensor_symmetric) raw.getAppArgs
      discard <| store (ns ++ `tensor_symmetric) p pf false (some ((← inferType pf).replace fun e => if e == raw then some tensor else none))
      return
    let χ := a `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂ fix
    let hDO ← mkAppM (ns ++ `original_inner) #[χ]
    let hDb ← mkAppM (ns ++ `original_frame_ball) #[χ,a (masks ++ `χ₂_support_chart) fix,a (masks ++ `chart_in_coefficient_ball) fix]
    let corePDE := a `JanetCartan.PhysicalPairs.OriginalPacketPDE.core_equation p
    let eqt := (← inferType corePDE).getAppArgs
    let O := eqt.back!
    let germ := a (pkt ++ `core_germ) p
    let germTerm := ((← getConstInfo (pkt ++ `core_germ)).value! (allowOpaque := true)).beta p
    unless germTerm.isAppOf (pkt ++ `realize_germ) do throwError "different signed packet core germ"
    let D := germTerm.getAppArgs[2]!
    let pdeRaw := ((← getConstInfo `JanetCartan.PhysicalPairs.OriginalPacketPDE.core_equation).value! (allowOpaque := true)).beta p
    unless pdeRaw.isAppOf ( `JanetCartan.PhysicalPairs.OriginalPacketPDE.from_global_and_core_tests ) do throwError "unexpected signed PDE producer"
    let rr := pdeRaw.getAppArgs[8]!
    let packet := (← inferType germ).bindingBody!.bindingBody!.getAppArgs[3]!
    withLocalDeclD `graphWidthForStrain hγType fun hγ => do
      let pf := a (ns ++ `from_true_pencil) #[d,hn,fix[4]!,fix[5]!,fix[6]!,F,part prop 0,part prop 1,part prop 2,γ,hγ,
        part (a `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.current_frame_bounds (g ++ dyn)) 0,
        a `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.current_frame_margin (g ++ dyn),D,O,hDO,hDb,a (pkt ++ `solved) p,rr,tensor,packet,
        a (pkt ++ `solved_smooth) p,a (pkt ++ `tensor_smooth) p,a (ns ++ `tensor_symmetric) p,germ,corePDE]
      let error := a `JanetCartan.PhysicalPairs.OriginalResidualEmbedding.error p
      forallBoundedTelescope (← inferType pf) (some 2) fun y ty => do
        let args := ty.getAppArgs
        let rhs := args.back!
        let nr := rhs.appArg!
        let resultType := ty.replace fun e => if e == nr.appArg! then some (mkApp error y[0]!) else none
        discard <| store (ns ++ `strain_to_original_error) (b ++ #[hγ] ++ p[37:].toArray) pf false (some (← mkForallFVars y resultType))
transfer_original_tensor_lag 0
transfer_original_tensor_lag 1
end JanetCartan.PhysicalPairs.OriginalTensorLag
end
