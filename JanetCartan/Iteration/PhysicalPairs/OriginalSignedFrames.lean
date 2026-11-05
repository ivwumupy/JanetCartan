module
public import JanetCartan.Iteration.PhysicalPairs.NativeFramePhase
public import JanetCartan.Iteration.PhysicalPairs.SampledQuadrature
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! # Original signed phase representatives at the native graph's SAME threshold

Use the already admitted native coefficient budget `Op.AQ` with its actual
reserve and unchanged current map. The sharp joint scalar phase estimate is
selected before a history, external ξ, sign, pair, or Fourier cutoff. No extra
scale or equality of separately chosen phases is needed. The representative
is only a smooth extension of the actual colored carrier on the entire fixed
physical buffer times the genuine outer parameter cube.
`main:prop:pairs`, `app:ch_regular:eq:source-tail`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalSignedFrames
open PhysicalSeed PhysicalInitialization ProtectedFlow ProjectedStressFrame GeometricProfile CurrentCoefficientProfiles
open ActualCarriers CurrentFullPhase FrozenMenu

set_option quotPrecheck false in
local notation "menuProof(" hn "," hD "," assign "," radial "," r "," hr "," AQ "," hAQ ")" =>
  NativeFramePhase.representatives (fun g ↦ (OriginalBoundary.D hn).patches (assign g).1 (assign g).2)
    (fun g ↦ OriginalBoundary.T hn (assign g)) (fun g ↦ (hD.2.2.2.2.1 (assign g).1 (assign g).2).1) radial
    (isCompact_closedBall 0 (OriginalRegular.coreRadius hn r))
    (fun g ↦ ((OriginalRegular.core_spec hn hr).2.2.2 (assign g)).2) AQ hAQ

theorem menu_cost {n : ℕ} (hn : 5 ≤ n) {c C : ℝ} (hD : (OriginalBoundary.D hn).IsValid c C)
    {G : Type} [Fintype G] (assign : G → OriginalPatchIndex hn) (radial : G → ℝ)
    {r : ℝ} (hr : 0 < r) (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) :
    type_of% (menuProof(hn,hD,assign,radial,r,hr,AQ,hAQ)) := menuProof(hn,hD,assign,radial,r,hr,AQ,hAQ)

theorem at_history {n : ℕ} (hn : 5 ≤ n) (ext : BallExtension.Parameters (Euclidean n))
    (h0 : ext.center=0) (hb : ext.radius=OriginalBoundary.b hn) (F : Euclidean n → Euclidean (embeddingDimension n))
    {G : Type} (assign : G → OriginalPatchIndex hn) {r : ℕ} (hr : 3 ≤ r) {L : ℝ} (hL : 1 ≤ L)
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m)
    (fram : ∀ K : Set (Euclidean n), IsCompact K → HasDerivativeProfile K (extendedProjectedStress ext F) r L AQ) :
    ∀ g m, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.T hn (assign g)).data.localReference.stateRadius)
      (m+1) (projectedStress F) ≤ AQ (m+1)*L^(m-2) := by
  intro g m
  let T := OriginalBoundary.T hn (assign g)
  have hp : ∀ z ∈ T.data.localReference.stateDomain, z.1 ∈ ball (0 : Euclidean n) ext.radius := by
    rw [hb]; exact OriginalBoundary.stateDomain_subset_ball hn (assign g)
  rw [NativeFramePhase.raw_frame_on_state T ext h0 hp F]
  exact (fram _ (isCompact_closedBall _ _) (m+1)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hAQ _))

theorem enough (d : ℕ) : 3 ≤ RegularSector.FiniteEvolution.sectorLowOrder d := by
  simp only [RegularSector.FiniteEvolution.sectorLowOrder,RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    FourierIntegral.WholeImageGeometry.wholeImagePhaseReserve,FourierIntegral.LowBounds.primitiveNormalReserve]
  omega

theorem current_scale_one {S R : ℝ} (hS : 2 ≤ S) (hR : S ≤ R) (j : ℕ) : 1 ≤ currentCoefficientScale R j :=
  one_le_currentCoefficientScale (by linarith) j
end JanetCartan.PhysicalPairs.OriginalSignedFrames
end

public meta section
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalSignedFrames
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSignedFrames
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def ob := `JanetCartan.PhysicalSeed.OriginalBoundary
private def sb := `JanetCartan.PhysicalSeed.SelectedBoundary
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def a (q : Name) (xs : Array Expr) := mkAppN (mkConst q) xs
private def down (e : Expr) : Nat → Expr | 0 => e | k+1 => down (.proj ``And 1 e) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (down e k)

elab "construct_actual_signed_frame " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p family => do
    let g := family.getAppArgs
    let fixed := g[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let hn := fixed[1]!
    let original := #[n] ++ fixed[1:21].toArray
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,original[20]!]
    let sel := original.set! 20 cap
    let hpos := a (reg ++ `screened_pos) #[n,hn,a `JanetCartan.PhysicalInitialization.OriginalProtected.r original,
      a (sb ++ `rMeasure) sel,a `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 original,a (sb ++ `hrMeasure) sel]
    let r := (← inferType hpos).appArg!
    let gf := ((← getConstInfo (poly ++ `GraphFamily)).value! (allowOpaque := true)).beta g
    let graph := gf.getAppArgs[3]!
    let S := gf.getAppArgs.back!
    unless S.isAppOfArity (op ++ `S) 33 do throwError "missing SAME original operator-profile threshold"
    let early := p[:36].toArray
    let x := p[:37].toArray
    let safe := p[:43].toArray
    let old := a `JanetCartan.PhysicalPairs.OriginalWindow.S x
    let numeric := a `JanetCartan.PhysicalPairs.OriginalWindow.scaleThreshold #[p[36]!]
    let prev ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[old,S],p[38]!]
    let opReached ← mkAppM ``le_trans #[← mkAppM ``le_max_right #[old,S],p[38]!]
    let graphReached ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[graph,numeric],prev]
    let now := early ++ #[p[37]!,graphReached] ++ p[39:43].toArray
    let cg := ((← getConstInfo (quad ++ `group_phase)).value! (allowOpaque := true)).beta now
    unless cg.isAppOfArity (quad ++ `radialCarrier) 11 do throwError "missing native colors of radial carrier"
    let ca := cg.getAppArgs
    let G := ca[5]!
    let assign := ca[6]!
    let radial := ca[7]!
    let coeff := S.getAppArgs
    let AQ := a (op ++ `AQ) coeff
    let hAQ := a (op ++ `fact1) coeff
    let actualGroups := ((← getConstInfo G.getAppFn.constName!).value! (allowOpaque := true)).beta G.getAppArgs
    let fin ← synthInstance (mkApp (mkConst `Fintype [.zero]) actualGroups)
    let hD := a (ob ++ `hD) #[n,hn]
    let ht := (← inferType hD).getAppArgs
    if piece.getNat == 0 then
      let native := a (ns ++ `menu_cost) #[n,hn,ht[ht.size-2]!,ht.back!,hD,G,fin,assign,radial,r,hpos,AQ,hAQ]
      discard <| store (ns ++ `joint_cost) early native
      logInfo "original 36-field menu and raw frame budget, before every label"
      return
    let costs := a (ns ++ `joint_cost) early
    let price ← mkAppM ``Classical.choose #[costs]
    let hs ← mkAppM ``Classical.choose_spec #[costs]
    if piece.getNat == 1 then
      let D ← store (ns ++ `jointProfile) early price true
      let nonneg := Expr.proj ``And 0 hs
      discard <| store (ns ++ `jointProfile_nonneg) early nonneg false (some ((← inferType nonneg).replace fun e => if e == price then some D else none))
      logInfo "prehistory original phase-jet price selected once"
      return
    let D := a (ns ++ `jointProfile) early
    let hL := a (ns ++ `current_scale_one) #[S,p[37]!,a (op ++ `fact0) coeff,opReached,p[39]!]
    let L := (← inferType hL).appArg!
    let cont := a (op ++ `continuation) (coeff ++ #[p[37]!,opReached] ++ p[39:43].toArray)
    let profile := down cont 2
    let pe ← forallBoundedTelescope (← inferType profile) (some 2) fun ds _ => do
      mkLambdaFVars ds (.proj ``And 0 (mkAppN profile ds))
    let Q := a (quad ++ `Q) now
    let qbody := ((← getConstInfo (quad ++ `Q)).value! (allowOpaque := true)).beta now
    unless qbody.isAppOf `JanetCartan.ProjectedStressFrame.projectedStress do throwError "missing original raw immersion"
    let F := qbody.appArg!
    let frame := a (ns ++ `at_history) #[n,hn,fixed[4]!,fixed[5]!,fixed[6]!,F,G,assign,coeff[28]!,
      a (ns ++ `enough) #[p[0]!],L,hL,AQ,hAQ,pe]
    if piece.getNat == 2 then
      discard <| store (ns ++ `state_profile) safe frame
      logInfo "raw frame jets at the unchanged original coefficient reserve"
      return
    let hq := a (ns ++ `state_profile) safe
    let low ← withLocalDeclD `group G fun gg => mkLambdaFVars #[gg] (mkApp (a (quad ++ `Q_low) now) (mkApp assign gg))
    let ready := mkAppN (.proj ``And 1 hs) #[Q,a (quad ++ `Q_smooth) now,low,L,hL,hq]
    let chosen ← mkAppM ``Classical.choose #[ready]
    let rep ← store (ns ++ `representative) safe chosen true
    let proofs ← mkAppM ``Classical.choose_spec #[ready]
    for (name,pf) in [(`smooth,Expr.proj ``And 0 proofs),(`original_germ,part proofs 1),(`joint_jets,down proofs 2)] do
      let ty := (← inferType pf).replace fun e => if e == chosen then some rep else if e == price then some D else none
      discard <| store (ns ++ name) safe pf false (some ty)
    unless safe.size == 43 && early.size == 36 do throwError "lost original strictly prelabel frame slots"
    logInfo "actual radial scalar on the SAME original raw projected immersion: full buffer × original cube germ; sharp complete joint jets with prehistory D, using the already admitted threshold/reserve—no reselected start or phase comparison premise"
construct_actual_signed_frame 0
construct_actual_signed_frame 1
construct_actual_signed_frame 2
construct_actual_signed_frame 3
end JanetCartan.PhysicalPairs.OriginalSignedFrames
end
