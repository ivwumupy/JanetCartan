module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.Basic
public import JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceDiscrepancy
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSourceDiscrepancy
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Full tensor strain on the actual sampling graph

The original sampling graph supplies its current immersion, full normal rank,
extended-frame margin, full uncut ambient response and classical tensor
equation. Only the original numerical frame tolerance and the supplied
tensor's symmetry occur in this intermediate comparison. The actual primary
quadratures discharge both in the subsequent native application.
Consumer: `main:eq:primary-strain`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate

private theorem response_germ {n N : ℕ} (D : Set (Euclidean n))
    (P Q : Euclidean n → Euclidean N) (h : P = Q) :
    ∀ x ∈ D, P =ᶠ[𝓝 x] Q :=
  fun _ _ ↦ Filter.Eventually.of_forall (fun y ↦ congrFun h y)

private theorem extension_mem {n : ℕ} (ext : BallExtension.Parameters (Euclidean n))
    {b : ℝ} (hc : ext.center = 0) (hb : ext.radius = b)
    {x : Euclidean n} (hx : x ∈ ball (0 : Euclidean n) b) :
    x ∈ closedBall ext.center ext.radius := by
  simpa only [hc,hb] using ball_subset_closedBall hx

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
private def graph := `JanetCartan.PhysicalInitialization.OriginalRegular.Graph
private def current := `JanetCartan.PhysicalInitialization.OriginalRegular.Current
private def full := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def response := `JanetCartan.PhysicalSampling.OriginalGraphResponse
private def source := `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular

private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private def part (e : Expr) : Nat → Expr
  | 0 => Expr.proj ``And 0 e
  | i+1 => part (Expr.proj ``And 1 e) i
private def termWith (p : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith p code)
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original tensor strain: unresolved original input in {key}"
    let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
    unless missing.isEmpty do throwError "original tensor strain: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original graph tensor strain {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "On the original sampling graph the SAME full uncut ambient response obeys the tensor strain bound by its actual smooth source-minus-identity discrepancy. Geometry, frame margin, classical equation, source forcing and full response identity are applied internally. The original numerical frame tolerance and tensor symmetry are explicit; no source-decay or response-success premise (main:eq:primary-strain; main:eq:lag-strain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original tensor strain: nonstandard axioms {ax}"
  logInfo m!"PASS original graph tensor strain {key}/{p.size}: {ax}"

/-- Build the comparison on the original graph42. The actual native primary
will supply the numerical tolerance and both compact symmetric tensors. -/
elab "derive_original_graph_tensor_strain" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (response ++ `B)).type (some 42) fun p _ => do
    unless p.size == 42 do throwError "original tensor strain: graph42 changed"
    let rawB := (((← getConstInfo (response ++ `B)).value! (allowOpaque := true)).beta p).headBeta
    unless rawB.isAppOfArity (full ++ `B) 38 do
      throwError "original tensor strain: original full uncut response changed"
    let weak := rawB.getAppArgs
    let fixed := weak[:23].toArray
    let reached ← inferType p[37]!
    unless reached.isAppOfArity ``LE.le 4 && reached.getAppArgs[2]!.isAppOfArity (graph ++ `S) 34 do
      throwError "original tensor strain: original reached graph bound changed"
    let g := reached.getAppArgs[2]!.getAppArgs
    let frameParams := g ++ p[36:42].toArray
    let frame := app (graph ++ `current_frame_bounds) frameParams
    let hmargin := app (graph ++ `current_frame_margin) frameParams
    let projected := app (current ++ `projected) weak
    let geometry := Expr.proj ``Subtype 1 projected
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let tolerance := app `JanetCartan.RawPrimary.ambientStrainFrameThreshold #[n,p[1]!]
    withLocalDeclD `hFrameTolerance (← mkAppM ``LE.le #[g[23]!,tolerance]) fun hTolerance => do
      let applyResponse := app (full ++ `apply) weak
      forallBoundedTelescope (← inferType applyResponse) (some 1) fun tensor _ => do
        let t := tensor[0]!
        let fullEq := mkApp applyResponse t
        let eq ← inferType fullEq
        unless eq.isAppOfArity ``Eq 3 && eq.getAppArgs[2]!.isAppOfArity `JanetCartan.AmbientResponse.completedVariation 5 do
          throwError "original tensor strain: full response is not the original completion"
        let packet := eq.getAppArgs[1]!
        let completed := eq.getAppArgs[2]!
        let operands := completed.getAppArgs
        let F := operands[2]!
        let u := operands[3]!
        let H := operands[4]!
        let symm ← termWith [(`H,H)] "∀ x, (H x).IsSymm"
        withLocalDeclD `hTensorSymmetric symm fun hsym => do
          let chi := app (regular ++ `χ₂) fixed
          let hDO ← mkAppM `JanetCartan.PhysicalPairs.OriginalTensorLag.original_inner #[chi]
          let hDb ← mkAppM `JanetCartan.PhysicalPairs.OriginalTensorLag.original_frame_ball
            #[chi,app (masks ++ `χ₂_support_chart) fixed,app (masks ++ `chart_in_coefficient_ball) fixed]
          let dotype ← inferType hDO
          let D := dotype.getAppArgs[dotype.getAppNumArgs-2]!
          let pde := app (source ++ `physical_eqOn_tensor) (weak.push t)
          let pdetype ← inferType pde
          unless pdetype.isAppOfArity ``Set.EqOn 5 do
            throwError "original tensor strain: classical original PDE changed"
          let O := pdetype.getAppArgs[4]!
          let forcingEq := app (source ++ `tensor_forcing_eq_stress) (weak.push t)
          let fet ← inferType forcingEq
          let forcing := fet.getAppArgs[1]!
          let input ← mkAppM ``DFunLike.coe #[app (source ++ `tensor_input) weak]
          let input := mkApp input t
          let discrepancy ← mkAppM ``DFunLike.coe #[app (source ++ `discrepancy) weak]
          let discrepancy := mkApp discrepancy input
          let r ← mkAppM ``HAdd.hAdd #[forcing,discrepancy]
          let hu := app `JanetCartan.PhysicalPrimary.OriginalUncutSolver.uncut_solver_smooth (weak.push input)
          let hH := Expr.proj ``And 0 (Expr.proj ``Subtype 1 t)
          let germ := app ``response_germ #[n,dim,D,packet,completed,fullEq]
          let bound := app `JanetCartan.PhysicalPairs.OriginalTensorLag.from_true_pencil
            #[p[0]!,p[1]!,fixed[4]!,fixed[5]!,fixed[6]!,F,
              part geometry 0,part geometry 1,part geometry 2,g[23]!,hTolerance,
              part frame 0,hmargin,D,O,hDO,hDb,u,r,H,packet,hu,hH,hsym,germ,pde]
          let target ← inferType bound
          let proof ← forallBoundedTelescope target (some 2) fun point result => do
            unless point.size == 2 && result.isAppOfArity ``LE.le 4 do
              throwError "original tensor strain: pointwise full-strain comparison changed"
            let x := point[0]!
            let hx := point[1]!
            let hxb := mkAppN hDb #[x,hx]
            let hxe := app ``extension_mem #[n,fixed[4]!,app `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,p[1]!],
              fixed[5]!,fixed[6]!,x,hxb]
            let T := result.getAppArgs[2]!.appArg!
            let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,p[1]!]
            let finished := app (root ++ `bound_after_tensor_forcing_cancellation)
              #[n,dim,fixed[4]!,F,H,forcing,discrepancy,forcingEq,x,hxe,T,C,mkAppN bound point]
            mkLambdaFVars point finished
          let conclusion := (← inferType proof).replace fun e =>
            if e == rawB then some (app (response ++ `B) p) else none
          save `graph_tensor_strain_le_discrepancy (p ++ #[hTolerance,t,hsym]) proof conclusion

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate
end
