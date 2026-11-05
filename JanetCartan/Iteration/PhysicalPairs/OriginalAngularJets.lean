module
public import JanetCartan.Iteration.PhysicalPairs.AngularMassJets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfiles
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate
/-! # Original whole-source node: variation instead of a derivative hypothesis

The original source53/Graph42 producer identifies the derivative of the
whole wave for its actual `WideInput` by commuting the same uncut response
through the original angular integral. Apply its native smoothness, original
open shift window and exact density. Only the **atomic** slow amplitude and
mixed-phase jets remain in this estimate, not a high derivative of the
complete angular wave. The final Picard datum and its uniform variation are
not chosen here. Consumer: `OriginalSelectedWaves.GenuineNodeProfile` for
`main:eq:pair-error`.
-/
public meta section
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 1800000
namespace JanetCartan.PhysicalPairs.OriginalAngularJets
open scoped Matrix.Norms.Frobenius
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalAngularJets
private abbrev Args := Array (Name × Expr)
private def atKey (xs : Args) (k : Name) : MetaM Expr := do
  let some (_,v) := xs.find? (·.1 == k) | throwError "native angular node: missing actual operand {k}"
  return v
private def arguments (k : Name) (v : Expr) : MetaM Args := do
  let v := v.headBeta
  unless v.isAppOf k do throwError "native angular node: expected {k}, found {v.getAppFn}"
  let mut t := (← getConstInfo k).type
  let mut xs := #[]
  for b in v.getAppArgs do
    let .forallE key _ rest _ := t | throwError "native angular node: malformed producer {k}"
    xs := xs.push (key,b)
    t := rest
  return xs
private def applyThrough (name last : Name) (xs : Args) : MetaM Expr := do
  let mut t := (← getConstInfo name).type
  let mut v := mkConst name
  while let .forallE key _ rest _ := t do
    v := mkApp v (← atKey xs key)
    if key == last then return v
    t := rest
  throwError "native angular node: missing end {last} of {name}"
run_cmd liftTermElabM do
  let whole := `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedDerivative_eq_integral
  let integral := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Whole.derivative_integral
  let info ← getConstInfo integral
  forallBoundedTelescope info.type (some 69) fun all t => do
    unless all.size == 69 && t.isAppOfArity ``Eq 3 do throwError "native angular node: missing actual physical integral at original69"
    let vals ← arguments whole ((info.value! (allowOpaque := true)).beta all)
    let raw ← arguments `JanetCartan.rawPrimaryDemodulatedIntegral t.appArg!
    let S ← atKey raw `S
    let A ← atKey raw `A
    let g := t.getAppArgs[1]!.appFn!
    let hg ← mkLambdaFVars all[67:].toArray (mkAppN (mkConst integral) all)
    let p := all[:67].toArray
    let hS ← applyThrough `JanetCartan.RawPrimary.contDiffOn_fullPhase `hphase vals
    let hA ← applyThrough `JanetCartan.CorrectedAtoms.contDiffOn_fullCorrectedDerivativeAmplitude `hresponse vals
    let hτ ← atKey vals `hτ
    let hshift ← atKey vals `hshift
    let ζ ← atKey raw `ζ
    let n ← atKey vals `n
    let Ω ← atKey vals `Ω
    let X ← atKey vals `X
    let V ← atKey vals `V
    let z ← atKey vals `z
    let τ ← atKey vals `τ
    let sliced := fun (h : Expr) => do
      let ty ← inferType h
      let fn := ty.getAppArgs[ty.getAppNumArgs-2]!
      let ft ← whnfR (← inferType fn)
      mkAppOptM ``AngularMassJets.slice_smooth #[n,ft.bindingBody!,none,none,Ω,X,V,z,ζ,τ,hτ,hshift,fn,h]
    let s ← sliced hS
    let a ← sliced hA
    let known := #[(`g,g),(`hg,hg),(`S,S),(`A,A),(`hS,s),(`hA,a),(`ζ,ζ)] ++ vals
    let proof ← applyThrough ``AngularMassJets.point_grade `hg known
    discard <| store (ns ++ `whole_derivative) p proof
  logInfo "Original67 whole uncut derivative: original dyadic support, original weighted wide density with its true L¹ mass and exact fixed whole-source solver; only individual angular amplitude and mixed phase jets, not complete-wave jets, are used."
end JanetCartan.PhysicalPairs.OriginalAngularJets
end
