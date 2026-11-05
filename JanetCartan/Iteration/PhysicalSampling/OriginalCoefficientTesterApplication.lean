module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarEventInputs
public meta import Lean.Elab.Command

/-!
# Contract the actual same-family native scalar tester

The only source-coordinate identity used below is the already constructed
`OriginalScalarFamily.scalar_band_kernel_eq`. Its phase, detector, Fourier
factor, square-root frequency, dyadic band and row cutoff are read *from that
identity*. The common multiplier is read from the actual selected coefficient
plateau. The three final parameters (mesh, shifts, prefix) remain free: the
parent uses the shifts of its one event, not another sampling theorem.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalCoefficientTesterApplication
open Lean Meta Elab Command

private def sampling := `JanetCartan.PhysicalSampling
private def family := sampling ++ `OriginalScalarFamily
private def tester := sampling ++ `OriginalCoefficientTester
private def selected := `JanetCartan.PhysicalSeed.SelectedBoundary

/-- An actual representation and contractive norm comparison, not a hypothesis
that a bounded scalar tester with the right kernel already exists. -/
elab "apply_original_scalar_coefficient_tester" : command => liftTermElabM do
  let nativeName := family ++ `scalar_band_kernel_eq
  forallBoundedTelescope (← getConstInfo nativeName).type (some 46) fun x _ => do
    unless x.size == 46 do throwError "coefficient tester: lost native scalar46"
    let fixed := x[:22].toArray
    let hkernel := mkAppN (mkConst nativeName) x
    let (hn,φ,b) ← forallBoundedTelescope (← inferType hkernel) (some 5) fun y eq => do
      unless y.size == 5 && eq.isAppOfArity ``Eq 3 do
        throwError "coefficient tester: expected row, original band, color/node, physical point, original frequency"
      let lhs := eq.getAppArgs[1]!
      let rhs := eq.getAppArgs[2]!
      unless lhs.isAppOf ``PhysicalSamplingShells.scalarBandKernel && rhs.isAppOfArity ``HMul.hMul 6 do
        throwError "coefficient tester: original coordinate equality changed"
      let some φ := rhs.find? (fun e => e.isAppOf ``rawPrimaryPhaseDifference && !e.hasLooseBVars)
        | throwError "coefficient tester: original finite-rate phase lost"
      let some b := rhs.find? (·.isAppOfArity ``PhysicalForwardMean.forwardScalarBandMask 4)
        | throwError "coefficient tester: original half-weighted detector missing"
      let a := lhs.getAppArgs
      return (a[a.size - 5]!, ← mkLambdaFVars #[y[0]!,y[2]!,y[4]!,y[3]!] φ,
        ← mkLambdaFVars #[y[0]!,y[1]!,y[4]!] b)
    let plateau := mkAppN (mkConst (tester ++ `one_on_coefficient_support)) fixed
    let (χ,row) ← forallBoundedTelescope (← inferType plateau) (some 3) fun z eq => do
      unless z.size == 3 && eq.isAppOfArity ``Eq 3 do throwError "coefficient tester: missing support collar"
      let some χ := (← inferType z[2]!).find? (·.isAppOfArity (selected ++ `χcoeff) 21)
        | throwError "coefficient tester: selected coefficient cutoff was replaced"
      return (χ,← mkLambdaFVars #[z[0]!,z[1]!] eq.getAppArgs[1]!)
    let geometry := χ.getAppArgs
    let hc ← mkAppM ``ContDiff.continuous #[mkAppN (mkConst (selected ++ `fact62)) geometry]
    let hr := mkAppN (mkConst (selected ++ `fact63)) geometry
    let ψ := mkAppN (mkConst (sampling ++ `OriginalWeights.φ)) fixed
    let B := mkAppN (mkConst (sampling ++ `OriginalWeights.B)) fixed
    let w := mkApp (mkConst (sampling ++ `OriginalWindow.window)) x[2]!
    let D := mkAppN (mkConst (family ++ `kernel)) x
    let h ← mkAppM (tester ++ `restrict_native_of_band_formula) #[hn,B,ψ,w,D,φ,b,row,χ,hc,hr,plateau,hkernel]
    let type ← instantiateMVars (← mkForallFVars x (← inferType h))
    let value ← instantiateMVars (← mkLambdaFVars x h)
    if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
        type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
      throwError "coefficient tester: actual curve/measure/bump coordinates did not close"
    addDecl (.thmDecl { name := family ++ `coefficient_tester, levelParams := [], type, value }) (forceExpose := true)
    logInfo "actual indexed scalar46 → same-prefix χcoeff tester, exact original native kernel and norm contraction"

end JanetCartan.PhysicalSampling.OriginalCoefficientTesterApplication
