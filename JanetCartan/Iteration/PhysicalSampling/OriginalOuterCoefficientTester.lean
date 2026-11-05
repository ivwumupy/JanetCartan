module

public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterCoefficientKernel
public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTester
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightBridge
public meta import Lean

/-!
# Outer μ, aggregate half weight, and the actual scalar46 family

Instantiate the restored native coordinate kernel with 71's original source
cutoff, no new exterior cutoff. Its norm is bounded by the very same scalar
family deviation: use its already constructed finite full-band continuum mean.
The final construction consumes this deviation from the one positive sampler.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalOuterTesterApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalSampling
private def sf := root ++ `OriginalScalarFamily
private def ext := root ++ `OriginalOuterWeights
private def ofam := `JanetCartan.PhysicalMean.OriginalWeightBridge.Original
private def dest := root ++ `OriginalOuterTester
private def selected := `JanetCartan.PhysicalSeed.SelectedBoundary
private def save (name : Name) (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let t ← instantiateMVars (← mkForallFVars xs (← inferType e))
  let v ← instantiateMVars (← mkLambdaFVars xs e)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar || t.hasSorry || v.hasSorry then
    throwError "outer scalar46: open {name}"
  let name := dest ++ name
  addDecl (.thmDecl {name,levelParams := [],type := t,value := v}) (forceExpose := true)
  return mkAppN (mkConst name) xs

elab "assemble_original_outer_scalar46_kernel" : command => liftTermElabM <| withTransparency .default do
  forallBoundedTelescope (← getConstInfo (sf ++ `scalar_band_kernel_eq)).type (some 46) fun x _ => do
    let fixed := x[:22].toArray
    let D := mkAppN (mkConst (sf ++ `kernel)) x
    let eq := mkAppN (mkConst (sf ++ `scalar_band_kernel_eq)) x
    let (hn,φ,det) ← forallBoundedTelescope (← inferType eq) (some 5) fun y t => do
      let ab := t.getAppArgs
      let lhs := ab[1]!.getAppArgs
      let some ph := ab[2]!.find? (fun e => e.isAppOf `JanetCartan.rawPrimaryPhaseDifference && !e.hasLooseBVars)
        | throwError "outer scalar46: original phase absent"
      let some b := ab[2]!.find? (·.isAppOfArity `JanetCartan.PhysicalForwardMean.forwardScalarBandMask 4)
        | throwError "outer scalar46: original forward detector absent"
      return (lhs[lhs.size-5]!,← mkLambdaFVars #[y[0]!,y[2]!,y[4]!,y[3]!] ph,
        ← mkLambdaFVars #[y[0]!] b.getAppArgs[1]!)
    let pl := mkAppN (mkConst (root ++ `OriginalCoefficientTester.one_on_coefficient_support)) fixed
    let (χ,row) ← forallBoundedTelescope (← inferType pl) (some 3) fun z t => do
      let some χ := (← inferType z[2]!).find? (·.isAppOfArity (selected ++ `χcoeff) 21)
        | throwError "outer scalar46: coefficient cutoff missing"
      return (χ,← mkLambdaFVars z[:2].toArray t.getAppArgs[1]!)
    let hc ← mkAppM `ContDiff.continuous #[mkAppN (mkConst (selected ++ `fact62)) χ.getAppArgs]
    let hr := mkAppN (mkConst (selected ++ `fact63)) χ.getAppArgs
    let I := (← whnf (← inferType D)).bindingDomain!
    withLocalDeclD `i I fun i => do
      let oc := fixed ++ #[i,x[43]!,mkApp D i]
      let Dout ← mkLambdaFVars #[i] (mkAppN (mkConst (ofam ++ `scalarKernel)) oc)
      let fact := mkAppN (mkConst (ofam ++ `scalarKernel_coordinate_factor)) oc
      let coef ← forallBoundedTelescope (← inferType fact) (some 5) fun v t => do
        let a := t.getAppArgs[2]!.getAppArgs[4]!.appArg!
        mkLambdaFVars #[i,v[2]!] a
      let oe ← mkLambdaFVars #[i] fact
      let B := mkAppN (mkConst (ext ++ `B)) fixed
      let ψ := mkAppN (mkConst (ext ++ `ψ)) fixed
      let w := mkApp (mkConst (root ++ `OriginalWindow.window)) x[2]!
      let fi ← synthInstance (← mkAppM ``Fintype #[I])
      let args : Array (Option Expr) := #[some I,some fi,none,none,none] ++
        #[hn,B,ψ,w,D,Dout,φ,det,coef,row,χ,hc,hr,pl,eq,oe].map some
      discard <| save `kernel_action x (← mkAppOptM (root ++ `OriginalCoefficientTester.restrict_outer_native) args)

/-- No exterior deviation assertion is necessary: the original22 comparison
transfers the interior deviation and the actual scalar46 input supplies the
full continuum mean. No new choice of a shift is made. -/
elab "apply_original_inner_deviation_to_outer_scalar46" : command => liftTermElabM <| withTransparency .default do
  forallBoundedTelescope (← getConstInfo (sf ++ `original_inputs)).type (some 46) fun x _ => do
    let inputs := mkAppN (mkConst (sf ++ `original_inputs)) x
    forallBoundedTelescope (← inferType inputs) (some 2) fun dyhp _ => do
      let fixed := x[:22].toArray
      let J := x[43]!
      let D := mkAppN (mkConst (sf ++ `kernel)) x
      let w := mkApp (mkConst (root ++ `OriginalWindow.window)) x[2]!
      let one ← mkNumeral (mkConst ``Real) 1
      let hw ← mkAppM (root ++ `OriginalWindow.window_bounds) #[dyhp[1]!]
      withLocalDeclD `mesh (mkConst ``Real) fun h => do
        let b := mkAppN (mkConst (ofam ++ `outer_scalar_common_event_bound)) (fixed ++ #[J,w,one,h,hw])
        forallBoundedTelescope (← inferType b) (some 4) fun admiss _ => do
          let hh := admiss[0]!
          let hU := admiss[3]!
          let U ← forallBoundedTelescope (← inferType hU) (some 3) fun y t => do
            let v := t.getAppArgs[0]!.getAppArgs.back!
            mkLambdaFVars y v
          let hasInput := mkAppN inputs (dyhp ++ #[h,← mkAppM `ne_of_gt #[hh]])
          let mean := Expr.proj ``And 1 hasInput
          let C := (← inferType mean).getAppArgs.back!
          let left := mkAppN b (admiss ++ #[D,J,C])
          forallBoundedTelescope (← inferType left) (some 2) fun evt _ => do
            let bound := mkAppN left (evt.push mean)
            discard <| save `native_bound_of_common_deviation (x ++ dyhp ++ #[h] ++ admiss ++ evt) bound
            let act := mkAppN (mkConst (dest ++ `kernel_action)) (x ++ #[h,U])
            let result ← mkAppM ``And.intro #[← mkAppM `le_trans #[Expr.proj ``And 0 act,bound],Expr.proj ``And 1 act]
            discard <| save `of_common_deviation (x ++ dyhp ++ #[h] ++ admiss ++ evt) result
  logInfo "original scalar46 -> actual exterior χ, restored incidence*spectator mask, full √μ √|η| aggregate and same χcoeff with exterior norm from the one inner deviation"

end JanetCartan.PhysicalSampling.OriginalOuterTesterApplication
end

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
assemble_original_outer_scalar46_kernel
apply_original_inner_deviation_to_outer_scalar46
