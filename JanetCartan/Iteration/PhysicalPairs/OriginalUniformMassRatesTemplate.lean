module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformStageLag
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformStageSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalRealMass
import all JanetCartan.Iteration.PhysicalPairs.OriginalRealMass
import all JanetCartan.Iteration.PhysicalPairs.OriginalMassRates
/-! # Both original mass rates with constants before every later source

Keep b²(∑√μ)² and the true (λh)^(-q) lag, with arbitrary real r≥0 and
λ^(r+1) for size. The old rate algebra is unchanged; its inputs now use the
universal-before-source actual pair producers, so no chosen current wave family
enters the constant (`main:eq:pair-error`, `main:eq:pair-high-size`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformMassRatesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformMassRates
private def lag := `JanetCartan.PhysicalPairs.OriginalUniformStageLag
private def size := `JanetCartan.PhysicalPairs.OriginalUniformStageSize
private def metric := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform mass rates: later source/history escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking source-uniform exact mass rate {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME finite original signed correction retains both exact b²(Σ√μ)² manuscript rates, with constants BEFORE every later source family and true λ^(r+1) for real orders r≥0; no Fourier cutoff or cardinality replaces the complete derivative profile (main:eq:pair-error; main:eq:pair-high-size)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform mass rates: nonstandard axioms {axioms}"
  logInfo m!"source-uniform exact mass rate {key}/{p.size}: {axioms}"
elab "define_original_uniform_mass_price" : command => liftTermElabM do
  let ci ← getConstInfo (lag ++ `constant)
  forallBoundedTelescope ci.type (some 40) fun p _ => do
    let raw := (ci.value! (allowOpaque := true)).beta p
    unless raw.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageLag.totalPrice 5 do
      throwError "uniform mass rate: original total price changed"
    let a := raw.getAppArgs
    let price := app `JanetCartan.PhysicalPairs.OriginalMassRates.price (a[:3].toArray.push a[4]!)
    save `constant p price (← inferType price) true
elab "prove_original_uniform_mass_lag" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (lag ++ `coefficient_mass_lag)).type (some 52) fun p _ => do
    let fixed := p[:40].toArray
    let stem := p[:37].toArray ++ p[41:49].toArray
    let native := stem ++ #[p[49]!,p[51]!]
    let eq := app (metric ++ `off_metric) native
    let ee := (← inferType eq).getAppArgs
    let sub := ee[2]!.getAppArgs
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let rapid := app `JanetCartan.PhysicalPairs.OriginalUniformCorrectedLag.pointwise
      (p[:39].toArray.push (app `JanetCartan.PhysicalPairs.OriginalStageLag.accuracy #[p[39]!]))
    let A ← mkAppM ``Classical.choose #[rapid]
    let hR := app `JanetCartan.PhysicalPairs.OriginalStageSize.stage_one
      #[app `JanetCartan.PhysicalPairs.SampledHistory.S p[:37].toArray,p[41]!,
        app `JanetCartan.PhysicalPairs.SampledHistory.hS p[:37].toArray,p[42]!,p[43]!]
    let R := (← inferType hR).appArg!
    let bound := app (lag ++ `coefficient_mass_lag) p
    let result ← forallBoundedTelescope (← inferType bound) (some 2) fun y _ => do
      let hv := mkAppN bound y
      let ty := (← inferType hv).getAppArgs
      let mass := ty.back!.appArg!
      let full := app ``JanetCartan.PhysicalPairs.OriginalMassRates.keep_mass
        #[n,p[1]!,A,R,p[51]!,p[39]!,mass,ty[2]!,hR,hv]
      let t := (← inferType full).getAppArgs
      let add := t[2]!.appArg!.getAppArgs
      let proof := app (metric ++ `transfer)
        #[n,ee[1]!,sub[sub.size-2]!,sub.back!,eq,add[add.size-2]!,y[0]!,t.back!,full]
      mkLambdaFVars y proof
    let raw := ((← getConstInfo (root ++ `constant)).value! (allowOpaque := true)).beta fixed
    let target := (← inferType result).replace fun e => if e == raw then some (app (root ++ `constant) fixed) else none
    save `metric_lag p result target
elab "prove_original_uniform_mass_real_size" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (size ++ `coefficient_mass_size)).type (some 52) fun p _ => do
    let pre := p[:40].toArray
    let later := p[41:].toArray
    let D := app `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection.D pre
    let natural ← withLocalDeclD `order (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (app (size ++ `coefficient_mass_size) (pre ++ #[k] ++ later))
    let zero := mkApp natural (mkNatLit 0)
    let ty ← inferType zero
    let some S := ty.find? (·.isAppOfArity (sum ++ `correction) 47)
      | throwError "uniform real mass size: original correction changed"
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let hR := app `JanetCartan.PhysicalPairs.OriginalStageSize.stage_one
      #[app `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection.S pre,p[41]!,
        app `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection.hS pre,p[42]!,p[43]!]
    let R := (← inferType hR).appArg!
    let hl := app ``JanetCartan.PhysicalPairs.OriginalRealMass.carrier_pos #[R,hR]
    let lam := (← inferType hl).appArg!
    let rhs := ty.appArg!
    let mass := rhs.appArg!
    let scale := rhs.getAppArgs[4]!.appArg!.getAppArgs[4]!
    let proof := app `JanetCartan.PhysicalPairs.OriginalRealMass.all_real #[n,N,S,D,scale,mass,lam,hl,natural]
    save `size (pre ++ later) proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalUniformMassRatesTemplate
end
