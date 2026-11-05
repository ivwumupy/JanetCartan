module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeSplit
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceChartRepresentative
/-! # The physical source summand is the SAME whole native inverse field

Join the actual86 source-data amplitude to actual89's full native field on the
entire original source chart. Only the old centered representative is removed;
no observation, prefix, original real adjoint, or global Q0 is changed. This is
the precise source-D input of the complete single-node R-profile for pairs
(`main:eq:mean-final-amplitude`, `main:prop:current-waves`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentityTemplate
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity
private def native := `JanetCartan.PhysicalPairs.OriginalSourceNative
private def split := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def remainingType (key : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for v in args do
    unless type.isForall do throwError "physical native source: changed telescope"
    type := type.bindingBody!.instantiate1 v
  return type
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "physical native source: unresolved {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"physical native source: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "The actual physical whole-source amplitude equals its SAME complete native individual inverse field on the entire original source chart, with the same mask, adjoint, prefix and global Q0 (main:prop:current-waves, main:eq:mean-final-amplitude)."
  liftM <| IO.eprintln s!"physical native source: kernel passed {name}"

elab "identify_original_complete_native_source " which:num : command => liftTermElabM do
  unless which.getNat < 4 do throwError "physical native source: unknown publication mode"
  PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p _ => do
    unless p.size == 53 do throwError "physical native source: expected actual89 prefix53"
    let h := app (native ++ `canonical_derivative_eq_native) p
    let statement := ((← getConstInfo (native ++ `identity_statement)).value! (allowOpaque := true)).beta p
    forallBoundedTelescope statement (some 3) fun sample eq => do
      unless sample.size == 3 && eq.isAppOfArity ``Eq 3 do
        throwError "physical native source: source/torus/sample identity changed"
      let u := sample[0]!
      let i := sample[2]!
      let field := eq.getAppArgs[2]!.appFn!
      let pre := p ++ #[u,i]
      if which.getNat == 0 then
        save `nativeAmplitude pre field (← inferType field) true
        return
      let D := app (ns ++ `nativeAmplitude) pre
      let source := p[:50].toArray ++ #[p[52]!,u,i]
      let S := app (split ++ `sourceAmplitude) source
      let gt ← remainingType `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.germ_statement source
      forallBoundedTelescope gt (some 2) fun point _ => do
        unless point.size == 2 do throwError "physical native source: original source-chart tail changed"
        let chart := (← inferType point[1]!).getAppArgs[3]!
        unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
          throwError "physical native source: not the original full source chart"
        let all := pre ++ point
        let dim := (← inferType point[0]!).appArg!
        if which.getNat == 1 then
          let z := app `JanetCartan.torusQuotient #[dim,point[0]!]
          let equation := mkAppN h #[u,z,i]
          let rep := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.representative_on_original_chart
            (chart.getAppArgs ++ point)
          let remove ← mkAppM ``congrArg #[field,rep]
          let proof ← mkAppM ``Eq.trans #[equation,remove]
          save `source_eq_native all proof (← mkEq (mkApp S point[0]!) (mkApp D point[0]!))
        else if which.getNat == 2 then
          let openChart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs
          let heq ← withLocalDeclD `y (← inferType point[0]!) fun y => do
            withLocalDeclD `hy (← mkAppM ``Membership.mem #[chart,y]) fun hy =>
              mkLambdaFVars #[y,hy] (app (ns ++ `source_eq_native) (pre ++ #[y,hy]))
          let matrix := (← inferType S).bindingBody!.getAppArgs
          let N := matrix[0]!.appArg!
          let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.germ_of_chart_eq
            #[dim,N,S,D,chart,openChart,heq,point[0]!,point[1]!]
          save `germ_on_original_chart all proof (← inferType proof)
        else
          withLocalDeclD `j (mkConst ``Nat) fun j => do
            let matrix := (← inferType S).bindingBody!.getAppArgs
            let N := matrix[0]!.appArg!
            let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude_jets_of_germ
              #[dim,N,S,D,point[0]!,app (ns ++ `germ_on_original_chart) all,j]
            save `jets_on_original_chart (all.push j) proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentityTemplate
end
