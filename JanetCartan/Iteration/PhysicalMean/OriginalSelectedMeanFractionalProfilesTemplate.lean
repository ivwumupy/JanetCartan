module
public import JanetCartan.Iteration.PhysicalMean.CompletedMeanFractionalProfiles
public import JanetCartan.Iteration.PhysicalMean.CompletedMeanPrimitiveProfiles
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Apply the lossless real-order estimate to the actual mean

Metadata is checkable independently of the integer producer. Its execution
uses the checked SAME physicalMean54 integer theorem at every order and the
already supplied initial-to-current scale proof from its actual completion.
No integer-profile or scale-positivity hypothesis is appended to the public
original-data telescope (`main:eq:mean-size`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanFractionalProfilesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles
private def fields := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some v := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual real mean profile: missing checked body {key}"
  return (v.beta p).headBeta.consumeMData
private def save (p : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual real mean profile: missing original constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual real mean profile: additional analytic field escaped"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ `physicalMean_real_sobolev_profile
  liftM <| IO.eprintln s!"actual real mean profile: kernel checking {name}/{p.size}"
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual SAME original Schwartz mean/J/full source/Picard count at EVERY real nonnegative physical Sobolev order. Apply genuine integer58 profiles with the existing 2πξ split at CURRENT R. Exact exponent R^r, coefficient CphysicalMean_N(0)+CphysicalMean_N(ceil r), before history; no added analytic hypothesis or geometric threshold (main:eq:mean-size)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual real mean profile: nonstandard axioms {name}: {ax}"
  logInfo m!"actual real mean profile: checked SAME original field, lossless R^r, early integer cost, {p.size}/std3 {ax}"
elab "construct_original_selected_mean_real_profile" : command => liftTermElabM do
  let integerName := root ++ `physicalMean_sobolev_profile
  forallBoundedTelescope (← getConstInfo integerName).type (some 57) fun p target => do
    unless p.size == 57 && target.isForall do
      throwError "actual real mean profile: changed original integer57 prefix"
    let some V := target.find? (·.isAppOfArity (fields ++ `physicalMean) 54)
      | throwError "actual real mean profile: lost SAME actual Schwartz field54"
    unless !V.hasLooseBVars && V.getAppArgs[:52].toArray == p[:52].toArray && V.getAppArgs[53]! == p[53]! do
      throwError "actual real mean profile: field depends on derivative order or changed original count"
    let C := app (root ++ `CphysicalMean) (p[:33].toArray.push p[53]!)
    let completion ← bodyAt (root ++ `completedMean_cNorm_profile) (p.push (mkNatLit 0))
    unless completion.isAppOfArity ``completedMean_profile_of_primitive_bounds 33 do
      throwError "actual real mean profile: exact genuine primitive-completion application changed"
    let a := completion.getAppArgs
    let R := a[16]!
    let hR := a[19]!
    unless R.isAppOfArity `JanetCartan.historyScale 3 do
      throwError "actual real mean profile: not the original CURRENT scale"
    withLocalDeclNoLocalInstanceUpdate `r .default (mkConst ``Real) fun r => do
      let hrType ← withTransparency .default <| Term.TermElabM.run'
        (PhysicalBackground.NativeReferenceSourceTemplate.termWith [(`r,r)] "(0 : ℝ) ≤ r")
      withLocalDeclNoLocalInstanceUpdate `hr .default hrType fun hr => do
        let proof := app ``physicalMean_real_profile_of_integer
          #[a[0]!,a[1]!,V,C,R,hR,app integerName p,r,hr]
        save (p ++ #[r,hr]) proof
end JanetCartan.PhysicalMean.OriginalSelectedMeanFractionalProfilesTemplate
end
