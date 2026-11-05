module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceAmplitude
/-! # The actual original observation has its already-proved smooth buffer

Prune only the unused inner carrier/admission binders from the checked
`Whole.G` constructor's open selected cell and observation-support certificate.
The constructor already proves both facts. No baseline is admitted by inner
support, no domain is enlarged, and no new cutoff is introduced. The consumer
is the auxiliary observed Schwartz representative needed by the unchanged
signed-pair source pipeline (`app:ch_pairs:lem:pairs-ledger`).
-/
public meta section
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalObservationBufferTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalObservationBuffer
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def save (key : Name) (p : Array Expr) (type value : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars || e.hasSorry then
      throwError "original observation buffer: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"original observation buffer: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"original observation buffer: kernel passed {name}"

elab "publish_original_observation_buffer " which:num : command => liftTermElabM do
  unless which.getNat < 2 do throwError "original observation buffer: unknown mode"
  withActualSelectedSourceWave fun p _ _ _ _ native64 _ => do
    unless native64.size == 64 do throwError "original observation buffer: literal native64 changed"
    let key := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.Whole.G
    let raw := app key native64
    let info ← getConstInfo key
    let proof ← forallBoundedTelescope (← inferType raw) (some 2) fun carrier _ => do
      unless carrier.size == 2 do throwError "original observation buffer: inner carrier/admission telescope changed"
      let constructor := (info.value! (allowOpaque := true)).beta (native64 ++ carrier)
      unless constructor.getAppFn.isConst && constructor.getAppNumArgs == 17 &&
          constructor.getAppFn.constName!.getString! == "nativePeriodicDerivative" do
        throwError "original observation buffer: not the already-checked native derivative constructor"
      let args := constructor.getAppArgs
      let hX := args[4]!
      let hψX := args[13]!
      for e in #[args[3]!,args[11]!,hX,hψX,← inferType hψX] do
        for forbidden in carrier ++ #[p[50]!,p[51]!] do
          if (e.find? (· == forbidden)).isSome then
            throwError "original observation buffer: inner carrier, prefix, or supplied source still occurs"
      mkAppM ``And.intro #[hX,hψX]
    let params := p[:50].toArray.push p[52]!
    if which.getNat == 0 then
      save `statement params (mkSort .zero) (← inferType proof) true
    else
      save `buffer params (app (ns ++ `statement) params) proof
end JanetCartan.PhysicalPairs.OriginalObservationBufferTemplate
end
