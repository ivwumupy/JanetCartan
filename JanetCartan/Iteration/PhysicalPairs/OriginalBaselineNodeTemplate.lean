module
public import JanetCartan.Iteration.PhysicalPairs.CombinedNode
public import JanetCartan.Iteration.PhysicalPairs.OriginalAngularJets
public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
/-! # The unchanged positive outer baseline's demodulated amplitude

Use the original outer-weight support, not the inner angular factor. The raw
joint smoothness and the same full response identify the literal baseline with
the native parent amplitude. Consumer: the source-data baseline-plus-angular
node profile for `main:prop:pairs`.
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalBaselineNodeTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private abbrev Args := Array (Name × Expr)
private def arguments (name : Name) (value : Expr) : MetaM Args := do
  unless value.isAppOf name do throwError "native baseline: changed producer {name}"
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  for e in value.getAppArgs do
    let .forallE key _ body _ := type.consumeMData | throwError "native baseline: malformed producer"
    result := result.push (key,e)
    type := body
  return result
private def atKey (xs : Args) (name : Name) : MetaM Expr := do
  let some (_,e) := xs.find? (·.1 == name) | throwError "native baseline: missing {name}"
  return e
private def applyKnown (name : Name) (xs : Args) : MetaM Expr := do
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut type := info.instantiateTypeLevelParams levels
  let mut value := mkConst name levels
  while let .forallE key _ body _ := type.consumeMData do
    value := mkApp value (← atKey xs key)
    type := body
  return value
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def bodyAt (name : Name) (xs : Array Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let some value := info.value? (allowOpaque := true) | throwError "native baseline: opaque source producer"
  return (value.beta xs).headBeta

private def save (key : Name) (params : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "native baseline: unresolved {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := `JanetCartan.PhysicalPairs.OriginalBaselineNode ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"original baseline: kernel passed {name}"

elab "publish_original_baseline_amplitude " mode:num : command => liftTermElabM do
  unless mode.getNat < 4 do throwError "native baseline: unknown publication mode"
  PhysicalMean.OriginalParentCorrectedProfilesTemplate.withActualParent fun d => do
    let rc := d.params52
    let s := d.source53
    let nativeType ← inferType (app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets rc)
    let some graph := nativeType.find? (·.isAppOfArity
        `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42) |
      throwError "native baseline: missing the exact instantiated graph42"
    if graph.hasLooseBVars then throwError "native baseline: graph uses later jet binders"
    let family := graph.getAppArgs ++
      #[24,25,30,32,33,34,35,36,37,38,40,45,46,47,48,49,50,51,52].map (fun k => s[k]!)
    let rawName := `JanetCartan.RawPrimary.contDiffOn_fullPrimaryAtom_of_leading_outputs
    let raw ← arguments rawName (← bodyAt (wave ++ `joint_raw_smooth) s)
    let outer := app (geo ++ `outer_weight_parameter) s
    forallBoundedTelescope (← inferType outer) (some 5) fun sample _ => do
      let hc := mkAppN outer sample
      let membership ← Core.betaReduce (← zetaReduce (← inferType hc))
      unless membership.isAppOfArity ``Membership.mem 5 do
        throwError "native baseline: original outer parameter admission changed"
      let c := membership.getAppArgs[4]!
      let params := family.push c
      let Z := app (wave ++ `Corrected.unrestricted_atom) params
      let literal ← bodyAt (wave ++ `Corrected.unrestricted_atom) params
      let correctedName := `JanetCartan.CorrectedAtoms.fullCorrectedPrimaryAtom
      let corrected ← arguments correctedName literal
      let known := corrected ++ raw
      let smooth := app (wave ++ `Corrected.on_source_chart) (params.push hc)
      let smoothType ← inferType smooth
      unless smoothType.isAppOfArity ``ContDiffOn 11 do
        throwError "native baseline: original source-chart smoothness changed"
      let X := smoothType.getAppArgs[10]!
      let response := app (wave ++ `Corrected.response_on_source_chart) (params.push hc)
      let responseType ← inferType response
      let Xsource := responseType.getAppArgs[10]!
      let hSourceOpen ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[Xsource]))
      let T ← atKey known `T
      let Q ← atKey known `Q
      let τ ← atKey known `τ
      let z ← mkAppM ``Prod.fst #[c]
      let θ ← termWith [(`T,T),(`Q,Q),(`τ,τ),(`z,z)] "(fun y => T.carrier Q y z / τ)"
      let hτ ← mkAppM `ne_of_gt #[d.full60[53]!]
      let n ← atKey known `n
      let N ← atKey known `N
      let space := smoothType.getAppArgs[2]!
      let A := app (parent ++ `amplitude) rc
      let result ← withLocalDeclD `x space fun x => do
        withLocalDeclD `hx (← mkAppM `Membership.mem #[X,x]) fun hx => do
          let hxSource := hx
          let w ← mkAppM ``Prod.mk #[x,c]
          let hw := mkAppN (app (geo ++ `source_product_in_current) s)
            #[w,← mkAppM ``And.intro #[hxSource,hc]]
          let hB ← termWith [(`h,response),(`hX,hSourceOpen),(`hx,hxSource)]
            "((h.contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp))"
          let native ← applyKnown
            `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude_eq_demodulated
            (#[(`hτ,hτ),(`w,w),(`hw,hw),(`hB,hB)] ++ known)
          if mode.getNat ≥ 2 then
            return (← mkLambdaFVars #[x,hx] native, ← mkForallFVars #[x,hx] (← inferType native))
          let exponential := app `JanetCartan.PhysicalPairs.CombinedNode.amplitude_eq_exp #[n,N,Z,θ,x]
          let ea := (← inferType exponential).getAppArgs
          let na := (← inferType native).getAppArgs
          let native := if mode.getNat == 1 then
            app `JanetCartan.PhysicalPairs.OriginalBaselineNode.native_demodulation (rc ++ sample ++ #[x,hx])
            else native
          let rev := mkAppN (mkConst ``Eq.symm [.succ .zero]) #[na[0]!,na[1]!,na[2]!,native]
          let eq := mkAppN (mkConst ``Eq.trans [.succ .zero]) #[ea[0]!,ea[1]!,ea[2]!,na[1]!,exponential,rev]
          let goal ← mkEq ea[1]! (mkApp A w)
          return (← mkLambdaFVars #[x,hx] eq, ← mkForallFVars #[x,hx] goal)
      liftM <| IO.eprintln s!"original baseline: exact outer amplitude mode {mode.getNat} before kernel"
      let statement := if mode.getNat < 2 then `amplitude_on_original_statement else `native_demodulation_statement
      let theoremName := if mode.getNat < 2 then `amplitude_on_original_chart else `native_demodulation
      if mode.getNat % 2 == 0 then
        save statement (rc ++ sample) result.2 true (some (mkSort .zero))
      else
        save theoremName (rc ++ sample) result.1 false
          (some (app (`JanetCartan.PhysicalPairs.OriginalBaselineNode ++ statement) (rc ++ sample)))
end JanetCartan.PhysicalPairs.OriginalBaselineNodeTemplate
end
