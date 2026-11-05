module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-!
# Instantiate the native uncontracted strain estimate

Only the exact original Source39/53 producer and its retained leading arguments
are inspected. The full-strain bound is obtained before stress contraction,
without changing the reference, scalar, source scale, or cutoff.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullStrainProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
open OriginalLocalWaveGeometryTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles
private def source := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def prescribed := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Prescribed

private def argumentsOf (name : Name) (value : Expr) : MetaM (Array (Name × Expr)) := do
  unless value.isAppOf name do throwError "original full strain: expected literal native producer {name}"
  let mut t := (← getConstInfo name).type
  let mut result := #[]
  for value in value.getAppArgs do
    let .forallE label _ body _ ← whnf t
      | throwError "original full strain: changed producer argument list"
    result := result.push (label,value)
    t := body.instantiate1 value
  return result

private def argument (known : Array (Name × Expr)) (name : Name) : MetaM Expr := do
  let some (_,value) := known.find? (fun p => p.1 == name)
    | throwError "original full strain: missing native argument {name}"
  return value

private def applyByName (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec inputs : Expr → MetaM (Array Expr)
    | .forallE label _ body _ => do
      return #[← argument known label] ++ (← inputs body)
    | .mdata _ body => inputs body
    | _ => pure #[]
  return mkAppN (mkConst name) (← inputs (← getConstInfo name).type)

private def chooseNamed (label : Name) (params : Array Expr) (h : Expr) : MetaM (Expr × Expr) := do
  let t ← whnf (← inferType h)
  unless t.isAppOfArity ``Exists 2 do throwError "original full strain: expected {label} witness"
  let value ← store (ns ++ label) params (← mkAppM ``Classical.choose #[h]) true
  let spec ← store (ns ++ Name.mkSimple s!"afterChoice_{label}") params
    (← mkAppM ``Classical.choose_spec #[h]) false (some (t.appArg!.beta #[value]))
  return (value,spec)

/-- Apply the retained leading and uncontracted full-strain producers to the
unchanged actual39 before all histories and dynamic scalar inputs. -/
elab "construct_original_full_strain_profiles" : command => liftTermElabM do
  withSourcePrefix 39 fun s => do
    let closed ← bodyAt (source ++ `S) s
    unless closed.isAppOfArity (prescribed ++ `S) 53 do
      throwError "original full strain: changed Actual39/Prescribed53 spine"
    let some originalBody := (← getConstInfo (prescribed ++ `initialized)).value? (allowOpaque := true)
      | throwError "original full strain: native initialization proof is not exposed"
    let original ← Core.betaReduce (originalBody.beta closed.getAppArgs)
    let known ← argumentsOf
      `JanetCartan.PhysicalPrimary.exists_history_leading_reducedSource_reserved_fourier_profiles original
    let n ← argument known `n
    let T ← argument known `T
    unless T.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.T 3 do
      throwError "original full strain: lost same original patch family"
    let patch := T.getAppArgs[2]!
    let cell ← argument known `cell
    let geom := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongGeometry.working_geometry)
      (#[n] ++ s[1:18].toArray)
    let physicalBall := mkAppN (.proj ``And 0 geom) #[patch,cell]
    let productType ← inferType (← argument known `hproduct)
    let target := productType.appArg!
    unless target.isAppOfArity `Metric.closedBall 4 do
      throwError "original full strain: native working product ball changed"
    let parameterCenter ← mkAppM ``Prod.snd #[target.getAppArgs[2]!]
    let physical ← mkAppOptM (ns ++ `working_ball_mapsTo_fst)
      #[some n,some parameterCenter,none,none,some physicalBall]
    let producer ← applyByName (ns ++ `exists_leading_profiles) (known.push (`hphysical,physical))
    logInfo "original full strain: fixed native working geometry and exact named static arguments"
    let producer ← store (ns ++ `initialized) s producer
    logInfo "original full strain: kernel-checked direct retained/fullStrain initialization"
    let (nativeS,hs) ← chooseNamed `nativeThreshold s producer
    discard <| store (ns ++ `nativeThreshold_ge_two) s (.proj ``And 0 hs)
    let (_,hC) ← chooseNamed `C s (.proj ``And 1 hs)
    discard <| store (ns ++ `C_nonneg) s (.proj ``And 0 hC)
    discard <| store (ns ++ `nativeContinuation) s (.proj ``And 1 hC)
    let sourceS := mkAppN (mkConst (source ++ `S)) s
    discard <| store (ns ++ `S) s (← mkAppM ``Max.max #[sourceS,nativeS]) true
    discard <| store (ns ++ `source_threshold_le) s (← mkAppM `le_max_left #[sourceS,nativeS])
    discard <| store (ns ++ `native_threshold_le) s (← mkAppM `le_max_right #[sourceS,nativeS])
    discard <| store (ns ++ `S_ge_two) s
      (← mkAppM `le_trans #[.proj ``And 0 hs,← mkAppM `le_max_right #[sourceS,nativeS]])
  logInfo "original39 uncontracted full strain: SAME native leading geometry/masks, scalar budget and reserve; threshold and C before history, source frequency and size"

/-- Consume the same fourteen original dynamic inputs, adding only the genuine
reached maximum threshold. No strain, response, or successful sample input is
introduced; the original k+16 scalar budget is retained unchanged. -/
elab "apply_original_full_strain_profiles" : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let fixed := s[:39].toArray
    let a ← sourceCurrent s
    let da := a.dataArgs
    let S := mkAppN (mkConst (ns ++ `S)) fixed
    withLocalDeclD `hReached (← mkAppM ``LE.le #[S,s[39]!]) fun hReached => do
      let hn ← mkAppM `le_trans
        #[mkAppN (mkConst (ns ++ `native_threshold_le)) fixed,hReached]
      let inputs := #[s[39]!,hn] ++ s[41:47].toArray ++ da[31:34].toArray ++
        #[a.datum] ++ s[47:53].toArray
      let native := mkAppN (mkConst (ns ++ `nativeContinuation)) (fixed ++ inputs)
      let nativeType ← whnf (← inferType native)
      unless nativeType.isAppOfArity ``And 2 do
        throwError "original full strain: native source conclusion lost its smoothness/jet pair"
      logInfo "original full strain: exact native Source53 conclusion instantiated"
      let hs : Expr := .proj ``And 0 native
      let hsType ← inferType hs
      unless hsType.isAppOf `ContDiffOn do
        throwError "original full strain: native conclusion is not local full matrix smoothness"
      let args := hsType.getAppArgs
      let originalEnvelope := args[args.size-2]!
      lambdaTelescope originalEnvelope fun _ body => do
        unless body.isAppOf `JanetCartan.ResponsePrimarySources.fullStrainEnvelope do
          throwError "original full strain: native result is not the uncontracted full matrix"
      -- All of T/Q/F/row/col/Phi/Y/scalar/chiEnv/tau are already fixed by the
      -- original39 application and its exact sourceCurrent dynamic arguments.
      -- Naming the inferred literal field avoids re-elaborating that same tuple.
      let envelope ← store (ns ++ `envelope) s originalEnvelope true
      let type := nativeType.replace fun e => if e == originalEnvelope then some envelope else none
      let profiles ← store (ns ++ `profiles) (s.push hReached) native false (some type)
      discard <| store (ns ++ `smooth) (s.push hReached) (.proj ``And 0 profiles)
      discard <| store (ns ++ `jets) (s.push hReached) (.proj ``And 1 profiles)
  logInfo "actual original53 matrix fullStrainEnvelope: entire univ x SAME V, full joint jets C k*(tau^3*size)*K^(k-rSource), unchanged k+16 scalar profile; no stress inversion or new response assumption"

end JanetCartan.PhysicalPrimary.OriginalFullStrainProfilesTemplate
end
