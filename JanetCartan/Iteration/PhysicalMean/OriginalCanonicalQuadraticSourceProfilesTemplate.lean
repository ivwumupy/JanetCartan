module

public import JanetCartan.Iteration.PhysicalMean.CanonicalQuadraticProfile
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceApplication
public meta import Lean

/-!
# Source-only quadratic profiles of the actual selected original operator

The shared actual primitive tuple is owned by `OriginalMeanQuadraticRealization`.
This application consumes that tuple without constructing another amplitude,
phase, mask, tester, row, inverse or sample. The generic source theorem produces
its individual and aggregate input estimates internally. The only source
hypothesis retained here is the input profile of the supplied smooth residual
(new:eq:source-bound, app:ch_mean_pairs:eq:block-bilinear).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (bodyAt)

def root := `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles
def inverse := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles

def getField (fields : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let hits := fields.filter (fun entry => entry.1 == key)
  unless hits.size == 1 do
    throwError "actual quadratic source: expected one actual field {key}, found {hits.size}"
  return hits[0]!.2

/-- The anonymous instance names differ between the frozen low and high
consumers. Reuse the literal original instances by their shared tuple keys. -/
def binderKey (name : Name) (domain : Expr) (bi : BinderInfo) : Name := Id.run do
  if bi == .instImplicit then
    for (head,key) in #[( ``Fintype, `instFintype), (``MetricSpace, `instMetricSpace),
        (``DiscreteTopology, `instDiscreteTopology), (``MeasurableSpace, `instMeasurableSpace),
        (``BorelSpace, `instBorelSpace)] do
      if domain.isAppOf head then return key
  return name.eraseMacroScopes

/-- Read the frozen consumer's exact residual type while applying its literal
supplied fields. In particular, source-profile nonnegativity reuses the stored
Real order/zero in its hM binder instead of synthesizing them in native53. -/
def applyFieldsWithType (name : Name) (fields : Array (Name × Expr))
    (stopBefore : Option Name := none) : MetaM (Expr × Expr) := do
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut term := mkConst name levels
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  while type.isForall do
    let .forallE binder domain body bi := type | throwError "unreachable quadratic binder"
    let key := binderKey binder domain bi
    if stopBefore == some key then return (term,type)
    let value ← getField fields key
    term := mkApp term value
    type := body.instantiate1 value
  if stopBefore.isSome then
    throwError "actual quadratic source: requested binder {stopBefore} absent from {name}"
  return (term,type)

/-- Apply only named supplied fields; never synthesize a second instance or
silently turn an unavailable primitive estimate into a new premise. -/
def applyFields (name : Name) (fields : Array (Name × Expr))
    (stopBefore : Option Name := none) : MetaM Expr := do
  return (← applyFieldsWithType name fields stopBefore).1

/-- Use100's actual global source budget, not a transported row inverse. -/
def withInverseBudget (params : Array Expr) (common : Array (Name × Expr)) :
    MetaM (Array (Name × Expr)) := do
  unless params.size == 44 || params.size == 45 || params.size == 53 do
    throwError "actual quadratic source: expected static44, static45 with moment guard, or actual53"
  let fixed := params[:44].toArray
  let cost := mkAppN (mkConst (inverse ++ `Cinv)) fixed
  let nonneg := mkAppN (mkConst (inverse ++ `Cinv_nonneg)) fixed
  for (key,value) in #[(`Cinv,cost),(`hCinv,nonneg)] do
    for old in common.filter (fun entry => entry.1 == key) do
      unless ← isDefEq old.2 value do
        throwError "actual quadratic source: shared tuple changed the global inverse field {key}"
  return (common.filter (fun entry => entry.1 != `Cinv && entry.1 != `hCinv)) ++
    #[(`Cinv,cost),(`hCinv,nonneg)]

/-- Every constant and its proof precedes R0/reach/history/shift/prefix. The
static numerical moment guard may occur only if the original budget API needs
it; it never licenses a source-dependent replacement cost. -/
def budgetPrefix (params : Array Expr) (common : Array (Name × Expr)) : MetaM (Array Expr) := do
  let keys := #[`n,`N,`Rbox,`χ,`hχ,`hχs,`hχcell,`aC,`aG,`p,`Badj,`Cinv,
    `haC,`haG,`hp,`hBadj,`hCinv,`Cbare,`Ctest,`hCtest]
  unless params.size == 44 || params.size == 45 || params.size == 53 do
    throwError "actual quadratic source: unrecognized static/actual parameter prefix"
  let late := if params.size == 53 then params[44:50].toArray ++ params[51:].toArray else #[]
  let momentGuard := if params.size == 53 then some params[50]! else
    if params.size == 45 then some params[44]! else none
  let mut needsMomentGuard := false
  for key in keys do
    let value ← getField common key
    for x in late do
      if value.containsFVar x.fvarId! then
        throwError "actual quadratic source: late scale/history/reach/prefix in static budget field {key}"
    if let some guard := momentGuard then
      if value.containsFVar guard.fvarId! then needsMomentGuard := true
  let mut fixed := params[:44].toArray
  if needsMomentGuard then
    let some guard := momentGuard | throwError "actual quadratic source: missing static moment guard"
    let guardType ← inferType guard
    unless guardType.isAppOfArity ``LE.le 4 && guardType.getAppArgs[0]! == mkConst ``Real &&
        guardType.getAppArgs[2]! == params[24]! do
      throwError "actual quadratic source: extra static input is not the numeric gamma bound"
    for x in late do
      if guardType.containsFVar x.fvarId! then
        throwError "actual quadratic source: moment guard is not static"
    fixed := fixed.push guard
  for key in keys do
    let closed ← mkLambdaFVars fixed (← getField common key)
    if closed.hasFVar || closed.hasLooseBVars then
      throwError "actual quadratic source: field {key} is not closed over the static prefix"
  return fixed

/-- No datum or proof is published with an unresolved primitive input. -/
def save (key : Name) (params : Array Expr) (term : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun name => (env.find? name).isNone)
  unless missing.isEmpty do
    throwError "actual quadratic source: missing released producers {missing.toList}"
  let target ← match expected with | some type => pure type | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do
      throwError "actual quadratic source: missing type/value producers {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual quadratic source: open or sorry-backed field {key}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original selected quadratic source profile. The source-input profile is legitimate; individual/aggregate/output estimates are proved internally from the SAME primitives, current and sample. Costs precede history, sample and fixed prefix (new:eq:source-bound, app:ch_mean_pairs:eq:block-bilinear)."
  logInfo m!"checked actual quadratic source {key}/{params.size}"

/-- Publish only the data cost. This command can consume89's reusable static
dictionary before any dynamic hG/An realization is available. -/
def publishBudget (params : Array Expr) (original : Array (Name × Expr)) : MetaM Unit := do
  let common ← withInverseBudget params original
  let fixed ← budgetPrefix params common
  let constant := `JanetCartan.PhysicalMean.canonicalQuadraticSourceProfileConstant
  let (_,beforeM) ← applyFieldsWithType constant common (some `M)
  let .forallE name profileType _ bi := beforeM |
    throwError "actual quadratic source: missing generic source-profile binder"
  withLocalDeclNoLocalInstanceUpdate name bi profileType fun M => do
    let (cost,costType) ← applyFieldsWithType constant (common.push (`M,M)) (some `s)
    save `CQ fixed (← mkLambdaFVars #[M] cost) true
      (some (← mkForallFVars #[M] costType))

/-- Publish nonnegativity in a separate command, reusing the SAME saved cost.
The hM domain is copied verbatim from the generic theorem after substitution;
there is no Real-order, zero, or numeral synthesis under native44/53. -/
def publishBudgetNonneg (params : Array Expr) (original : Array (Name × Expr)) : MetaM Unit := do
  let common ← withInverseBudget params original
  let fixed ← budgetPrefix params common
  let constant := `JanetCartan.PhysicalMean.canonicalQuadraticSourceProfileConstant
  let nonnegative := `JanetCartan.PhysicalMean.canonicalQuadraticSourceProfileConstant_nonneg
  let (_,beforeM) ← applyFieldsWithType nonnegative common (some `M)
  let .forallE name profileType _ bi := beforeM |
    throwError "actual quadratic source: missing generic source-profile binder"
  withLocalDeclNoLocalInstanceUpdate name bi profileType fun M => do
    let fields := common.push (`M,M)
    let (_,beforeHM) ← applyFieldsWithType nonnegative fields (some `hM)
    let .forallE hName hMType _ hBi := beforeHM |
      throwError "actual quadratic source: missing literal generic hM binder"
    withLocalDeclNoLocalInstanceUpdate hName hBi hMType fun hM => do
      let (proof,proofType) ← applyFieldsWithType nonnegative
        (fields.push (`hM,hM)) (some `s)
      let cost ← applyFields constant fields (some `s)
      let named := mkAppN (mkConst (root ++ `CQ)) (fixed.push M)
      let target := proofType.replace fun e => if e == cost then some named else none
      unless (target.find? (·.isAppOf (root ++ `CQ))).isSome do
        throwError "actual quadratic source: named static cost missing from nonnegativity target"
      save `CQ_nonneg fixed (← mkLambdaFVars #[M,hM] proof) false
        (some (← mkForallFVars #[M,hM] target))

/-- Both all-order tails use the same actual global Q0 on the supplied source.
No bare `source_regular` adjoint certificate is mistaken for Q0 regularity. -/
def sourceTail (params : Array Expr) (known : Array (Name × Expr))
    (regularity : Bool) : MetaM Expr := do
  let n ← getField known `n
  let u ← getField known `u
  let realization := mkApp (mkConst `JanetCartan.CurrentMean.smoothResidualToL2) n
  let w ← mkAppM ``DFunLike.coe #[realization,u]
  withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
    let hw := mkAppN (mkConst `JanetCartan.CurrentMean.smoothResidualToL2_mem) #[n,u,j]
    let producer ← if regularity then getField known `Q0_regular else
      pure (mkAppN (mkConst (inverse ++ `inverse_profile)) params[:50].toArray)
    let proof := mkAppN producer #[j,w,hw]
    mkLambdaFVars #[j] proof

/-- Fill the exact generic consumer, binding ONLY its legitimate source/numeric
inputs. Every other field must come from the actual shared producer. -/
partial def publishSourceProfile (params : Array Expr)
    (original : Array (Name × Expr)) : MetaM Unit := do
  unless params.size == 53 do
    throwError "actual quadratic source: dynamic source profile requires the unchanged actual53 tuple"
  let common ← withInverseBudget params original
  let fixed ← budgetPrefix params common
  let consumer := `JanetCartan.PhysicalMean.fixedSourceQuadratic_source_profile
  let info ← getConstInfo consumer
  let levels := info.levelParams.map (fun _ => Level.zero)
  let literal := mkConst consumer levels
  let type := info.type.instantiateLevelParams info.levelParams levels
  let allowed := #[`M,`hM,`R,`h,`hR,`hTR,`hh,`u,`hsource,`s]
  let rec go (type : Expr) (args : Array Expr) (known : Array (Name × Expr))
      (bound : Array Expr) : MetaM Unit := do
    match type with
    | .forallE binder domain body bi =>
      let key := binderKey binder domain bi
      if key == `hreg || key == `hinverse then
        let proof ← sourceTail params known (key == `hreg)
        go (body.instantiate1 proof) (args.push proof) (known.push (key,proof)) bound
      else if allowed.contains key then
        if (known.any (fun entry => entry.1 == key)) then
          throwError "actual quadratic source: shared tuple unexpectedly supplies source input {key}"
        withLocalDeclNoLocalInstanceUpdate binder bi domain fun x =>
          go (body.instantiate1 x) (args.push x) (known.push (key,x)) (bound.push x)
      else
        let value ← getField known key
        go (body.instantiate1 value) (args.push value) known bound
    | target =>
      let proof := mkAppN literal args
      let M ← getField known `M
      let cost ← applyFields `JanetCartan.PhysicalMean.canonicalQuadraticSourceProfileConstant
        known (some `s)
      let namedCost := mkAppN (mkConst (root ++ `CQ)) (fixed.push M)
      let xs := params[:50].toArray
      let shift := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
      let namedQuadratic := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic)
        (xs ++ #[shift,params[52]!])
      let some rawQuadratic := target.find? (·.isAppOf `JanetCartan.PhysicalMean.fixedSourceQuadratic) |
        throwError "actual quadratic source: fixed quadratic object missing from consumer"
      let target := target.replace fun e =>
        if e == cost then some namedCost else
          if e == rawQuadratic then some namedQuadratic else none
      unless (target.find? (·.isAppOf (root ++ `CQ))).isSome &&
          (target.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic)).isSome do
        throwError "actual quadratic source: expected named original cost/operator missing"
      let term ← mkLambdaFVars bound proof
      let target ← mkForallFVars bound target
      save `source_profile params term false (some target)
  go type #[] common #[]

end JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
end
