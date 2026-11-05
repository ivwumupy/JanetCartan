module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEvent
public meta import Lean

/-!
# Actual global inverse source profiles on the original history

Decode the same positive initial-profile certificate that already supplies the
native event. Its global admission39 is the one used by the positive scalar,
not the per-row transport inverse. The source reserve is the v2 integer order
`2 * (n / 2 + 2)` (new:sec:mean-source-equation, new:eq:source-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles

/-- The v2 source order and canonical carrier shift fit in the actual native
density reserve; no additional reserve or source estimate is assumed. -/
theorem sourceReserve_shift_le_density {n : ℕ} (hn : 5 ≤ n) :
    2 * (n / 2 + 2) + ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤
      16 + (RawPrimary.SliceBounds.rawSliceParameterOrder n + n + 1) := by
  simp only [ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder,
    RawPrimary.SliceBounds.rawSliceParameterOrder,
    RawPrimary.SliceBounds.rawSliceJetOrder]
  omega

/-- The existing source reserve already pays the same order in the original
map profile, whose reserve is rStar (not the history index kMin). -/
theorem sourceReserve_shift_le_map {n rStar : ℕ} (hn : 5 ≤ n)
    (hSourceReserve :
      (16 + (RawPrimary.SliceBounds.rawSliceParameterOrder n + n + 1)) +
          (3 + (n - 1)) + 2 +
          ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar) :
    2 * (n / 2 + 2) + ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar := by
  have h := sourceReserve_shift_le_density hn
  omega

end JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (withActualRow bodyAt)

private def ps := `JanetCartan.PhysicalSampling
private def graded := ps ++ `OriginalNativeGradedEvent
private def smooth := ps ++ `OriginalNativeSmoothEvent
private def initial := ps ++ `OriginalNativeInitialEvent
private def density := `JanetCartan.PhysicalBackground.NativeDensityProfiles
private def profiles := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Source
private def current := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current
private def canonical := `JanetCartan.PhysicalMean.OriginalCanonicalCurrent
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles

def app (name : Name) (xs : Array Expr) : Expr := mkAppN (mkConst name) xs

private def numericalTrans (h k : Expr) : MetaM Expr := do
  let a ← inferType h
  let b ← inferType k
  unless a.isAppOfArity ``LE.le 4 && b.isAppOfArity ``LE.le 4 do
    throwError "actual inverse source: changed reached-scale inequality"
  unless a.getAppArgs[3]! == b.getAppArgs[2]! do
    throwError "actual inverse source: the original threshold chain no longer matches"
  let inst ← synthInstance (mkApp (mkConst ``Preorder [.zero]) (mkConst ``Real))
  return mkAppN (mkConst ``le_trans [.zero])
    #[mkConst ``Real,inst,a.getAppArgs[2]!,a.getAppArgs[3]!,b.getAppArgs[3]!,h,k]

private def namedArguments (e : Expr) (name : Name) (count : Nat) : MetaM (Array Expr) := do
  let some t := e.find? (·.isAppOfArity name count) |
    throwError "actual inverse source: missing original producer {name}/{count}"
  if t.hasLooseBVars then
    throwError "actual inverse source: a later point entered {name}"
  return t.getAppArgs

structure ActualInverse where
  parameters : Array Expr
  source45 : Array Expr
  native39 : Array Expr

/-- Read existing reached-threshold proofs and the exact native initial-profile
application. No frame, source, inverse, history or sample is reconstructed. -/
def withActualInverse (go : ActualInverse → MetaM Unit) : MetaM Unit :=
  withActualRow fun d => do
    let p := d.parameters[:50].toArray
    let fixed := p[:44].toArray
    let hSmooth := app (graded ++ `event_le) fixed
    let smooth47 ← namedArguments (← inferType hSmooth) (smooth ++ `S) 47
    let hHigh := app (smooth ++ `event_le) smooth47
    let high47 ← namedArguments (← inferType hHigh) (initial ++ `S) 47
    let reached ← numericalTrans hHigh (← numericalTrans hSmooth p[45]!)
    let a53 := high47 ++ #[p[44]!,reached] ++ p[46:50].toArray
    let initialProof ← bodyAt (initial ++ `native_initial_profile) a53
    let atRow := (mkApp initialProof d.row).headBeta
    let a46 ← namedArguments atRow (density ++ `initial_profile) 46
    unless a46.back! == d.row do
      throwError "actual inverse source: initial density belongs to another row"
    let x := a46[:45].toArray
    for arg in x do
      if arg.containsFVar d.row.fvarId! || arg.hasLooseBVars then
        throwError "actual inverse source: row or point entered global source data"
    let native ← OriginalCanonicalCurrentApplication.nativeCurrentArguments d
    unless ← isDefEq x[0]! d.raw13[0]! do
      throwError "actual inverse source: changed dimension {x[0]!} / {d.raw13[0]!}"
    unless x[38]! == p[44]! do
      throwError "actual inverse source: changed initial scale {x[38]!} / {p[44]!}"
    unless x[40]! == p[46]! do
      throwError "actual inverse source: changed stage {x[40]!} / {p[46]!}"
    go ⟨p,x,native⟩

private def save (key : Name) (p : Array Expr) (term : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType term
  let env ← getEnv
  for e in #[target,term] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual inverse source: missing producer constants {missing.toList}"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p term)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual inverse source: unclosed field or extra input {key}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual SAME global admission39 source inverse and original native density profiles, on the unchanged native50 history. Constants precede history and samples; no per-row transport inverse or new source (new:sec:mean-source-equation, new:eq:source-bound)."
  logInfo m!"checked actual global inverse source {key}/{p.size}"
  return app name p

/-- The inverse source budget is fixed on prehistory44; the native density
profile has no dependence on a subsequently selected row. -/
elab "publish_actual_inverse_source_budget" : command => liftTermElabM <|
    withActualInverse fun d => do
  let fixed := d.parameters[:44].toArray
  let args := d.source45[:38].toArray
  let cost := app (profiles ++ `Craw) args
  let C ← save `Cinv fixed cost true (some (← mkArrow (mkConst ``Nat) (mkConst ``Real)))
  let proof := app (profiles ++ `Craw_nonneg) args
  let sourceTarget ← inferType proof
  let .forallE j jType body bi := sourceTarget.consumeMData
    | throwError "actual inverse source: changed pointwise nonnegativity telescope"
  unless jType == mkConst ``Nat && body.isAppOfArity ``LE.le 4 do
    throwError "actual inverse source: changed scalar nonnegativity shape"
  -- Preserve the producer's exact real order and zero. Its inferred type can
  -- expose the product defining Craw; kernel conversion checks the named cost.
  let target := Expr.forallE j jType
    (mkAppN body.getAppFn (body.getAppArgs.set! 3 (mkApp C (.bvar 0)))) bi
  discard <| save `Cinv_nonneg fixed proof false (some target)

/-- Kernel-check that the source-profile specialization uses the literal same
global inverse as the existing current, despite proof-irrelevant reach paths. -/
elab "publish_actual_inverse_source_identity" : command => liftTermElabM <|
    withActualInverse fun d => do
  let x := d.source45
  let fromSource := x[:33].toArray ++ x[38:44].toArray
  let Q := app (current ++ `Q0) fromSource
  let originalQ := app (canonical ++ `Q0) d.parameters
  discard <| save `Q0_eq d.parameters (← mkEqRefl Q) false (some (← mkEq Q originalQ))

/-- Specialize each original source-only estimate with the concrete v2
reserve. Both numerical obligations are proved from the native data. -/
elab "publish_actual_inverse_source_profile " which:num : command => liftTermElabM <|
    withActualInverse fun d => do
  let x := d.source45
  let n := x[0]!
  let two := mkNatLit 2
  let reserve := app ``Nat.mul #[two,app ``Nat.add #[app ``Nat.div #[n,two],two]]
  let hScalar := app (root ++ `sourceReserve_shift_le_density) #[n,x[1]!]
  let hMap := app (root ++ `sourceReserve_shift_le_map) #[n,x[26]!,x[1]!,x[37]!]
  let scalarType ← inferType hScalar
  unless scalarType.isAppOfArity ``LE.le 4 do
    throwError "actual inverse source: changed scalar reserve theorem"
  unless ← isDefEq scalarType.getAppArgs[3]! x[33]! do
    throwError "actual inverse source: native density reserve is not the prescribed fixed order"
  let sourceReserveType ← inferType x[37]!
  unless sourceReserveType.isAppOfArity ``LE.le 4 &&
      sourceReserveType.getAppArgs[3]! == x[26]! do
    throwError "actual inverse source: x26 is no longer the original map reserve rStar"
  let args := x[:38].toArray ++ #[reserve,hMap,hScalar] ++ x[38:].toArray
  let fields := #[`coefficient_profile,`paired_profile,`raw_profile,`inverse_profile,`carrier_normal_tail]
  unless which.getNat < fields.size do
    throwError "actual inverse source: unknown source profile field"
  let key := fields[which.getNat]!
  let proof := app (profiles ++ key) args
  let rawCost := app (profiles ++ `Craw) x[:38].toArray
  let namedCost := app (root ++ `Cinv) d.parameters[:44].toArray
  let target := (← inferType proof).replace fun e =>
    if e == rawCost then some namedCost else none
  discard <| save key d.parameters proof false (some target)

end JanetCartan.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
end
