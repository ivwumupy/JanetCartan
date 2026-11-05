module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredHermitianProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedQuadratureApplication.CorrectedSquares
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
public meta import Lean

/-!
# Read the actual unscaled positive-background geometry

The native positive scalar and entire source response come from the SAME saved
original event and measured row. The baseline uses the actual spatial carrier,
not the root-local extended carrier or the annular coefficient cutoff. In
particular neither an inner mask nor a Fourier normalization multiplies it.
Consumers are original background quadrature and the full physical mean
(`app:ch_waves:eq:background-quadrature`, `app:ch_mean_pairs:eq:comparison-input`).
-/

public meta section
namespace JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def ns := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian

def bodyAt (name : Name) (args : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "original positive Hermitian: missing checked body {name}"
  return (value.beta args).headBeta

/-- A read-only view of the saved theorem; no density, D or sample is chosen. -/
structure ActualRow where
  parameters : Array Expr
  row : Expr
  native64 : Array Expr
  mean70 : Array Expr
  initial62 : Array Expr
  raw13 : Array Expr

private def nativeTelescope (type : Expr) (count : Nat)
    (k : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  go count type #[]
where
  go : Nat → Expr → Array Expr → MetaM Unit
    | 0, result, xs => k xs result
    | remaining + 1, type, xs => do
      let .forallE name domain body bi := type.consumeMData
        | throwError "original positive Hermitian: native telescope ended at {xs.size}"
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => go remaining (body.instantiate1 x) (xs.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
          go remaining (body.instantiate1 x) (xs.push x)

/-- Open only the native50 telescope and its existing row index. -/
def withActualRow (go : ActualRow → MetaM Unit) : MetaM Unit := do
  nativeTelescope (← getConstInfo (ps ++ `OriginalNativeGradedEvent.exists_on_original_history)).type
      50 fun p result => do
    unless p.size == 50 do throwError "original positive Hermitian: changed saved50"
    let some D := result.find? (·.isAppOfArity (ps ++ `OriginalJointEvent.measured_kernel) 60)
      | throwError "original positive Hermitian: original measured60 missing"
    if D.hasLooseBVars then throwError "original positive Hermitian: a newly chosen sample entered the row"
    let family ← bodyAt (ps ++ `OriginalJointEvent.measured_kernel) D.getAppArgs
    nativeTelescope (← inferType D) 1 fun i _ => do
      unless i.size == 1 do throwError "original positive Hermitian: changed original label"
      let row := (mkAppN family i).headBeta
      unless row.isAppOfArity (ps ++ `OriginalMeasuredFamily.Row.kernel) 64 do
        throwError "original positive Hermitian: lost exact native64"
      let a := row.getAppArgs
      let m0 ← bodyAt (ps ++ `OriginalMeasuredCurrent.mean_on_full_response) a[:60].toArray
      unless m0.isAppOfArity (ps ++ `OriginalMeasuredCurrent.mean_before_response) 62 do
        throwError "original positive Hermitian: changed uncut mean62"
      let m ← bodyAt (ps ++ `OriginalMeasuredCurrent.mean_before_response) m0.getAppArgs
      unless m.isAppOfArity (ps ++ `OriginalMeasuredMean.continuation) 70 do
        throwError "original positive Hermitian: lost actual C/source mean70"
      let m := m.getAppArgs
      let initial ← bodyAt (ps ++ `OriginalMeasuredMean.initialized) m[:37].toArray
      unless initial.isAppOfArity (ps ++ `OriginalChoices.Mean.continuation) 62 do
        throwError "original positive Hermitian: changed prehistory geometry62"
      let t ← inferType m[56]!
      let A := t.getAppArgs[t.getAppNumArgs-2]!
      unless A.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
        throwError "original positive Hermitian: lost actual raw thirteen"
      unless (m[54]!.find? (·.isAppOf `JanetCartan.PhysicalBackground.NativeAdmission.labels)).isSome do
        throwError "original positive Hermitian: native positive scalar was replaced"
      go ⟨p ++ i,i[0]!,a,m,initial.getAppArgs,A.getAppArgs⟩

def save (short : Name) (p : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasLooseBVars || value.hasLooseBVars ||
      type.hasSorry || value.hasSorry then
    throwError "original positive Hermitian: open/recovered actual field {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Same original native50/row64 positive-background data, without inner annular masks, root-local carrier extension, Fourier normalization, or a new sample. The actual physical measurement and full source response are unchanged (app:ch_waves:eq:background-quadrature)."
  logInfo m!"checked original unscaled positive-background {short} at {p.size} inputs"
  return mkAppN (mkConst name) p

/-- The actual reference carrier, as a function on the original three coordinates. -/
def referenceCarrier (d : ActualRow) : MetaM Expr := do
  let reference ← mkAppM `JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily.reference #[d.raw13[5]!]
  mkAppM `JanetCartan.ActualCarriers.CarrierPhaseReference.spatialPatch #[reference]

/-- The physical node map is the existing canonical coordinate identification.
It is not an isometry from the sampling sup norm to the Euclidean ℓ² norm. -/
def nodeAt (z : Expr) : MetaM Expr := do
  mkAppM ``WithLp.toLp #[← mkNumeral (mkConst ``ENNReal) 2,z]

def nativeAmplitude (d : ActualRow) : Expr :=
  mkAppN (mkConst `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude)
    (d.raw13[:12].toArray ++ #[d.mean70[52]!,d.mean70[53]!,d.raw13[12]!])

/-- Proof metadata read from the existing native52 jet theorem. This is not a
new mathematical bundle, source selection, analytic hypothesis or response. -/
structure SavedResponse where
  source53 : Array Expr
  full60 : Array Expr

/-- Preserve the exact existing source-reached proof and full physical60 spine.
Consumers are the positive native-self identity and the whole-parent corrected
profiles; neither consumer needs to replay an original stage construction. -/
def savedResponse (d : ActualRow) (color : Expr) : MetaM SavedResponse := do
  let proof ← bodyAt (ps ++ `OriginalNativeGradedEvent.uncut_response_jets)
    (d.parameters.push color)
  let some full := proof.find? (·.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.derivative_jets 60)
    | throwError "original positive Hermitian: saved full physical60 missing"
  let some window := proof.find? (·.isAppOfArity (ps ++ `OriginalResponseWindow.working_in_native_graded_domain) 54)
    | throwError "original positive Hermitian: saved actual source53 window missing"
  if full.hasLooseBVars || window.hasLooseBVars then
    throwError "original positive Hermitian: a later jet/point leaked into the source"
  let f := full.getAppArgs
  let s := f[:21].toArray ++ window.getAppArgs[22:54].toArray
  unless s.size == 53 do throwError "original positive Hermitian: changed original source53"
  unless ← isDefEq f[52]! (mkApp d.native64[61]! color) do
    throwError "original positive Hermitian: changed actual color rate"
  unless s[49]!.isAppOfArity (ps ++ `OriginalNativeSourceScalar.scalar) 40 do
    throwError "original positive Hermitian: changed native scalar subtype"
  let boxed ← bodyAt (ps ++ `OriginalNativeSourceScalar.scalar) s[49]!.getAppArgs
  unless boxed.isAppOfArity ``Subtype.mk 4 do
    throwError "original positive Hermitian: changed native scalar constructor"
  unless ← isDefEq boxed.getAppArgs[2]! d.raw13[12]! do
    throwError "original positive Hermitian: unscaled native positive scalar was replaced"
  return ⟨s,f⟩

/-- Publish the literal data before proving any background identification. -/
elab "retain_original_positive_background_data " which:num : command => liftTermElabM <|
    withTransparency .reducible <| withActualRow fun d => do
  let p := d.parameters
  let a := d.native64
  match which.getNat with
  | 0 => discard <| save `C p d.mean70[37]! true
  | 1 => discard <| save `T p d.raw13[5]! true
  | 2 => discard <| save `ζ p (← referenceCarrier d) true
  | 3 => discard <| save `amplitude p (nativeAmplitude d) true
  | 4 => discard <| save `rate p a[61]! true
  | 5 => discard <| save `ψ p (mkAppN (mkConst (ps ++ `OriginalOuterWeights.ψ)) (a[:22].toArray.push d.row)) true
  | 6 =>
    let C := mkAppN (mkConst (ns ++ `C)) p
    let ζ := mkAppN (mkConst (ns ++ `ζ)) p
    let amp := mkAppN (mkConst (ns ++ `amplitude)) p
    let rate := mkAppN (mkConst (ns ++ `rate)) p
    let colorType := (← inferType rate).bindingDomain!
    let physical := (← inferType C).bindingDomain!
    let H ← withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
      withLocalDeclNoLocalInstanceUpdate `x .default physical fun x => do
        withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.SeparatedSampling.Point) fun z => do
          let node ← nodeAt z
          let w ← mkAppM ``Prod.mk #[x,← mkAppM ``Prod.mk #[node,mkApp ζ node]]
          let tensor ← mkAppM `JanetCartan.hermitianTensor #[mkAppN amp #[mkApp rate color,w]]
          let value := mkApp (← mkAppM ``DFunLike.coe #[mkApp C x]) tensor
          mkLambdaFVars #[color,x,z] value
    discard <| save `H p H true
  | 14 =>
    if (d.mean70[37]!.find? (· == d.row)).isSome then
      throwError "original positive Hermitian: common measurement unexpectedly depends on the row"
    discard <| save `commonC p[:50].toArray d.mean70[37]! true
  | 15 =>
    let target ← mkEq (mkAppN (mkConst (ns ++ `C)) p)
      (mkAppN (mkConst (ns ++ `commonC)) p[:50].toArray)
    discard <| save `C_eq_common p (← mkEqRefl d.mean70[37]!) false (some target)
  | 16 =>
    let n := d.raw13[0]!
    let merged := mkAppN (mkConst (ps ++ `samplingCappedExtra)) #[a[0]!,a[1]!,a[2]!,a[21]!]
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,a[1]!,merged]
    let seed := #[n,a[1]!] ++ a[3:21].toArray ++ #[capped]
    let field (k : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ k)) seed
    let hD := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.hD) #[n,a[1]!]
    let hI ← mkAppM `JanetCartan.ContinuumInverse.retained_incidence_channel_nonempty
      #[a[1]!,.proj ``And 0 hD,field `centers,field `εcover,field `fact5,field `fact7]
    let allRows ← mkLambdaFVars #[d.row] d.mean70[38]!
    let rowType ← inferType d.row
    let proposition ← inferType d.mean70[38]!
    let level := (← inferType rowType).sortLevel!
    let proof := mkAppN (mkConst ``Nonempty.elim [level]) #[rowType,proposition,hI,allRows]
    discard <| save `commonC_smooth p[:50].toArray proof
  | 25 => discard <| save `C_smooth p d.mean70[38]!
  | _ => throwError "original positive Hermitian: unknown actual data field"

end JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate
end
