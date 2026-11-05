module
public import JanetCartan.Iteration.PhysicalMean.CompletedMeanPrimitiveProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedNormalizedTargetProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionBufferProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularity
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Application template for the actual fixed-geometry completed mean

This only implements the application to original W/target/full-H/normal
producers. No analytic field is made a theorem parameter. The execution leaf
must supply the actual117 W proof and actual116 H declarations; until that
execution is kernel checked this is NOT an actual completed-mean profile.
Consumer: original physicalMean54 Sobolev profile (`main:eq:mean-size`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesTemplate
private theorem full_field_profile_on_subset {n N : ℕ}
    {K L U : Set (Euclidean n)} (hL : IsCompact L) (hKL : K ⊆ L) (hLU : L ⊆ U)
    (hU : IsOpen U) (F W : Euclidean n → Euclidean N)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (s : ℕ) (B : ℝ)
    (h : cNorm L s W + cNorm L s (linearizedMetric F W) ≤ B) :
    cNorm K s W + cNorm K s (linearizedMetric F W) ≤ B := by
  have hstrain := AmbientResponse.contDiffOn_linearizedMetric hU hF hW
  apply (add_le_add
    (cNorm_mono_set_of_contDiffAt hKL hL (fun x hx ↦
      (hW.contDiffAt (hU.mem_nhds (hLU hx))).of_le (by simp)))
    (cNorm_mono_set_of_contDiffAt hKL hL (fun x hx ↦
      (hstrain.contDiffAt (hU.mem_nhds (hLU hx))).of_le (by simp)))).trans h
end JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles
private def fieldsRoot := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def normalRoot := `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles
private def baseRoot := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def hermitianRoot := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def targetRoot := `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some v := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual completed profile: unavailable {key}"
  return (v.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- Metadata only. CW and its proof come from actual117, not local theorem
hypotheses. Extra initial gates are verified to have RHS the ORIGINAL R0. -/
structure ActualPacket where
  selected : Array Expr
  native : Array Expr
  native39 : Array Expr
  fields : Array Expr
  J : Expr
  N : Expr
  hAux : Expr
  hBuffer : Expr
  hTarget : Expr
  extraInitialGates : Array Expr
  CW : Expr
  hCW : Expr
  hWprofile : Expr

private def validate (d : ActualPacket) : MetaM Unit := do
  unless d.selected.size == 52 && d.native.size == 50 && d.native39.size == 39 && d.fields.size == 7 do
    throwError "actual completed profile: changed SAME source/history field boundaries"
  unless d.J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
    throwError "actual completed profile: not the ONE actual full-source prefix"
  for gate in d.extraInitialGates do
    let t ← inferType gate
    unless t.isAppOfArity ``LE.le 4 && t.getAppArgs[3]! == d.native[44]! do
      throwError "actual completed profile: extra gate is not an initial numerical reach"
  let early := d.selected[:33].toArray.push d.N
  for e in #[d.CW,d.hCW] do
    let closed ← instantiateMVars (← mkLambdaFVars early e)
    if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
      throwError "actual completed profile: W budget depends on history or later data"

private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual completed profile: missing producers {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual completed profile: extra or unresolved analytic field in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual completed profile: kernel checking {name}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original full-source completed physical mean, from fixed110 normal multiplier and actual117 FULL W/strain,14 normalized target,116 FULL sampled self. All coefficients precede history; only numeric initial/stage gates remain. No N-dependent geometric threshold, new cutoff or analytic success premise (main:eq:mean-size)."
  liftM <| IO.eprintln s!"actual completed profile: kernel passed {name}/{p.size}"

private def costs (d : ActualPacket) : MetaM (Array Expr × Array Expr) := do
  validate d
  let fixed := d.native[:44].toArray
  let early := d.selected[:33].toArray.push d.N
  let u ← OriginalSelectedMeanRegularity.targetArguments d.selected
  let Cn := app (normalRoot ++ `Cbuffer) fixed
  let hn := app (normalRoot ++ `Cbuffer_nonneg) fixed
  let Ct := app (targetRoot ++ `Ctarget) #[d.fields[0]!,u[1]!]
  let ht := app (targetRoot ++ `Ctarget_nonneg) #[d.fields[0]!,u[1]!]
  let Ch := app (hermitianRoot ++ `CH) early
  let hh := app (hermitianRoot ++ `CH_nonneg) early
  return (#[Cn,d.CW,Ct,Ch],#[hn,d.hCW,ht,hh])

/-- Publish only the static explicit convolution cost/nonnegativity. No new
geometric threshold is chosen after CW_N/CH_N. -/
def publishBudget (d : ActualPacket) (nonnegative : Bool) : MetaM Unit := do
  let (C,hC) ← costs d
  let early := d.selected[:33].toArray.push d.N
  if !nonnegative then
    let v := app ``completedMeanOrderConstant C
    save `Cmean early v (← inferType v) true
  else
    withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
      let v := app ``completedMeanOrderConstant_nonneg (C ++ hC ++ #[s])
      let old := app ``completedMeanOrderConstant (C.push s)
      let named := mkApp (app (root ++ `Cmean) early) s
      let t := (← inferType v).replace fun e => if e == old then some named else none
      save `Cmean_nonneg early (← mkLambdaFVars #[s] v) (← mkForallFVars #[s] t)

/-- Execute the true-R completion bound on actual fields. All analytic terms
are existing proved constants; no such term is appended to the public telescope. -/
def publishCompletedProfile (d : ActualPacket) : MetaM Unit := withTransparency .default do
  let (C,hC) ← costs d
  let stage := d.selected ++ #[d.J,d.N]
  let early := d.selected[:33].toArray.push d.N
  let fixed := d.native[:44].toArray
  let n := d.fields[0]!
  let N := d.fields[1]!
  let F := d.fields[2]!
  let W := app (fieldsRoot ++ `initializedField) stage
  let target := app (fieldsRoot ++ `normalizedTarget) d.selected
  let H := app (fieldsRoot ++ `fullSampledSelf) stage
  let D := app (baseRoot ++ `Dsmooth) fixed
  let r := app (baseRoot ++ `rBuffer) fixed
  let chart ← termWith [(`D,D),(`n,n)] "D.chart n"
  let a ← termWith [(`D,D)] "D.chartRadius"
  let K ← termWith [(`n,n),(`r,r)] "closedBall (0 : JanetCartan.Euclidean n) r"
  let buffers := app (baseRoot ++ `buffer_containments) fixed
  let geometry := app (baseRoot ++ `radius_geometry) fixed
  let raw ← bodyAt `JanetCartan.PhysicalBackground.NativeAdmission.raw d.native39
  unless raw.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent 47 do
    throwError "actual completed profile: changed original raw/current geometry"
  let geo (key : Name) := app (`JanetCartan.PhysicalBackground.NativeDensity ++ key) raw.getAppArgs
  let hWwide := app (fieldsRoot ++ `initializedField_smooth) stage
  let wide := (← inferType hWwide).getAppArgs.back!
  let hcwide ← termWith [(`b,buffers),(`chart,chart),(`wide,wide)]
    "(fun x hx ↦ b.2.2.2 (Metric.ball_subset_closedBall (b.2.1 hx)) : chart ⊆ wide)"
  let hF ← termWith [(`h,geo `current_hF_on),(`hc,hcwide)] "h.mono hc"
  let hW ← termWith [(`h,hWwide),(`hc,hcwide)] "h.mono hc"
  let hi ← termWith [(`h,geo `current_immersion),(`hc,hcwide)] "fun x hx ↦ h x (@hc x hx)"
  let hrank ← termWith [(`h,geo `current_fullNormalRank),(`hc,hcwide)] "fun x hx ↦ h x (@hc x hx)"
  let ht ← termWith [(`h,app (fieldsRoot ++ `normalizedTarget_smooth) d.selected),(`U,chart),(`T,target)]
    "(h.contDiffOn : ContDiffOn ℝ ∞ T U)"
  let hh ← termWith [(`h,app (fieldsRoot ++ `fullSampledSelf_smooth) stage),(`U,chart),(`H,H)]
    "(h.contDiffOn : ContDiffOn ℝ ∞ H U)"
  let delta ← termWith [(`T,target),(`F,F),(`W,W),(`H,H)] "T - JanetCartan.linearizedMetric F W - H"
  let hdelta ← termWith [(`ht,ht),(`hF,hF),(`hW,hW),(`hH,hh)]
    "(ht.sub (JanetCartan.AmbientResponse.contDiffOn_linearizedMetric Metric.isOpen_ball hF hW)).sub hH"
  let hInitial ← mkAppM ``le_trans
    #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,d.native[45]!]
  let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,d.native[46]!]
  let part (i : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e ↦ Expr.proj ``And 1 e) i facts)
  let R := app `JanetCartan.historyScale #[d.native[44]!,mkConst `JanetCartan.growthExponent,d.native[46]!]
  let Tscale := app `JanetCartan.currentCoefficientScale #[d.native[44]!,d.native[46]!]
  let hT ← termWith [(`h,part 1)] "le_trans (show (0 : ℝ) ≤ 1 by norm_num) h"
  let hnormal ← withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s =>
    mkLambdaFVars #[s] (app (normalRoot ++ `meanNormalCorrection_bound)
      (d.native ++ #[d.hBuffer,delta,hdelta,s]))
  let hTarget ← withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s =>
    mkLambdaFVars #[s] (app (fieldsRoot ++ `normalizedTarget_cNorm_profile)
      (d.selected ++ #[d.hTarget,K,s]))
  let hSelf ← withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s =>
    mkLambdaFVars #[s] (app (hermitianRoot ++ `full_self_profile)
      (d.selected ++ #[d.hAux,d.N,s]))
  let b := app `JanetCartan.PhysicalSeed.OriginalBoundary.b d.native39[:2].toArray
  let Kw ← termWith [(`n,n),(`b,b)] "closedBall (0 : JanetCartan.Euclidean n) b"
  let hKw ← termWith [(`n,n),(`b,b)] "ProperSpace.isCompact_closedBall (0 : JanetCartan.Euclidean n) b"
  let hOpen ← termWith [(`wide,wide)] "(Metric.isOpen_ball : IsOpen wide)"
  let hWbuffer ← withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
    let hb := mkApp d.hWprofile s
    let B := (← inferType hb).getAppArgs[3]!
    let proof := app ``full_field_profile_on_subset
      #[n,N,K,Kw,wide,hKw,Expr.proj ``And 0 (Expr.proj ``And 1 (Expr.proj ``And 1 buffers)),
        Expr.proj ``And 1 (Expr.proj ``And 1 (Expr.proj ``And 1 buffers)),
        hOpen,F,W,geo `current_hF_on,hWwide,s,B,hb]
    mkLambdaFVars #[s] proof
  withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
    let proof := app ``completedMean_profile_of_primitive_bounds
      (#[n,N,F,W,target,H,r,a,Expr.proj ``And 0 (Expr.proj ``And 1 geometry),hF,hW,ht,hh,hi,hrank,
        Tscale,R,hT,part 2,part 0] ++ C ++ hC ++ #[hnormal,hWbuffer,hTarget,hSelf,s])
    let old := app `JanetCartan.CurrentMean.completedMeanField #[n,N,F,W,target,H]
    let named := app (fieldsRoot ++ `completedMean) stage
    let oldCost := app ``completedMeanOrderConstant (C.push s)
    let namedCost := mkApp (app (root ++ `Cmean) early) s
    let targetType := (← inferType proof).replace fun e =>
      if e == old then some named else if e == oldCost then some namedCost else none
    let params := d.selected ++ #[d.hAux,d.N] ++ d.extraInitialGates ++ #[d.hBuffer,d.hTarget,s]
    save `completedMean_cNorm_profile params proof targetType

/-- The physical Sobolev coefficient is fixed before history and all target
parameters; the cutoff loses no derivative order. -/
def publishPhysicalBudget (d : ActualPacket) (nonnegative : Bool) : MetaM Unit := do
  validate d
  let early := d.selected[:33].toArray.push d.N
  let D := app (baseRoot ++ `Dsmooth) d.native[:44].toArray
  withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
    let cutoff := app ``physicalMeanCutoffConstant #[d.fields[0]!,d.fields[1]!,D,s]
    let C := mkApp (app (root ++ `Cmean) early) s
    let value ← termWith [(`A,cutoff),(`B,C)] "A * B"
    if !nonnegative then
      let value ← mkLambdaFVars #[s] value
      save `CphysicalMean early value (← inferType value) true
    else
      let hc := app ``physicalMeanCutoffConstant_nonneg #[d.fields[0]!,d.fields[1]!,D,s]
      let hm := mkApp (app (root ++ `Cmean_nonneg) early) s
      let proof ← termWith [(`hc,hc),(`hm,hm)] "mul_nonneg hc hm"
      let named := mkApp (app (root ++ `CphysicalMean) early) s
      let target := (← inferType proof).replace fun e => if e == value then some named else none
      save `CphysicalMean_nonneg early (← mkLambdaFVars #[s] proof) (← mkForallFVars #[s] target)

/-- Apply the lossless 2πξ norm transfer to literal physicalMean54. The
physical cutoff and support are the originals, not the residual core. -/
def publishPhysicalProfile (d : ActualPacket) : MetaM Unit := withTransparency .default do
  validate d
  let fixed := d.native[:44].toArray
  let early := d.selected[:33].toArray.push d.N
  let stage := d.selected ++ #[d.J,d.N]
  let n := d.fields[0]!
  let N := d.fields[1]!
  let D := app (baseRoot ++ `Dsmooth) fixed
  let r := app (baseRoot ++ `rBuffer) fixed
  let V := app (fieldsRoot ++ `completedMean) stage
  let hV := app (fieldsRoot ++ `completedMean_smooth) stage
  let U := (← inferType hV).getAppArgs.back!
  let hU ← termWith [(`U,U)] "(Metric.isOpen_ball : IsOpen U)"
  let buffers := app (baseRoot ++ `buffer_containments) fixed
  let support := app (baseRoot ++ `cutoff_support_buffer) fixed
  let geometry := app (baseRoot ++ `radius_geometry) fixed
  let hcut ← termWith [(`h,support),(`b,buffers)] "h.trans (b.2.2.1.trans b.2.2.2)"
  let hr ← termWith [(`h,geometry)] "h.2.2.2.2.2.2.le"
  let hrU ← termWith [(`b,buffers)] "b.2.2.1.trans b.2.2.2"
  let raw := app `JanetCartan.PhysicalPrimary.cutSchwartzOfSupport #[n,N,D,V,U,hU,hV,hcut]
  let physical := app (fieldsRoot ++ `physicalMean) stage
  let R := app `JanetCartan.historyScale #[d.native[44]!,mkConst `JanetCartan.growthExponent,d.native[46]!]
  withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
    let params := d.selected ++ #[d.hAux,d.N] ++ d.extraInitialGates ++ #[d.hBuffer,d.hTarget,s]
    let hp := app (root ++ `completedMean_cNorm_profile) params
    let C := mkApp (app (root ++ `Cmean) early) s
    let proof := app ``physicalMean_cutoff_profile #[n,N,D,V,U,hU,hV,hcut,r,hr,hrU,C,R,s,hp]
    let cutoff := app ``physicalMeanCutoffConstant #[n,N,D,s]
    let oldCost ← termWith [(`A,cutoff),(`B,C)] "A * B"
    let namedCost := mkApp (app (root ++ `CphysicalMean) early) s
    let target := (← inferType proof).replace fun e =>
      if e == raw then some physical else if e == oldCost then some namedCost else none
    unless (target.find? (· == physical)).isSome do
      throwError "actual physical mean profile: literal Schwartz carrier disappeared"
    save `physicalMean_sobolev_profile params proof target

end JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesTemplate
end
