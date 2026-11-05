module
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEvent
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
import all JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

public meta section
open Lean Meta Elab Command
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate
open JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate (termWith)
open JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
namespace JanetCartan.PhysicalMean.OriginalMeanLinearComparison
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def ps := `JanetCartan.PhysicalSampling
private def ni := ps ++ `OriginalNativeInitialEvent
private def br := ps ++ `OriginalBareEvent
private def po := ps ++ `OriginalPositiveEvent
private def st := ps ++ `OriginalCommonStage
private def sm := ps ++ `OriginalNativeSmoothEvent
private def cur := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent
private def co := `JanetCartan.PhysicalNormalInverse.OriginalComparison
private def gd := ps ++ `OriginalNativeGradedEvent
private def nat := `JanetCartan.PhysicalBackground.NativeAdmission
private def app (n : Name) (a : Array Expr) := mkAppN (mkConst n) a
private def mark (label : String) : MetaM Unit := do
  let hb ← getRemainingHeartbeats
  IO.eprintln s!"{label}: {hb}"
private def tail (e : Expr) (k : Nat) := Nat.repeat (fun v => Expr.proj ``And 1 v) k e
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (tail e k)
private def bodyAt (n : Name) (a : Array Expr) : MetaM Expr := do
  let some b := (← getConstInfo n).value? (allowOpaque := true) | throwError "missing producer {n}"
  return (b.beta a).headBeta
private def need (e : Expr) (n : Name) (k : Nat) : MetaM (Array Expr) := do
  let some a := e.find? (·.isAppOfArity n k) | throwError "missing literal {n}/{k}"
  return a.getAppArgs
private def save (n : Name) (xs : Array Expr) (v : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let ty ← instantiateMVars (← mkForallFVars xs (← match target with | none => inferType v | some t => pure t))
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  let env ← getEnv
  for e in #[ty,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual comparison missing producer constants {missing.toList}"
  if ty.hasFVar || ty.hasMVar || ty.hasLevelMVar || ty.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasSorry then
    throwError "open actual transport {n}"
  let name := `JanetCartan.PhysicalMean.OriginalMeanLinearComparison ++ n
  if data then addDecl (.defnDecl {name,levelParams := [],type := ty,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type := ty,value}) (forceExpose := true)
  logInfo m!"actual transport current {n}: {xs.size}"
  return app name xs

private def trans (h k : Expr) : MetaM Expr := do
  let a ← inferType h
  let b ← inferType k
  unless a.isAppOfArity ``LE.le 4 && b.isAppOfArity ``LE.le 4 do
    throwError "transport threshold chain ceased to be numerical"
  let inst ← synthInstance (mkApp (mkConst ``Preorder [.zero]) (mkConst ``Real))
  return mkAppN (mkConst ``le_trans [.zero])
    #[mkConst ``Real,inst,a.getAppArgs[2]!,a.getAppArgs[3]!,b.getAppArgs[3]!,h,k]

/-- Read the already kernel-checked50 telescope, rather than rebuilding its
entire prehistory factory inside every downstream proof. -/
private def withPublishedStage (run : NativeGradedStage → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (gd ++ `uncut_response_jets)).type (some 50) fun x _ => do
    let p := x[:44].toArray
    let ev := app (gd ++ `event_le) p
    let smooth ← need (← inferType ev) (sm ++ `S) 47
    let initial := app (sm ++ `event_le) smooth
    let high ← need (← inferType initial) (ni ++ `S) 47
    let cresp := app (gd ++ `Cresp) p
    let I := (← whnf (← inferType cresp)).bindingDomain!
    withLocalDeclD `i I fun i => do
      let q ← need (← bodyAt (gd ++ `Cresp) (p.push i))
        `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.Cresp 44
      let source := q[:39].toArray
      let scalar ← bodyAt (ni ++ `initialC) (high[:44].toArray.push i)
      unless scalar.isAppOfArity `JanetCartan.PhysicalBackground.NativeDensityProfiles.initialC 39 do
        throwError "transport published initial data changed"
      let sampler := p[:3].toArray ++ source[2:20].toArray ++ #[source[20]!.appArg!]
      let d : JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication.Data :=
        ⟨smooth[:44].toArray,high[:44].toArray,sampler,scalar.getAppArgs[:33].toArray,source,i,I⟩
      let hs ← trans ev x[45]!
      let hr ← trans (app (gd ++ `response_le) (p.push i)) x[45]!
      let hist := x[46:50].toArray
      let prior := app (sm ++ `exists_of_quantitative_uncut_jets) (smooth ++ #[x[44]!,hs] ++ hist)
      logInfo m!"published50 view remaining heartbeats: {← getRemainingHeartbeats}"
      run ⟨d,p,q,x,smooth,high,hist,prior,hs,hr,x[45]!⟩

elab "construct_original_mean_linear_comparison_current " which:num : command => liftTermElabM do
  withPublishedStage fun g => do
    let d := g.data
    let i := d.i
    let R := g.args50[44]!
    let hh ← trans (app (sm ++ `event_le) g.smooth47) g.hSmooth
    let bare ← need (← bodyAt (ni ++ `S) g.high47) (br ++ `S) 46
    let pos ← need (← bodyAt (br ++ `S) bare) (po ++ `S) 47
    let hb ← trans (app (ni ++ `event_le) g.high47) hh
    let hp ← trans (app (br ++ `event_le) bare) hb
    let hs ← trans (app (po ++ `stage_le) pos) hp
    let stage := pos[:46].toArray
    let static := stage[:40].toArray ++ #[i,mkApp stage[41]! i,mkApp stage[42]! i]
    let hc ← trans (app (st ++ `S_current) (stage.push i)) hs
    let current := static ++ #[R,hc] ++ g.history
    let hn ← trans (app (ni ++ `native_le) g.high47) hh
    let native39 := d.native33 ++ #[R,hn] ++ g.history
    logInfo m!"transport before native52: {← getRemainingHeartbeats}"
    let positive ← bodyAt (nat ++ `positive_inverse_exists) native39
    unless positive.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.all_densities 52 do
      throwError "transport lost positive original52"
    logInfo m!"transport after native52: {← getRemainingHeartbeats}"
    let density := ((positive.getAppArgs[47:52].toArray.map (fun e => mkApp e i)).set! 0
      (app (nat ++ `labels) (native39.push i))).set! 4
      (app (nat ++ `labels_C15) (native39.push i))
    let comp ← need (← bodyAt (cur ++ `S) static) (co ++ `S) 35
    logInfo m!"transport after comparison35: {← getRemainingHeartbeats}"
    let budget := comp ++ #[mkApp (app (gd ++ `Cresp) g.params44) i,
      mkApp (app (gd ++ `Cresp_nonneg) g.params44) i,
      mkConst (ps ++ `OriginalWindow.mollifier),mkConst (ps ++ `OriginalWindow.compact),
      mkConst (ps ++ `OriginalWindow.smooth),mkConst (ps ++ `OriginalWindow.mass),
      mkConst (ps ++ `OriginalWindow.nonneg),mkConst (ps ++ `OriginalWindow.support),
      g.params44[43]!,← termWith [] "(1 : ℝ)",← termWith [] "(show (0 : ℝ) < 1 from zero_lt_one)"]
    if which.getNat == 0 then
      discard <| save `Ccompare (g.params44.push i) (app (co ++ `Ccompare) budget) true
      return
    let n := (← inferType d.native33[1]!).appArg!
    let rpar := app `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder #[n]
    let retained := app (cur ++ `retained_profiles) current
    let retained := mkAppN retained (density ++ #[rpar,d.initial44[40]!])
    logInfo m!"transport static/positive setup remaining heartbeats: {← getRemainingHeartbeats}"
    let hfloor ← termWith [(`n,n)]
      "(show 20*(n+1)+1 ≤ JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder n from by dsimp only [JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder, JanetCartan.RawPrimary.SliceBounds.rawSliceJetOrder]; omega)"
    let hStar ← termWith [(`rpar,rpar),(`rStar,d.native33[26]!),(`hSourceReserve,g.params44[40]!)]
      "(show 14+(rpar+2) ≤ rStar from by omega)"
    let hInitialOrder ← termWith [(`rpar,rpar),(`rInitial,d.initial44[40]!)]
      "(show 14+(rpar+2) ≤ rInitial from by omega)"
    let initialProfile := app (ni ++ `native_initial_profile) (g.high47 ++ #[R,hh] ++ g.history ++ #[i])
    let coeff := mkAppN retained #[hfloor,hStar,hInitialOrder,initialProfile]
    logInfo m!"transport numeric reserves remaining heartbeats: {← getRemainingHeartbeats}"
    if which.getNat == 1 then
      discard <| save `retained (g.args50.push i) coeff
      return
    let coeff := app `JanetCartan.PhysicalMean.OriginalMeanLinearComparison.retained (g.args50.push i)
    mark "before measurement projection"
    let measure := app (cur ++ `measurement) current
    let hC := part measure 0
    let C := (← inferType hC).appArg!
    mark "after measurement projection"
    let ambient := app (cur ++ `ambient_geometry) current
    let hF := part ambient 0
    let hFt ← inferType hF
    let F := hFt.getAppArgs[hFt.getAppNumArgs-2]!
    mark "after ambient geometry"
    let sm0 := part coeff 4
    let sm0t ← inferType sm0
    let amp := sm0t.getAppArgs[sm0t.getAppNumArgs-2]!
    mark "after leading coefficient"
    unless amp.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
      throwError "transport current lost literal leading amplitude"
    let a := amp.getAppArgs
    let initialized ← bodyAt (co ++ `initialized) budget
    unless initialized.isAppOf `JanetCartan.PhysicalSampling.OriginalChoices.Comparison.continuation do
      throwError "transport actual comparison factory changed"
    let geometry := initialized.getAppArgs[:7].toArray
    mark "after original comparison initializer"
    let margin := tail (app (cur ++ `phase_margins) current) 3
    let low ← mkAppM `lt_of_lt_of_le #[margin,
      app `JanetCartan.PhysicalSampling.OriginalChoices.Comparison.hδ_threshold geometry]
    mark "after original low margin"
    let smooth := mkApp (app (sm ++ `uncut_response_smooth)
      (g.smooth47 ++ #[R,g.hSmooth] ++ g.history)) i
    let tensor ← need (← inferType smooth) `JanetCartan.CorrectedAtoms.fullPrimaryResponse 18
    mark "after full response extraction"
    let sourceTag (e : Expr) := if e.getAppFn.isConst then toString e.getAppFn.constName! else "lambda"
    IO.eprintln s!"initial scalar heads: {sourceTag a[12]!} / {sourceTag tensor[15]!}"
    -- The full comparison below consumes this actual response with the retained
    -- scalar; the kernel checks their identity there, without a duplicate large
    -- Meta.isDefEq normalization in this coefficient-only prefix.
    let hPhase ← termWith [(`hdom,part coeff 3)] "(Set.Subset.trans Metric.ball_subset_closedBall hdom)"
    mark "after original phase domain"
    let hOne ← termWith [(`hS,app (ni ++ `hS) g.high47),(`hR,hh)]
      "(show (1 : ℝ) ≤ _ from (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR))"
    let hL ← mkAppM `JanetCartan.one_le_currentCoefficientScale #[hOne,g.history[0]!]
    let L := (← inferType hL).appArg!
    mark "after actual coefficient scale"
    let lower := mkAppN (app (cur ++ `measurement_at_reserve) current) #[rpar,
      ← termWith [(`hStar,hStar)] "(by omega)" (some (← mkAppM ``LE.le
        #[← mkAppM ``HAdd.hAdd #[mkNatLit 2,rpar],d.native33[26]!]))]
    let first27 := #[C,hC,F,hF,part ambient 1,tail ambient 2,
      part coeff 0,part coeff 1,part coeff 2,margin,low] ++ a[8:12].toArray ++
      #[tensor[12]!,tensor[13]!,a[12]!,hPhase,sm0,part coeff 5,part coeff 6,part coeff 7,
      L,rpar,hL,hfloor]
    unless first27.size == 27 do throwError "transport expected actual dynamic27 before physical profile"
    let expected ← whnf (← inferType (app (co ++ `continuation) (budget ++ first27)))
    let target := expected.bindingDomain!
    unless target.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do
      throwError "transport expected literal physical measurement profile"
    let measured := mkApp (part lower 1) target.getAppArgs[6]!
    let args := first27 ++ #[measured,part coeff 8,part coeff 9,part coeff 10,part coeff 11,part coeff 12]
    unless args.size == 33 do throwError "transport expected actual dynamic33 before rates"
    let result := app (co ++ `continuation) (budget ++ args)
    mark "before exact comparison79 kernel publication"
    discard <| save `before_rates (g.args50.push i) result

private def namedArg (e : Expr) (key : Name) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  forallBoundedTelescope info.type (some e.getAppNumArgs) fun xs _ => do
    for j in [:xs.size] do
      if (← getFVarLocalDecl xs[j]!).userName.eraseMacroScopes == key then
        return e.getAppArgs[j]!
    throwError "actual transport: missing original argument {key}"

private def continuousOfSmooth (h : Expr) : MetaM Expr := do
  let t ← inferType h
  let info ← getConstInfo ``ContDiff.continuous
  forallTelescope info.type fun xs _ => do
    let formal := (← inferType xs.back!).getAppArgs
    let actual := t.getAppArgs
    let mut values := #[]
    for x in xs.pop do
      let some j := formal.findIdx? (· == x) | throwError "transport smoothness projection changed"
      values := values.push actual[j]!
    return mkAppN (mkConst ``ContDiff.continuous (info.levelParams.map fun _ => .zero)) (values.push h)

/-- Apply the actual common dyadic rates, actual full response jets and original
finite quadrature to the already checked same-current coefficient application. -/
elab "construct_original_mean_linear_comparison_rates " which:num : command => liftTermElabM do
  withPublishedStage fun g => do
    let d := g.data
    let i := d.i
    let R := g.args50[44]!
    let hh ← trans (app (sm ++ `event_le) g.smooth47) g.hSmooth
    let bare ← need (← bodyAt (ni ++ `S) g.high47) (br ++ `S) 46
    let pos ← need (← bodyAt (br ++ `S) bare) (po ++ `S) 47
    let hs ← trans (app (po ++ `stage_le) pos)
      (← trans (app (br ++ `event_le) bare) (← trans (app (ni ++ `event_le) g.high47) hh))
    let stage := pos[:46].toArray
    let full ← bodyAt `JanetCartan.PhysicalMean.OriginalMeanLinearComparison.before_rates (g.args50.push i)
    unless full.isAppOfArity (co ++ `continuation) 79 do throwError "transport coefficient application changed"
    let v := full.getAppArgs
    let init ← bodyAt (co ++ `initialized) v[:46].toArray
    let iv := init.getAppArgs
    let amp ← need (← inferType v[65]!)
      `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13
    let rates := app (st ++ `stage_rates) (stage ++ #[R,hs,g.history[0]!])
    let hFine := part rates 1
    let Lambda := (← inferType hFine).appArg!
    let hlam := part rates 2
    let lam := (← inferType hlam).appArg!
    let J := app `JanetCartan.RawInputPartition.cutoffCount #[Lambda]
    let hJ := mkApp (mkConst ``Nat.le_refl) J
    let every := mkApp (tail rates 6) i
    let smooth := mkApp (app (sm ++ `uncut_response_smooth)
      (g.smooth47 ++ #[R,g.hSmooth] ++ g.history)) i
    let rate ← forallBoundedTelescope (← inferType smooth) (some 1) fun cs t => do
      let ten ← need t `JanetCartan.CorrectedAtoms.fullPrimaryResponse 18
      mkLambdaFVars cs ten[14]!
    let hpos ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ =>
      mkLambdaFVars cs (part (mkAppN every cs) 0)
    let hrateOne ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ =>
      mkLambdaFVars cs (part (mkAppN every cs) 1)
    let hκΩ ← termWith [(`hs,iv[38]!),(`hK,iv[34]!)] "(Set.Subset.trans hs hK)"
    let hA ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ => do
      let c := cs[0]!
      let hne ← termWith [(`ht,mkApp hpos c)] "(ne_of_gt ht)"
      let hc := app `JanetCartan.Sampling.contDiff_cutCorrectedDerivativeAmplitude
        (amp[:12].toArray ++ #[v[61]!,v[62]!,v[63]!,iv[35]!,iv[31]!,iv[33]!,iv[36]!,
          hκΩ,v[64]!,v[65]!,v[66]!,v[67]!,v[68]!,mkApp rate c,hne,mkApp smooth c])
      mkLambdaFVars cs (← continuousOfSmooth hc)
    mark "after actual corrected amplitude continuity"
    let hn ← trans (app (ni ++ `native_le) g.high47) hh
    let native := d.native33 ++ #[R,hn] ++ g.history
    let oldSample := #[d.sampler22[0]!,d.sampler22[2]!,d.sampler22[1]!] ++ d.sampler22[3:22].toArray
    let prefixArgs := oldSample ++ native[21:39].toArray ++ #[J,Lambda,hJ]
    let Ezero ← bodyAt `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Transport.leadingMean (prefixArgs.push i)
    let some Dzero := Ezero.find? (·.isAppOf `JanetCartan.Sampling.CorrectedTransport.leadingCrossTransportKernelData)
      | throwError "transport lost exact positive-current zero endpoint"
    let hA0 ← namedArg Dzero `hA₀
    let Md ← namedArg Dzero `Md
    let hMd ← namedArg Dzero `hMd
    let hdb ← namedArg Dzero `hdb
    mark "after actual positive-current leading endpoint"
    let caps := app (ps ++ `OriginalMargins.ε_caps) (d.sampler22.push i)
    let bands ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ => do
      let b := tail (mkAppN every cs) 3
      forallBoundedTelescope (← inferType b) (some 1) fun js _ => do
        mkLambdaFVars (cs ++ js) (← trans (mkAppN b js) (tail caps 4))
    let radial ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ => do
      let ic ← mkAppM ``Prod.mk #[i,cs[0]!]
      mkLambdaFVars cs (app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Rcolor
        (d.sampler22.push ic))
    let hradial ← forallBoundedTelescope (← inferType rate) (some 1) fun cs _ => do
      let ic ← mkAppM ``Prod.mk #[i,cs[0]!]
      mkLambdaFVars cs (app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.radial_ge_one
        (d.sampler22.push ic))
    let hOne ← termWith [(`hS,app (gd ++ `hS) g.params44),(`hR,g.hR)]
      "(show (1 : ℝ) ≤ _ from (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR))"
    let hT ← termWith [(`hOne,hOne),(`stage,g.history[0]!)]
      "(hOne.trans (JanetCartan.le_historyScale hOne stage))"
    let mesh := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalBareEvent.mesh_bounds)
      #[(← inferType hT).appArg!,hT]
    let h := (← inferType (part mesh 0)).appArg!
    let rateEq ← termWith [(`rate,rate),(`radial,radial),(`lam,lam)]
      "(show ∀ c, rate c = (radial c*lam)⁻¹ from by intro c; rfl)"
    let buffer ← trans (mkApp (part rates 5) i) (part caps 2)
    let e := (← inferType (part caps 2)).appArg!
    let buffer ← termWith [(`Lambda,Lambda),(`lam,lam),(`eps,e),(`hb,buffer)]
      "(show 2*Lambda/((1:ℝ)*lam) ≤ eps from by simpa only [one_mul] using hb)"
    let jets := mkApp (app (gd ++ `uncut_response_jets) g.args50) i
    let late := #[J,rate,hpos,hrateOne,smooth,jets,hA,hA0,Md,hMd,hdb,bands,radial,hradial,
      h,lam,Lambda,part mesh 0,tail mesh 1,hlam,hFine,rateEq,buffer,hJ,J,hJ]
    unless late.size == 26 do throwError "transport expected all26 actual rate/quadrature fields"
    let result := mkAppN (app `JanetCartan.PhysicalMean.OriginalMeanLinearComparison.before_rates (g.args50.push i)) late
    mark "before actual comparison105 kernel publication"
    if which.getNat == 0 then
      discard <| save `comparison (g.args50.push i) result
      return
    let result := app `JanetCartan.PhysicalMean.OriginalMeanLinearComparison.comparison (g.args50.push i)
    let complex := part result 0
    let ct ← inferType complex
    unless ct.isAppOfArity ``LE.le 4 do throwError "transport comparison output changed"
    let difference := ct.getAppArgs[2]!.appArg!
    unless difference.isAppOf ``HSub.hSub do throwError "transport comparison difference changed"
    let rhs := ct.getAppArgs[3]!
    let ra := rhs.getAppArgs
    let num := ra[4]!
    let inner := num.getAppArgs[4]!
    let ccompare := inner.getAppArgs[4]!
    if which.getNat == 4 then
      discard <| save `actualCcompare g.args50 (← mkLambdaFVars #[i] ccompare) true
      return
    let ca := difference.getAppArgs
    if which.getNat == 1 then
      discard <| save `correctedMean g.args50 (← mkLambdaFVars #[i] ca[ca.size-2]!) true
      return
    if which.getNat == 2 then
      discard <| save `zero_eq (g.args50.push i) (← mkEqRefl ca.back!) false
        (some (← mkEq ca.back! Ezero))
      return
    let real := tail result 1
    let target := (← inferType real).replace fun e =>
      if e == ca.back! then some Ezero
      else if e == ca[ca.size-2]! then
        some (mkApp (app `JanetCartan.PhysicalMean.OriginalMeanLinearComparison.correctedMean g.args50) i)
      else none
    discard <| save `real_comparison (g.args50.push i) real false (some target)

end JanetCartan.PhysicalMean.OriginalMeanLinearComparison
end
