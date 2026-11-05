module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeBudgets
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate

/-!
# Actual corrected envelopes and sharp original atomic jets

Apply the already published native parent coefficient tuple and before-history
costs to the SAME uncut full response. The physical phase identity, displacement
reserve, original colored radial bounds and old physical cutoff chart are
retained. No new raw profile, response estimate, scalar, inverse, geometry,
cutoff or successful primary bound is an input. The final sampled-primary
construction still requires the actual fixed-K Picard and Fourier-mass parents
(`app:ch_response:eq:current-atomic-amplitudes`, `main:eq:primary-fixed-scales`).

The displacement command is repeated here under a distinct command name so its
large `ContDiffOn.mono` application is built from the already inferred type
spine, rather than reverse-unifying through the full response expression. The
frozen raw/template artifact is not edited.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeApplication
open Lean Meta Elab Command
open JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
open JanetCartan.PhysicalMean.OriginalParentCorrectedProfilesTemplate
open JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def physical := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def tail (e : Expr) (k : Nat) := Nat.repeat (fun v => Expr.proj ``And 1 v) k e
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (tail e k)
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "actual corrected application: declaration arity changed"
    type := rest.instantiate1 arg
  return type

private def applyThrough (name last : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut value := mkConst name
  while let .forallE key _ rest _ := type.consumeMData do
    let some (_,arg) := known.find? (·.1 == key) |
      throwError "actual corrected application: missing exact {name}.{key}"
    value := mkApp value arg
    if key == last then return value
    type := rest
  throwError "actual corrected application: missing last argument {last}"
private def emit (key : Name) (xs : Array Expr) (v : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual envelope application: checking {key}"
  -- Do not eagerly infer the enormous native term when its exact type is known.
  -- The kernel still checks the declaration against that explicit type below.
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  let resultType ← match target with
    | some t => pure t
    | none => inferType v
  let type ← instantiateMVars (← mkForallFVars xs resultType)
  if type.hasFVar || type.hasMVar || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "actual corrected application: open or incomplete declaration {name}"
  if data then
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  let out := mkAppN (mkConst name) xs
  addDocStringCore (ns ++ key)
    "Actual same-native-scalar corrected parent response jet, with original uncut response and no new field or cutoff (main:eq:primary-fixed-scales)."
  logInfo m!"actual original corrected envelope application: checked {key} / {xs.size}"
  return out

private def retainedBudgetProof (xs : Array Expr) (mode : Nat) : MetaM (Expr × Expr) := do
  let info ← getConstInfo `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native.A_nonneg
  let some value := info.value? (allowOpaque := true) |
    throwError "actual corrected application: frozen budget nonnegativity proof is unavailable"
  let proof := (value.beta xs).headBeta
  unless proof.isAppOfArity `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.correctedCost_nonneg 12 do
    throwError "actual corrected application: frozen budget nonnegativity spine changed"
  let args := proof.getAppArgs
  let applied := mkAppN proof.getAppFn args[:7+mode].toArray
  let .forallE _ target _ _ := (← exactType applied).consumeMData |
    throwError "actual corrected application: frozen budget proof domain changed"
  return (args[7+mode]!,target)

private def withStaticCosts (go : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native.A
  let some body := info.value? (allowOpaque := true) |
    throwError "actual corrected application: frozen native45 cost is unavailable"
  bindNative 45 info.type #[] fun xs => do
    let cost := (body.beta xs).headBeta
    unless cost.isAppOfArity `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.correctedCost 7 do
      throwError "actual corrected application: frozen corrected cost spine changed"
    go xs cost.getAppArgs
where
  bindNative : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,xs,next => next xs
    | remaining+1,type,xs,next => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual corrected application: native45 ended at {xs.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        bindNative remaining (body.instantiate1 x) (xs.push x) next

elab "publish_native_corrected_envelope_budget " mode:num : command => liftTermElabM do
  withStaticCosts fun xs costs => do
    let keys : Array (Name × Name × Nat) :=
      #[(`Pξ,`Pξ_nonneg,2),(`Clead,`Clead_nonneg,3),(`Ccorr,`Ccorr_nonneg,4)]
    unless mode.getNat < keys.size do throwError "actual corrected application: unknown static cost"
    let (key,nonnegKey,position) := keys[mode.getNat]!
    let cost := costs[position]!
    let target ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    let named ← emit key xs cost true (some target)
    liftM <| IO.eprintln "actual static budget: reading frozen nonnegativity"
    let (h,originalType) ← retainedBudgetProof xs mode.getNat
    let hType := originalType.replace fun e => if e == cost then some named else none
    unless (hType.find? (· == named)).isSome do
      throwError "actual corrected application: static nonnegative cost alias changed"
    discard <| emit nonnegKey xs h false (some hType)

elab "publish_native_corrected_envelope_combined_cost " mode:num : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let p := g.params44.push g.data.i
    let target ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    if mode.getNat == 0 then
      let A := app (ns ++ `Clead) p
      let B := app (ns ++ `Ccorr) p
      let D := app (physical ++ `Cdisp) g.physical44
      let hD := app (physical ++ `Cdisp_nonneg) g.physical44
      let σ := g.data.native33[21]!
      let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 g.data.native33[23]!]
      let literal := app (ns ++ `correctedDisplacementCost) #[A,B,D,σ]
      let cost ← emit `Adisp p literal true (some target)
      let proof := app (ns ++ `correctedDisplacementCost_nonneg)
        #[A,B,D,σ,app (ns ++ `Clead_nonneg) p,app (ns ++ `Ccorr_nonneg) p,hD,hσ]
      let proofType := (← exactType proof).replace fun e => if e == literal then some cost else none
      discard <| emit `Adisp_nonneg p proof false (some proofType)
    else if mode.getNat == 1 then
      let sharp := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
      let one ← mkNumeral (mkConst ``Real) 1
      let hOne ← termWith [] "(show (0 : ℝ) ≤ 1 from zero_le_one)"
      let cf := app (sharp ++ `Cfrequency) g.data.sampler22
      let hcf ← mkAppM `le_trans #[hOne,app (sharp ++ `Cfrequency_ge_one) g.data.sampler22]
      let A := app (ns ++ `Adisp) p
      let P := app (ns ++ `Pξ) p
      let literal := app (sharp ++ `sharpJetCost) #[one,cf,A,P]
      let cost ← emit `Cphysical p literal true (some target)
      let proof := app (sharp ++ `sharpJetCost_nonneg)
        #[one,cf,hOne,hcf,A,P,app (ns ++ `Adisp_nonneg) p,app (ns ++ `Pξ_nonneg) p]
      let proofType := (← exactType proof).replace fun e => if e == literal then some cost else none
      discard <| emit `Cphysical_nonneg p proof false (some proofType)
    else throwError "actual corrected application: unknown combined cost"

elab "publish_native_corrected_envelope_phase" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let a ← parentGeometry g
    let p := g.params44.push g.data.i
    let hPξ := app (ns ++ `Pξ_nonneg) p
    let result ← mkAppM (ns ++ `phase_spatial_jets_of_retained_profile)
      #[a.raw13[5]!,a.raw13[6]!,a.compact_proof,a.open_proof,a.compact_in_open,
        part a.coeff 3,a.scale_one_le,hPξ,part a.coeff 8]
    discard <| emit `phase_spatial_jets (g.args50.push g.data.i) result
    logInfo "actual raw phase jets checked directly from retained parent profile"


/-- Construct the actual corrected displacement jets without changing the frozen
raw/template root. The response smoothness restriction uses the explicit
ContDiffOn application spine, avoiding reverse elaboration of its huge proof. -/
elab "publish_native_corrected_envelope_displacement " mode:num : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    liftM <| IO.eprintln "actual displacement: published native stage"
    let a ← parentGeometry g
    liftM <| IO.eprintln "actual displacement: original parent geometry"
    let p := g.params44.push g.data.i
    let hPξ := app (ns ++ `Pξ_nonneg) p
    let hLead := app (ns ++ `Clead_nonneg) p
    let hCorr := app (ns ++ `Ccorr_nonneg) p
    withNativeResponseColor g fun color => do
      liftM <| IO.eprintln "actual displacement: original source53/response60"
      let s := color.source53
      let w := color.weak38
      let hcurrent := app (geo ++ `current_cell) s
      let cellArgs := a.radius.getAppArgs
      let hW := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec cellArgs
      let c ← mkAppM ``Prod.snd #[a.center]
      let dim := app ``Nat.sub #[a.raw13[0]!,mkNatLit 1]
      let rawDomain := (← exactType hcurrent).getAppArgs[3]!
      let window := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow cellArgs
      let hParent := app (ns ++ `parent_compact_in_response)
        #[a.raw13[0]!,dim,c,a.radius,a.radius_pos,rawDomain,window,hcurrent,tail hW 3]
      liftM <| IO.eprintln "actual displacement: parent in unchanged response region"
      let source57 := s ++ #[w[24]!,w[29]!,w[30]!,w[33]!]
      let hFull := app `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity.full_response_smooth source57
      let hBall := app (ns ++ `parent_ball_in_parameter_window)
        #[a.raw13[0]!,← mkAppM ``HSub.hSub #[a.raw13[0]!,mkNatLit 1],c,a.radius]
      let hBallType ← inferType hBall
      unless hBallType.isAppOfArity ``LE.le 4 do
        throwError "actual corrected application: parent ball subset changed"
      let hBallArgs := hBallType.getAppArgs
      let parentSet := hBallArgs[2]!
      let fullType ← exactType hFull
      unless fullType.isAppOfArity ``ContDiffOn 11 do
        throwError "actual corrected application: full response smoothness type changed"
      let fullArgs := fullType.getAppArgs
      let hResponse := mkAppN (mkConst ``ContDiffOn.mono fullType.getAppFn.constLevels!)
        (fullArgs[:8].toArray ++ #[fullArgs[10]!,fullArgs[9]!,fullArgs[8]!,hFull,parentSet,hBall])
      let hResponseJets ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        let joint := (← inferType a.compact).appArg!
        withLocalDeclD `w joint fun q => do
          withLocalDeclD `hw (← mkAppM `Membership.mem #[a.compact,q]) fun hq => do
            let h := app (physical ++ `displacement_jets)
              (color.full60 ++ #[j,q,mkAppN hParent #[q,hq]])
            let hType ← exactType h
            unless hType.isAppOfArity ``LE.le 4 do
              throwError "actual corrected application: response displacement inequality changed"
            let C := mkApp (app (physical ++ `Cdisp) g.physical44) j
            let weighted := app (ns ++ `response_displacement_weight)
              #[hType.getAppArgs[2]!,C,g.data.native33[21]!,s[47]!,s[45]!,j,g.physical44[42]!,h]
            mkLambdaFVars #[j,q,hq] weighted
      let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 g.data.native33[23]!]
      let hD ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        let h ← mkAppM ``mul_nonneg
          #[hσ,mkApp (app (physical ++ `Cdisp_nonneg) g.physical44) j]
        mkLambdaFVars #[j] h
      let χ := (← inferType (app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth
        s[:23].toArray)).appArg!
      let B := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B w
      let raw := a.raw13
      let D ← withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
        mkLambdaFVars #[j] (← mkAppM ``HMul.hMul
          #[g.data.native33[21]!,mkApp (app (physical ++ `Cdisp) g.physical44) j])
      let Pξ := app (ns ++ `Pξ) p
      let Clead := app (ns ++ `Clead) p
      let Ccorr := app (ns ++ `Ccorr) p
      let rpar := g.physical44[42]!
      let known := #[(`n,raw[0]!),(`N,raw[1]!),(`P,raw[2]!),(`U,raw[3]!),(`hU,raw[4]!),
        (`T,raw[5]!),(`Q,raw[6]!),(`F,raw[7]!),(`row,raw[8]!),(`col,raw[9]!),
        (`Φ,raw[10]!),(`Y,raw[11]!),(`χ,χ),(`B,B),(`r,raw[12]!),
        (`J,a.compact),(`Ω,a.openSet),(`hJ,a.compact_proof),(`hΩ,a.open_proof),
        (`hJΩ,a.compact_in_open),(`hphase,part a.coeff 3),
        (`hν₀,part a.coeff 4),(`hν₁,part a.coeff 5),(`hV₀,part a.coeff 6),(`hV₁,part a.coeff 7),
        (`rpar,rpar),(`C,Pξ),(`A₀,Clead),(`A₁,Ccorr),(`B₀,Clead),(`B₁,Ccorr),(`Cresp,D),
        (`hC,hPξ),(`hA₀,hLead),(`hA₁,hCorr),(`hB₀,hLead),(`hB₁,hCorr),(`hCresp,hD),
        (`τ,s[47]!),(`L,s[45]!),(`hτ,s[48]!),(`hτ₁,color.full60[58]!),(`hL,a.scale_one_le),
        (`hpξ,part a.coeff 8),(`hpν₀,part a.coeff 9),(`hpν₁,part a.coeff 10),
        (`hpV₀,part a.coeff 11),(`hpV₁,part a.coeff 12),(`hresponse,hResponse),
        (`hresponseDisplacementJets,hResponseJets)]
      liftM <| IO.eprintln "actual displacement: applying literal corrected coefficient theorem"
      let graded ← applyThrough `JanetCartan.CorrectedAtoms.fullCorrectedDisplacementAmplitude_joint_bounds
        `hresponseDisplacementJets known
      let mixed ← applyThrough `JanetCartan.CorrectedAtoms.fullCorrectedDisplacementAmplitude_mixed_bounds
        `hresponseDisplacementJets known
      let gradedType ← exactType graded
      if mode.getNat == 0 then
        let (result,resultType) ← forallBoundedTelescope gradedType (some 3) fun point resultType => do
          unless point.size == 3 && resultType.isAppOfArity ``And 2 do
            throwError "actual corrected application: changed jet/point/membership tail"
          return (← mkLambdaFVars point (part (mkAppN graded point) 0),
            ← mkForallFVars point resultType.getAppArgs[0]!)
        discard <| emit `displacement_jets (g.args50 ++ #[g.data.i,color.color]) result false (some resultType)
      else if mode.getNat == 1 then
        let (unreserved,unreservedType) ← forallBoundedTelescope gradedType (some 3) fun point _ => do
          let hzero := app ``Nat.zero_le #[rpar]
          let h := mkAppN mixed #[point[0]!,mkNatLit 0,hzero,point[1]!,point[2]!]
          let hType ← exactType h
          unless hType.isAppOfArity ``And 2 do
            throwError "actual corrected application: unchanged mixed-jet conjunction missing"
          return (← mkLambdaFVars point (part h 0),← mkForallFVars point hType.getAppArgs[0]!)
        discard <| emit `displacement_unreserved_jets (g.args50 ++ #[g.data.i,color.color]) unreserved false (some unreservedType)
      else throwError "actual corrected application: unknown displacement reserve"

private def smoothMono (h target inclusion : Expr) : MetaM Expr := do
  let type ← exactType h
  unless type.isAppOfArity ``ContDiffOn 11 do
    throwError "actual corrected application: expected original ContDiffOn11"
  let a := type.getAppArgs
  return mkAppN (mkConst ``ContDiffOn.mono type.getAppFn.constLevels!)
    (a[:8].toArray ++ #[a[10]!,a[9]!,a[8]!,h,target,inclusion])

elab "publish_native_corrected_envelope_sharp" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let a ← parentGeometry g
    let p := g.params44.push g.data.i
    let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
    let sharp := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
    let gd := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
    withNativeResponseColor g fun color => do
      let s := color.source53
      let w := color.weak38
      let raw := a.raw13
      let cp := raw[0:1].toArray ++ #[s[1]!] ++ a.radius.getAppArgs[2:4].toArray
      let hcut := app (geo ++ `smoothing_chart_in_source_chart) s[:23].toArray
      let hchart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_in_cell
        (s[:23].toArray ++ cp[2:4].toArray)
      let hx ← mkAppM `Set.Subset.trans #[hcut,hchart]
      let cutType ← exactType hcut
      let X := cutType.getAppArgs[2]!
      let c ← mkAppM ``Prod.snd #[a.center]
      let dim := app ``Nat.sub #[raw[0]!,mkNatLit 1]
      let hproduct := app (ns ++ `cutoff_chart_product_in_parent) #[raw[0]!,dim,c,a.radius,X,hx]
      let productType ← exactType hproduct
      let rectangle := productType.getAppArgs[2]!
      let cell := rectangle.appArg!
      let hX ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[X]))
      let hcurrent := app (geo ++ `current_cell) s
      let hW := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec cp
      let rawDomain := (← exactType hcurrent).getAppArgs[3]!
      let window := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow cp
      let hparent := app (ns ++ `parent_compact_in_response)
        #[raw[0]!,dim,c,a.radius,a.radius_pos,rawDomain,window,hcurrent,tail hW 3]
      liftM <| IO.eprintln "actual sharp jets: parent in unchanged response region"
      let hregion := app (physical ++ `region_open) color.full60
      let region := (← exactType hregion).appArg!
      let pointType := (← inferType region).appArg!
      let restrict (h : Expr) : MetaM Expr := withLocalDeclNoLocalInstanceUpdate `q .default pointType fun q => do
        withLocalDeclNoLocalInstanceUpdate `hq .default (← mkAppM `Membership.mem #[region,q]) fun hq =>
          mkLambdaFVars #[q,hq] (mkAppN h #[q,Expr.proj ``And 0 hq])
      let hspace ← restrict (app (geo ++ `current_space) s)
      let hphase ← restrict (app (geo ++ `current_phase) s)
      let hnonzero ← restrict (app (wave ++ `nullvectors_nonzero) s)
      let hSubset ← withLocalDeclNoLocalInstanceUpdate `q .default pointType fun q => do
        withLocalDeclNoLocalInstanceUpdate `hq .default (← mkAppM `Membership.mem #[region,q]) fun hq =>
          mkLambdaFVars #[q,hq] (Expr.proj ``And 0 hq)
      let hα ← smoothMono (app (wave ++ `scalar_smooth) s) region hSubset
      let hresponse := app (physical ++ `response_smooth) color.full60
      let hTwo ← mkAppM `le_trans #[app (gd ++ `hS) g.params44,g.hR]
      let hOne ← termWith [(`hTwo,hTwo)] "(by linarith only [hTwo])"
        (some (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 1,g.args50[44]!]))
      let pic ← mkAppM ``Prod.mk #[g.data.i,color.color]
      let rates := app (sharp ++ `rate_comparisons)
        (g.data.sampler22 ++ #[g.args50[44]!,hOne,g.history[0]!,pic])
      let hL ← mkAppM `le_trans #[← termWith [] "(show (0 : ℝ) ≤ 1 from zero_le_one)",a.scale_one_le]
      let hfreq ← mkAppM `le_trans #[← termWith [] "(show (0 : ℝ) ≤ 1 from zero_le_one)",
        app (sharp ++ `Cfrequency_ge_one) g.data.sampler22]
      let rateType ← inferType (part rates 2)
      let rateRhs ← mkAppM ``HMul.hMul
        #[← mkNumeral (mkConst ``Real) 1,rateType.getAppArgs[3]!]
      let hRate ← termWith [(`h,part rates 2)] "(by simpa only [one_mul] using h)"
        (some (← mkAppM ``LE.le #[rateType.getAppArgs[2]!,rateRhs]))
      let χ := (← exactType (app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth
        s[:23].toArray)).appArg!
      let B := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B w
      withLocalDeclNoLocalInstanceUpdate `param .default (← inferType c) fun param => do
        withLocalDeclNoLocalInstanceUpdate `hparam .default (← mkAppM `Membership.mem #[cell,param]) fun hparam => do
          let inParent ← withLocalDeclNoLocalInstanceUpdate `x .default (← inferType X).appArg! fun x => do
            withLocalDeclNoLocalInstanceUpdate `hx .default (← mkAppM `Membership.mem #[X,x]) fun hx => do
              let pair ← mkAppM ``Prod.mk #[x,param]
              let hpair ← mkAppM ``And.intro #[hx,hparam]
              mkLambdaFVars #[x,hx] (mkAppN hproduct #[pair,hpair])
          let inRegion ← forallBoundedTelescope (← inferType inParent) (some 2) fun x _ => do
            let pair ← mkAppM ``Prod.mk #[x[0]!,param]
            mkLambdaFVars x (mkAppN hparent #[pair,mkAppN inParent x])
          let makeJets (key : Name) (inputs : Array Expr) : MetaM Expr :=
            withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
              forallBoundedTelescope (← inferType inParent) (some 2) fun x _ => do
                let pair ← mkAppM ``Prod.mk #[x[0]!,param]
                mkLambdaFVars (#[j] ++ x)
                  (app (ns ++ key) (inputs ++ #[j,pair,mkAppN inParent x]))
          let displacement ← makeJets `displacement_unreserved_jets (g.args50 ++ #[g.data.i,color.color])
          let phase ← makeJets `phase_spatial_jets (g.args50.push g.data.i)
          let rateFacts ← Core.betaReduce (← zetaReduce (← exactType rates))
          let lam := rateFacts.getAppArgs[0]!.getAppArgs[3]!
          let one ← withLCtx {} #[] <| mkNumeral (mkConst ``Real) 1
          let known := #[(`n,raw[0]!),(`N,raw[1]!),(`P,raw[2]!),(`U,raw[3]!),(`hU,raw[4]!),
            (`T,raw[5]!),(`Q,raw[6]!),(`F,raw[7]!),(`row,raw[8]!),(`col,raw[9]!),
            (`Φ,raw[10]!),(`Y,raw[11]!),(`χ,χ),(`B,B),(`r,raw[12]!),
            (`Ω,region),(`hΩ,hregion),(`hspace,hspace),(`hphase,hphase),
            (`hF,app (wave ++ `current_map_smooth) s),(`hi,app (wave ++ `current_immersion) s),
            (`hrank,app (wave ++ `current_full_rank) s),(`hα,hα),(`hnonzero,hnonzero),
            (`τ,s[47]!),(`hτ,s[48]!),(`hresponse,hresponse),(`O,X),(`hO,hX),(`param,param),(`hOΩ,inRegion),
            (`a,app (ns ++ `Adisp) p),(`s,app (ns ++ `Pξ) p),
            (`ha,app (ns ++ `Adisp_nonneg) p),(`hs,app (ns ++ `Pξ_nonneg) p),
            (`lam,lam),(`L,s[45]!),(`Cτ,one),(`Cfreq,app (sharp ++ `Cfrequency) g.data.sampler22),
            (`hlam,part rates 0),(`hL,hL),(`hLlam,tail rates 4),(`hCfreq,hfreq),
            (`hfrequency,part rates 3),(`hτlam,hRate),(`hdisplacement,displacement),(`hphaseJets,phase)]
          liftM <| IO.eprintln "actual sharp jets: applying literal corrected atom theorem"
          let h ← applyThrough (sharp ++ `corrected_atom_sharp_spatial_jets) `hphaseJets known
          discard <| emit `atom_sharp_spatial_jets
            (g.args50 ++ #[g.data.i,color.color,param,hparam]) h false (some (← exactType h))

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_original_corrected_envelope_stage_rates
publish_native_corrected_envelope_phase
publish_native_corrected_envelope_displacement 0
publish_native_corrected_envelope_displacement 1
publish_native_corrected_envelope_sharp

end
