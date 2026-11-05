module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! The actual native positive scalar and its already-proved high profile
instantiate the original retained raw fields BEFORE restricting their parent
compact to the sampling sub-ball. No density/profile/response is assumed here. -/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
open PhysicalSampling.OriginalNativeGradedEventApplication

private def ns := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def ps := `JanetCartan.PhysicalSampling
private def ni := ps ++ `OriginalNativeInitialEvent
private def br := ps ++ `OriginalBareEvent
private def po := ps ++ `OriginalPositiveEvent
private def st := ps ++ `OriginalCommonStage
private def sm := ps ++ `OriginalNativeSmoothEvent
private def cur := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent
private def retainedNS := `JanetCartan.PhysicalNormalInverse.OriginalRetained
private def nat := `JanetCartan.PhysicalBackground.NativeAdmission
private def app (n : Name) (a : Array Expr) := mkAppN (mkConst n) a
private def tail (e : Expr) (k : Nat) := Nat.repeat (fun v => Expr.proj ``And 1 v) k e
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (tail e k)
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private partial def headOnly (e : Expr) : Expr :=
  match e.headBeta with
  | .letE _ _ v b _ => headOnly (b.instantiate1 v)
  | result => result
private def bodyAt (n : Name) (a : Array Expr) : MetaM Expr := do
  let some b := (← getConstInfo n).value? (allowOpaque := true) |
    throwError "actual corrected envelope: missing producer {n}"
  return headOnly (b.beta a)
private def need (e : Expr) (n : Name) (k : Nat) : MetaM (Array Expr) := do
  let some a := e.find? (·.isAppOfArity n k) |
    throwError "actual corrected envelope: missing literal {n}/{k}"
  return a.getAppArgs
private def emit (key : Name) (xs : Array Expr) (v : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ key) xs v data target
  addDocStringCore (ns ++ key) "Actual same-native-scalar raw/corrected displacement and phase profiles on the unchanged parent cell, with prehistory constants and the original uncut response; no new field, norm hypothesis or physical cutoff (app:ch_response:eq:current-atomic-amplitudes, main:eq:primary-fixed-scales)."
  logInfo m!"actual original corrected envelope: checked {key} / {xs.size}"
  return h

private def checkpoint (label : String) : MetaM Unit := do
  let left ← getRemainingHeartbeats
  liftM <| IO.eprintln s!"actual envelope checkpoint {label}: {left} heartbeats remain"
  liftM <| (← IO.getStderr).flush

private def gd := ps ++ `OriginalNativeGradedEvent

/-- Ordered real transitivity avoids reverse unification through the large
native threshold choices. The middle expressions are the original getters. -/
private def trans (h k : Expr) : MetaM Expr := do
  let a ← inferType h
  let b ← inferType k
  unless a.isAppOfArity ``LE.le 4 && b.isAppOfArity ``LE.le 4 do
    throwError "actual corrected envelope: threshold chain ceased to be numerical"
  let inst ← synthInstance (mkApp (mkConst ``Preorder [.zero]) (mkConst ``Real))
  return mkAppN (mkConst ``le_trans [.zero])
    #[mkConst ``Real,inst,a.getAppArgs[2]!,a.getAppArgs[3]!,b.getAppArgs[3]!,h,k]

/-- A read-only view of the already published actual50 theorem. This is the
same NativeGradedStage, without replaying its original prehistory choices. -/
def withPublishedNativeStage (run : NativeGradedStage → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (gd ++ `uncut_response_jets)).type (some 50) fun x _ => do
    unless x.size == 50 do throwError "actual corrected envelope: actual graded50 changed"
    checkpoint "opened-published50"
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
        throwError "actual corrected envelope: published native initial39 changed"
      let sampler := p[:3].toArray ++ source[2:20].toArray ++ #[source[20]!.appArg!]
      let d : PhysicalSampling.OriginalNativeSourceRowsApplication.Data :=
        ⟨smooth[:44].toArray,high[:44].toArray,sampler,scalar.getAppArgs[:33].toArray,source,i,I⟩
      let hs ← trans ev x[45]!
      let hr ← trans (app (gd ++ `response_le) (p.push i)) x[45]!
      let hist := x[46:50].toArray
      let prior := app (sm ++ `exists_of_quantitative_uncut_jets) (smooth ++ #[x[44]!,hs] ++ hist)
      checkpoint "published-stage-view"
      run ⟨d,p,q,x,smooth,high,hist,prior,hs,hr,x[45]!⟩

structure NativeRawRow where
  stage : NativeGradedStage
  highReached : Expr
  nativeReached : Expr
  current49 : Array Expr
  retained40 : Array Expr
  coeff : Expr
  stageRates : Expr

/-- Read the actual original graded stage, positive scalar and its high profile.
The retained tuple is unchanged; use its original σcover compact rather than
the strictly smaller sampling-radius specialization. -/
def withNativeRawRow (go : NativeRawRow → MetaM Unit) : MetaM Unit :=
  withPublishedNativeStage fun g => do
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
    checkpoint "native39-thresholds"
    let positive ← bodyAt (nat ++ `positive_inverse_exists) native39
    unless positive.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.all_densities 52 do
      throwError "actual corrected envelope: lost original positive density52"
    let density := (positive.getAppArgs[47:52].toArray.map (fun e => mkApp e i)).set! 4
      (app (nat ++ `labels_C15) (native39.push i))
    let original40 ← need (← bodyAt (cur ++ `retained_profiles) current)
      (retainedNS ++ `on_original_sampling_radius) 40
    checkpoint "parent-retained40"
    let n := (← inferType d.native33[1]!).appArg!
    let rpar := app `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder #[n]
    let add (a b : Expr) := mkAppM ``HAdd.hAdd #[a,b]
    let floor ← add (← mkAppM ``HMul.hMul #[mkNatLit 20,← add n (mkNatLit 1)]) (mkNatLit 1)
    let required ← add (mkNatLit 14) (← add rpar (mkNatLit 2))
    let hfloor ← termWith []
      "(by dsimp only [JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder, JanetCartan.RawPrimary.SliceBounds.rawSliceJetOrder]; omega)"
      (some (← mkAppM ``LE.le #[floor,rpar]))
    let sourceReserveType ← inferType d.source39[38]!
    unless sourceReserveType.isAppOfArity ``LE.le 4 do
      throwError "actual corrected envelope: source39 lost its numerical reserve"
    let hStar ← termWith [(`hSourceReserve,d.source39[38]!)] "(by clear * - hSourceReserve; omega)"
      (some (← mkAppM ``LE.le #[required,sourceReserveType.getAppArgs[3]!]))
    let hInitialOrder ← termWith [] "(by omega)"
      (some (← mkAppM ``LE.le #[required,d.initial44[40]!]))
    checkpoint "raw-numeric-reserves"
    let initialProfile := app (ni ++ `native_initial_profile)
      (g.high47 ++ #[R,hh] ++ g.history ++ #[i])
    let coeff := app (retainedNS ++ `positive_continuation)
      (original40 ++ density ++ #[rpar,d.initial44[40]!,hfloor,hStar,hInitialOrder,initialProfile])
    let rates := app (st ++ `stage_rates) (stage ++ #[R,hs,g.history[0]!])
    go ⟨g,hh,hn,current,original40,coeff,rates⟩

elab "publish_original_corrected_envelope_raw" : command => liftTermElabM do
  withNativeRawRow fun row => do
    let g := row.stage
    checkpoint "raw-before-kernel"
    discard <| emit `raw_coefficients (g.args50.push g.data.i) row.coeff

elab "publish_original_corrected_envelope_stage_rates" : command => liftTermElabM do
  withNativeRawRow fun row => do
    discard <| emit `stage_rates row.stage.args50 row.stageRates

elab "publish_original_corrected_envelope_budget " field:num : command => liftTermElabM do
  let keys : Array (Name × Name × Nat) := #[(`Pξ,`Pξ_nonneg,3),(`Clead,`Clead_nonneg,5),(`Ccorr,`Ccorr_nonneg,6)]
  unless field.getNat < keys.size do throwError "actual corrected envelope: unknown budget field"
  let (key,nonneg,k) := keys[field.getNat]!
  withNativeRawRow fun row => do
    let g := row.stage
    let b := row.retained40[:34].toArray
    discard <| emit key (g.params44.push g.data.i) (app (retainedNS ++ `Budgets ++ key) b) true
    let pos := app (retainedNS ++ `Budgets ++ Name.mkSimple s!"fact{k}") b
    let proof ← forallBoundedTelescope (← inferType pos) (some 1) fun j _ => do
      let positive := mkAppN pos j
      let t ← inferType positive
      unless t.isAppOfArity ``LT.lt 4 do throwError "actual corrected envelope: changed strict budget positivity"
      let a := t.getAppArgs
      mkLambdaFVars j (← mkAppOptM ``le_of_lt #[some a[0]!,none,some a[2]!,some a[3]!,some positive])
    discard <| emit nonneg (g.params44.push g.data.i) proof

structure ParentGeometry where
  coeff : Expr
  raw13 : Array Expr
  compact : Expr
  openSet : Expr
  center : Expr
  radius : Expr
  radius_pos : Expr
  compact_proof : Expr
  open_proof : Expr
  compact_in_open : Expr
  scale_one_le : Expr

/-- Geometry and phase-scale facts for the SAME already-published raw tuple. -/
def parentGeometry (g : NativeGradedStage) : MetaM ParentGeometry := do
  let coeff := app (ns ++ `raw_coefficients) (g.args50.push g.data.i)
  let smoothType ← inferType (part coeff 4)
  let smoothArgs := smoothType.getAppArgs
  let amplitude := smoothArgs[smoothArgs.size-2]!
  unless amplitude.isAppOfArity
      `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
    throwError "actual corrected envelope: raw amplitude13 changed"
  let a := amplitude.getAppArgs
  let O := smoothArgs.back!
  let profileType ← inferType (part coeff 8)
  unless profileType.isAppOf `JanetCartan.HasDerivativeProfile do
    throwError "actual corrected envelope: missing retained joint phase profile"
  let p := profileType.getAppArgs
  let J := p[p.size-5]!
  let center := J.getAppArgs[J.getAppNumArgs-2]!
  let radius ← Core.betaReduce (← zetaReduce J.appArg!)
  unless radius.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.σcover 4 do
    throwError "actual corrected envelope: lost original parent σcover"
  let hσ := tail (app `JanetCartan.PhysicalSeed.OriginalBoundary.comparison_pos radius.getAppArgs) 8
  let hJ ← termWith [] "(isCompact_closedBall _ _)" (some (← mkAppM `IsCompact #[J]))
  let hO ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[O]))
  let hJO ← termWith [(`hσ,hσ)]
    "(by exact Metric.closedBall_subset_ball (by linarith only [hσ]))"
    (some (← mkAppM `Set.Subset #[J,O]))
  let hTwo ← trans (app (gd ++ `hS) g.params44) g.hR
  let hL ← mkAppM
    `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
    #[hTwo,g.history[0]!]
  return ⟨coeff,a,J,O,center,radius,hσ,hJ,hO,hJO,hL⟩

elab "publish_original_corrected_envelope_costs" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let p := g.params44.push g.data.i
    let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 g.data.native33[23]!]
    let A := app (ns ++ `Clead) p
    let B := app (ns ++ `Ccorr) p
    let D := app `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.Cdisp g.physical44
    let hD := app `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.Cdisp_nonneg g.physical44
    discard <| emit `Adisp p
      (app (ns ++ `correctedDisplacementCost) #[A,B,D,g.data.native33[21]!]) true
    discard <| emit `Adisp_nonneg p (← mkAppM (ns ++ `correctedDisplacementCost_nonneg)
      #[app (ns ++ `Clead_nonneg) p,app (ns ++ `Ccorr_nonneg) p,hD,hσ])

elab "publish_original_corrected_envelope_phase" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let a ← parentGeometry g
    let p := g.params44.push g.data.i
    let result ← mkAppM (ns ++ `phase_spatial_jets_of_retained_profile)
      #[a.raw13[5]!,a.raw13[6]!,a.compact_proof,a.open_proof,a.compact_in_open,
        part a.coeff 3,a.scale_one_le,app (ns ++ `Pξ_nonneg) p,part a.coeff 8]
    discard <| emit `phase_spatial_jets (g.args50.push g.data.i) result

structure NativeResponseColor where
  color : Expr
  source53 : Array Expr
  weak38 : Array Expr
  full60 : Array Expr
  graph42 : Array Expr

/-- The SAME source53/weak38 and response60 as the closed actual sampler;
only the response's parent-domain use below differs from its K restriction. -/
def withNativeResponseColor (g : NativeGradedStage)
    (go : NativeResponseColor → MetaM Unit) : MetaM Unit := do
  let d := g.data
  let R := g.args50[44]!
  let hh ← trans (app (sm ++ `event_le) g.smooth47) g.hSmooth
  let hNat ← trans (app (ni ++ `native_le) g.high47) hh
  let hRows ← trans (app (sm ++ `source_le) g.smooth47) g.hSmooth
  let hSrc ← trans (app (ps ++ `OriginalNativeSourceRows.source_le) (d.fixed.push d.i)) hRows
  let smooth := app (sm ++ `uncut_response_smooth)
    (g.smooth47 ++ #[R,g.hSmooth] ++ g.history ++ #[d.i])
  forallBoundedTelescope (← inferType smooth) (some 1) fun color _ => do
    unless color.size == 1 do throwError "actual corrected envelope: missing native color"
    let c := color[0]!
    let fullType ← inferType (mkApp smooth c)
    let tensor ← need fullType `JanetCartan.CorrectedAtoms.fullPrimaryResponse 18
    let rate := tensor[14]!
    unless tensor[13]!.isAppOfArity (ps ++ `OriginalGraphResponse.B) 42 do
      throwError "actual corrected envelope: lost SAME measured graph42 response"
    let w ← need (← bodyAt (ps ++ `OriginalGraphResponse.B) tensor[13]!.getAppArgs)
      `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38
    let pic ← mkAppM ``Prod.mk #[d.i,c]
    let hradial := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.radial_ge_one
      (d.sampler22.push pic)
    let hTwo ← trans (app (gd ++ `hS) g.params44) g.hR
    let hOne ← termWith [(`hTwo,hTwo)] "(by linarith only [hTwo])"
      (some (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 1,R]))
    let win ← mkAppM `JanetCartan.PhysicalPrimary.OriginalReservedWords.colored_window_of_radial
      #[hOne,hradial,g.history[0]!]
    let K := app `JanetCartan.currentCoefficientScale #[R,g.history[0]!]
    let scalar := app (ps ++ `OriginalNativeSourceScalar.scalar)
      (d.native33 ++ #[R,hNat] ++ g.history ++ #[d.i])
    let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 d.native33[23]!]
    let hRate := part win 0
    let sourceArgs := d.fixed ++ g.high47[44:47].toArray ++ #[R,hh] ++ g.history ++
      #[d.i,hSrc,rate,hRate]
    let highProof := app `JanetCartan.PhysicalPrimary.OriginalActualInitialSource.source52 sourceArgs
    let s := d.source39 ++ #[R,hSrc] ++ g.history ++
      #[K,← mkAppM `le_refl #[K],rate,hRate,scalar,d.native33[21]!,hσ,highProof]
    unless s.size == 53 do throwError "actual corrected envelope: actual Source53 changed"
    let rateOne ← termWith [(`hinv,part win 1)]
      "(by simpa only [inv_inv] using inv_le_one_of_one_le₀ hinv)"
      (some (← mkAppM ``LE.le #[rate,← mkNumeral (mkConst ``Real) 1]))
    let full60 := g.physical44 ++ #[R,g.hPhysical] ++ s[41:53].toArray ++ #[rateOne,tail win 2]
    unless full60.size == 60 do throwError "actual corrected envelope: response60 changed"
    go ⟨c,s,w,full60,tensor[13]!.getAppArgs⟩

elab "publish_original_corrected_envelope_displacement" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let a ← parentGeometry g
    let p := g.params44.push g.data.i
    withNativeResponseColor g fun color => do
      let s := color.source53
      let w := color.weak38
      let hcurrent := app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.current_cell s
      let cellArgs := a.radius.getAppArgs
      let hW := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec cellArgs
      let hParent ← mkAppM (ns ++ `parent_compact_in_response)
        #[a.radius_pos,hcurrent,tail hW 3]
      let source57 := s ++ #[w[24]!,w[29]!,w[30]!,w[33]!]
      let hFull := app `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity.full_response_smooth source57
      let c ← mkAppM ``Prod.snd #[a.center]
      let hBall := app (ns ++ `parent_ball_in_parameter_window)
        #[a.raw13[0]!,← mkAppM ``HSub.hSub #[a.raw13[0]!,mkNatLit 1],c,a.radius]
      let hResponse ← mkAppM `ContDiffOn.mono #[hFull,hBall]
      let physical := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
      let hResponseJets ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        let joint := (← inferType a.compact).appArg!
        withLocalDeclD `w joint fun q => do
          withLocalDeclD `hw (← mkAppM `Membership.mem #[a.compact,q]) fun hq => do
            let h := app (physical ++ `displacement_jets)
              (color.full60 ++ #[j,q,mkAppN hParent #[q,hq]])
            mkLambdaFVars #[j,q,hq] (← mkAppM (ns ++ `response_displacement_weight) #[h])
      let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 g.data.native33[23]!]
      let hD ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        let h ← mkAppM `mul_nonneg
          #[hσ,mkApp (app (physical ++ `Cdisp_nonneg) g.physical44) j]
        mkLambdaFVars #[j] h
      let χ := (← inferType (app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth
        s[:23].toArray)).appArg!
      let B := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B w
      let raw := a.raw13
      let hLead := app (ns ++ `Clead_nonneg) p
      let hCorr := app (ns ++ `Ccorr_nonneg) p
      let args := raw[5:12].toArray ++ #[χ,B,raw[12]!,a.compact_proof,a.open_proof,
        a.compact_in_open,part a.coeff 3,part a.coeff 4,part a.coeff 5,
        part a.coeff 6,part a.coeff 7,app (ns ++ `Pξ_nonneg) p,
        hLead,hCorr,hLead,hCorr,hD,s[48]!,color.full60[58]!,a.scale_one_le,
        part a.coeff 8,part a.coeff 9,part a.coeff 10,part a.coeff 11,
        part a.coeff 12,hResponse,hResponseJets]
      unless args.size == 34 do throwError "actual corrected envelope: changed displacement theorem inputs"
      let graded ← mkAppM `JanetCartan.CorrectedAtoms.fullCorrectedDisplacementAmplitude_joint_bounds args
      let mixed ← mkAppM `JanetCartan.CorrectedAtoms.fullCorrectedDisplacementAmplitude_mixed_bounds args
      let result ← forallBoundedTelescope (← inferType graded) (some 3) fun point _ => do
        unless point.size == 3 do throwError "actual corrected envelope: changed jet/point/membership tail"
        mkLambdaFVars point (part (mkAppN graded point) 0)
      discard <| emit `displacement_jets (g.args50 ++ #[g.data.i,color.color]) result
      let rpar := g.physical44[42]!
      let unreserved ← forallBoundedTelescope (← inferType graded) (some 3) fun point _ => do
        let hzero := app ``Nat.zero_le #[rpar]
        let h := mkAppN mixed #[point[0]!,mkNatLit 0,hzero,point[1]!,point[2]!]
        mkLambdaFVars point (part h 0)
      discard <| emit `displacement_unreserved_jets (g.args50 ++ #[g.data.i,color.color]) unreserved

private def sharp := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def physical := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse

elab "publish_original_corrected_envelope_sharp_cost" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let p := g.params44.push g.data.i
    let one ← mkNumeral (mkConst ``Real) 1
    let hOne ← termWith [] "(show (0 : ℝ) ≤ 1 from zero_le_one)"
    let cf := app (sharp ++ `Cfrequency) g.data.sampler22
    let hcf ← termWith [(`h,app (sharp ++ `Cfrequency_ge_one) g.data.sampler22)]
      "(by linarith only [h])" (some (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,cf]))
    discard <| emit `Cphysical p
      (app (sharp ++ `sharpJetCost) #[one,cf,app (ns ++ `Adisp) p,app (ns ++ `Pξ) p]) true
    discard <| emit `Cphysical_nonneg p (← mkAppM (sharp ++ `sharpJetCost_nonneg)
      #[hOne,hcf,app (ns ++ `Adisp_nonneg) p,app (ns ++ `Pξ_nonneg) p])

elab "publish_original_corrected_envelope_sharp" : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let a ← parentGeometry g
    let p := g.params44.push g.data.i
    withNativeResponseColor g fun color => do
      let s := color.source53
      let w := color.weak38
      let raw := a.raw13
      let cp := raw[0:1].toArray ++ #[s[1]!] ++ a.radius.getAppArgs[2:4].toArray
      let hcut := app (geo ++ `smoothing_chart_in_source_chart) s[:23].toArray
      let hchart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_in_cell
        (s[:23].toArray ++ cp[2:4].toArray)
      let hx ← mkAppM `Set.Subset.trans #[hcut,hchart]
      let hproduct ← mkAppM (ns ++ `cutoff_chart_product_in_parent) #[hx]
      let productType ← inferType hproduct
      let rectangle := productType.getAppArgs[productType.getAppNumArgs-2]!
      let X := rectangle.getAppArgs[rectangle.getAppNumArgs-2]!
      let cell := rectangle.appArg!
      let hX ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[X]))
      let hcurrent := app (geo ++ `current_cell) s
      let hW := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec cp
      let hparent ← mkAppM (ns ++ `parent_compact_in_response)
        #[a.radius_pos,hcurrent,tail hW 3]
      let hregion := app (physical ++ `region_open) color.full60
      let region := (← inferType hregion).appArg!
      let pointType := (← inferType region).appArg!
      let restrict (h : Expr) : MetaM Expr := withLocalDeclD `q pointType fun q => do
        withLocalDeclD `hq (← mkAppM `Membership.mem #[region,q]) fun hq =>
          mkLambdaFVars #[q,hq] (mkAppN h #[q,Expr.proj ``And 0 hq])
      let hspace ← restrict (app (geo ++ `current_space) s)
      let hphase ← restrict (app (geo ++ `current_phase) s)
      let hnonzero ← restrict (app (wave ++ `nullvectors_nonzero) s)
      let hSubset ← withLocalDeclD `q pointType fun q => do
        withLocalDeclD `hq (← mkAppM `Membership.mem #[region,q]) fun hq =>
          mkLambdaFVars #[q,hq] (Expr.proj ``And 0 hq)
      let hα ← mkAppM `ContDiffOn.mono #[app (wave ++ `scalar_smooth) s,hSubset]
      let hresponse := app (physical ++ `response_smooth) color.full60
      let hTwo ← trans (app (gd ++ `hS) g.params44) g.hR
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
      let χ := (← inferType (app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth
        s[:23].toArray)).appArg!
      let B := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B w
      withLocalDeclD `param (← inferType (← mkAppM ``Prod.snd #[a.center])) fun param => do
        withLocalDeclD `hparam (← mkAppM `Membership.mem #[cell,param]) fun hparam => do
          let inParent ← withLocalDeclD `x (← inferType X).appArg! fun x => do
            withLocalDeclD `hx (← mkAppM `Membership.mem #[X,x]) fun hx => do
              let pair ← mkAppM ``Prod.mk #[x,param]
              let hpair ← mkAppM ``And.intro #[hx,hparam]
              mkLambdaFVars #[x,hx] (mkAppN hproduct #[pair,hpair])
          let inRegion ← forallBoundedTelescope (← inferType inParent) (some 2) fun x _ => do
            let pair ← mkAppM ``Prod.mk #[x[0]!,param]
            mkLambdaFVars x (mkAppN hparent #[pair,mkAppN inParent x])
          let makeJets (key : Name) (inputs : Array Expr) : MetaM Expr :=
            withLocalDeclD `j (mkConst ``Nat) fun j => do
              forallBoundedTelescope (← inferType inParent) (some 2) fun x _ => do
                let pair ← mkAppM ``Prod.mk #[x[0]!,param]
                mkLambdaFVars (#[j] ++ x)
                  (app (ns ++ key) (inputs ++ #[j,pair,mkAppN inParent x]))
          let displacement ← makeJets `displacement_unreserved_jets
            (g.args50 ++ #[g.data.i,color.color])
          let phase ← makeJets `phase_spatial_jets (g.args50.push g.data.i)
          let h ← mkAppM (sharp ++ `corrected_atom_sharp_spatial_jets)
            (raw[5:12].toArray ++ #[χ,B,raw[12]!,hregion,hspace,hphase,
              app (wave ++ `current_map_smooth) s,app (wave ++ `current_immersion) s,
              app (wave ++ `current_full_rank) s,hα,hnonzero,s[48]!,hresponse,hX,
              param,inRegion,app (ns ++ `Adisp) p,app (ns ++ `Pξ) p,
              app (ns ++ `Adisp_nonneg) p,app (ns ++ `Pξ_nonneg) p,
              part rates 0,hL,tail rates 4,hfreq,part rates 3,hRate,displacement,phase])
          discard <| emit `atom_sharp_spatial_jets
            (g.args50 ++ #[g.data.i,color.color,param,hparam]) h

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
end
