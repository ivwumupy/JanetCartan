module

public meta import Lean

/-!
# Actual full-parent corrected-amplitude application

Read the saved native event and the actual parent raw tuple, retaining its
unrestricted positive scalar. The original response, cutoff and inverse are
not reconstructed. All constants close over prehistory44 and the original row.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalParentCorrectedProfilesTemplate
open Lean Meta Elab Command

private def ns := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles
private def native := ns ++ `Native
private def physical := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
private def envelope := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def budgets := `JanetCartan.PhysicalNormalInverse.OriginalRetained.Budgets
private def graded := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
private def app (n : Name) (a : Array Expr) := mkAppN (mkConst n) a
private def tail (p : Expr) (j : Nat) := Nat.repeat (fun q ↦ Expr.proj ``And 1 q) j p
private def part (p : Expr) (j : Nat) := Expr.proj ``And 0 (tail p j)

private def smoothMono (h target subset : Expr) : MetaM Expr := do
  let type ← inferType h
  unless type.isAppOfArity `ContDiffOn 11 do
    throwError "actual parent amplitude: changed joint smoothness signature"
  let a := type.getAppArgs
  return mkAppN (mkConst `ContDiffOn.mono type.getAppFn.constLevels!)
    (a[:8].toArray ++ #[a[10]!,a[9]!,a[8]!,h,target,subset])

private def realTrans (h k : Expr) : MetaM Expr := do
  let a ← inferType h
  let b ← inferType k
  unless a.isAppOfArity ``LE.le 4 && b.isAppOfArity ``LE.le 4 do
    throwError "actual parent amplitude: threshold chain ceased to be numerical"
  let inst ← synthInstance (mkApp (mkConst `Preorder [.zero]) (mkConst `Real))
  return mkAppN (mkConst `le_trans [.zero])
    #[mkConst `Real,inst,a.getAppArgs[2]!,a.getAppArgs[3]!,b.getAppArgs[3]!,h,k]

private def save (key : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let proof ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || proof.hasFVar || type.hasMVar || proof.hasMVar ||
      type.hasLevelMVar || proof.hasLevelMVar || type.hasLooseBVars || proof.hasLooseBVars ||
      type.hasSorry || proof.hasSorry then
    throwError "actual parent amplitude: late/open or recovered operand in {key}"
  if data then
    addDecl (.defnDecl {name := native ++ key,levelParams := [],type,value := proof,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name := native ++ key,levelParams := [],type,value := proof}) (forceExpose := true)
  addDocStringCore (native ++ key) "Actual whole-parent corrected derivative amplitude on the unchanged native event, full source response and original positive scalar; no inner coefficient mask or replaced inverse (app:ch_waves:eq:background-quadrature, app:ch_response:eq:current-atomic-amplitudes)."
  logInfo m!"checked original full-parent amplitude {key}/{params.size}"
  return app (native ++ key) params

structure ActualParent where
  params52 : Array Expr
  static45 : Array Expr
  full60 : Array Expr
  source53 : Array Expr
  coeff : Expr
  raw13 : Array Expr
  compact : Expr
  rawOpen : Expr
  center : Expr
  radius : Expr
  radius_pos : Expr
  window : Expr
  window_spec : Expr
  static_geometry : Expr
  Pξ : Expr
  Clead : Expr
  Ccorr : Expr

private def nativeTelescope (type : Expr) (count : Nat)
    (go : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,result,xs => go xs result
    | remaining+1,type,xs => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual parent amplitude: native telescope ended at {xs.size}"
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop remaining (body.instantiate1 x) (xs.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
          loop remaining (body.instantiate1 x) (xs.push x)

/-- Extract the real response60 from its already-checked native52 proof, then
read raw51 BEFORE the original working-radius restriction. No callback is rerun. -/
def withActualParent (go : ActualParent → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo (graded ++ `uncut_response_jets)
  let some body := info.value? (allowOpaque := true) |
    throwError "actual parent amplitude: missing saved native response"
  nativeTelescope info.type 52 fun p _ => do
    unless p.size == 52 do throwError "actual parent amplitude: native52 changed"
    let value := (body.beta p).headBeta
    let some full := value.find? (·.isAppOfArity (physical ++ `derivative_jets) 60) |
      throwError "actual parent amplitude: missing SAME full response60"
    let some window := value.find? (·.isAppOfArity
        `JanetCartan.PhysicalSampling.OriginalResponseWindow.working_in_native_graded_domain 54) |
      throwError "actual parent amplitude: missing original source53 route"
    if full.hasLooseBVars || window.hasLooseBVars then
      throwError "actual parent amplitude: response/source depends on later jet point"
    let f := full.getAppArgs
    let s := f[:21].toArray ++ window.getAppArgs[22:54].toArray
    let coeff := app (envelope ++ `raw_coefficients) p[:51].toArray
    let hν ← inferType (part coeff 4)
    let νargs := hν.getAppArgs
    let normal := νargs[νargs.size-2]!
    unless normal.isAppOfArity
        `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
      throwError "actual parent amplitude: lost uncontracted raw13"
    let raw := normal.getAppArgs
    let profile ← inferType (part coeff 8)
    unless profile.isAppOf `JanetCartan.HasDerivativeProfile do
      throwError "actual parent amplitude: missing raw phase profile"
    let q := profile.getAppArgs
    let J := q[q.size-5]!
    let radius ← Core.betaReduce (← zetaReduce J.appArg!)
    unless radius.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.σcover 4 do
      throwError "actual parent amplitude: compact is not the ORIGINAL parent cover"
    let center := J.getAppArgs[J.getAppNumArgs-2]!
    let cp := radius.getAppArgs
    let hσ := tail (app `JanetCartan.PhysicalSeed.OriginalBoundary.comparison_pos cp) 8
    let ws := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.parameterComparisonWindow_spec cp
    let W := (← inferType (part ws 0)).appArg!
    let c ← mkAppM ``Prod.snd #[center]
    let d := app ``Nat.sub #[raw[0]!,mkNatLit 1]
    let hg := app (ns ++ `parent_static_geometry) #[raw[0]!,d,c,radius,hσ,W,part ws 0,tail ws 3]
    let A := (← inferType (part coeff 9)).appArg!
    let B := (← inferType (part coeff 10)).appArg!
    go ⟨p,p[:44].toArray.push p[50]!,f,s,coeff,raw,J,νargs.back!,center,radius,hσ,W,ws,hg,
      q.back!,A,B⟩

private def budget_nonneg (cost : Expr) (k : Nat) : MetaM Expr := do
  let h := app (budgets ++ Name.mkSimple s!"fact{k}") cost.getAppArgs
  forallBoundedTelescope (← inferType h) (some 1) fun j _ => do
    let positive := mkAppN h j
    let t ← inferType positive
    unless t.isAppOfArity ``LT.lt 4 do
      throwError "actual parent amplitude: original budget positivity changed"
    let a := t.getAppArgs
    let inst ← synthInstance (mkApp (mkConst `Preorder [.zero]) a[0]!)
    mkLambdaFVars j (mkAppN (mkConst `le_of_lt [.zero]) #[a[0]!,inst,a[2]!,a[3]!,positive])

/-- Constants and compact are closed over original prehistory44 plus row ONLY. -/
elab "publish_original_parent_static " which:num : command => liftTermElabM <| withActualParent fun d => do
  let stage := which.getNat
  let n := d.raw13[0]!
  let N := d.raw13[1]!
  let f := d.full60
  let C := app (physical ++ `Cresp) f[:44].toArray
  if stage == 0 then
    discard <| save `A d.static45 (app (ns ++ `correctedCost) #[n,N,d.Pξ,d.Clead,d.Ccorr,C,f[55]!]) true
  else if stage == 1 then
    discard <| save `A_nonneg d.static45 (← mkAppM (ns ++ `correctedCost_nonneg)
      #[n,N,← budget_nonneg d.Pξ 3,← budget_nonneg d.Clead 5,← budget_nonneg d.Ccorr 6,
        app (physical ++ `Cresp_nonneg) f[:44].toArray,f[56]!])
  else if stage == 2 then
    discard <| save `J d.static45 d.compact true
  else if stage == 3 then
    discard <| save `Ω d.static45 (← inferType (part d.static_geometry 1)).appArg! true
  else if stage == 4 then
    discard <| save `J_compact d.static45 (part d.static_geometry 0)
  else if stage == 5 then
    discard <| save `Ω_open d.static45 (part d.static_geometry 1)
  else if stage == 6 then
    discard <| save `J_in_Ω d.static45 (tail d.static_geometry 2)
  else throwError "actual parent amplitude: unknown static publication"

/-- Apply the actual full source response and all five retained raw profiles
on the original parent compact, with the native colored rate already admitted. -/
elab "publish_original_parent_dynamic " which:num : command => liftTermElabM <| withActualParent fun d => do
  let stage := which.getNat
  let f := d.full60
  let raw := d.raw13
  let hFull := app (physical ++ `response_smooth) f
  let some response := (← inferType hFull).find? (·.isAppOfArity
      `JanetCartan.CorrectedAtoms.fullPrimaryResponse 18) |
    throwError "actual parent amplitude: literal full response disappeared"
  let response := response.getAppArgs
  let amp := app `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude
    (raw[:12].toArray ++ #[response[12]!,response[13]!,raw[12]!,f[52]!])
  if stage == 0 then
    discard <| save `amplitude d.params52 amp true
    return
  let hcurrent := app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.current_cell d.source53
  let sourceRegion := (← inferType hcurrent).appArg!
  let center ← mkAppM ``Prod.snd #[d.center]
  let hg := app (ns ++ `parent_geometry)
    #[raw[0]!,app ``Nat.sub #[raw[0]!,mkNatLit 1],center,d.radius,d.radius_pos,
      sourceRegion,d.window,hcurrent,part d.window_spec 0,tail d.window_spec 3]
  let hJ := part hg 0
  let hO := part hg 1
  let hJO := part hg 2
  let hRaw := part hg 3
  let hRegion := tail hg 4
  let O := (← inferType hO).appArg!
  let point := (← inferType O).appArg!
  if stage == 1 then
    let inclusion ← withLocalDeclD `w point fun w => do
      withLocalDeclD `hw (← mkAppM `Membership.mem #[d.compact,w]) fun hw =>
        mkLambdaFVars #[w,hw] (mkAppN hRegion #[w,mkAppN hJO #[w,hw]])
    discard <| save `parent_in_response d.params52 inclusion
    return
  let hResponse ← smoothMono hFull O hRegion
  let hphase ← withLocalDeclD `w point fun w => do
    withLocalDeclD `hw (← mkAppM `Membership.mem #[O,w]) fun hw =>
      mkLambdaFVars #[w,hw] (mkAppN (part d.coeff 3) #[w,mkAppN hRaw #[w,hw]])
  let smooth ← (#[4,5,6,7] : Array Nat).mapM fun j =>
    smoothMono (part d.coeff j) O hRaw
  if stage == 2 then
    let h := app (ns ++ `corrected_smooth_of_coefficients)
      (raw[:12].toArray ++ #[response[12]!,response[13]!,raw[12]!,O,hO,hphase] ++ smooth ++
        #[f[52]!,← mkAppM `ne_of_gt #[f[53]!],hResponse])
    discard <| save `smooth d.params52 h
    return
  let hJets ← withLocalDeclD `j (mkConst ``Nat) fun j => do
    withLocalDeclD `w point fun w => do
      withLocalDeclD `hw (← mkAppM `Membership.mem #[d.compact,w]) fun hw => do
        let hInside := mkAppN hRegion #[w,mkAppN hJO #[w,hw]]
        let h := app (physical ++ `derivative_jets) (f ++ #[j,w,hInside])
        mkLambdaFVars #[j,w,hw] (← mkAppM (ns ++ `response_derivative_weight) #[h])
  let hC ← withLocalDeclD `j (mkConst ``Nat) fun j => do
    mkLambdaFVars #[j] (← mkAppM `mul_nonneg
      #[f[56]!,mkApp (app (physical ++ `Cresp_nonneg) f[:44].toArray) j])
  let hTwo ← realTrans (app (graded ++ `hS) d.params52[:44].toArray) d.params52[45]!
  let hK ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
    #[hTwo,d.params52[46]!]
  let hLead ← budget_nonneg d.Clead 5
  let hCorr ← budget_nonneg d.Ccorr 6
  let responseCost ← forallBoundedTelescope (← inferType hC) (some 1) fun j type => do
    unless type.isAppOfArity ``LE.le 4 do
      throwError "actual parent amplitude: source-size-weighted response cost changed"
    mkLambdaFVars j type.appArg!
  let gradedArgs := raw[:12].toArray ++ #[response[12]!,response[13]!,raw[12]!,d.compact,O,
      hJ,hO,hJO,hphase] ++ smooth ++
    #[f[42]!,d.Pξ,d.Clead,d.Ccorr,d.Clead,d.Ccorr,responseCost,
      ← budget_nonneg d.Pξ 3,hLead,hCorr,hLead,hCorr,hC,f[52]!,f[50]!,f[53]!,f[58]!,hK,
      part d.coeff 8,part d.coeff 9,part d.coeff 10,part d.coeff 11,part d.coeff 12,hResponse,hJets]
  unless gradedArgs.size == 50 do throwError "actual parent amplitude: joint-profile50 ABI changed"
  let bound := app `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude_joint_bounds gradedArgs
  nativeTelescope (← inferType bound) 3 fun q _ => do
    let value := part (mkAppN bound q) 0
    let type ← inferType value
    unless type.isAppOfArity ``LE.le 4 && type.appArg!.isAppOf ``HMul.hMul do
      throwError "actual parent amplitude: changed original joint-jet profile shape"
    let rhs ← mkAppM ``HMul.hMul
      #[mkApp (app (native ++ `A) d.static45) q[0]!,type.appArg!.appArg!]
    let target ← mkAppM ``LE.le #[type.getAppArgs[2]!,rhs]
    unless ← withTransparency .default <| isDefEq type target do
      throwError "actual parent amplitude: source size or corrected reserve/cost changed"
    discard <| save `jets d.params52 (← mkLambdaFVars q value) false
      (some (← mkForallFVars q target))

end JanetCartan.PhysicalMean.OriginalParentCorrectedProfilesTemplate
end
