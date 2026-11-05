module
public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import Lean
/-! The actual BEFORE-B raw derivative amplitude on the original parent sigma
cover. Its original five coefficient profiles give the genuine coefficient
scale, not physical-lambda jets or a Fourier-cutoff ceiling. Consumer: the
primary half-stress source first-mask bound at the original unshifted phase
(main:eq:primary-strain; app:ch_regular:eq:source-tail). The full-source raw
identity/moment synthesis remains a separate actual instantiation. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitudeApplication
open Lean Meta Elab Command
open PhysicalMean.OriginalParentCorrectedProfilesTemplate (withActualParent)
private def root := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles
private def graded := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
private def poly := `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def tail (e : Expr) (k : Nat) : Expr := Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (tail e k)
private def nonnegative (cost : Expr) (k : Nat) : MetaM Expr := do
  let h := app (`JanetCartan.PhysicalNormalInverse.OriginalRetained.Budgets ++ Name.mkSimple s!"fact{k}") cost.getAppArgs
  forallBoundedTelescope (← inferType h) (some 1) fun j _ => do
    mkLambdaFVars j (← mkAppM `le_of_lt #[mkAppN h j])
private def smoothMono (h target subset : Expr) : MetaM Expr := do
  let t ← inferType h
  unless t.isAppOfArity `ContDiffOn 11 do throwError "actual raw amplitude: smoothness ABI changed"
  let a := t.getAppArgs
  return mkAppN (mkConst `ContDiffOn.mono t.getAppFn.constLevels!)
    (a[:8].toArray ++ #[a[10]!,a[9]!,a[8]!,h,target,subset])
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    unless (e.getUsedConstants.filter (fun c => (env.find? c).isNone)).isEmpty do
      throwError "actual raw amplitude: missing dependencies"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw amplitude: unresolved original input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"checking actual before-B amplitude {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual BEFORE-B raw derivative amplitude on the SAME original parent sigma-cover, from the five retained raw coefficient profiles. Genuine coefficient-scale jets; no corrected amplitude, output cutoff, Kmax, response estimate or angular success premise (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  logInfo m!"checked actual before-B raw amplitude {key}/{p.size}"

elab "prove_actual_raw_primary_amplitude " which:num : command => liftTermElabM <| withActualParent fun d => do
  let mode := which.getNat
  unless mode < 5 do throwError "actual raw amplitude: unknown mode"
  let raw := d.raw13
  let f := d.full60
  let cost := app (poly ++ `derivativeProfile) #[raw[0]!,raw[1]!,d.Pξ,d.Clead,d.Ccorr,d.Clead,d.Ccorr]
  let amp := app `JanetCartan.RawPrimary.fullDerivativeAmplitude (raw.push f[52]!)
  if mode == 0 then
    save `C d.static45 cost (← inferType cost) true
  else if mode == 1 then
    let bound ← mkAppM (poly ++ `polynomialProfiles_nonneg)
      #[raw[0]!,raw[1]!,← nonnegative d.Pξ 3,← nonnegative d.Clead 5,← nonnegative d.Ccorr 6,
        ← nonnegative d.Clead 5,← nonnegative d.Ccorr 6]
    forallBoundedTelescope (← inferType bound) (some 1) fun order _ => do
      let proof := tail (mkAppN bound order) 4
      let result ← inferType proof
      let result := result.replace fun e => if e == cost then some (app (root ++ `C) d.static45) else none
      save `C_nonneg d.static45 (← mkLambdaFVars order proof) (← mkForallFVars order result)
  else if mode == 2 then
    save `amplitude d.params52 amp (← inferType amp) true
  else
    let hJ := part d.static_geometry 0
    let hO := part d.static_geometry 1
    let hJO := tail d.static_geometry 2
    let O := (← inferType hO).appArg!
    let point := (← inferType O).appArg!
    let hRaw ← Term.TermElabM.run' <| PhysicalBackground.NativeReferenceSourceTemplate.termWith
      [(`O,O),(`rawOpen,d.rawOpen)]
      "(show O ⊆ rawOpen from Set.inter_subset_left)"
    let hphase ← withLocalDeclNoLocalInstanceUpdate `w .default point fun w => do
      withLocalDeclNoLocalInstanceUpdate `hw .default (← mkAppM `Membership.mem #[O,w]) fun hw =>
        mkLambdaFVars #[w,hw] (mkAppN (part d.coeff 3) #[w,mkAppN hRaw #[w,hw]])
    let smooth ← (#[4,5,6,7] : Array Nat).mapM fun j => smoothMono (part d.coeff j) O hRaw
    if mode == 3 then
      let proof := app `JanetCartan.RawPrimary.AmplitudeGrades.contDiffOn_fullAmplitudes_of_coefficients
        (raw ++ #[O,hO,hphase] ++ smooth ++ #[f[52]!,← mkAppM `ne_of_gt #[f[53]!]])
      let proof := Expr.proj ``And 1 proof
      let result := (← inferType proof).replace fun e => if e == amp then some (app (root ++ `amplitude) d.params52) else none
      save `smooth d.params52 proof result
    else
      let hTwo ← mkAppM `le_trans #[app (graded ++ `hS) d.params52[:44].toArray,d.params52[45]!]
      let hK ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le #[hTwo,d.params52[46]!]
      let hP ← nonnegative d.Pξ 3
      let hLead ← nonnegative d.Clead 5
      let hCorr ← nonnegative d.Ccorr 6
      let args := raw ++ #[d.compact,O,hJ,hO,hJO,hphase] ++ smooth ++
        #[f[42]!,d.Pξ,d.Clead,d.Ccorr,d.Clead,d.Ccorr,hP,hLead,hCorr,hLead,hCorr,
          f[52]!,f[50]!,f[53]!,f[58]!,hK,part d.coeff 8,part d.coeff 9,part d.coeff 10,
          part d.coeff 11,part d.coeff 12]
      unless args.size == 44 do throwError "actual raw amplitude: original joint-profile44 changed"
      let bound := app (poly ++ `full_amplitude_joint_bounds) args
      forallBoundedTelescope (← inferType bound) (some 3) fun point _ => do
        let proof := part (mkAppN bound point) 1
        let result := (← inferType proof).replace fun e =>
          if e == amp then some (app (root ++ `amplitude) d.params52)
          else if e == cost then some (app (root ++ `C) d.static45) else none
        save `jets d.params52 (← mkLambdaFVars point proof) (← mkForallFVars point result)
end JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitudeApplication
end
prove_actual_raw_primary_amplitude 0
prove_actual_raw_primary_amplitude 1
prove_actual_raw_primary_amplitude 2
prove_actual_raw_primary_amplitude 3
prove_actual_raw_primary_amplitude 4
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude.C
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude.C_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude.amplitude
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude.smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude.jets
