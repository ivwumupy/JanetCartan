module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticRealization
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometry
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
public meta import Lean

/-!
# Coordinates of the same actual quadratic primitives

This leaf retains the original full-rate phase, one angular mask, fixed prefix,
cut corrected amplitude, and whole annular integral. It imports the frozen
selected testers without reselecting an event or changing a native measure.
The consumer is `fixedSourceQuadratic_low_bound` and the shared high-source
application (`app:ch_mean_pairs:eq:block-bilinear`, `new:eq:mean-operators`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open RawInputPartition PhysicalForwardMean

/-- Static original working-ball support controls the whole joint cutoff;
no current-amplitude success premise is needed. -/
theorem cutoff_in_phase_domain {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (center : Euclidean n × (Euclidean 3 × Euclidean (n-1))) {ρ : ℝ}
    (hρ : 0 < ρ) (hκ : tsupport κ ⊆ closedBall center ρ)
    (hphase : closedBall center (2*ρ) ⊆ domain T) : tsupport κ ⊆ domain T :=
  hκ.trans ((closedBall_subset_closedBall (by linarith)).trans hphase)

/-- Projection from the unchanged full joint phase domain. -/
theorem phase_domain_point {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) :
    ∀ w ∈ domain T, (w.1,w.2.2) ∈ phaseDomain T := fun _ hw => hw

/-- The original angular factor can vanish and occurs exactly once. The
original radial bands supply compact support and the high-pass floor. -/
theorem original_full_mask_regular {n J : ℕ} {ηb : Euclidean (n-1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (a : ℝ) :
    Continuous (fun z : RefinedIndex J × Euclidean (n-1) ↦ a * singleBareScalarMask (originalForwardDetector hηb hr) z) ∧
    HasCompactSupport (fun z : RefinedIndex J × Euclidean (n-1) ↦ a * singleBareScalarMask (originalForwardDetector hηb hr) z) ∧
    (∀ z : RefinedIndex J × Euclidean (n-1), ‖z.2‖ ≤ 1 → a * singleBareScalarMask (originalForwardDetector hηb hr) z = 0) := by
  exact ⟨continuous_const.mul (continuous_singleBareScalarMask (contDiff_originalForwardDetector hηb hr).continuous),
    (hasCompactSupport_singleBareScalarMask (originalForwardDetector hηb hr)).mul_left,
    full_bare_mask_high hηb hr a⟩

/-- Use only the fixed geometric-row cost, never the number of samples or
retained bands, for the exact kernel reserve. -/
theorem forward_jet_budget_mono {n N : ℕ}
    (amp : Fin N → Fin n → Euclidean (n-1) → Euclidean n → ℂ)
    (K : Set (Euclidean n)) (A B : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hAB : ∀ j, A j ≤ B j)
    (h : ∀ a c η, ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (amp a c η) x‖ ≤ A j*T^(j-(2*(n/2+2)+(n/2+1)))) :
    ∀ a c η, ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (amp a c η) x‖ ≤ B j*T^(j-(2*(n/2+2)+(n/2+1))) := by
  intro a c η x hx j
  exact (h a c η x hx j).trans (mul_le_mul_of_nonneg_right (hAB j) (pow_nonneg (zero_le_one.trans hT) _))

/-- The same physical measurement, not a newly imposed joint cutoff,
places the measured cross amplitude in the common core. -/
theorem physical_measurement_core {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {μ : ℝ} (hμ : 0 < μ) :
    tsupport (Sampling.canonicalSamplingMeasurement Q hμ) ⊆ closedBall 0 (4*μ) :=
  (Sampling.tsupport_canonicalSamplingMeasurement Q hμ).trans
    (ContinuumRow.FixedCutoffs.physical_tsupport_four hμ 1)

/-- A proved equality of full phases transports the same chart, not a new
choice of its trade or normalized phase representative. -/
theorem chart_phase_transport {n J : ℕ}
    {φ φ' : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ}
    {Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ}
    {m : RefinedIndex J × Euclidean (n-1) → ℝ}
    {L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n}
    {K : Set (Euclidean n)} {DL DP : ℕ → ℝ} {rStar : ℕ} {T : ℝ}
    (heq : φ = φ') (h : OriginalSampledMomentGeometry.SampledChart φ Φ m L K DL DP rStar T) :
    OriginalSampledMomentGeometry.SampledChart φ' Φ m L K DL DP rStar T := heq ▸ h

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def root := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles
private def actual := root ++ `Actual
private def app (s : Name) (xs : Array Expr) := mkAppN (mkConst s) xs
private def part (e : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun q => Expr.proj ``And 1 q) j e)

private def save (key : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) (hints : ReducibilityHints := .abbrev) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  let name := actual ++ key
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual coordinates {name}: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "actual coordinates: open {name}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking {name}/{xs.size}"
  out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "Exact original quadratic coordinate or primitive, with the same whole annular sum, one angular factor, original measure and fixed prefix (app:ch_mean_pairs:eq:block-bilinear)."
  out.putStrLn s!"kernel passed {name}/{xs.size}"
  out.flush

/-- Retain the raw corrected phase without the two numerical chart guards;
transport the independently presented moment frame by its proved equality. -/
elab "construct_actual_quadratic_raw_phase " mode:num : command => liftTermElabM do
  let point := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry.AtPoint
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitude)).type (some 53) fun p _ => do
    OriginalMeanQuadraticApplication.withActualMomentAt p fun hγ hR xs => do
      if mode.getNat == 2 then
        let mask ← bodyAt (point ++ `mask) xs
        save `rawMask p mask true
        return
      let eq := app (actual ++ `moment_frame_eq_corrected) (p ++ #[hγ,hR])
      let qa := (← inferType eq).getAppArgs
      unless qa.size == 3 do throwError "actual coordinates: lost frame identity"
      let ph ← bodyAt (point ++ `φ) xs
      unless ph.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12 do
        throwError "actual coordinates: lost unchanged finite-rate phase"
      unless ph.getAppArgs[6]! == qa[1]! do throwError "actual coordinates: changed moment frame"
      let raw := ph.replace fun e => if e == qa[1]! then some qa[2]! else none
      if mode.getNat == 0 then
        save `rawPhase p raw true
        return
      let f ← withLocalDeclNoLocalInstanceUpdate `Q .default qa[0]! fun q => do
        mkLambdaFVars #[q] (ph.replace fun e => if e == qa[1]! then some q else none)
      let mut phaseType := (← getConstInfo (actual ++ `rawPhase)).type
      for v in p do
        let .forallE _ _ body _ := phaseType | throwError "actual coordinates: changed phase parameters"
        phaseType := body.instantiate1 v
      let proof := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
        #[qa[0]!,phaseType,qa[1]!,qa[2]!,f,eq]
      let target := mkAppN (mkConst ``Eq [.succ .zero])
        #[phaseType,app (point ++ `φ) xs,app (actual ++ `rawPhase) p]
      save `moment_phase_eq_raw (p ++ #[hγ,hR]) proof false (some target)

/-- Close original-mask regularity without any sample-weight nonzero premise. -/
elab "construct_actual_quadratic_raw_mask_regular" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `rawMask)).type (some 53) fun p _ => do
    let m ← bodyAt (actual ++ `rawMask) p
    let proof ← lambdaTelescope m fun args body => do
      unless args.size == 1 do throwError "actual mask: changed literal mask function"
      let some bare := body.find? (·.isAppOfArity `JanetCartan.PhysicalForwardMean.singleBareScalarMask 4)
        | throwError "actual mask: lost original scalar mask"
      let ba := bare.getAppArgs
      let det := ba[2]!
      unless det.isAppOfArity `JanetCartan.PhysicalForwardMean.originalForwardDetector 5 do
        throwError "actual mask: lost original detector"
      let da := det.getAppArgs
      unless body.isAppOfArity ``HMul.hMul 6 do throwError "actual mask: lost one angular factor"
      return app ``OriginalMeanQuadraticProfiles.Actual.original_full_mask_regular
        (#[ba[0]!,ba[1]!] ++ da[1:].toArray ++ #[body.getAppArgs[4]!])
    let target := (← inferType proof).replace fun e => if e == m then some (app (actual ++ `rawMask) p) else none
    save `rawMask_regular p proof false (some target)

/-- The checked chart keeps its original trade and fixed before-history costs. -/
elab "construct_actual_quadratic_raw_chart" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `moment_chart_envelope)).type (some 56) fun p _ => do
    let h := app (actual ++ `moment_chart_envelope) p
    let a := (← inferType h).getAppArgs
    let raw := app (actual ++ `rawPhase) p[:53].toArray
    let heq := app (actual ++ `moment_phase_eq_raw) p[:55].toArray
    let proof := app ``OriginalMeanQuadraticProfiles.Actual.chart_phase_transport
      (a[:3].toArray ++ #[raw] ++ a[3:].toArray ++ #[heq,h])
    save `raw_moment_chart p proof

/-- Apply the original static working-radius specification to its already
selected joint cutoff, before all reference/current data. -/
elab "construct_actual_quadratic_cutoff_phase_support" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalSampling.OriginalChoices.Cutoff
  forallBoundedTelescope (← getConstInfo (ns ++ `hκ_support)).type (some 7) fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let hκ := app (ns ++ `hκ_support) p
    let buffers := app `JanetCartan.PhysicalSampling.originalSamplingRadius_spec
      #[n,p[2]!,p[3]!,p[4]!,p[5]!,p[6]!]
    let hphase := part buffers 1
    let ball := (← inferType hκ).getAppArgs.back!
    let b := ball.getAppArgs
    let ρ := b.back!
    let rad ← match ρ with
      | .proj ``Subtype 0 v => pure v
      | _ => if ρ.isAppOfArity ``Subtype.val 3 then pure ρ.appArg! else throwError "actual cutoff: changed radius"
    let target := (← inferType hphase).getAppArgs.back!
    unless target.isAppOf `JanetCartan.LeadingWave.FullModulation.domain do throwError "actual cutoff: lost phase domain"
    let proof := app ``OriginalMeanQuadraticProfiles.Actual.cutoff_in_phase_domain
      (target.getAppArgs ++ #[app (ns ++ `κ) p,b[b.size-2]!,ρ,Expr.proj ``Subtype 1 rad,hκ,hphase])
    save `originalCutoff_phase_support p proof

/-- The actual unchanged common coefficient supplies measured-amplitude
support on the common physical core, without a joint-cutoff containment. -/
elab "construct_actual_quadratic_measurement_core" : command => liftTermElabM do
  let C := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.commonC
  forallBoundedTelescope (← getConstInfo C).type (some 50) fun p _ => do
    let raw ← bodyAt C p
    unless raw.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
      throwError "actual coordinates: lost same common measurement"
    let proof := app ``OriginalMeanQuadraticProfiles.Actual.physical_measurement_core raw.getAppArgs
    let target := (← inferType proof).replace fun e => if e == raw then some (app C p) else none
    save `common_measurement_support p proof false (some target)

/-- Retain the fixed all-row forward amplitude cost on the exact kernel order. -/
elab "construct_actual_quadratic_forward_envelope" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitude)).type (some 53) fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let fixed := p[:44].toArray
    let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
    let K := app (root ++ `Geometry.K) sampler
    let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
    let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
    let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
      #[p[44]!,hR,p[46]!]
    let source := fixed.push p[50]!
    let proof := app ``OriginalMeanQuadraticProfiles.Actual.forward_jet_budget_mono
      #[n,N,app (actual ++ `forwardAmplitude) p,K,
        app (actual ++ `forwardAmplitudeBudget) source,app (actual ++ `forwardAmplitudeBudgetTotal) fixed,T,hT,
        app (actual ++ `forwardAmplitudeBudget_le_total) source,app (actual ++ `forwardAmplitude_physical_jets) p]
    save `forwardAmplitude_total_jets p proof

private partial def supply (t term : Expr) (fields : Array (Name × Expr))
    (next : Expr → MetaM Unit) : MetaM Unit := do
  let .forallE k _ s _ := t | return ← next term
  let k := k.eraseMacroScopes
  let some (_,v) := fields.find? (·.1 == k) | throwError "actual annular coordinates: missing original input {k}"
  supply (s.instantiate1 v) (mkApp term v) fields next

/-- The native whole annular identity has no remaining support, phase-domain,
or amplitude premise: each is supplied by the same original static geometry. -/
elab "construct_actual_quadratic_native_coordinates" : command => liftTermElabM do
  let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
  let src := root ++ `Kernel.full_refined_annuli
  let model := actual ++ `retained_coordinates_on_original_annuli
  forallBoundedTelescope (← getConstInfo src).type (some 67) fun p rt => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let J := (← inferType p[65]!).getAppArgs[1]!
    let r := rt.getAppArgs[2]!
    let a := r.getAppArgs[4]!
    let observed := r.getAppArgs[5]!
    let ψ := observed.getAppArgs[4]!.appFn!
    let x := observed.getAppArgs[4]!.appArg!
    let inside := observed.getAppArgs[5]!
    let some rawA := inside.find? (·.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 17)
      | throwError "actual annular coordinates: lost corrected matrix"
    let aa := rawA.getAppArgs
    let A := rawA.appFn!
    let some detector := inside.find? (·.isAppOfArity `JanetCartan.Sampling.originalConicDetector 5)
      | throwError "actual annular coordinates: lost raw detector"
    let ds := detector.getAppArgs
    let family := p[:61].toArray
    let fixed := p[:22].toArray
    let i := app (wave ++ `original_sample_row) family
    let row := fixed.push i
    let o := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_support fixed
    let K := (← inferType o).getAppArgs.back!
    let ht := app (actual ++ `originalCutoff_plateau) row
    let c := app `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row row
    let hrow := mkApp (app (wave ++ `Whole.inner_factor_support) family) p[64]!
    let .forallE _ nz mem _ ← inferType hrow | throwError "actual annular coordinates: missing nonzero branch"
    let par := mem.getAppArgs[4]!
    let hgraph ← withLocalDeclNoLocalInstanceUpdate `ha .default nz fun ha => do
      mkLambdaFVars #[ha] (mkAppN (part c 3) #[par,mkApp hrow ha])
    let hκ ← withLocalDeclNoLocalInstanceUpdate `ha .default nz fun ha => do
      withLocalDeclNoLocalInstanceUpdate `y .default (app `JanetCartan.Euclidean #[n]) fun y => do
        withLocalDeclNoLocalInstanceUpdate `hy .default (← mkAppM ``Membership.mem #[K,y]) fun hy => do
          mkLambdaFVars #[ha,y,hy] (mkAppN ht #[y,hy,par,mkApp hrow ha])
    let κ ← forallBoundedTelescope (← inferType hκ) (some 5) fun _ r => do
      unless r.isAppOfArity ``Eq 3 do throwError "actual annular coordinates: missing plateau"
      return r.getAppArgs[1]!.appFn!
    let gm := (← inferType hgraph).bindingBody!
    let ball := gm.getAppArgs[3]!
    let z₀ := ball.getAppArgs[2]!.getAppArgs[2]!
    let Zraw := gm.getAppArgs[4]!.getAppArgs[2]!
    let ρ := ball.getAppArgs[3]!.getAppArgs[4]!
    let rad ← match ρ with
      | .proj ``Subtype 0 v => pure v
      | _ => if ρ.isAppOfArity ``Subtype.val 3 then pure ρ.appArg! else throwError "actual annular coordinates: lost radius"
    let node := p[64]!
    let Z ← nodeAt node
    let heq := app ``JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate.outer_sampling_node #[node]
    let shift := app (root ++ `Whole.refined_shift_le_quarter) p[:64].toArray
    unless κ.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Cutoff.κ 7 do
      throwError "actual annular coordinates: changed static cutoff"
    let hs := app (actual ++ `originalCutoff_phase_support) κ.getAppArgs
    let Ω := (← inferType hs).getAppArgs.back!
    let hp := app (actual ++ `phase_domain_point) Ω.getAppArgs
    let fields := #[(`Ω,Ω),(`hs,hs),(`hphase,hp),(`e,p[0]!),(`N,aa[1]!),(`J,J),(`P,aa[2]!),(`U,aa[3]!),(`hU,aa[4]!),(`T,aa[5]!),(`Q,aa[6]!),
      (`z₀,z₀),(`Z,Z),(`Zraw,Zraw),(`heq,heq),(`ρ,ρ),(`hρ,Expr.proj ``Subtype 1 rad),(`τ,aa[15]!),
      (`a,a),(`ψ,ψ),(`K,K),(`hψK,o),(`ηb,ds[1]!),(`r,ds[2]!),(`hηb,ds[3]!),(`hr,ds[4]!),
      (`A,A),(`κ,κ),(`hgraph,hgraph),(`hκ,hκ),(`hshift,shift),(`x,x),(`w,p[65]!)]
    for (k,e) in fields do
      if e.hasLooseBVars then throwError "actual annular coordinate {k} escaped under integration"
    supply (← getConstInfo model).type (mkConst model) fields fun h => do
      let ht ← inferType h
      let eq := mkAppN (mkConst ``Eq.trans [.succ .zero]) (rt.getAppArgs ++ #[ht.getAppArgs[2]!,app src p,h])
      save `native_forward_realization p eq

/-- Name exactly the existing consumer's hG predicate so the native and
actual specializations share their integral expression before kernel checking. -/
elab "construct_actual_quadratic_forward_predicate" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `prefix_annular_realization)).type (some 7) fun p rest => do
    let .forallE _ domain _ _ := rest | throwError "actual forward: lost exact consumer hG"
    save `ForwardAnnularRealization p domain true (some (mkSort .zero)) (.regular 0)

/-- Cache the already proved native whole annular identity under that exact
predicate. No hypothesis or summand changes in this repackaging. -/
elab "construct_actual_quadratic_native_forward_packed" : command => liftTermElabM do
  let src := actual ++ `native_forward_realization
  forallBoundedTelescope (← getConstInfo src).type (some 65) fun p ht => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let some ph := ht.find? (·.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12)
      | throwError "native forward: lost exact full phase"
    let some mul := ht.find? fun e => e.isAppOfArity ``HMul.hMul 6 &&
        e.getAppArgs[5]!.isAppOfArity `JanetCartan.PhysicalForwardMean.singleBareScalarMask 4
      | throwError "native forward: lost exactly one angular mask"
    let bare := mul.getAppArgs[5]!.appFn!
    let angular := mul.getAppArgs[4]!
    let mask ← forallBoundedTelescope (← inferType bare) (some 1) fun z _ => do
      mkLambdaFVars z (mkAppN mul.appFn!.appFn! #[angular,mkAppN bare z])
    let some slice := ht.find? (·.isAppOfArity (actual ++ `forwardSlice) 7)
      | throwError "native forward: lost original corrected slice"
    let J := ph.getAppArgs[1]!
    let A ← forallBoundedTelescope (← inferType slice) (some 2) fun ac _ => do
      withLocalDeclNoLocalInstanceUpdate `j .default
          (app `JanetCartan.RawInputPartition.RefinedIndex #[J]) fun j => do
        mkLambdaFVars (ac.push j) (mkAppN slice ac)
    for e in #[ph,mask,A] do if e.hasLooseBVars then throwError "native forward: escaped integral variable"
    let target := app (actual ++ `ForwardAnnularRealization)
      #[n,slice.getAppArgs[1]!,J,app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G p,ph,mask,A]
    save `native_forward_realization_packed p (app src p) false (some target)

/-- Validate the exact inferred actual53 proposition separately from applying
its already checked native65 proof. Both declarations are definitionally the
same old whole-annular identity, with no extra analytic premise. -/
elab "construct_actual_quadratic_forward_specialization " mode:num : command => liftTermElabM do
  let G := `JanetCartan.PhysicalMean.OriginalCanonicalActual.G
  forallBoundedTelescope (← getConstInfo G).type (some 53) fun p _ => do
    let raw ← bodyAt G p
    unless raw.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
      throwError "actual forward: changed native derivative"
    let proof := app (actual ++ `native_forward_realization_packed) raw.getAppArgs
    if mode.getNat == 0 then
      save `actual_forward_proposition p (← inferType proof) true (some (mkSort .zero)) (.regular 0)
    else if mode.getNat == 1 then
      save `actual_forward_proof p proof false (some (app (actual ++ `actual_forward_proposition) p))
    else throwError "actual forward: unknown specialization mode"

/-- The exact actual whole-annular derivative in the named shared coordinates:
unchanged G53, corrected full phase, one angular mask, and corrected amplitude. -/
elab "construct_actual_quadratic_forward_realization" : command => liftTermElabM do
  let G := `JanetCartan.PhysicalMean.OriginalCanonicalActual.G
  forallBoundedTelescope (← getConstInfo G).type (some 53) fun p _ => do
    let raw ← bodyAt (actual ++ `rawPhase) p
    unless raw.isAppOfArity `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase 12 do
      throwError "actual forward: lost full raw phase"
    let J := raw.getAppArgs[1]!
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let amp := app (actual ++ `forwardAmplitude) p
    let A ← forallBoundedTelescope (← inferType amp) (some 2) fun ac _ => do
      withLocalDeclNoLocalInstanceUpdate `j .default
          (app `JanetCartan.RawInputPartition.RefinedIndex #[J]) fun j => do
        mkLambdaFVars (ac.push j) (mkAppN amp ac)
    let target := app (actual ++ `ForwardAnnularRealization)
      #[n,N,J,app G p,app (actual ++ `rawPhase) p,app (actual ++ `rawMask) p,A]
    save `unprefixed_forward_realization p (app (actual ++ `actual_forward_proof) p) false (some target)

end JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
end

construct_actual_quadratic_raw_phase 0
construct_actual_quadratic_raw_phase 1
construct_actual_quadratic_raw_phase 2
construct_actual_quadratic_raw_mask_regular
construct_actual_quadratic_raw_chart
construct_actual_quadratic_cutoff_phase_support
construct_actual_quadratic_measurement_core
construct_actual_quadratic_forward_envelope
construct_actual_quadratic_native_coordinates
construct_actual_quadratic_forward_predicate
construct_actual_quadratic_native_forward_packed
construct_actual_quadratic_forward_specialization 0
construct_actual_quadratic_forward_specialization 1
construct_actual_quadratic_forward_realization
