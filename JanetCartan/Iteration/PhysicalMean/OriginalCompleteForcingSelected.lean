module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingLeading
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingAssembly
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSample
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmission
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open CurrentMean
/-- Pointwise substitution of the three actual source components for the
initialized physical residual (`new:eq:reduced-mean-identity`). -/
theorem completeSource_value_of_components {n : ℕ}
    (leading target sampledSelf : SmoothResidual n) (x : Torus n) (L M S : Euclidean n)
    (hL : leading.val x () = L) (hM : target.val x () = M) (hS : sampledSelf.val x () = S) :
    (completeSource leading target sampledSelf).val x () = L + M - S := by
  rw [completeSource_value,hL,hM,hS]
/-- The actual leading comparison is the measured leading mean minus the
SAME corrected continuum, represented smoothly via the signed quadrature. -/
theorem leadingComparison_value_of_fields {n : ℕ}
    (leading quadrature sampledSelf : SmoothResidual n) (x : Torus n) (L C : Euclidean n)
    (hL : leading.val x () = L)
    (hC : (correctedContinuumField quadrature sampledSelf).val x () = C) :
    (leadingComparison leading quadrature sampledSelf).val x () = L - C := by
  change leading.val x () - (correctedContinuumField quadrature sampledSelf).val x () = _
  rw [hL,hC]


/-- The sum of the measured target and the genuinely signed sample error in
`new:eq:mean-source`; the leading-continuum difference is *not* put to zero. -/
def sumMeasuredSample {n : ℕ} (quadrature target : SmoothResidual n) : SmoothResidual n := quadrature + target

theorem sumMeasuredSample_apply {n : ℕ} (a b : SmoothResidual n) (x : Torus n) (t h w : Euclidean n)
    (ha : a.val x () = h-w) (hb : b.val x () = t) : (sumMeasuredSample a b).val x () = t+h-w := by
  change a.val x () + b.val x () = _
  rw [ha,hb]; abel

/-- A prehistory majorant for precisely these two terms. -/
def sampleTargetCost (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (q : ℕ) (quad : ℝ) : ℝ :=
  |quad| + uniformTargetBudget n D CM q

theorem sampleTargetCost_nonneg (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (q : ℕ) (quad : ℝ) :
    0 ≤ sampleTargetCost n D CM q quad :=
  add_nonneg (abs_nonneg _) (zero_le_one.trans (one_le_uniformTargetBudget _ _ _ _))

/-- Only now pass the genuine comparison-scale `h*T^(q-s₀)_+` to the larger
forcing scale `h*R^(q-s₀)_+`; no `h*T ≤ 1` claim occurs. -/
theorem sumMeasuredSample_profile {n : ℕ} (D : LocalDomain) (CM : ℕ → ℝ) (R₀ : ℝ) (hR₀ : 2 ≤ R₀)
    (j q : ℕ) (a b : SmoothResidual n) (Q : ℝ) :
    let R := iterationScale R₀ growthExponent j
    let T := currentCoefficientScale R₀ j
    let h := R ^ (-separationExponent)
    let e := q - RevisedScales.sourceOrder n
    residualSobolevSeminorm n q a ≤ Q*h*T^e →
    periodicSobolevNorm q (fun x ↦ b.val x ()) ≤ uniformTargetBudget n D CM q*h*R^e →
    residualSobolevSeminorm n q (sumMeasuredSample a b) ≤ sampleTargetCost n D CM q Q*h*R^e := by
  intro R T h e ha hb
  have hc := fixedPicard_history_scale_facts hR₀ j
  have hT : 0 ≤ T := zero_le_one.trans hc.2.1
  have hh : 0 ≤ h := hc.2.2.2.1
  have hq : Q*h*T^e ≤ |Q| * h * R^e :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hh) (pow_nonneg hT _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hc.2.2.1 _) (mul_nonneg (abs_nonneg _) hh))
  have hb' : residualSobolevSeminorm n q b ≤ uniformTargetBudget n D CM q*h*R^e := by
    simpa only [residualSobolevSeminorm, DensityDiscrepancy.densitySobolevSeminorm_eq_norm,
      DensityDiscrepancy.norm_densitySobolevRealization] using hb
  exact (((residualSobolevSeminorm n q).add_le' a b).trans (add_le_add (ha.trans hq) hb')).trans_eq
    (by unfold sampleTargetCost; ring)
end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeasuredAssembly
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedAtPoint)
open OriginalBackgroundHermitianTemplate (bodyAt)
private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def quad := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
private def admit := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
private def selection := `JanetCartan.PhysicalMean.OriginalCanonicalSelection
private def app (k : Name) (p : Array Expr) : Expr := mkAppN (mkConst k) p
private def tel (type : Expr) (count : Nat) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,t,p => go p t
    | k+1,t,p => do
      let .forallE n dom body bi := t.consumeMData | throwError "missing original binder {p.size}"
      if bi == .instImplicit then withLocalDecl n bi dom fun x => loop k (body.instantiate1 x) (p.push x)
      else withLocalDeclNoLocalInstanceUpdate n bi dom fun x => loop k (body.instantiate1 x) (p.push x)
private def stripLet (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .letE _ _ v b _ => (b.instantiate1 v).headBeta
  | x => x
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "selected source {key}: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then throwError "selected source {key}: non-original input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original selected source component on the one original sample, original gamma and one physical ceiling (new:eq:mean-source). The full source has all three signed terms; its leading-comparison estimate must come from the actual transport producer."
  logInfo m!"selected measured source component {key}/{p.size}"

private def withHistory (next : Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withSelectedAtPoint fun p vars _ => next p[:50].toArray vars[:39].toArray
private def withTarget (next : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := withHistory fun p vars => do
  let stem := app (ns ++ `scaled_measured_target) p
  tel (← inferType stem) 13 fun extras conclusion => do
    let e := stripLet conclusion
    unless e.isAppOfArity ``Exists 2 do throwError "actual scaled target has changed"
    next p (vars ++ extras) (mkAppN stem extras) e
private def originalProfile (p : Array Expr) (q : Expr) : MetaM (Expr × Expr) := do
  let proof := app (quad ++ `forcing_source_profile_order_one) (p ++ #[mkConst (admit ++ `pOrder_eq_one),q])
  let t ← inferType proof
  unless t.isAppOfArity ``LE.le 4 do throwError "different original selected quadrature estimate"
  let product := t.getAppArgs[3]!
  unless product.isAppOfArity ``HMul.hMul 6 && product.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do throwError "missing true h*T^e quadrature profile"
  return (proof,product.getAppArgs[4]!.getAppArgs[4]!)

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun _ vars existsT e => do
  let args := e.getAppArgs
  let chosen := mkAppN (mkConst ``Classical.choose e.getAppFn.constLevels!) (args.push existsT)
  save `selectedMeasuredTarget vars chosen args[0]! true

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun _ vars existsT e => do
  let args := e.getAppArgs
  let spec := mkAppN (mkConst ``Classical.choose_spec e.getAppFn.constLevels!) (args.push existsT)
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let t := (args[1]!.beta #[target]).headBeta
  unless t.isAppOfArity ``And 2 && t.getAppArgs[1]!.isAppOfArity ``And 2 do throwError "lost pointwise identity or uniformity"
  save `selected_target_value vars (.proj ``And 0 spec) t.getAppArgs[0]!
  save `selected_target_uniform_profile vars (.proj ``And 1 (.proj ``And 1 spec)) t.getAppArgs[1]!.getAppArgs[1]!

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ e => do
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let sample := app (quad ++ `selected_forcing) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  save `selectedSampleAndTarget vars (app (ns ++ `sumMeasuredSample) #[n,sample,target]) e.getAppArgs[0]! true

run_cmd liftTermElabM <| withTransparency .reducible <| withHistory fun p vars => do
  let a := (← bodyAt (ns ++ `measured_target) p).getAppArgs
  withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
    let (_,C) ← originalProfile p q
    let fixed := vars[:33].toArray
    let arg := #[a[0]!,a[1]!,a[3]!,q,C]
    let val := app (ns ++ `sampleTargetCost) arg
    save `selectedSampleTargetBudget fixed (← mkLambdaFVars #[q] val) (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
    let nn := app (ns ++ `sampleTargetCost_nonneg) arg
    let ot ← inferType nn
    let named := mkApp (app (ns ++ `selectedSampleTargetBudget) fixed) q
    let tgt := mkAppN ot.getAppFn (ot.getAppArgs.set! 3 named)
    save `selectedSampleTargetBudget_nonneg fixed (← mkLambdaFVars #[q] nn) (← mkForallFVars #[q] tgt)

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ _ => do
  let nn := (← bodyAt (ns ++ `measured_target) p).getAppArgs[0]!
  let sample := app (quad ++ `selected_forcing) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let partialTerm := app (ns ++ `sumMeasuredSample) #[nn,sample,target]
  let namedSum := app (ns ++ `selectedSampleAndTarget) vars
  let shift := app (selection ++ `shift) p
  let q := app (ns ++ `quadrature_eq_continuum_sub_sample) (p.push shift)
  let t := app (ns ++ `selected_target_value) vars
  tel (← inferType t) 1 fun xs _ => do
    let z := xs[0]!
    let ht := mkApp t z
    let hq := mkApp q z
    let qt := (← inferType hq).getAppArgs[2]!
    unless qt.isAppOfArity ``HSub.hSub 6 do throwError "wrong sign of the sampled term"
    let v := app (ns ++ `sumMeasuredSample_apply) #[nn,sample,target,z,(← inferType ht).getAppArgs[2]!,qt.getAppArgs[4]!,qt.getAppArgs[5]!,hq,ht]
    let statement := (← inferType v).replace fun e => if e == partialTerm then some namedSum else none
    unless (statement.find? (· == namedSum)).isSome do throwError "lost same measured partial source"
    save `selected_sample_and_target_value vars (← mkLambdaFVars xs v) (← mkForallFVars xs statement)

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ _ => do
  let a := (← bodyAt (ns ++ `measured_target) p).getAppArgs
  let sample := app (quad ++ `selected_forcing) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let partialTerm := app (ns ++ `sumMeasuredSample) #[a[0]!,sample,target]
  let namedSum := app (ns ++ `selectedSampleAndTarget) vars
  withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
    let (hq,C) ← originalProfile p q
    let hb := mkApp (app (ns ++ `selected_target_uniform_profile) vars) q
    let v := app (ns ++ `sumMeasuredSample_profile) #[a[0]!,a[1]!,a[3]!,a[5]!,a[6]!,a[7]!,q,sample,target,C,hq,hb]
    let rawCost := app (ns ++ `sampleTargetCost) #[a[0]!,a[1]!,a[3]!,q,C]
    let namedCost := mkApp (app (ns ++ `selectedSampleTargetBudget) vars[:33].toArray) q
    let statement := (← inferType v).replace fun e => if e == rawCost then some namedCost else if e == partialTerm then some namedSum else none
    unless (statement.find? (· == namedSum)).isSome && (statement.find? (· == namedCost)).isSome do throwError "lost original data or prehistory budget"
    save `selected_sample_and_target_profile vars (← mkLambdaFVars #[q] v) (← mkForallFVars #[q] statement)

/- Native DATA of the genuine signed leading comparison, with no new target,
cutoff, shift, continuum, or norm hypothesis. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  tel (← getConstInfo (ns ++ `leadingMean)).type 50 fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let leading := app (ns ++ `leadingMean) p
    let sample := app (quad ++ `selected_forcing) p
    let self := app (ns ++ `selectedSampleSelf) p
    let v := app (ns ++ `leadingComparison) #[n,leading,sample,self]
    save `selectedLeadingComparison p v (← inferType v) true

run_cmd liftTermElabM <| withTransparency .reducible do
  tel (← getConstInfo (ns ++ `leadingMean)).type 50 fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let leading := app (ns ++ `leadingMean) p
    let sample := app (quad ++ `selected_forcing) p
    let self := app (ns ++ `selectedSampleSelf) p
    let raw := app (ns ++ `leadingComparison) #[n,leading,sample,self]
    let named := app (ns ++ `selectedLeadingComparison) p
    let value := app (ns ++ `leading_mean_value) p
    tel (← inferType value) 1 fun xs _ => do
      let z := xs[0]!
      let hL := mkApp value z
      let hC := mkApp (app (ns ++ `corrected_continuum_family_value) p) z
      let v := app (ns ++ `leadingComparison_value_of_fields)
        #[n,leading,sample,self,z,(← inferType hL).getAppArgs[2]!,
          (← inferType hC).getAppArgs[2]!,hL,hC]
      let statement := (← inferType v).replace fun e => if e == raw then some named else none
      unless (statement.find? (· == named)).isSome do throwError "lost the actual signed leading comparison"
      save `selected_leading_comparison_value p (← mkLambdaFVars xs v) (← mkForallFVars xs statement)

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ e => do
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let leading := app (ns ++ `leadingMean) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let self := app (ns ++ `selectedSampleSelf) p
  let v := app (ns ++ `completeSource) #[n,leading,target,self]
  save `selectedFullSource vars v e.getAppArgs[0]! true

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ _ => do
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let leading := app (ns ++ `leadingMean) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let self := app (ns ++ `selectedSampleSelf) p
  let raw := app (ns ++ `completeSource) #[n,leading,target,self]
  let named := app (ns ++ `selectedFullSource) vars
  let value := app (ns ++ `selected_target_value) vars
  tel (← inferType value) 1 fun xs _ => do
    let z := xs[0]!
    let hL := mkApp (app (ns ++ `leading_mean_value) p) z
    let hM := mkApp value z
    let hS := mkApp (app (ns ++ `selected_sample_self_value) p) z
    let v := app (ns ++ `completeSource_value_of_components)
      #[n,leading,target,self,z,(← inferType hL).getAppArgs[2]!,
        (← inferType hM).getAppArgs[2]!,(← inferType hS).getAppArgs[2]!,hL,hM,hS]
    let statement := (← inferType v).replace fun e => if e == raw then some named else none
    unless (statement.find? (· == named)).isSome do throwError "lost the complete original source"
    save `selected_full_source_value vars (← mkLambdaFVars xs v) (← mkForallFVars xs statement)

run_cmd liftTermElabM <| withTransparency .reducible <| withTarget fun p vars _ _ => do
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let leading := app (ns ++ `leadingMean) p
  let target := app (ns ++ `selectedMeasuredTarget) vars
  let self := app (ns ++ `selectedSampleSelf) p
  let sample := app (quad ++ `selected_forcing) p
  let rawSource := app (ns ++ `completeSource) #[n,leading,target,self]
  let rawComparison := app (ns ++ `leadingComparison) #[n,leading,sample,self]
  let full := app (ns ++ `selectedFullSource) vars
  let comparison := app (ns ++ `selectedLeadingComparison) p
  let v := app (ns ++ `completeSource_eq_three_summands) #[n,leading,target,self,sample]
  let statement := (← inferType v).replace fun e =>
    if e == rawSource then some full else if e == rawComparison then some comparison else none
  unless (statement.find? (· == full)).isSome && (statement.find? (· == comparison)).isSome do
    throwError "lost a genuine signed summand of the complete source"
  save `selected_full_source_decomposition vars v statement

end JanetCartan.PhysicalMean.OriginalSelectedMeasuredAssembly
end
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_sample_and_target_value
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_sample_and_target_profile

#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedLeadingComparison
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_leading_comparison_value
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_full_source_value
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_full_source_decomposition
