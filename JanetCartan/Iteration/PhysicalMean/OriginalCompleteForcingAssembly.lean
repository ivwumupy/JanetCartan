module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSample
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSample
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection

/-!
# The same sampled tensor and the full source algebra

The native declarations construct the measured self tensor of the original
baseline on the ONE selected sample, and a smooth representative of the SAME
corrected colored continuum. The generic full-source constructor records all
three signed summands of `new:eq:mean-source`; the transported leading profile
must still come from its actual original-data producer, not an identification
of the corrected and leading continua.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open CurrentMean SmoothPeriodicFamily

/-- The measured self tensor of the actual weighted unscaled baseline. The
weight appears once, outside the full Hermitian self tensor. -/
def measuredSampleSelf {n N : ℕ} {I : Type*} [Fintype I] (μ : I → ℝ)
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (base : SmoothPeriodicFamily n I (Matrix (Fin N) (Fin n) ℂ)) : SmoothResidual n :=
  measurementFamily C hC (tensorBilinear μ base base)

theorem measuredSampleSelf_value {n N : ℕ} {I : Type*} [Fintype I] (μ : I → ℝ)
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (base : SmoothPeriodicFamily n I (Matrix (Fin N) (Fin n) ℂ)) (x : Torus n) :
    (measuredSampleSelf μ C hC base).val x () = C x (weightedHermitianTensor μ base.val x) := by
  change C x ((tensorBilinear μ base base).val x ()) = _
  rw [tensorBilinear_self]

/-- The smooth quadrature plus the SAME smooth sampled tensor is precisely
the corrected continuum. This is only its value, not a leading comparison. -/
def correctedContinuumField {n : ℕ} (quadrature sampledSelf : SmoothResidual n) : SmoothResidual n :=
  quadrature + sampledSelf

theorem correctedContinuumField_value {n : ℕ} (quadrature sampledSelf : SmoothResidual n)
    (x : Torus n) (continuum self : Euclidean n)
    (hq : quadrature.val x () = continuum - self) (hs : sampledSelf.val x () = self) :
    (correctedContinuumField quadrature sampledSelf).val x () = continuum := by
  change quadrature.val x () + sampledSelf.val x () = _
  rw [hq,hs,sub_add_cancel]

/-- The FULL source in `new:eq:mean-source`: measured affine leading mean,
plus measured signed smoothed target, minus the SAME sampled self tensor.
No transport difference is omitted or assumed to vanish. -/
def completeSource {n : ℕ} (leading target sampledSelf : SmoothResidual n) : SmoothResidual n :=
  leading + target - sampledSelf

theorem completeSource_value {n : ℕ} (leading target sampledSelf : SmoothResidual n) (x : Torus n) :
    (completeSource leading target sampledSelf).val x () =
      leading.val x () + target.val x () - sampledSelf.val x () := rfl

/-- The corrected colored continuum is retained between the two signed
pieces. Its smooth representative follows from the already actual quadrature
identity, so no extra geometric extension is introduced. -/
def leadingComparison {n : ℕ} (leading quadrature sampledSelf : SmoothResidual n) : SmoothResidual n :=
  leading - (quadrature + sampledSelf)

theorem leadingComparison_value {n : ℕ} (leading quadrature sampledSelf : SmoothResidual n)
    (continuum : Torus n → Euclidean n)
    (hquad : ∀ x, quadrature.val x () = continuum x - sampledSelf.val x ()) (x : Torus n) :
    (leadingComparison leading quadrature sampledSelf).val x () = leading.val x () - continuum x := by
  change leading.val x () - (quadrature.val x () + sampledSelf.val x ()) = _
  rw [hquad x,sub_add_cancel]

/-- The exact three-summand forcing decomposition used for the Picard input.
The middle term is the genuine leading-minus-corrected continuum, not zero. -/
theorem completeSource_eq_three_summands {n : ℕ} (leading target sampledSelf quadrature : SmoothResidual n) :
    completeSource leading target sampledSelf = quadrature + leadingComparison leading quadrature sampledSelf + target := by
  unfold completeSource leadingComparison
  abel

/-- The same seminorm triangle inequality combines the three actual source
profiles once their original-data producers have supplied them. -/
theorem completeSource_profile {n q : ℕ} (leading target sampledSelf quadrature : SmoothResidual n)
    (Q E M R : ℝ) (hquad : residualSobolevSeminorm n q quadrature ≤ Q * R)
    (htransport : residualSobolevSeminorm n q (leadingComparison leading quadrature sampledSelf) ≤ E * R)
    (htarget : residualSobolevSeminorm n q target ≤ M * R) :
    residualSobolevSeminorm n q (completeSource leading target sampledSelf) ≤ (Q + E + M) * R := by
  rw [completeSource_eq_three_summands leading target sampledSelf quadrature]
  exact (((residualSobolevSeminorm n q).add_le' _ _).trans
    (add_le_add (((residualSobolevSeminorm n q).add_le' _ _).trans (add_le_add hquad htransport)) htarget)).trans_eq
      (by ring)
end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCompleteSampleSelfApplication
open Lean Meta Elab Command
open OriginalCanonicalSampledApplication (withActualSample)
private def source := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def quad := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
private def measurement := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
private def app (k : Name) (args : Array Expr) := mkAppN (mkConst k) args
private def fields (k : Name) (args : Array Expr) : MetaM (Array (Name × Expr)) := do
  let mut ty := (← getConstInfo k).type
  let mut result := #[]
  for arg in args do
    let .forallE name _ b _ := ty | throwError "changed original sampled tensor binder"
    result := result.push (name.eraseMacroScopes,arg)
    ty := b.instantiate1 arg
  return result
private def save (key : Name) (p : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun k => (env.find? k).isNone)
    unless missing.isEmpty do throwError "actual sampled self {key}: missing {missing}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then throwError "actual sampled self {key}: leaked data"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := source ++ key
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"actual selected sampled self {key}/{p.size}"

private def withSelf (go : Array Expr → Expr → Array Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withTransparency .reducible <| withActualSample fun p _ _ _ _ => do
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
    let hq := app (source ++ `quadrature_eq_continuum_sub_sample) (p.push shift)
    forallBoundedTelescope (← inferType hq) (some 1) fun z _ => do
      unless z.size == 1 do throwError "missing original torus point"
      let hq := mkApp hq z[0]!
      let t ← inferType hq
      let rhs := t.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSub.hSub 6 do throwError "lost sign of the original quadrature"
      let self := rhs.getAppArgs[5]!
      let some weighted := self.find? (·.isAppOf `JanetCartan.CurrentMean.weightedHermitianTensor)
        | throwError "lost literal weighted self tensor"
      let f ← fields weighted.getAppFn.constName! weighted.getAppArgs
      let get (name : Name) : MetaM Expr := do
        let some (_,v) := f.find? (fun a => a.1 == name) | throwError "missing original weighted tensor input {name}"
        return v
      let I ← get `ι
      let mut wtype := (← getConstInfo weighted.getAppFn.constName!).type
      let mut originalFinite : Option Expr := none
      for a in weighted.getAppArgs do
        let .forallE _ domain b _ := wtype | throwError "lost weighted tensor input telescope"
        if domain.isAppOfArity ``Fintype 1 && domain.getAppArgs[0]! == I then
          originalFinite := some a
        wtype := b.instantiate1 a
      let some fI := originalFinite | throwError "lost exact original sampled finite instance"
      let n := mkApp (mkConst ``Nat.succ) p[0]!
      let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
      let base := app `JanetCartan.PhysicalMean.OriginalCanonicalSampled.base (p.push shift)
      let args := #[n,N,I,fI,← get `μ,app (measurement ++ `Cper) p,app (measurement ++ `Cper_smooth) p,base]
      let data := mkAppN (mkConst (source ++ `measuredSampleSelf) [.zero]) args
      let hself := mkAppN (mkConst (source ++ `measuredSampleSelf_value) [.zero]) (args.push z[0]!)
      go p z[0]! args data hself hq rhs

run_elab withSelf fun p _ args data _ _ _ => do
  save `selectedSampleSelf p data (← inferType data) true
  let v := app (source ++ `correctedContinuumField) #[args[0]!,app (quad ++ `selected_forcing) p,app (source ++ `selectedSampleSelf) p]
  save `correctedContinuumFamily p v (← inferType v) true

run_elab withSelf fun p z _ data hself _ rhs => do
  let t ← inferType hself
  let lhs := t.getAppArgs[1]!.replace fun e => if e == data then some (app (source ++ `selectedSampleSelf) p) else none
  let target := mkAppN t.getAppFn #[t.getAppArgs[0]!,lhs,rhs.getAppArgs[5]!]
  save `selected_sample_self_value p (← mkLambdaFVars #[z] hself) (← mkForallFVars #[z] target)

run_elab withSelf fun p z args _ _ hq rhs => do
  let sample := app (source ++ `selectedSampleSelf) p
  let quadrature := app (quad ++ `selected_forcing) p
  let hs := mkApp (app (source ++ `selected_sample_self_value) p) z
  let term := app (source ++ `correctedContinuumField_value)
    #[args[0]!,quadrature,sample,z,rhs.getAppArgs[4]!,rhs.getAppArgs[5]!,hq,hs]
  let raw := app (source ++ `correctedContinuumField) #[args[0]!,quadrature,sample]
  let target := (← inferType term).replace fun e => if e == raw then some (app (source ++ `correctedContinuumFamily) p) else none
  save `corrected_continuum_family_value p (← mkLambdaFVars #[z] term) (← mkForallFVars #[z] target)
end JanetCartan.PhysicalMean.OriginalCompleteSampleSelfApplication
end
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedSampleSelf
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_sample_self_value
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.corrected_continuum_family_value
