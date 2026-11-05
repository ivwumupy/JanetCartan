module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowActualBridge
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowActualBridge
/-!
# The actual measured adjoint coefficient

This leaf closes the measured coefficient fields used by the actual mean-pair
row and high quadratic profile (`app:ch_mean_pairs:defn:mean-canonical`). It keeps
the SAME canonical C, cut corrected amplitudes, retained carrier, physical rate,
and fixed original shell/prefix. The coefficient contains only inverse cF and
complex conjugation; the original scalar mask retains the carrier, radial,
angular, and halfweight factors.

Consumers: the exact `hAn` sampled-moment representation and the common actual
89/102 source tuple. No sampled size, prefix size, or analytic-success premise is
admitted by the generated native53 fields.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
private theorem measured_power_nonneg (T : ℝ) (hT : 1 ≤ T) (j : ℕ) : 0 ≤ T ^ j :=
  pow_nonneg (zero_le_one.trans hT) j
end
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.SliceGenerator
open OriginalBackgroundHermitianTemplate
private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def mp := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def store (label : Name) (params : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do throwError "measured slice missing value {missing.toList}"
  let t ← match target with | some t => pure t | none => inferType term
  let missing := t.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do throwError "measured slice missing target {missing.toList}"
  let type ← instantiateMVars (← mkForallFVars params t)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "measured slice missing closed {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "measured slice open declaration {label}"
  let name := ns ++ label
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual measured slice {label}/{params.size}"
  return app name params

elab "publish_actual_measured_slice " which:num : command => liftTermElabM do
  withActualRow fun d => do
    forallBoundedTelescope (← inferType d.native64[61]!) (some 1) fun colors _ => do
      withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.SeparatedSampling.Point) fun z => do
        let c := colors[0]!
        let p := d.parameters ++ colors
        let params := p.push z
        let H := app (ns ++ `measuredCross) p
        let hH := app (ns ++ `measuredCross_contDiff) p
        let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
        let a := raw.getAppArgs
        let Z ← nodeAt z
        let ζ ← mkAppM `JanetCartan.Sampling.MeasuredAmplitude.extendedRetainedCarrier #[a[5]!,a[34]!,a[36]!,Z]
        let τ := mkApp d.native64[61]! c
        let amp ← mkAppM ``measuredAdjointSlice #[H,Z,ζ,τ]
        let named := app (ns ++ `ameasAtPoint) params
        match which.getNat with
        | 0 => discard <| store `ameasAtPoint params amp true
        | 1 =>
          let hc ← forallBoundedTelescope (← inferType amp) (some 1) fun a _ => do
            let hc ← mkAppM ``measuredAdjointSlice_contDiff #[hH,Z,ζ,τ,a[0]!]
            mkLambdaFVars a hc
          let t ← inferType hc
          let t := t.replace fun e => if e == amp then some named else none
          discard <| store `ameasAtPoint_contDiff params hc false (some t)
        | 2 =>
          let static := d.parameters[:44].toArray
          let n := mkApp (mkConst ``Nat.succ) d.parameters[0]!
          let hD := app (ns ++ `measuredCrossBudget_nonneg) (static.push d.row)
          let hr := mkApp (mkConst `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.mean_kernel_reserve_le_original) n
          let hj := app (ns ++ `measuredCross_jets_global) p
          let sliceBound ← mkAppM ``measuredAdjointSlice_jets #[hH,hD,d.mean70[62]!,hr,hj,Z,ζ,τ]
          let bound ← forallBoundedTelescope (← inferType sliceBound) (some 4) fun axj _ => do
            let j := axj[3]!
            let hlocal := mkAppN sliceBound axj
            let ht ← inferType hlocal
            let rhs := ht.getAppArgs.back!
            let power := rhs.getAppArgs.back!
            let rowBound ← mkAppM ``measuredFamilyBudget_row_le
              #[n,app (ns ++ `measuredCrossBudget_nonneg) static,d.row,j]
            let powerArgs := power.getAppArgs
            let hpow ← mkAppM ``measured_power_nonneg #[d.mean70[60]!,d.mean70[62]!,powerArgs.back!]
            let total ← mkAppM ``mul_le_mul_of_nonneg_right #[rowBound,hpow]
            mkLambdaFVars axj (← mkAppM ``le_trans #[hlocal,total])
          let t ← inferType bound
          let total ← mkAppM ``measuredFamilyBudget #[n,app (ns ++ `measuredCrossBudget) static]
          let t := t.replace fun e => if e == amp then some named else
            if e == total then some (app (ns ++ `measuredAmplitudeBudget) static) else none
          discard <| store `ameasAtPoint_jets params bound false (some t)
        | 3 =>
          let cut := mkApp (app (mp ++ `cutAmplitude) d.parameters) c
          let insertion ← mkAppM `JanetCartan.Sampling.CorrectedMean.retainedCarrierInsertion
            #[a[5]!,a[34]!,a[36]!]
          let B ← forallBoundedTelescope (← inferType cut) (some 1) fun w _ =>
            mkLambdaFVars w (mkApp cut (mkAppN insertion w))
          let proof ← mkAppM ``measuredAdjointSlice_cross_support #[d.mean70[37]!,B,cut,Z,ζ,τ]
          let target ← forallBoundedTelescope (← inferType amp) (some 2) fun aη _ => do
            let left ← mkAppM ``tsupport #[mkAppN named aη]
            let commonC := app `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.commonC d.parameters[:50].toArray
            let right ← mkAppM ``tsupport #[commonC]
            mkForallFVars aη (← mkAppM ``Set.Subset #[left,right])
          discard <| store `ameasAtPoint_support_measurement params proof false (some target)
        | _ => throwError "unknown measured slice field"
publish_actual_measured_slice 0
publish_actual_measured_slice 1
publish_actual_measured_slice 2
publish_actual_measured_slice 3
end JanetCartan.PhysicalMean.OriginalCanonicalRow.SliceGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint_jets
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint_support_measurement

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open SamplingKernelBounds RawInputPartition PhysicalForwardMean
open OriginalMeanQuadraticProfiles.Actual

/-- Exact scalar algebra joining the measured raw band with the SAME original
prefix mask and the adjoint coefficient. No radial, angular, carrier, or sample
weight is divided out (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem originalMeasuredBand_eq_moment {n J : ℕ}
    (H : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (Z : Euclidean 3) (ζ : Euclidean (n-1)) (τ b : ℝ)
    (φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
    (det : Euclidean (n-1) → ℝ) (L : ℕ) (a : Fin n)
    (j : RefinedIndex J) (η : Euclidean (n-1)) (x : Euclidean n) :
    Complex.ofReal (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) *
      (if j.1.val < L then (b : ℂ) *
        (bandKernel (φ j) (fun η ↦ (det η : ℂ))
          (fun η x ↦ (((2 * Real.pi) ^ (-(n : ℝ) / 2) * radialBand n j.1.val η : ℝ) : ℂ) •
            H (x,Z,ζ + τ • η)) η x) a else 0) =
      sampledMomentKernel (fun u : RefinedIndex J × Euclidean (n-1) ↦ φ u.1 u.2)
        (halfWeightedMomentMask (prefixMask L (fun u ↦ b * singleBareScalarMask det u)))
        (fun u ↦ measuredAdjointSlice H Z ζ τ a u.2) x (j,η) := by
  by_cases hj : j.1.val < L
  · simp only [hj,ite_true,sampledMomentKernel,halfWeightedMomentMask,prefixMask,prefixGate,
      bandKernel,PiLp.smul_apply,smul_eq_mul,measuredAdjointSlice,star_star,
      singleBareScalarMask,Complex.ofReal_mul,NormalComparison.oscillatoryFactor,one_mul,neg_div]
    rw [mul_comm (φ j η x : ℂ) Complex.I]
    ring
  · simp only [hj,ite_false,sampledMomentKernel,halfWeightedMomentMask,prefixMask,prefixGate,
      zero_mul,mul_zero,Complex.ofReal_zero]
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open OriginalBackgroundHermitianTemplate
elab "publish_actual_measured_amplitude_identity" : command => liftTermElabM do
  withActualRow fun d => do
    let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
    unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData 45 do
      throwError "amplitude identity lost corrected kernel45"
    let r := raw.getAppArgs
    let D := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalRow.D) d.parameters
    let amp ← mkAppM `JanetCartan.SamplingKernelBounds.BandKernelData.amplitude #[D]
    let pty := (← inferType r[27]!).bindingDomain!
    let n := mkApp (mkConst ``Nat.succ) d.parameters[0]!
    let X := mkApp (mkConst `JanetCartan.Euclidean) n
    let E := mkApp (mkConst `JanetCartan.Euclidean) (mkApp2 (mkConst ``Nat.sub) n (mkNatLit 1))
    let coefficient ← withLocalDeclNoLocalInstanceUpdate `q .default pty fun q =>
      withLocalDeclNoLocalInstanceUpdate `x .default X fun x =>
      withLocalDeclNoLocalInstanceUpdate `η .default E fun η => do
        let C := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalRow.measuredCross)
          (d.parameters.push (mkApp r[27]! q))
        let p ← mkAppM ``Prod.mk #[mkApp r[29]! q,η]
        let p ← mkAppM ``Prod.mk #[x,p]
        mkLambdaFVars #[q,x,η] (mkApp C p)
    let ζ ← withLocalDeclNoLocalInstanceUpdate `q .default pty fun q => do
      let z ← mkAppM `JanetCartan.Sampling.MeasuredAmplitude.extendedRetainedCarrier
        #[r[5]!,r[34]!,r[36]!,mkApp r[29]! q]
      mkLambdaFVars #[q] z
    let τ ← withLocalDeclNoLocalInstanceUpdate `q .default pty fun q =>
      mkLambdaFVars #[q] (mkApp r[19]! (mkApp r[27]! q))
    let result ← forallBoundedTelescope (← inferType amp) (some 1) fun q _ => do
      let rhs ← mkAppM `JanetCartan.Sampling.RawKernel.measuredBandAmplitude #[coefficient,ζ,τ,q[0]!]
      let lhs := mkAppN amp q
      unless ← isDefEq lhs rhs do throwError "actual measured cross is not definitionally the D coefficient"
      let value ← mkLambdaFVars q (← mkEqRefl lhs)
      let type ← mkForallFVars q (← mkEq lhs rhs)
      pure (type,value)
    let type ← instantiateMVars (← mkForallFVars d.parameters result.1)
    let value ← instantiateMVars (← mkLambdaFVars d.parameters result.2)
    let env ← getEnv
    for e in #[result.1,result.2,type,value] do
      let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
      unless missing.isEmpty do throwError "amplitude identity missing {missing.toList}"
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "amplitude identity retained open proof data"
    let name := `JanetCartan.PhysicalMean.OriginalCanonicalRow.D_amplitude_eq_measuredCross
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    logInfo "checked actual D amplitude equals SAME cross52 at native51"
publish_actual_measured_amplitude_identity
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.D_amplitude_eq_measuredCross
