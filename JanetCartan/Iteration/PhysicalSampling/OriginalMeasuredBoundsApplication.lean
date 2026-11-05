module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelData
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
public meta import Lean

/-!
# Numerical estimates for the already constructed original measured kernel

Keep the literal kernel definition fixed while applying its genuine retained
coefficient profiles and full uncut-response jets. This separation prevents a
numerical-bound correction from rebuilding the native kernel construction;
it changes no source, history, phase, rate or analytic hypothesis
(`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredBoundsApplication
private theorem original_mask_unit_nonnegative : (0 : ℝ) ≤ 1 := zero_le_one
private theorem abs_of_original_cutoff_bounds {A : Type*} {κ : A → ℝ}
    (h : ∀ a, 0 ≤ κ a ∧ κ a ≤ 1) : ∀ a, |κ a| ≤ 1 := fun a ↦ (abs_of_nonneg (h a).1).le.trans (h a).2
private theorem original_two_times {t e : ℝ} (h : t ≤ e / 2) : 2 * t ≤ e := by linarith
private theorem restrict_measurement_bound {A F : Type*} [Norm F] {C : A → F} {M : ℝ}
    (S : Set A) (h : ∀ x, ‖C x‖ ≤ M) : ∀ x ∈ S, ‖C x‖ ≤ M := fun x _ ↦ h x
end JanetCartan.PhysicalSampling.OriginalMeasuredBoundsApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredBoundsApplication
open Lean Meta Elab Command
open OriginalMeasuredKernelsApplication (save withRow withRaw)
private def sampling := `JanetCartan.PhysicalSampling
private def current := sampling ++ `OriginalMeasuredCurrent
private def ns := sampling ++ `OriginalMeasuredFamily.Row

/-- Use the original full-response derivative estimate only on its specified
whole K, together with the already-retained four smooth fields and five
profiles. The resulting zeroth amplitude bound is precisely the numeric
prehistory family budget after applying the original row's profile budgets. -/
elab "bound_original_measured_row_amplitude" : command => liftTermElabM <| withTransparency .reducible <| withRow fun x later init m =>
    withRaw x later init fun D kernelParams => do
  let source := `JanetCartan.Sampling.correctedColoredCrossBandData_uniform_bounds_of_profiles
  let args := D.getAppArgs
  let cap := mkAppN (mkConst (sampling ++ `OriginalChoices.Cutoff.hκ_bounds)) init[:7].toArray
  let hCut ← mkAppM ``abs_of_original_cutoff_bounds #[cap]
  let unit := (← inferType (mkConst ``original_mask_unit_nonnegative)).appArg!
  let current49 := x[:43].toArray ++ x[45:51].toArray
  let hC := mkAppN (mkConst (current ++ `measurement_bound)) current49
  let support := mkAppN (mkConst (sampling ++ `OriginalMeasuredFamily.support)) (x[:22].toArray.push x[40]!)
  let hC' ← mkAppM ``restrict_measurement_bound #[support, hC]
  let MC := mkApp init[60]! (mkNatLit 0)
  let numeric := #[unit, MC, mkConst ``original_mask_unit_nonnegative, mkApp init[61]! (mkNatLit 0),
    init[36]!, hCut, hC', later[0]!]
  let profiles := init[28:33].toArray ++ m[55:60].toArray ++ #[m[61]!] ++ init[16:28].toArray ++
    #[m[60]!, later[2]!, later[3]!, m[62]!] ++ m[65:70].toArray ++ #[later[4]!, later[5]!]
  unless args.size == 45 do throwError "original measured kernel: expected the actual 45-input kernel"
  let firstCountable ← synthInstance (← mkAppOptM ``FirstCountableTopology #[some args[23]!,some args[24]!])
  let locallyCompact ← synthInstance (← mkAppOptM ``LocallyCompactSpace #[some args[23]!,some args[24]!])
  let kernelPrefix := args[:25].toArray ++ #[firstCountable,locallyCompact] ++ args[25:44].toArray
  let full := mkAppN (mkConst source D.getAppFn.constLevels!) (kernelPrefix ++ profiles ++ numeric)
  let conclusion := Expr.proj ``And 0 full
  let type ← inferType conclusion
  let named := mkAppN (mkConst (ns ++ `kernel)) kernelParams
  let type := type.replace fun e => if e == D then some named else none
  discard <| save `amplitude_bound (x ++ later) conclusion false (some type)

private def component (h : Expr) (j : Nat) : Expr :=
  Expr.proj ``And 0 ((List.range j).foldl (fun e _ => Expr.proj ``And 1 e) h)

/-- The input rate bound is the SAME original ε for every scalar/measured and
comparison endpoint. Only the RHS of the actual dyadic inequality is changed. -/
private def withDyadic (x : Array Expr) (expected : Expr) (k : Expr → MetaM Unit) : MetaM Unit := do
  let eps := mkAppN (mkConst (sampling ++ `OriginalMargins.ε)) x[:22].toArray
  let type ← forallBoundedTelescope expected (some 2) fun c b => do
    unless b.isAppOfArity ``LE.le 4 do throwError "original measured kernel: missing fine dyadic inequality"
    mkForallFVars c (← mkAppM ``LE.le #[b.getAppArgs[2]!, eps])
  withLocalDeclD `hrate type k

/-- Prove the continuum mean and both sharp refinements for the one literal
kernel, without another choice of support, working radius, mesh or mask. -/
elab "bound_original_measured_row_operator " which:num : command => liftTermElabM <| withTransparency .reducible <| withRow fun x later init _ =>
    withRaw x later init fun D kernelParams => do
  let a := D.getAppArgs
  unless a.size == 45 do throwError "original measured kernel: expected the literal 45-input corrected kernel"
  let named := mkAppN (mkConst (ns ++ `kernel)) kernelParams
  let meanPrefix := mkAppN (mkConst (current ++ `mean_on_full_response)) (x ++ later ++ #[a[20]!, a[41]!, a[42]!, a[43]!])
  let expected := (← whnf (← inferType meanPrefix)).bindingDomain!
  let wr := x[:22].toArray.push x[40]!
  let caps := mkAppN (mkConst (sampling ++ `OriginalMargins.ε_caps)) wr
  withDyadic x expected fun rateOK => do
    let parameters := x ++ later ++ #[rateOK]
    match which.getNat with
    | 0 =>
      let mut phaseCap := caps
      for _ in [:4] do phaseCap := Expr.proj ``And 1 phaseCap
      let cap ← mkAppM `le_min #[component caps 1, phaseCap]
      let hsmall ← forallBoundedTelescope (← inferType rateOK) (some 2) fun c _ => do
        mkLambdaFVars c (← mkAppM `le_trans #[mkAppN rateOK c, cap])
      let win := mkApp (mkConst (sampling ++ `OriginalWindow.window)) x[2]!
      withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0, x[2]!]) fun hp =>
        withLocalDeclD `mesh (mkConst ``Real) fun mesh => do
          let zero ← mkNumeral (mkConst ``Real) 0
          withLocalDeclD `hmesh (← mkAppM ``Ne #[mesh, zero]) fun hmesh => do
            let r := mkAppN meanPrefix #[hsmall, win, ← mkAppM (sampling ++ `OriginalWindow.window_bounds) #[hp],
              mkApp (mkConst (sampling ++ `OriginalWindow.window_continuous)) x[2]!, mesh, hmesh]
            let t ← whnf (← inferType r)
            let t := t.replace fun e => if e == D then some named else none
            discard <| save `mean_bound (parameters ++ #[hp, mesh, hmesh]) r false (some t)
    | 1 =>
      let geometry49 := x[:43].toArray ++ x[45:51].toArray
      let firstCountable ← synthInstance (← mkAppOptM ``FirstCountableTopology #[some a[23]!,some a[24]!])
      let locallyCompact ← synthInstance (← mkAppOptM ``LocallyCompactSpace #[some a[23]!,some a[24]!])
      let band := mkAppN (mkConst (current ++ `band_on_full_response)) (x ++
        #[a[17]!, a[18]!, a[25]!, a[26]!] ++ later[1:6].toArray ++ #[a[20]!, a[21]!, a[22]!,
        mkAppN (mkConst (current ++ `measurement_bound)) geometry49,
        mkAppN (mkConst (current ++ `measurement_support)) geometry49] ++ #[a[23]!, a[24]!, firstCountable, locallyCompact] ++
        a[27:31].toArray ++ #[a[37]!, a[41]!, a[42]!, a[43]!, later[0]!])
      let colorType := a[17]!
      let point := a[23]!.getAppArgs[1]!
      let phi := mkAppN (mkConst (sampling ++ `OriginalWeights.φ)) wr
      withLocalDeclD `c colorType fun c => withLocalDeclD `z point fun z => do
        let zero ← mkNumeral (mkConst ``Real) 0
        withLocalDeclD `hphi (← mkAppM ``Ne #[mkApp phi z, zero]) fun hphi => do
          let admitted := mkAppN (mkConst (sampling ++ `OriginalAdmission.cutoff_on_actual_selected_row)) wr
          let mut nodes := admitted
          for _ in [:5] do nodes := Expr.proj ``And 1 nodes
          let node := mkAppN nodes #[z, hphi]
          let par ← mkAppM ``Prod.mk #[c, z]
          let op := mkAppN band #[par, component node 1, Expr.proj ``And 1 (Expr.proj ``And 1 node)]
          forallBoundedTelescope (← inferType op) (some 1) fun j _ => do
            let hwin ← mkAppM ``original_two_times #[← mkAppM `le_trans #[mkAppN rateOK #[c, j[0]!], component caps 3]]
            let result := mkAppN op #[j[0]!, hwin]
            let t ← whnf (← inferType result)
            let t := t.replace fun e => if e == D then some named else none
            discard <| save `sharp_bound (parameters ++ #[c, z, hphi] ++ j) result false (some t)
    | _ => throwError "original measured kernel: unknown operator field"

end JanetCartan.PhysicalSampling.OriginalMeasuredBoundsApplication
end
