module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmission
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfiles
public import JanetCartan.Iteration.RevisedStage.Cutoff
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
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

/-!
# A fixed initial reach for the actual history and auxiliary coefficients

The auxiliary selector is a choice from the physical coefficient estimate on
one reference, set of cutoffs and physical history band. Factor that **same**
choice through its physical prefix: the forward proposition does not mention
any Neumann depth, target smoothing order, scalar reserve or observation order.
Use `B=2` from the final Fourier cutoff, the actual v2 source reserve, and the
already fixed protected reference order (`m ≥ 6`, not the stage smoothing
order). The resulting maximum with the selected native/task90 threshold is a
genuine constraint on **R₀**, never inferred from a later stage reach.

Consumers: `OriginalMeanLinearProfiles.Auxiliary.coefficient_smooth` and the
initial reach of `RevisedGlobal.UniformHistoryCorrection`
(`main:eq:history-data`, `new:sec:order-of-choices`, `main:eq:step-band`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCanonicalStaticReach

/-- The exact outer Fourier multiplier radius of `RevisedStage.increment`. -/
def historyBand : ℝ := 2

theorem one_le_historyBand : 1 ≤ historyBand := one_le_two

/-- The physical band of the original final cutoff, with no dependence on
smoothing, wave, Picard or Fourier-tail orders. -/
theorem increment_band {n N : ℕ} {R : ℝ} (hR : 0 < R)
    (P W : SchwartzMap (Euclidean n) (Euclidean N)) :
    PhysicalBernstein.HasFourierSupport (historyBand * R ^ bandExponent)
      (RevisedStage.increment R P W) := RevisedStage.hasFourierSupport_increment hR P W

private theorem join_left (a b : ℝ) : a ≤ max a b := le_max_left a b
private theorem join_right (a b : ℝ) : b ≤ max a b := le_max_right a b

end JanetCartan.PhysicalMean.OriginalCanonicalStaticReach
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalStaticReachTemplate
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedBefore)
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)

private def dest := `JanetCartan.PhysicalMean.OriginalCanonicalStaticReach
private def aux := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Auxiliary
private def admission := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
private def inverse := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
private def app (key : Name) (xs : Array Expr) := mkAppN (mkConst key) xs

private def store (key : Name) (xs : Array Expr) (v : Expr) (data := false)
    (goal : Option Expr := none) : MetaM Unit := do
  let t ← match goal with | some t => pure t | none => inferType v
  let type ← instantiateMVars (← mkForallFVars xs t)
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "static reach: an extra parameter or obligation escaped {key}"
    let hidden := e.getUsedConstants.filter fun n => (env.find? n).isNone
    unless hidden.isEmpty do throwError "static reach: hidden producers in {key}: {hidden.toList}"
  let name := dest ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The original physical coefficient choice, factored through its fixed prehistory inputs; R₀ is reached before any accuracy-dependent estimate (new:sec:order-of-choices)."
  logInfo m!"checked fixed prehistory {key} on {xs.size} inputs"

/-- Physical23, fixed band with positivity, rStar, kMin, numerical history
order, source reserve and its map bound. Not a single estimate is assumed. -/
def physicalInputs (x : Array Expr) : Array Expr :=
  x[:23].toArray ++ x[24:28].toArray ++ #[x[29]!,x[38]!,x[39]!]

elab "factor_original_auxiliary_choice " which:num : command => liftTermElabM do
  let mode := which.getNat
  let info ← getConstInfo (aux ++ `exists_profiles)
  forallBoundedTelescope info.type (some 41) fun x t => do
    let fixed := physicalInputs x
    let proof := (info.value! (allowOpaque := true)).beta x
    unless proof.isAppOfArity `JanetCartan.PhysicalMean.exists_history_auxiliary_source_coefficients 25 do
      throwError "static reach: original coefficient producer changed"
    -- Audit the actual predicate as well as the proof: the choice only sees the
    -- reference, masks, band, kMin, and source reserve (proof irrelevance).
    let data := x[:23].toArray ++ #[x[24]!,x[27]!,x[38]!]
    unless x.all (fun v => !t.containsFVar v.fvarId! || data.contains v) do
      throwError "static reach: variable depth entered the choice predicate"
    match mode with
    | 0 => store `physicalS fixed (← mkAppM ``Classical.choose #[proof]) true
    | 1 =>
      let budget := Expr.proj ``And 1 (← mkAppM ``Classical.choose_spec #[proof])
      store `physicalCcoef fixed (← mkAppM ``Classical.choose #[budget]) true
    | 2 | 3 =>
      let (key,old,new) := if mode == 2 then (`S_eq_physical,`S,`physicalS)
        else (`Ccoef_eq_physical,`Ccoef,`physicalCcoef)
      let original := app (aux ++ old) x
      store key x (← mkEqRefl original) false (some (← mkEq original (app (dest ++ new) fixed)))
    | _ => throwError "static reach: unknown factorization mode"

/-- The selected31 telescope fixes the original protected coefficient order and
all geometric choices first. It specializes the *dependent* selected33 to the
actual final band `2` before opening any later binder. -/
def withHistoryBand (next : Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let rec walk (fuel : Nat) (i : Nat) (type : Expr) (args kept : Array Expr) : MetaM Unit := do
    match fuel with
    | 0 => next args kept type
    | fuel+1 =>
      let .forallE name dom body bi ← whnf type | throwError "static reach: missing static input {i}"
      if i == 23 || i == 24 then
        let v := mkConst (dest ++ (if i == 23 then `historyBand else `one_le_historyBand))
        walk fuel (i+1) (body.instantiate1 v) (args.push v) kept
      else
        let k := fun v => walk fuel (i+1) (body.instantiate1 v) (args.push v) (kept.push v)
        if bi == .instImplicit then withLocalDecl name bi dom k
        else withLocalDeclNoLocalInstanceUpdate name bi dom k
  walk 33 0 (← getConstInfo (admission ++ `commonS)).type #[] #[]

/-- Reuse the concrete source45 reduction of the checked global inverse. Only
its fixed source coordinates are transported; the history at native44 and all
later inputs are verified absent, not erased by an equality hypothesis. -/
def withFixedOriginal (next : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withActualInverse fun d => do
    let x := d.source45
    let n := x[0]!
    let two := mkNatLit 2
    let reserve := app ``Nat.mul #[two,app ``Nat.add #[app ``Nat.div #[n,two],two]]
    let hMap := app (inverse ++ `sourceReserve_shift_le_map) #[n,x[26]!,x[1]!,x[37]!]
    let hDensity := app (inverse ++ `sourceReserve_shift_le_density) #[n,x[1]!]
    let x41 := x[:38].toArray ++ #[reserve,hMap,hDensity]
    let native44 := d.parameters[:44].toArray
    let terms ← x41.mapM (mkLambdaFVars native44 ·)
    unless terms.all (fun term => !term.hasFVar) do throwError "static reach: history entered auxiliary coefficient choice"
    withSelectedBefore 44 fun original params _ => do
      let raw ← original.mapM (mkLambdaFVars params ·)
      withHistoryBand fun selected kept _ => do
        let native := raw.map (·.beta selected)
        let actual := terms.map (·.beta native)
        unless kept.size == 31 && selected.size == 33 && native.size == 44 && actual.size == 41 do
          throwError "static reach: original binder counts moved"
        unless actual[24]! == mkConst (dest ++ `historyBand) && actual[27]! == native[32]! do
          throwError "static reach: physical band or fixed kMin differs between sources"
        next selected kept native actual

elab "join_original_auxiliary_reach " which:num : command => liftTermElabM do
  withFixedOriginal fun selected kept _ actual => do
    let old := app (admission ++ `commonS) selected
    let physical := app (dest ++ `physicalS) (physicalInputs actual)
    let Tref := app (dest ++ `Tref) kept
    match which.getNat with
    | 0 => store `Tref kept (← mkAppM ``Max.max #[old,physical]) true
    | 1 =>
      let target ← mkAppM ``LE.le #[old,Tref]
      store `commonS_le_Tref kept (app ``OriginalCanonicalStaticReach.join_left #[old,physical]) false (some target)
    | 2 =>
      let target ← mkAppM ``LE.le #[app (aux ++ `S) actual,Tref]
      store `Saux_le_Tref kept (app ``OriginalCanonicalStaticReach.join_right #[old,physical]) false (some target)
    | _ => throwError "static reach: unknown actual maximum mode"

end JanetCartan.PhysicalMean.OriginalCanonicalStaticReachTemplate
end

factor_original_auxiliary_choice 0
factor_original_auxiliary_choice 1
factor_original_auxiliary_choice 2
factor_original_auxiliary_choice 3
join_original_auxiliary_reach 0
join_original_auxiliary_reach 1
join_original_auxiliary_reach 2
