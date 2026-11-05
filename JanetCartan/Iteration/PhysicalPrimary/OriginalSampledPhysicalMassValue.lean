module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSynthesis
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassValue
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# The exact physical Fourier mass on native source DATA

The frozen physical synthesis uses the same original detector/input Fourier
mass as native DATA53. Prove that equality before substituting the actual
complete-forcing Picard source, then transport only a scalar inequality.
The original detector has bound one; it is not replaced by the constant-one
detector. The input is unweighted by the angular scalar, not a changed source.
Consumer: `OriginalFullSourcePhysicalPrimary.physical_profiles`, the physical
norm estimate `main:eq:primary-fixed-scales`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValueApplication
private theorem mass_le {a b c : ℝ} (h : a = b) (hb : b ≤ c) : a ≤ c := h ▸ hb
end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValueApplication
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValueApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValue
private def profiles := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def dataRoot := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual physical input mass: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual physical input mass: unresolved native source or sample"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let out ← liftM IO.getStdout
  liftM <| out.putStrLn s!"actual physical input mass: checking {key}/{p.size}"
  liftM <| out.flush
  addDecl (.thmDecl {name := ns ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (ns ++ key) "The frozen physical synthesis's literal original detector/input Fourier mass is exactly the unguarded native DATA53 value, before any finite Picard source substitution. Scalar bound transport preserves the genuine producer, original sample and Fourier normalization (main:eq:primary-fixed-scales)."
  logInfo m!"actual physical input mass: checked {key}/{p.size}"

elab "publish_original_physical_mass_value " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 2 do throwError "actual physical input mass: unknown bridge"
  let ci ← getConstInfo (profiles ++ `selectedSourceCombinedWave_mass_statement)
  let some body := ci.value? (allowOpaque := true) |
    throwError "actual physical input mass: frozen physical statement body unavailable"
  forallBoundedTelescope ci.type (some 53) fun p _ => do
    unless p.size == 53 do throwError "actual physical input mass: native source53 changed"
    let mass ← lambdaTelescope (body.beta p).headBeta fun point target => do
      unless point.size == 3 && target.isAppOfArity ``LE.le 4 do
        throwError "actual physical input mass: physical derivative/point statement changed"
      let rhs := target.getAppArgs[3]!
      unless rhs.isAppOfArity ``HMul.hMul 6 do
        throwError "actual physical input mass: lost literal mass product"
      let total := rhs.getAppArgs[5]!
      unless total.isAppOfArity ``HAdd.hAdd 6 do
        throwError "actual physical input mass: lost unscaled positive baseline"
      let mass := total.getAppArgs[5]!
      if (← mkLambdaFVars p mass).hasFVar then
        throwError "actual physical input mass: mass depends on derivative or physical point"
      unless (mass.find? (·.isConstOf `JanetCartan.RawInputPartition.weightedWideDensity)).isSome do
        throwError "actual physical input mass: original detector/input density changed"
      return mass
    let named := app (dataRoot ++ `fourierMassValueData) p
    if mode == 0 then
      let target := mkAppN (mkConst ``Eq [.one]) #[mkConst ``Real,mass,named]
      let proof := mkAppN (mkConst ``Eq.refl [.one]) #[mkConst ``Real,named]
      save `literalSourceMass_eq_inputValue p proof target
    else
      withLocalDeclD `upper (mkConst ``Real) fun upper => do
        let domain ← mkAppM ``LE.le #[named,upper]
        withLocalDeclD `hinput domain fun hinput => do
          let target ← mkAppM ``LE.le #[mass,upper]
          save `physicalMass_le_of_inputValue (p ++ #[upper,hinput]) hinput target
end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValueApplication
end

publish_original_physical_mass_value 0
publish_original_physical_mass_value 1
#print axioms JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValue.literalSourceMass_eq_inputValue
#print axioms JanetCartan.PhysicalPrimary.OriginalSampledPhysicalMassValue.physicalMass_le_of_inputValue
