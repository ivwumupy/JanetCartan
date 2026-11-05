module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSchwartz
/-! # All complete derivative-amplitude jets survive the actual observation

The phase is extracted from the checked canonical/physical angular identity;
it is the SAME original carrier used for the whole corrected node. The wave
is the actual original-ψ Schwartz representative, not a new physical cutoff.
The source-chart germ preserves the full demodulated derivative and every jet,
including the lower-order response (`main:prop:pairs`, `main:eq:mean-final-amplitude`).
No R-bound for the oscillatory displacement is asserted.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
open UniformStep
/-- Locality of the FULL corrected derivative amplitude, with the same phase. -/
theorem amplitude_germ_of_germ {n N : ℕ}
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : Euclidean n → ℝ)
    {x : Euclidean n} (h : Z =ᶠ[𝓝 x] W) :
    sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () =ᶠ[𝓝 x]
      sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) () := by
  filter_upwards [h.eventually_nhds] with y hy
  exact ObservedSchwartz.amplitude_eq_of_germ Z W θ hy
/-- No principal-part truncation: every derivative of the complete amplitude
agrees at a source-chart point. -/
theorem amplitude_jets_of_germ {n N : ℕ}
    (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ) {x : Euclidean n}
    (h : A =ᶠ[𝓝 x] B) (j : ℕ) :
    iteratedFDeriv ℝ j A x = iteratedFDeriv ℝ j B x :=
  (h.iteratedFDeriv ℝ j).eq_of_nhds
end JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
private def schw := `JanetCartan.PhysicalPairs.OriginalSourceSchwartz
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def remainingType (key : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for v in args do
    unless type.isForall do throwError "actual complete amplitude: changed actual source telescope"
    type := type.bindingBody!.instantiate1 v
  return type
private def save (key : Name) (p : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual complete amplitude: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual complete amplitude: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"actual complete amplitude: kernel passed {name}"

elab "publish_original_complete_amplitude " which:num : command => liftTermElabM do
  unless which.getNat < 5 do throwError "actual complete amplitude: unknown publication mode"
  withActualSelectedSourceWave fun p _ _ _ _ _ _ => do
    let angular ← body `JanetCartan.PhysicalPairs.OriginalSourceAmplitude.observed_angular_statement p
    let some literal := angular.find? (·.isAppOfArity ``JanetCartan.UniformStep.sampledDerivativeAmplitude 7) |
      throwError "actual complete amplitude: missing the checked same-phase angular amplitude"
    let a := literal.getAppArgs
    unless a[2]! == mkConst ``Unit do throwError "actual complete amplitude: changed same-node Unit family"
    let n := a[0]!
    let N := a[1]!
    let phase := (mkApp a[4]! (mkConst ``Unit.unit)).headBeta
    if phase.hasLooseBVars then throwError "actual complete amplitude: phase depends on later torus point"
    if which.getNat == 0 then
      save `phase p phase (← inferType phase) true
      return
    let θ := app (ns ++ `phase) p
    let raw := app ``JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
    let observed ← mkAppM ``DFunLike.coe #[app (schw ++ `wave) p]
    let singleton (f : Expr) := mkLambda `u .default (mkConst ``Unit) f
    let amplitude (f : Expr) := mkAppN (mkConst ``JanetCartan.UniformStep.sampledDerivativeAmplitude [.zero])
      #[n,N,mkConst ``Unit,singleton f,singleton θ,mkConst ``Unit.unit]
    if which.getNat == 1 then
      let value := amplitude raw
      save `rawAmplitude p value (← inferType value) true
      return
    if which.getNat == 2 then
      let value := amplitude observed
      save `amplitude p value (← inferType value) true
      return
    let gt ← remainingType (schw ++ `germ_statement) p
    forallBoundedTelescope gt (some 2) fun point _ => do
      unless point.size == 2 do throwError "actual complete amplitude: changed source-chart germ admission"
      let all := p ++ point
      let A := app (ns ++ `amplitude) p
      let B := app (ns ++ `rawAmplitude) p
      if which.getNat == 3 then
        let h := app (schw ++ `germ_on_original_chart) all
        let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude_germ_of_germ
          #[n,N,observed,raw,θ,point[0]!,h]
        let type ← inferType proof
        unless type.isAppOfArity ``Filter.EventuallyEq 5 do
          throwError "actual complete amplitude: changed same-phase amplitude germ"
        let target := mkAppN type.getAppFn ((type.getAppArgs.set! 3 A).set! 4 B)
        save `germ_on_original_chart all proof target
      else
        withLocalDeclD `j (mkConst ``Nat) fun j => do
          let h := app (ns ++ `germ_on_original_chart) all
          let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude_jets_of_germ
            #[n,N,A,B,point[0]!,h,j]
          save `jets_on_original_chart (all.push j) proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeTemplate
end
