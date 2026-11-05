module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedCorrection
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageMetric
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
/-! # The exact original signed angles of the actual complete wave

The complete wave uses the literal inverse native radial rate, while the signed
construction writes its phase as lambda times the native radial scalar. Only
inverse/multiplication algebra relates these two presentations. No carrier
factor, source annulus, historyMap, or sample is changed. This identity is the
last phase-convention join before the genuine complete-amplitude R-profile is
used by the original signed ledger (`main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSourceSignedPhase
/-- Literal original rate, including zero-safe total inverse conventions. -/
theorem original_rate_phase (a r l : ℝ) : a / (r*l)⁻¹ = l*(r*a) := by
  rw [div_inv_eq_mul]
  ring
/-- A singleton presentation and the full sampled presentation have identical
complete derivative amplitudes on the same phase. -/
theorem amplitude_on_same_phase {n N : ℕ} {ι : Type}
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (i : ι) (phase : Euclidean n → ℝ) (h : θ i = phase) :
    UniformStep.sampledDerivativeAmplitude Z θ i =
      UniformStep.sampledDerivativeAmplitude (fun _ : Unit ↦ Z i) (fun _ : Unit ↦ phase) () := by
  rw [← h]
  rfl
end JanetCartan.PhysicalPairs.OriginalSourceSignedPhase
end
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceSignedPhaseTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSourceSignedPhase
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual signed phase: unresolved native phase/amplitude {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual signed phase: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "The actual complete original wave and its original signed construction use the SAME phase and complete derivative amplitude, with identical native radial rate, protected sampler22 and original sample; no doubled rate or replacement history map (main:prop:pairs)."
  liftM <| IO.eprintln s!"actual signed phase: kernel passed {name}"
elab "identify_original_signed_source_phase " which:num : command => liftTermElabM do
  unless which.getNat < 4 do throwError "actual signed phase: unknown mode"
  let correction := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
  forallBoundedTelescope (← getConstInfo correction).type (some 55) fun p _ => do
    let original ← body correction p
    unless original.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedSum.correction 47 do
      throwError "actual signed phase: original finite correction changed"
    let sp := original.getAppArgs
    let θ := app `JanetCartan.PhysicalPairs.OriginalStageMetric.angles sp[:45].toArray
    let source := p[:44].toArray ++ p[45:53].toArray
    forallBoundedTelescope (← inferType θ) (some 1) fun samples _ => do
      unless samples.size == 1 do throwError "actual signed phase: sample type changed"
      let i := samples[0]!
      let pre := p.push i
      let phase := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.phase (source.push i)
      if which.getNat == 0 then
        let actualBody ← body `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.phase (source.push i)
        let angleBody ← body `JanetCartan.PhysicalPairs.OriginalStageMetric.angles sp[:45].toArray
        withLocalDeclD `x (← inferType phase).bindingDomain! fun x => do
          let ax := (mkApp actualBody x).headBeta
          let bx := (mkApp (mkApp angleBody i) x).headBeta
          unless ax.isAppOfArity ``HDiv.hDiv 6 && bx.isAppOfArity ``HMul.hMul 6 do
            throwError "actual signed phase: native inverse-rate presentation changed"
          let group := bx.getAppArgs[5]!
          unless group.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase 45 do
            throwError "actual signed phase: not the SAME original radial carrier"
          let radial ← body `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase group.getAppArgs[:42].toArray
          unless radial.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.radialCarrier 11 do
            throwError "actual signed phase: original radial-family presentation changed"
          let r := mkApp radial.getAppArgs[7]! group.getAppArgs[42]!
          let a := ax.getAppArgs[4]!
          let parameter := a.appArg!
          unless parameter.getUsedConstantsAsSet.contains `JanetCartan.ContinuumRow.CanonicalCarrier.parameter do
            throwError "actual signed phase: original parameter coordinate conversion changed"
          let node := parameter.appArg!.appArg!
          let hcoord := app ``JanetCartan.PhysicalMean.OriginalBackgroundHermitianSupportTemplate.outer_sampling_node #[node]
          let hcarrier ← mkAppM ``congrArg #[a.appFn!,hcoord]
          let anew := (← inferType hcarrier).appArg!
          let algebra := app ``JanetCartan.PhysicalPairs.OriginalSourceSignedPhase.original_rate_phase
            #[anew,r,bx.getAppArgs[4]!]
          let quotient ← withLocalDeclD `t (mkConst ``Real) fun t =>
            mkLambdaFVars #[t] (mkAppN ax.getAppFn (ax.getAppArgs.set! 4 t))
          let first ← mkAppM ``congrArg #[quotient,hcarrier]
          let proof ← mkAppM ``Eq.trans #[first,algebra]
          save `phase_point (pre.push x) proof (← mkEq (mkApp phase x) (mkApp (mkApp θ i) x))
        return
      if which.getNat == 1 then
        let proof ← mkAppM ``funext #[app (root ++ `phase_point) pre]
        save `phase_eq pre proof (← mkEq phase (mkApp θ i))
        return
      let Z ← withLocalDeclD `k (← inferType i) fun k => do
        let w ← mkAppM ``DFunLike.coe #[mkApp sp[45]! k]
        mkLambdaFVars #[k] w
      let ptype ← inferType phase
      let n := ptype.bindingDomain!.appArg!
      let valueType := (← inferType Z).bindingBody!.bindingBody!
      let N := valueType.appArg!.appArg!
      let A := mkAppN (mkConst ``JanetCartan.UniformStep.sampledDerivativeAmplitude [.zero])
        #[n,N,← inferType i,Z,θ,i]
      if which.getNat == 2 then
        save `signedAmplitude pre A (← inferType A) true
      else
        let same := app ``JanetCartan.PhysicalPairs.OriginalSourceSignedPhase.amplitude_on_same_phase
          #[n,N,← inferType i,Z,θ,i,phase,← mkAppM ``Eq.symm #[app (root ++ `phase_eq) pre]]
        let proof ← mkAppM ``Eq.symm #[same]
        let actual := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude (source.push i)
        save `amplitude_eq_signed pre proof (← mkEq actual (app (root ++ `signedAmplitude) pre))
end JanetCartan.PhysicalPairs.OriginalSourceSignedPhaseTemplate
end
