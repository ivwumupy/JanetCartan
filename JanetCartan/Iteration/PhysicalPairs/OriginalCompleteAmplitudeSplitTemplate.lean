module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitude
public import JanetCartan.Iteration.PhysicalPairs.CombinedNode
/-! # Actual complete amplitude = original unscaled baseline + same canonical source

This is the physical derivative-amplitude split, not a redefinition of the
canonical baseline. The whole angular correction is kept, including the SAME
response B. Original ψ support and plateau supply differentiability internally
on the entire original source chart; no inner positivity or new admission is
added (`main:eq:mean-final-amplitude`, `main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit
open UniformStep
/-- The existing observation's plateau lies in its already proved smooth buffer. -/
theorem differentiableAt_of_existing_observation {n N : ℕ}
    (ψ : Euclidean n → ℝ) (X : Set (Euclidean n))
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N)) (x : Euclidean n)
    (hX : IsOpen X) (hs : tsupport ψ ⊆ X) (hp : ψ =ᶠ[𝓝 x] fun _ ↦ 1)
    (hZ : ContDiffOn ℝ ∞ Z X) : DifferentiableAt ℝ Z x := by
  have h1 : ψ x = 1 := hp.eq_of_nhds
  have hx : x ∈ X := hs (subset_tsupport ψ (by change ψ x ≠ 0; rw [h1]; exact one_ne_zero))
  exact (hZ.contDiffAt (hX.mem_nhds hx)).differentiableAt (by simp)
/-- No support gate is applied to the baseline. Smoothness of the full sum and
of its whole angular summand suffices for exact derivative linearity. -/
theorem amplitude_add_of_right {n N : ℕ}
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : Euclidean n → ℝ)
    (x : Euclidean n) (hZW : DifferentiableAt ℝ (Z+W) x) (hW : DifferentiableAt ℝ W x) :
    sampledDerivativeAmplitude (fun _ : Unit ↦ Z+W) (fun _ ↦ θ) () x =
      sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () x +
        sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) () x := by
  have hZ : DifferentiableAt ℝ Z x := by simpa only [add_sub_cancel_right] using hZW.sub hW
  simpa only [one_smul] using CombinedNode.amplitude_add_smul Z W θ 1 x hZ hW
/-- Pointwise equality on the original open chart preserves all amplitude jets. -/
theorem germ_of_chart_eq {n N : ℕ}
    (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (U : Set (Euclidean n))
    (hU : IsOpen U) (heq : EqOn A B U) (x : Euclidean n) (hx : x ∈ U) :
    A =ᶠ[𝓝 x] B := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,heq⟩
end JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplitTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit
private def amp := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def remainingType (key : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for v in args do
    unless type.isForall do throwError "actual amplitude split: changed actual source telescope"
    type := type.bindingBody!.instantiate1 v
  return type
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def save (key : Name) (p : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual amplitude split: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual amplitude split: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "Actual complete original-phase amplitude equals the unscaled physical baseline plus SAME canonical whole-source derivative on the entire original source chart; no extra cutoff, source, phase or angular support gate (main:eq:mean-final-amplitude, main:prop:pairs)."
  liftM <| IO.eprintln s!"actual amplitude split: kernel passed {name}"

elab "split_original_complete_amplitude " which:num : command => liftTermElabM do
  unless which.getNat < 5 do throwError "actual amplitude split: unknown publication mode"
  withActualSelectedSourceWave fun p _ _ literal _ _ _ => do
    unless literal.isAppOfArity (wave ++ `Combined.field) 69 do
      throwError "actual amplitude split: changed COMPLETE baseline-plus-angular constructor"
    let combined ← body (wave ++ `Combined.field) literal.getAppArgs
    unless combined.isAppOfArity ``HAdd.hAdd 6 do throwError "actual amplitude split: the complete field is not the original sum"
    let base := combined.getAppArgs[4]!
    let angular := combined.getAppArgs[5]!
    unless angular.isAppOfArity (wave ++ `Whole.full_angular.corrected) 66 do
      throwError "actual amplitude split: angular summand is not the literal whole original source"
    let A := app (amp ++ `amplitude) p
    let Atype ← inferType A
    unless Atype.isForall && Atype.bindingBody!.isAppOfArity ``Matrix 3 do
      throwError "actual amplitude split: changed actual matrix field"
    let matrix := Atype.bindingBody!.getAppArgs
    let n := matrix[1]!.appArg!
    let N := matrix[0]!.appArg!
    let θ := app (amp ++ `phase) p
    let singleton (f : Expr) := mkLambda `u .default (mkConst ``Unit) f
    let ampl (f : Expr) := mkAppN (mkConst ``JanetCartan.UniformStep.sampledDerivativeAmplitude [.zero])
      #[n,N,mkConst ``Unit,singleton f,singleton θ,mkConst ``Unit.unit]
    if which.getNat == 0 then
      let B := ampl base
      save `baselineAmplitude p B (← inferType B) true
      return
    let gt ← remainingType `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.germ_statement p
    forallBoundedTelescope gt (some 2) fun point _ => do
      unless point.size == 2 do throwError "actual amplitude split: changed source-chart point/admission"
      let x := point[0]!
      let all := p ++ point
      let sourceProof := app `JanetCartan.PhysicalPairs.OriginalSourceAmplitude.angular_on_original_chart all
      let sourceEq ← inferType sourceProof
      unless sourceEq.isAppOfArity ``Eq 3 do throwError "actual amplitude split: changed actual complete canonical/angular identity"
      if which.getNat == 1 then
        let sourceFn ← mkLambdaFVars #[x] sourceEq.getAppArgs[1]!
        save `sourceAmplitude p sourceFn (← inferType sourceFn) true
        return
      let B := app (ns ++ `baselineAmplitude) p
      let S := app (ns ++ `sourceAmplitude) p
      let sum ← mkAppM ``HAdd.hAdd #[B,S]
      let chart := (← inferType point[1]!).getAppArgs[3]!
      unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
        throwError "actual amplitude split: not the unchanged full original chart"
      if which.getNat == 2 then
        let bp := p[:50].toArray.push p[52]!
        let certificate := app `JanetCartan.PhysicalPairs.OriginalObservationBuffer.buffer bp
        let bt ← body `JanetCartan.PhysicalPairs.OriginalObservationBuffer.statement bp
        let X := bt.getAppArgs[0]!.appArg!
        let st := bt.getAppArgs[1]!.getAppArgs
        let ψ := st[st.size-2]!.appArg!
        let plateau := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
          (chart.getAppArgs ++ point)
        let full := app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
        let hc := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.differentiableAt_of_existing_observation
          #[n,N,ψ,X,full,x,.proj ``And 0 certificate,.proj ``And 1 certificate,plateau,
            app `JanetCartan.PhysicalPairs.OriginalSelectedCell.smooth p]
        let ha := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.differentiableAt_of_existing_observation
          #[n,N,ψ,X,angular,x,.proj ``And 0 certificate,.proj ``And 1 certificate,plateau,
            app (wave ++ `Whole.full_angular_smooth_on_selected_cell.corrected) angular.getAppArgs]
        let add := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.amplitude_add_of_right
          #[n,N,base,angular,θ,x,hc,ha]
        let addType ← inferType add
        let putSource ← mkAppM ``congrArg #[addType.getAppArgs[2]!.appFn!,← mkAppM ``Eq.symm #[sourceProof]]
        let rawSplit ← mkAppM ``Eq.trans #[add,putSource]
        let sameGerm := app (amp ++ `germ_on_original_chart) all
        let observedEq ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[sameGerm]
        let proof ← mkAppM ``Eq.trans #[observedEq,rawSplit]
        let target ← mkEq (mkApp A x) (mkApp sum x)
        save `amplitude_eq_base_add_source all proof target
      else if which.getNat == 3 then
        let hU ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM ``IsOpen #[chart]))
        let eqOn ← withLocalDeclD `y Atype.bindingDomain! fun y => do
          withLocalDeclD `hy (← mkAppM ``Membership.mem #[chart,y]) fun hy =>
            mkLambdaFVars #[y,hy] (app (ns ++ `amplitude_eq_base_add_source) (p ++ #[y,hy]))
        let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.germ_of_chart_eq
          #[n,N,A,sum,chart,hU,eqOn,x,point[1]!]
        save `germ_on_original_chart all proof (← inferType proof)
      else
        withLocalDeclD `j (mkConst ``Nat) fun j => do
          let proof := app ``JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude_jets_of_germ
            #[n,N,A,sum,x,app (ns ++ `germ_on_original_chart) all,j]
          save `jets_on_original_chart (all.push j) proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplitTemplate
end
