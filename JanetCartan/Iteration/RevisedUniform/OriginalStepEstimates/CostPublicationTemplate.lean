module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.CostsTemplate
public meta import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
public meta import Lean

/-!
# Publish the original step coefficient independently of the dynamic inputs

Only the original static norm, smoothing, signed and background prices are
needed here. Changes to the mean/pair/primary proof applications therefore do
not require reconstructing those prices. The nonnegativity proof reads the
already published constant, preserving the identical original choices.
Consumer: `step_of_primary_strain` (`main:thm:step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepCostPublicationTemplate

open Lean Meta Elab Command
open OriginalStepEstimatesTemplate OriginalUniformCorrectionTemplate

private def root := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def strainRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
private def uniformRoot := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | value => value

private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- The actual common Picard count, before the history. -/
def originalStrainCount (n k : Expr) : MetaM Expr := do
  let q := app (uniformRoot ++ `meanOrder) #[n,k]
  let accuracy ← termWith [(`q,q)] "(q : ℝ) + 1"
  pure (app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionSteps #[n,accuracy])

/-- The original strain price at the same count and joint primary order. -/
def originalStrainCost (selected33 : Array Expr) (n k count : Expr) : Expr :=
  app (strainRoot ++ `Cstrain)
    (selected33 ++ #[count,app (uniformRoot ++ `primaryOrder) #[n,k]])

private def checkedProducer (name : Name) : MetaM Unit := do
  let _ ← getConstInfo name
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual early step cost: unfinished producer {name}: {axioms}"

private def save (key : Name) (p : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let actual := key == `C || key == `C_nonneg
  unless p.size == (if actual then 8 else 9) do
    throwError "actual early step cost: changed fixed metric/accuracy boundary"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual early step cost: history or unresolved input entered {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "actual early step cost: unavailable original metadata {missing.toList}"
  let name := root ++ key
  if (env.find? name).isSome then throwError "actual early step cost: duplicate declaration {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Checking original early step coefficient {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name (if actual then
    "The actual common original physical step price, with the genuine Cstrain35 substituted into the same norm, signed, smoothing and background prices. It is fixed on the original metric and accuracy before every history and target dilation. This coefficient alone does not assert a step estimate (main:thm:step; main:prop:current-scale)."
    else "The common original physical step price, fixed on the original metric and accuracy before every history and target dilation. The exact original norm, signed, smoothing and background prices are supplied internally; only the primary strain price awaits its named actual producer. No estimate is asserted by this constant alone (main:thm:step; main:prop:current-scale).")
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual early step cost: nonstandard axioms {axioms}"
  logInfo m!"PASS original early step coefficient {key}/{p.size}: {axioms}"

elab "publish_original_early_step_cost " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual early step cost: unknown mode"
  if mode.getNat == 0 then
    withFixedMetric fun fixed => do
      withLocalDeclD `k (mkConst ``Nat) fun k => do
        withLocalDeclD `Cstrain (mkConst ``Real) fun Cstrain => do
          let (value,_) ← originalStepCost fixed.parameters fixed.dimension fixed.selected33 k Cstrain
          save `C_of_primary_strain (fixed.parameters ++ #[k,Cstrain]) value (mkConst ``Real) true
  else
    let info ← getConstInfo (root ++ `C_of_primary_strain)
    forallBoundedTelescope info.type (some 9) fun p result => do
      unless p.size == 9 && result.isConstOf ``Real do
        throwError "actual early step cost: published static9 changed"
      let value := head ((info.value! (allowOpaque := true)).beta p)
      unless value.isAppOfArity (root ++ `finalConstant) 4 do
        throwError "actual early step cost: published original coefficient changed"
      let a := value.getAppArgs
      unless a[1]!.isAppOfArity (root ++ `lowerConstant) 1 do
        throwError "actual early step cost: published lower-price maximum changed"
      let hC := app (root ++ `lowerConstant_nonneg) #[a[1]!.appArg!]
      let proof := app (root ++ `finalConstant_nonneg) (a.push hC)
      let target ← mkAppM ``LE.le
        #[← mkNumeral (mkConst ``Real) 0,app (root ++ `C_of_primary_strain) p]
      save `C_of_primary_strain_nonneg p proof target

/-- Publish the actual early coefficient independently of the dynamic
primary-strain proof, once its genuine cost declaration has been released. -/
elab "construct_actual_original_step_cost " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual original step cost: unknown mode"
  checkedProducer (strainRoot ++ `Cstrain)
  checkedProducer (root ++ `C_of_primary_strain)
  checkedProducer (root ++ `C_of_primary_strain_nonneg)
  if mode.getNat == 0 then
    withFixedMetric fun fixed => do
      withLocalDeclD `k (mkConst ``Nat) fun k => do
        let n := mkApp (mkConst ``Nat.succ) fixed.dimension[0]!
        let count ← originalStrainCount n k
        let Cstrain := originalStrainCost fixed.selected33 n k count
        let args := fixed.parameters ++ #[k,Cstrain]
        save `C (fixed.parameters.push k) (app (root ++ `C_of_primary_strain) args)
          (mkConst ``Real) true
  else
    let info ← getConstInfo (root ++ `C)
    forallBoundedTelescope info.type (some 8) fun p result => do
      unless p.size == 8 && result.isConstOf ``Real do
        throwError "actual original step cost: changed published static8"
      let value := head ((info.value! (allowOpaque := true)).beta p)
      unless value.isAppOfArity (root ++ `C_of_primary_strain) 9 do
        throwError "actual original step cost: the original strain substitution changed"
      let proof := app (root ++ `C_of_primary_strain_nonneg) value.getAppArgs
      let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,app (root ++ `C) p]
      save `C_nonneg p proof target

end JanetCartan.RevisedUniform.OriginalStepCostPublicationTemplate
end
