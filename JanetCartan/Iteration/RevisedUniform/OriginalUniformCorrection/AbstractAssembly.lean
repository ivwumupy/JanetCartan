module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.AssemblyTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Thresholds
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
Conditional deduction for the exact final assembly. The local
step premise uses the actual selectedSource19 binder domains, followed by
the two final numerical gates. Its outcome is the original Components
outcome, including its literal `-(2 * k)` exponent. The local T_reaches
premise copies the actual five-budget theorem with only T replaced.

The real constants and then the actual step producer are substituted by
`ActualStatic` and the unconditional root. All five inputs remain explicit
here; this lemma alone does not claim an actual uniform correction or
Theorem 1.1 (`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open scoped Matrix.Norms.Frobenius ContDiff

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionAbstractTemplate

open Lean Meta Elab Command

private def uniform := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def stepRoot := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

private def stepContract (fixed : Array Expr) (C T : Expr) : MetaM Expr := do
  let source := app (uniform ++ `selectedSource) fixed
  forallBoundedTelescope (← inferType source) (some 12) fun stage _ => do
    unless stage.size == 12 do throwError "scratch assembly: original stage19 changed"
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let R := app `JanetCartan.iterationScale
      #[stage[0]!,mkConst `JanetCartan.growthExponent,stage[2]!]
    let G := app `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.Gmap fixed[:2].toArray
    let D := app `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.D fixed[:2].toArray
    let g := app (uniform ++ `targetFamily) fixed
    let one ← mkNumeral (mkConst ``Real) 1
    let initial := app `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial.Tpair
      (fixed[:2].toArray.push one)
    withLocalDeclD `hInitialPair (← mkAppM ``LE.le #[initial,stage[0]!]) fun hPair => do
      withLocalDeclD `hT (← mkAppM ``LE.le #[mkApp T stage[9]!,R]) fun hT => do
        let result ← termWith [(`n,n),(`N,N),(`R,R),(`G,G),(`D,D),(`g,g),
            (`u,stage[3]!),(`s,stage[6]!),(`k,stage[9]!),(`C,C)]
          ("(∃ U : SchwartzMap (JanetCartan.Euclidean n) (JanetCartan.Euclidean N), " ++
            "JanetCartan.PhysicalBernstein.HasFourierSupport (2 * R ^ JanetCartan.bandExponent) U ∧ " ++
            "JanetCartan.PhysicalBernstein.physicalL2Norm U ≤ " ++
            "C k * R ^ (-(k : ℝ)) * R ^ JanetCartan.RevisedScales.displacementLoss n ∧ " ++
            "JanetCartan.cNorm D 0 " ++
            "(JanetCartan.inducedMetric (JanetCartan.RevisedGlobal.finiteMap G u + ⇑U) - g s) ≤ " ++
            "C k * (R ^ (-(k : ℝ)) * R ^ (-(2 * (k : ℝ))) + " ++
            "(R ^ (-(k : ℝ))) ^ 3 * R ^ JanetCartan.RevisedScales.cubicLoss n))")
        mkForallFVars (stage ++ #[hPair,hT]) result

private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  unless p.size == 12 do throwError "scratch assembly: expected fixed7 and five explicit local contracts"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "scratch assembly: unresolved or hidden success input"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "scratch assembly: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "scratch assembly: nonstandard axioms {axioms}"
  logInfo m!"PASS kernel-checked conditional {key}/12: {axioms}"

run_meta do
  let cap := `JanetCartan.RevisedUniform.OriginalMetricPreparation.metricCap
  forallBoundedTelescope (← getConstInfo cap).type (some 7) fun fixed _ => do
    unless fixed.size == 7 do throwError "scratch assembly: original metric7 changed"
    let familyType ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    withLocalDeclD `C familyType fun C => do
      let nonneg ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        mkForallFVars #[k] (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,mkApp C k])
      withLocalDeclD `C_nonneg nonneg fun hC => do
        withLocalDeclD `T familyType fun T => do
          let originalT := app (stepRoot ++ `T) fixed
          let originalReaches ← instantiateForall (← getConstInfo (stepRoot ++ `T_reaches)).type fixed
          let reachesType := originalReaches.replace fun e => if e == originalT then some T else none
          if reachesType.getUsedConstants.contains (stepRoot ++ `T) then
            throwError "scratch assembly: T_reaches did not use the local T"
          withLocalDeclD `T_reaches reachesType fun hReach => do
            let stepType ← stepContract fixed C T
            withLocalDeclD `step stepType fun step => do
              let p := fixed ++ #[C,hC,T,hReach,step]
              let (proof,target) ←
                RevisedUniform.OriginalUniformCorrectionAssemblyTemplate.correctionTerm fixed C hC T hReach step
              save `uniformCorrection_of_contracts p proof target

end JanetCartan.RevisedUniform.OriginalUniformCorrectionAbstractTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.uniformCorrection_of_contracts
