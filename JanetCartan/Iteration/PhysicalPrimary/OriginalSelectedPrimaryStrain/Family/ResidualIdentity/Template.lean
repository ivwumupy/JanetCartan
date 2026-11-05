module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphData
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Exact source identities for the original residual estimate

The observed-chain estimate reconstructs the original current from
`Family.historyMap`. The source data already use that same current. These two
identities permit the residual estimate to be transported to the named source
field and carrier without normalizing the complete construction inside a norm.

The consumer is `Discrepancy.point_of_cnorm_of_source_identities`, and hence
`main:eq:primary-strain` and `app:ch_regular:eq:inverse-remainder` in paper-v2.
Neither an analytic estimate nor a source-success hypothesis is an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentityTemplate

open Lean Meta Elab Command

private def familyRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family
private def statementRoot := familyRoot ++ `ResidualIdentity
private def sourceRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def discrepancyRoot := `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def bodyAt (name : Name) (p : Array Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let some value := info.value? (allowOpaque := true) |
    throwError "original residual identity: missing original body {name}"
  return (value.beta p).headBeta

private def save (name : Name) (p : Array Expr) (value target : Expr)
    (isStatement : Bool) : MetaM Unit := do
  unless p.size == 35 do
    throwError "original residual identity: expected selected33, N, and the original label"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  if (env.find? name).isSome then
    throwError "original residual identity: duplicate public declaration {name}"
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original residual identity: unresolved or additional source input"
    let missing := e.getUsedConstants.filter (fun key => (env.find? key).isNone)
    unless missing.isEmpty do
      throwError "original residual identity: missing original metadata {missing.toList}"
    if e.getUsedConstants.any (fun key => key.toString.startsWith "JanetCartan.Scratch." ||
        key.toString.startsWith "Scratch.") then
      throwError "original residual identity: Scratch dependency"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Kernel checking exact original residual identity {name}/35"
  (← IO.getStdout).flush
  if isStatement then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The observed residual reconstructs the SAME original current, smooth source and undoubled carrier as the full selected33+N family. Only the original source label follows the fixed data; no analytic estimate, changed cutoff or new history is assumed. Consumer: the actual primary discrepancy transport (main:eq:primary-strain; app:ch_regular:eq:inverse-remainder)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original residual identity: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS exact original residual identity {name}/35: {axioms}"

/-- Keep the published input domains verbatim, without classifying their
large source-membership propositions as possible local instances. -/
private def withStatement (name : Name)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  loop 35 (← getConstInfo name).type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain body bi := type.consumeMData |
        throwError "original residual identity: statement telescope ended at {p.size}"
      withLocalDeclNoLocalInstanceUpdate key bi (domain.instantiateRev p) fun x =>
        loop k body (p.push x)

/-- Publish either exact proposition on the actual full observed family.
The frequency and source statements are independent kernel checks. -/
def publishStatement (frequency : Bool) : MetaM Unit := do
  FamilyTemplate.withFamily fun c => do
    SourceResidual.Template.withGraph fun x g weak coefficient _ => do
      let substitute (e : Expr) : MetaM Expr := do
        return ((← mkLambdaFVars x e).beta c.graph[:36].toArray).headBeta
      let g ← g.mapM substitute
      let weak ← weak.mapM substitute
      let coefficient ← coefficient.mapM substitute
      let (current,_,rho,_,_) ← SourceResidual.Template.currentAt
        g weak coefficient (c.at `historyMap)
      let p := c.fixed.push c.label
      let (key,alpha,lhs,rhs) ← if frequency then
          pure (`history_frequency_statement,mkConst ``Real,rho,c.at `frequency)
        else do
          let original ← bodyAt (sourceRoot ++ `discrepancy) c.sourceArgs
          unless original.isAppOfArity ``DFunLike.coe 6 &&
              original.getAppArgs[4]!.isAppOfArity (discrepancyRoot ++ `discrepancy) 38 do
            throwError "original residual identity: original positive discrepancy changed"
          -- The smooth-source and output types are fixed before the history.
          -- Reuse their checked coercion annotations and replace only the
          -- current-dependent map and the SAME named smooth source.
          let a := original.getAppArgs
          let observed := mkAppN original.getAppFn
            ((a.set! 4 (app (discrepancyRoot ++ `discrepancy) current)).set! 5
              (c.at `smoothInput))
          let alpha ← FamilyTemplate.resultAt (familyRoot ++ `discrepancy) p
          pure (`observed_discrepancy_statement,alpha,observed,c.at `discrepancy)
      let target := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,lhs,rhs]
      save (statementRoot ++ key) p target (mkSort .zero) true

/-- Prove the exact checked statement by folding the already published named
field. The kernel verifies the original current and datum conversions. -/
def publishProof (frequency : Bool) : MetaM Unit := do
  let statement := statementRoot ++
    (if frequency then `history_frequency_statement else `observed_discrepancy_statement)
  let name := familyRoot ++
    (if frequency then `history_frequency_eq else `observed_discrepancy_eq)
  withStatement statement fun p _ => do
    let eq ← bodyAt statement p
    unless eq.isAppOfArity ``Eq 3 do
      throwError "original residual identity: statement is not the exact equality"
    let a := eq.getAppArgs
    let value := mkAppN (mkConst ``Eq.refl eq.getAppFn.constLevels!) #[a[0]!,a[2]!]
    save name p value (app statement p) false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentityTemplate
end
