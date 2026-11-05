module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceData
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularPrefix
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public meta import Lean

/-!
# Exact original source data in the prefixed raw angular formula

The consumer is `Factorization.observed_raw_angular_of_prefixed`, followed by
the actual source application in `Factorization.Source`. The original
primitive53, source, sample, unweighted component adjoint, fixed prefix and
whole raw angular field are retained. The only later premise is the exact
original prefixed differential identity (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template

open Lean Meta

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge
private def factor := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
private def actual := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def grouped := `JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization
private def source := `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile
private def app := SourceTemplate.app
private def bodyAt := SourceTemplate.bodyAt
private def typeAt := SourceTemplate.typeAt

private structure Context where
  data : SourceTemplate.Data
  point : Array Expr
  prefixed : Expr
  prefixEq : Expr
  groupedProof : Expr
  groupedEq : Expr
  derivative : Expr
  prefixField : Expr
  compactField : Expr

private def Context.params (c : Context) := c.data.params ++ c.point

/-- Read the SAME source and actual prefix predicate before assuming its
proof. The independent field and annular-sum equalities need no new premise. -/
private def withInputs (next : Context → MetaM Unit) : MetaM Unit :=
  SourceTemplate.withSource fun d => do
    let inputs := d.actualArgs ++ #[d.primitive[52]!, d.refinedInput]
    let stem := app (actual ++ `prefixed_forward_statement) inputs
    forallBoundedTelescope (← typeAt stem) (some 2) fun point _ => do
      unless point.size == 2 do
        throwError "raw source bridge: original physical point/source tail changed"
      let prefixed := mkAppN stem point
      let prefixEq ← bodyAt prefixed
      let groupedProof := app (grouped ++ `raw_annular_sum_eq_field) (d.params.push point[0]!)
      let groupedEq ← typeAt groupedProof
      unless prefixEq.isAppOfArity ``Eq 3 && groupedEq.isAppOfArity ``Eq 3 do
        throwError "raw source bridge: original prefix/grouped equality changed"
      let lhs := prefixEq.getAppArgs[1]!
      let some derivative := lhs.find? (·.isAppOf ``fderiv) |
        throwError "raw source bridge: missing actual raw angular derivative"
      let a := derivative.getAppArgs
      let prefixField := a[a.size-2]!
      unless prefixField.isAppOfArity (actual ++ `raw_angular) 54 do
        throwError "raw source bridge: prefix no longer uses the actual raw angular field"
      next {
        data := d
        point := point
        prefixed := prefixed
        prefixEq := prefixEq
        groupedProof := groupedProof
        groupedEq := groupedEq
        derivative := derivative
        prefixField := prefixField
        compactField := app (actual ++ `raw_angular) (d.actualArgs.push d.input) }

/-- Keep the exact original domains and substitute the final body once. -/
private def withStoredTelescope (key : Name) (count : Nat)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  unless count == 55 || count == 56 || count == 57 || count == 58 do
    throwError "raw source bridge: unexpected original telescope size"
  loop count (← getConstInfo key).type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain rest bi := type.consumeMData |
        throwError "raw source bridge: stored telescope ended at {p.size}"
      if bi == .instImplicit then
        withLocalDecl key bi (domain.instantiateRev p) fun x => loop k rest (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate key bi (domain.instantiateRev p) fun x =>
          loop k rest (p.push x)

private def save (name : Name) (p : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type, value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw source bridge: unresolved original source operand in {name}"
    let missing := e.getUsedConstants.filter fun key => (env.find? key).isNone
    unless missing.isEmpty do
      throwError "raw source bridge: missing original private metadata {missing.toList}"
  let (type, value) := Lean.ShareCommon.shareCommon (type, value)
  IO.println s!"Kernel checking SAME original source bridge {name}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .regular 0, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "Exact original source/prefix substitution for the SAME whole raw angular field, unweighted component adjoint, source, sample, inverse, phase and raw annular amplitude. No norm, corrected-G identity or analytic success premise is added. The final implication takes only the existing precise prefixed identity, supplied by the actual parent application (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "raw source bridge: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS SAME original source bridge {name}/{p.size}: {axioms}"

private def publishField (statement : Bool) : MetaM Unit :=
  withInputs fun c => do
    let α ← typeAt c.compactField
    if statement then
      let target := mkAppN (mkConst ``Eq [.one]) #[α, c.prefixField, c.data.angularField]
      save (root ++ `field_statement) c.data.params target (mkSort .zero) true
    else
      let proof := mkAppN (mkConst ``Eq.refl [.one]) #[α, c.compactField]
      save (root ++ `field_eq) c.data.params proof (app (root ++ `field_statement) c.data.params)

private def publishRhs (statement : Bool) : MetaM Unit :=
  withInputs fun c => do
    let p := c.data.params.push c.point[0]!
    let a := c.prefixEq.getAppArgs
    let b := c.groupedEq.getAppArgs
    if statement then
      let target := mkAppN (mkConst ``Eq c.prefixEq.getAppFn.constLevels!) #[a[0]!, a[2]!, b[1]!]
      save (root ++ `rhs_statement) p target (mkSort .zero) true
    else
      -- The compact original prefix sum is the actual side of this equality.
      let proof := mkAppN (mkConst ``Eq.refl c.prefixEq.getAppFn.constLevels!) #[a[0]!, a[2]!]
      save (root ++ `rhs_eq_grouped) p proof (app (root ++ `rhs_statement) p)

private def closeSource : MetaM Unit :=
  withInputs fun c => do
    let all := c.params
    withLocalDeclD `hPrefixed c.prefixed fun forward => do
      let a := c.prefixEq.getAppArgs
      let b := c.groupedEq.getAppArgs
      let fieldEq ← bodyAt (app (root ++ `field_statement) c.data.params)
      unless fieldEq.isAppOfArity ``Eq 3 do
        throwError "raw source bridge: actual field equality disappeared"
      let f := fieldEq.getAppArgs
      let context ← withLocalDeclD `rawField f[0]! fun v =>
        mkLambdaFVars #[v] (a[1]!.replace fun e => if e == c.prefixField then some v else none)
      let namedLeft := (context.beta #[f[2]!]).headBeta
      let changed := mkAppN (mkConst ``congrArg [.one, .one])
        #[f[0]!, a[0]!, f[1]!, f[2]!, context, app (root ++ `field_eq) c.data.params]
      let reverse := mkAppN (mkConst ``Eq.symm c.prefixEq.getAppFn.constLevels!)
        #[a[0]!, a[1]!, namedLeft, changed]
      let trans := mkConst ``Eq.trans c.prefixEq.getAppFn.constLevels!
      let groupedStep := mkAppN trans
        #[a[0]!, a[2]!, b[1]!, b[2]!, app (root ++ `rhs_eq_grouped)
          (c.data.params.push c.point[0]!), c.groupedProof]
      let prefixStep := mkAppN trans #[a[0]!, a[1]!, a[2]!, b[2]!, forward, groupedStep]
      let proof := mkAppN trans #[a[0]!, namedLeft, a[1]!, b[2]!, reverse, prefixStep]
      save (factor ++ `observed_raw_angular_of_prefixed) (all.push forward) proof
        (app (factor ++ `observed_raw_angular_statement) all)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
end
