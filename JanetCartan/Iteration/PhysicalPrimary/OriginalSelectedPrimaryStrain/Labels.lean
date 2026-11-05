module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# One original-data label family for both primary source quadratures

The source-localization constants in `main:eq:primary-strain` must precede
every history, target and sample. The label type below retains all of those
original data together with the real/imaginary choice, after fixing only the
original selected static tuple and finite Picard count. Its fields contain no
analytic estimate or successful-construction assumption: the sole additional
proof is the existing numerical auxiliary reach.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.LabelsTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def save (key : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original primary source labels: later field escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original primary source labels {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
    (forceExpose := true)
  addDocStringCore name "The original complete-source primary label retains its actual history, target, sample and real/imaginary choice after selected33+N. It assumes no source, profile, inverse or localization success; the original numerical auxiliary reach is explicit (main:eq:primary-strain; app:ch_regular:lem:finite-chain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original primary source labels: nonstandard axioms {ax}"
  logInfo m!"PASS original primary source labels {key}/{p.size}: {ax}"

private def withShape
    (next : RawProfilesTemplate.Data → Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  RawProfilesTemplate.withData fun d =>
    withLocalDeclD `imaginary (mkConst ``Bool) fun imaginary => do
      let fields := d.selected[33:].toArray ++ #[d.hAux,d.sample,imaginary]
      unless fields.size == 22 do throwError "original primary source labels: late-data shape changed"
      let mut type := mkConst ``Unit
      let mut value := mkConst ``Unit.unit
      for f in fields.reverse do
        let family ← mkLambdaFVars #[f] type
        let A ← inferType f
        value ← mkAppOptM ``PSigma.mk #[A,family,f,value]
        type ← mkAppM ``PSigma #[family]
      next d imaginary fields type value

run_meta do
  withShape fun d _ _ type _ => save `Labels d.fixed type (mkSort .one)

run_meta do
  withShape fun d imaginary _ _ value =>
    save `label (d.profileArgs.push imaginary) value (app (root ++ `Labels) d.fixed)

/-- A downstream producer receives every original operand on the same label;
this is data projection, not a retraction or a choice of a new history. -/
def withLabels
    (next : Array Expr → Expr → Expr → RawProfilesTemplate.Data → Expr → MetaM Unit) : MetaM Unit :=
  withShape fun d _ fields _ _ => do
    let labels := app (root ++ `Labels) d.fixed
    withLocalDeclD `sourceLabel labels fun t => do
      let mut values := #[]
      let mut rest := t
      for _ in fields do
        values := values.push (Expr.proj ``PSigma 0 rest)
        rest := Expr.proj ``PSigma 1 rest
      let replace (e : Expr) : MetaM Expr := do
        return (← mkLambdaFVars fields e).beta values
      let native ← d.native.mapM replace
      let selected ← d.selected.mapM replace
      let actual : RawProfilesTemplate.Data := {
        native := native
        selected := selected
        hAux := ← replace d.hAux
        steps := d.steps
        sample := ← replace d.sample
        sourceArgs := ← d.sourceArgs.mapM replace
        baselineArgs := ← d.baselineArgs.mapM replace
        baseline := ← replace d.baseline
        source := ← replace d.source
        hBaseline := ← replace d.hBaseline }
      next d.fixed labels t actual values.back!

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.LabelsTemplate
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Labels
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.label
