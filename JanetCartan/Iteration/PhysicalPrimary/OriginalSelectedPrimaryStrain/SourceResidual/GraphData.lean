module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledChains
public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalPairs.OriginalTailPrice
public meta import Lean

/-!
# Exact original graph coordinates for the primary source remainder

Read the graph already used by `OriginalSampledChains`. Source labels may
repeat a history and carry a source, sample, target and quadrature. The
original regular inverse and coefficient tuple are recovered literally;
no new analytic field or history is selected (`main:eq:primary-strain`,
`app:ch_regular:eq:inverse-remainder`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template

open Lean Meta Elab Command

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual
def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
def operators := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
def polynomial := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
def observed := `JanetCartan.PhysicalInitialization.OriginalSampledChains.observed_residual_powers
def native := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native
def app (key : Name) (args : Array Expr) : Expr := mkAppN (mkConst key) args
def down (h : Expr) : Nat → Expr | 0 => h | k+1 => down (.proj ``And 1 h) k
def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (down h k)

/-- The already checked source-family prefix, graph34, native32, coefficient33
and actual graph type. The callback may bind its own source labels. -/
def withGraph
    (go : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo observed).type (some 38) fun p _ => do
    unless p.size == 38 do throwError "primary source graph: original source prefix changed"
    let graph := (← inferType p[37]!).bindingBody!
    unless graph.isAppOfArity (polynomial ++ `GraphFamily) 34 do
      throwError "primary source graph: source labels do not map to the SAME original graph"
    let g := graph.getAppArgs
    let fixed := g[:23].toArray
    let weak := fixed ++ #[g[25]!,app (regular ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let reserve := app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[g[0]!]
    let coeff := weak[:28].toArray ++ #[reserve,weak[28]!,weak[29]!,
      app (polynomial ++ `coefficient_reserve) #[g[0]!,weak[27]!,weak[30]!],weak[31]!]
    let raw := ((← getConstInfo (polynomial ++ `GraphFamily)).value! (allowOpaque := true)).beta g
    unless raw.isAppOfArity (polynomial ++ `Histories) 5 &&
        raw.getAppArgs[4]! == app (operators ++ `S) coeff do
      throwError "primary source graph: original coefficient reserve/threshold changed"
    go p[:36].toArray g weak coeff graph

/-- Recover the SAME admitted current38, true coefficient scale and carrier
at one original graph index. The output proof retains both initial thresholds. -/
def currentAt (g weak coeff : Array Expr) (i : Expr) :
    MetaM (Array Expr × Expr × Expr × Expr × Expr) := do
  let rawGraph := ((← getConstInfo (polynomial ++ `GraphFamily)).value! (allowOpaque := true)).beta g
  let data := app (polynomial ++ `admitted_data)
    (rawGraph.getAppArgs ++ #[app (operators ++ `fact0) coeff,i])
  let raw ← mkAppM ``Subtype.val #[i]
  let field (key : Name) := app (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ key)
    #[g[0]!,mkConst ``Unit,raw]
  let reached := app (regular ++ `Graph.regular_reached) (g ++ #[field `R₀,part data 0])
  let current := weak ++ #[field `R₀,reached,field `length,field `u,field `ell,part data 2]
  let L := app `JanetCartan.currentCoefficientScale #[field `R₀,field `length]
  let htwo ← mkAppM ``le_trans #[app (operators ++ `fact0) coeff,part data 1]
  let hL ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
    #[htwo,field `length]
  let admitted ← mkAppM ``Subtype.property #[i]
  let hgap ← mkAppM ``le_trans #[down data 5,part admitted 4]
  let window ← mkAppM ``And.intro #[hL,← mkAppM ``And.intro #[part admitted 2,hgap]]
  return (current,L,field `lam,data,window)

/-- Store only a closed kernel term, with exact early/later binder ordering. -/
def save (key : Name) (p : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "primary source residual: open or incomplete original-data term {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original primary source residual {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original admitted graph, full Q/B, measured residual, native inverse and literal adjoint supply this primary-source remainder input. Constants precede the queried histories/source labels; no source recut or new analytic success hypothesis (main:eq:primary-strain; app:ch_regular:eq:inverse-remainder)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "primary source residual: nonstandard axioms {ax}"
  logInfo m!"Original primary source residual {key}/{p.size}: {ax}"
  return app name p

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
end
