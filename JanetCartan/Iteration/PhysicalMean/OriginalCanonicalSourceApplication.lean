module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampled
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurement
public meta import Lean

/-!
# Actual fixed-source operators on the original sample and global Q0

The quadratic operator uses exactly93's A52/weights51, the actual full G prefix,
the unchanged common Cper, and the global native39 Q0 extracted from the same
positive scalar. No baseline, successful iteration or quadratic bound is
assumed (`new:sec:mean-source-equation`, `app:ch_mean_pairs:eq:single-iteration`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalSourceApplication
open Lean Meta Elab Command
open OriginalCanonicalSampledApplication OriginalCanonicalCurrentApplication

private def save (short : Name) (xs : Array Expr) (term : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual fixed source: missing producer constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual fixed source: extra/unresolved input in {short}"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource ++ short
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  addDocStringCore name "The actual fixed operator on the SAME original native50 history, original shift, fixed prefix, A/G/weights/common measurement and global admission39 Q0. No successful source or new inverse is selected (new:sec:mean-source-equation)."
  logInfo m!"actual fixed-source {short}: native{xs.size}, SAME global inverse and original sample"

/-- Read the one actual quadratic packing. The callback receives native52
(native50, original shift, fixed prefix), J, global native39,
`#[μ,C,hC,A,G,Q0]`, and the exact constructed bilinear operator. -/
def withActualQuadratic
    (next : Array Expr → Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  withActualSample fun xs ξ _ J originalFintype => do
    withCurrentAt xs fun native39 => do
      withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
        let shifted := xs.push ξ
        let params := shifted.push L
        let row := `JanetCartan.PhysicalMean.OriginalCanonicalRow
        let actualG := `JanetCartan.PhysicalMean.OriginalCanonicalSampled.Gprefix
        let measured := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
        let μ := mkAppN (mkConst (row ++ `weights)) shifted
        let A := mkAppN (mkConst (row ++ `A)) params
        let G := mkAppN (mkConst actualG) params
        let C := mkAppN (mkConst (measured ++ `Cper)) xs
        let hC := mkAppN (mkConst (measured ++ `Cper_smooth)) xs
        let Q0 := mkAppN (mkConst
          `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0) native39
        let value ← withLetDecl `originalFintype (← inferType originalFintype) originalFintype fun fi => do
          let result ← withLocalInstances [← fi.fvarId!.getDecl] <|
            mkAppM `JanetCartan.PhysicalMean.fixedSourceQuadratic #[μ,C,hC,A,G,Q0]
          return (← instantiateMVars result).replaceFVar fi originalFintype
        next params J native39 #[μ,C,hC,A,G,Q0] value

elab "construct_actual_canonical_source_quadratic" : command => liftTermElabM do
  withActualQuadratic fun params _ _ _ value => save `quadratic params value

end JanetCartan.PhysicalMean.OriginalCanonicalSourceApplication
end
