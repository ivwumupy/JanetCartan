module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Retain the actual original defect core without choosing a new mask or
adding any post-contraction input (`main:thm:step`). -/

public meta section
namespace JanetCartan.RevisedUniform.OriginalCoreTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def src := `JanetCartan.PhysicalInitialization.OriginalRegular
private def dst := `JanetCartan.RevisedUniform.OriginalCore

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

/-- This is a definition from the already selected original23 bump. In
particular, no source scale, reference contraction, history or target occurs. -/
elab "retain_actual_original_defect_core" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (src ++ `χ₂)).type (some 23) fun xs _ => do
    unless xs.size == 23 do throwError "fixed original core: expected original23"
    let orig (q : Name) := mkAppN (mkConst (src ++ q)) xs
    let χ := orig `χ₂
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let h := mkAppN (mkConst (dst ++ `inverse_bump_core_spec)) #[n, χ]
    let t ← inferType h
    let r := t.appFn!.appArg!.appArg!
    let r ← store (dst ++ `radius) xs r true
    let eucl := mkApp (mkConst `JanetCartan.Euclidean) n
    let zero ← mkAppOptM ``OfNat.ofNat #[eucl, mkNatLit 0, none]
    let D ← mkAppM `Metric.closedBall #[zero, r]
    let D ← store (dst ++ `D) xs D true
    let t := t.replace fun e => if e.isAppOf `Metric.closedBall then some D else none
    let h ← store (dst ++ `spec) xs h false (some t)
    for (label, idx) in [(`radius_pos,0), (`isCompact,1), (`nonempty,2),
        (`zero_mem_interior,3), (`interior_nonempty,4), (`subset_solver_domain,5), (`plateau,6)] do
      discard <| store (dst ++ label) xs (part h idx)
    let hsupp := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 (.proj ``And 1
      (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 h))))))
    discard <| store (dst ++ `subset_bump_support) xs hsupp
    let nest := part (orig `afterChoice_χ₃) 2
    let χsrc := mkAppN (mkConst (src ++ `χsrc)) xs[:21].toArray
    let f := orig `f
    let input := Expr.proj `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily 8 f
    let masks := mkAppN (mkConst (dst ++ `inverse_bump_core_masks))
      #[n, χ, orig `χ₃, χsrc, input, nest, orig `χsrc_plateau, orig `source_input_plateau]
    discard <| store (dst ++ `original_cutoffs) xs masks
    let domains := mkAppN (mkConst (dst ++ `inverse_bump_core_source_geometry))
      #[n, xs[1]!, χ, χsrc, orig `χsrc_mul_χ₂, orig `source_cell_support]
    discard <| store (dst ++ `source_geometry) xs domains
  logInfo "actual compact original23 defect core: fixed inside the SAME native inverse PDE plateau, with original source and envelope cutoffs and every full original source domain"

end JanetCartan.RevisedUniform.OriginalCoreTemplate
end
