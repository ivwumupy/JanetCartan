module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! The exact original23 χ₃ envelope, fixed core and original doubled source
cells, without any additional choice (`app:ch_response:eq:response-graded-source`). -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSourceMasksTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def src := `JanetCartan.PhysicalInitialization.OriginalRegular
private def coreNS := `JanetCartan.RevisedUniform.OriginalCore
private def ns := `JanetCartan.PhysicalPrimary.OriginalSourceMasks

private def tail (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => tail (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (tail h k)

/-- All masks and full-cell product domains are fixed on the original23
prefix. Patch/cell specialization adds only the actual original indices. -/
elab "retain_actual_original_source_masks" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (src ++ `χ₃)).type (some 23) fun xs _ => do
    unless xs.size == 23 do throwError "original source masks: expected original23"
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let hn := xs[1]!
    let original := #[n] ++ xs[1:21].toArray
    let orig (q : Name) := mkAppN (mkConst (src ++ q)) xs
    let f := orig `f
    let fargs := (← inferType f).getAppArgs
    let physicalRadius := Expr.proj `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily 6 f
    let r := orig `r
    let radius ← mkAppM ``min #[r, physicalRadius]
    let eucl := mkApp (mkConst `JanetCartan.Euclidean) n
    let zero ← mkAppOptM ``OfNat.ofNat #[eucl, mkNatLit 0, none]
    let chart ← store (ns ++ `chart) xs (← mkAppM `Metric.ball #[zero, radius]) true
    discard <| store (ns ++ `chart_open) xs
      (mkAppN (mkConst (ns ++ `original_chart_open)) #[n,radius])
    let core := mkAppN (mkConst (coreNS ++ `D)) xs
    let bumps := orig `afterChoice_χ₃
    discard <| store (ns ++ `χ₂_support_chart) xs (part bumps 0)
    let h₃ ← store (ns ++ `χ₃_support_chart) xs (part bumps 1)
    discard <| store (ns ++ `χ₃_on_χ₂) xs (part bumps 2)
    discard <| store (ns ++ `source_product) xs (orig `χsrc_mul_χ₂)
    let germs := mkAppN (mkConst (coreNS ++ `original_cutoffs)) xs
    let germ ← forallBoundedTelescope (← inferType germs) (some 2) fun y _ => do
      mkLambdaFVars y (part (mkAppN germs y) 1)
    let germ ← store (ns ++ `χ₃_germ_on_D) xs germ
    let args := #[n,core,chart,orig `χ₃,h₃,germ]
    let env ← store (ns ++ `χenv) xs (mkAppN (mkConst (ns ++ `bumpOutputCutoff)) args) true
    discard <| store (ns ++ `χenv_toFun) xs (mkAppN (mkConst (ns ++ `bumpOutputCutoff_toFun)) args)
    for (bump, smooth, compact) in [(`χ₂,`χ₂_smooth,`χ₂_compact), (`χ₃,`χ₃_smooth,`χ₃_compact)] do
      let h := mkAppN (mkConst (ns ++ `bump_properties)) #[n,orig bump]
      discard <| store (ns ++ smooth) xs (.proj ``And 0 h)
      discard <| store (ns ++ compact) xs (.proj ``And 1 h)
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,original[20]!]
    let native (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ q)) (original.set! 20 capped)
    let μ := native `rMeasure
    let hμ := native `hrMeasure
    discard <| store (ns ++ `χsrc_smooth) xs (mkAppN (mkConst (ns ++ `measured_source_smooth)) #[n,μ,hμ])
    let protect (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalInitialization.OriginalProtected ++ q)) original
    let geometry := mkAppN (mkConst (ns ++ `chart_geometry))
      #[xs[0]!,hn,protect `r,μ,protect `fact2,hμ,fargs[5]!,fargs[6]!,f,r]
    let geometry ← store (ns ++ `geometry) xs geometry
    let chartBall ← store (ns ++ `chart_in_coefficient_ball) xs (.proj ``And 0 geometry)
    let b := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b) #[n,hn]
    discard <| store (ns ++ `χenv_support_coefficient_ball) xs
      (mkAppN (mkConst (ns ++ `output_support_in_coefficient_ball)) #[n,core,chart,env,b,chartBall])
    let cells := .proj ``And 1 geometry
    forallBoundedTelescope (← inferType cells) (some 2) fun indexes _ => do
      let args := #[n,hn,indexes[0]!,indexes[1]!]
      let params := xs ++ indexes
      discard <| store (ns ++ `V) params (mkAppN (mkConst (ns ++ `parameterWindow)) args) true
      let h := mkAppN (mkConst (ns ++ `parameterWindow_spec)) args
      for (label,k) in [(`V_open,0),(`V_subset_wholeWindow,1),(`V_closure_compact,2),(`V_closure_Csrc,3)] do
        discard <| store (ns ++ label) params (part h k)
      discard <| store (ns ++ `V_contains_original_closed_cell) params (tail h 4)
      let h := mkAppN cells indexes
      discard <| store (ns ++ `chart_in_cell) params (.proj ``And 0 h)
      discard <| store (ns ++ `product_in_comparison_cell) params (.proj ``And 1 h)
  logInfo "actual original23 chiEnv is LITERALLY chi3 on the SAME original52 D; full original doubled-cell product geometry, smooth real source masks and no additional selection"

end JanetCartan.PhysicalPrimary.OriginalSourceMasksTemplate
end
