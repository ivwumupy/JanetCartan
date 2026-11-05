module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Same-original native-core physical smoothing, with the one target interval
and support selected before finite order/history (`main:lem:smoothing`). -/

public meta section
set_option warningAsError true
namespace JanetCartan.RevisedUniform.OriginalSmoothingTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.RevisedUniform.OriginalSmoothing
private def src := `JanetCartan.PhysicalInitialization.OriginalRegular
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def coreNS := `JanetCartan.RevisedUniform.OriginalCore

private def tail (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => tail (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (tail h k)

private def chooseNamed (base : Name) (label : Name) (params : Array Expr) (h : Expr) : MetaM (Expr × Expr) := do
  let t ← whnf (← inferType h)
  unless t.isAppOfArity ``Exists 2 do throwError "original smoothing: expected existential {label}"
  let v ← store (base ++ label) params (← mkAppM ``Classical.choose #[h]) true
  let rest ← store (base ++ Name.mkSimple s!"afterChoice_{label}") params
    (← mkAppM ``Classical.choose_spec #[h]) false (some (t.appArg!.beta #[v]))
  return (v,rest)

/-- The smoothing domain is a literal constructor on the same original χ₂;
its chart is not a replacement domain for the flat reference. -/
elab "construct_actual_original_smoothing_domain" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (src ++ `χ₂)).type (some 23) fun xs _ => do
    unless xs.size == 23 do throwError "original smoothing domain: expected original23"
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let hn := xs[1]!
    let original := #[n] ++ xs[1:21].toArray
    let χ := mkAppN (mkConst (src ++ `χ₂)) xs
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) original[:18].toArray
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) original[:18].toArray
    let boundary (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ q)) #[n,hn]
    let hR ← mkAppM (src ++ `radius_lt_same_chart) #[same,boundary `R_lt_chartRadius]
    let hbchart ← mkAppM `lt_trans #[boundary `b_lt_R,hR]
    let hhalf := Expr.proj `JanetCartan.LocalDomain 4 (.proj `JanetCartan.FlatReference 0 H)
    let hbhalf ← store (ns ++ `b_lt_half) xs (← mkAppM `lt_trans #[hbchart,hhalf])
    let masksField (q : Name) := mkAppN (mkConst (masks ++ q)) xs
    let hsupport ← store (ns ++ `χ₂_support_coefficient_ball) xs (← mkAppM `Set.Subset.trans
      #[masksField `χ₂_support_chart,masksField `chart_in_coefficient_ball])
    let args := #[xs[0]!,χ,boundary `b,hbhalf,hsupport]
    let D ← store (ns ++ `Dsmooth) xs (mkAppN (mkConst (ns ++ `bumpSmoothingDomain)) args) true
    let hs := mkAppN (mkConst (ns ++ `bumpSmoothingDomain_spec)) args
    let actualCore := mkAppN (mkConst (coreNS ++ `D)) xs
    let coreSet := mkAppN (mkConst `JanetCartan.LocalDomain.core) #[D,n]
    discard <| store (ns ++ `core_eq) xs (part hs 0) false (some (← mkEq coreSet actualCore))
    let chartSet := mkAppN (mkConst `JanetCartan.LocalDomain.chart) #[D,n]
    let chart := (← inferType (part hs 1)).appArg!
    discard <| store (ns ++ `chart_eq) xs (part hs 1) false (some (← mkEq chartSet chart))
    discard <| store (ns ++ `chart_plateau) xs (tail hs 2)
  logInfo "actual original23 smoothing domain: exact52 D and native chi2 PDE chart, unchanged reference domain and no new radius choice"

/-- Apply the already proved physical finite-moment producer to the same
original source scale/reference and normalized target, without choosing a new
normalizing matrix. The support and target interval precede accuracy/history. -/
elab "apply_physical_smoothing_to_original_core" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (src ++ `Gref)).type (some 25) fun xs _ => do
    unless xs.size == 25 do throwError "original smoothing: expected original25 reference prefix"
    let fixed := xs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let G := mkAppN (mkConst (src ++ `Gref)) xs
    let D := mkAppN (mkConst (ns ++ `Dsmooth)) fixed
    let coreSet := mkAppN (mkConst `JanetCartan.LocalDomain.core) #[D,n]
    let actualCore := mkAppN (mkConst (coreNS ++ `D)) fixed
    let chartSet := mkAppN (mkConst `JanetCartan.LocalDomain.chart) #[D,n]
    let solverBall := (← inferType (mkAppN (mkConst (ns ++ `chart_eq)) fixed)).appArg!
    let raw := mkAppN (mkConst `JanetCartan.PhysicalSmoothing.exists_original_target_history_smoothing)
      #[n,D,G,xs[23]!, .proj ``And 0 xs[24]!]
    let t := (← inferType raw).replace fun e ↦
      if e == coreSet then some actualCore else if e == chartSet then some solverBall else none
    let raw ← store (ns ++ `source_interval) xs raw false (some t)
    forallBoundedTelescope (← inferType raw) (some 10) fun target _ => do
      unless target.size == 10 do throwError "original smoothing: expected normalized target6 and numerical4"
      let params := xs ++ target
      let h ← store (ns ++ `on_target) params (mkAppN raw target)
      let (_,hs) ← chooseNamed ns `s₀ params h
      discard <| store (ns ++ `s₀_pos) params (part hs 0)
      discard <| store (ns ++ `s₀_le_one) params (part hs 1)
      discard <| store (ns ++ `target_maps) params (part hs 2)
      let (_,hk) ← chooseNamed ns `K params (tail hs 3)
      discard <| store (ns ++ `support_compact) params (part hk 0)
      discard <| store (ns ++ `support_solver_ball) params (part hk 1)
      let orders ← store (ns ++ `orders) params (tail hk 2)
      forallBoundedTelescope (← inferType orders) (some 2) fun m _ => do
        let all := params ++ m
        let atOrder ← store (ns ++ `at_order) all (mkAppN orders m)
        select (ns ++ `Accuracy) all atOrder
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let Gmap ← mkAppM `JanetCartan.FlatReference.map #[G]
    withLocalDeclD `j (mkConst ``Nat) fun j => do
      let norm := mkAppN (mkConst `JanetCartan.PhysicalSmoothing.normalizedSource_eq) #[n,N,j,D]
      forallBoundedTelescope (← inferType norm) (some 4) fun data _ => do
        discard <| store (ns ++ `normalization) (xs ++ #[j] ++ data) (mkAppN norm (data ++ #[Gmap]))
  logInfo "actual original25/target6/numerical4 smoothing: one cap and support BEFORE m/history, all native low/high tails and revised source profiles on actual52 D, same normalizedSource/Gref without target reselection"

end JanetCartan.RevisedUniform.OriginalSmoothingTemplate
end
