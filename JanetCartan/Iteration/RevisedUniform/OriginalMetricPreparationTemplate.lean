module
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistory
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingPreparation
public meta import Lean

/-!
# The original metric on the dimension-only physical prehistory

Use the very coordinate normalization and positive chart interval from the
original final-core target reduction, and the very physical interval from the
original target-history smoother (`main:prop:seed`, `main:thm:main`). Neither
is a new geometric choice. The two-tail stage reach is constructed before the
history, separately from the frozen initial threshold (`main:eq:metric-two-errors`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.RevisedUniform.OriginalMetricPreparation

/-- The original normalization supplies its own genuine metric domain, not
an assumed normalized metric (`main:prop:seed`). -/
theorem pullback_domain_inputs {n : ℕ} {g : MetricField n} {V : Set (Euclidean n)}
    (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V) (hg : IsRiemannianMetricOn g V)
    (A : MetricTensor n) (hA : IsUnit A) :
    IsOpen (coordinateMap A ⁻¹' V) ∧ (0 : Euclidean n) ∈ coordinateMap A ⁻¹' V ∧
      IsRiemannianMetricOn (coordinatePullback g A) (coordinateMap A ⁻¹' V) :=
  ⟨hV.preimage (coordinateMap A).continuous, by simpa only [mem_preimage, map_zero] using h0,
    isRiemannianMetricOn_coordinatePullback hg A hA⟩

/-- Intersect the existing physical and coordinate intervals. The original
source dilation and reference/core are unchanged (`main:prop:seed`). -/
def preparationCap (a b : ℝ) : ℝ := min a b

theorem preparationCap_spec {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < preparationCap a b ∧ preparationCap a b ≤ a ∧ preparationCap a b ≤ b :=
  ⟨lt_min ha hb,min_le_left _ _,min_le_right _ _⟩

/-- Use the common cap inside the SAME physical smoothing interval
(`main:lem:smoothing`), rather than constructing another smoother. -/
theorem extend_preparation_interval {s a b : ℝ} (hab : a ≤ b)
    (hs : s ∈ Icc 0 a) : s ∈ Icc 0 b := ⟨hs.1,hs.2.trans hab⟩
end JanetCartan.RevisedUniform.OriginalMetricPreparation
end

public meta section
namespace JanetCartan.RevisedUniform.OriginalMetricPreparationTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate (bodyAt)
open JanetCartan.RevisedUniform.OriginalSelectedPrehistoryTemplate (withDimensionHistory)
private def ns := `JanetCartan.RevisedUniform.OriginalMetricPreparation
private def selected := `JanetCartan.RevisedUniform.OriginalSelectedPrehistory
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def fc := `JanetCartan.RevisedUniform.OriginalFinalCore
private def app (c : Name) (as : Array Expr) := mkAppN (mkConst c) as
private def tel (type : Expr) (count : Nat) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,t,p => go p t
    | k+1,t,p => do
      let .forallE n dom b bi := t.consumeMData | throwError "dimension-only metric: missing original target binder"
      if bi.isInstImplicit then withLocalDecl n bi dom fun x => loop k (b.instantiate1 x) (p.push x)
      else withLocalDeclNoLocalInstanceUpdate n bi dom fun x => loop k (b.instantiate1 x) (p.push x)
private def tailProof (e : Expr) : Nat → Expr
  | 0 => e
  | k+1 => Expr.proj ``And 1 (tailProof e k)
private def tailType (e : Expr) : Nat → Expr
  | 0 => e
  | k+1 => (tailType e k).getAppArgs[1]!
private def part (e : Expr) (i : Nat) := Expr.proj ``And 0 (tailProof e i)
private def compType (e : Expr) (i : Nat) := (tailType e i).getAppArgs[0]!
private def witness (h t : Expr) := mkAppN (mkConst ``Classical.choose t.getAppFn.constLevels!) (t.getAppArgs.push h)
private def spec (h t : Expr) := mkAppN (mkConst ``Classical.choose_spec t.getAppFn.constLevels!) (t.getAppArgs.push h)
private def predAt (t a : Expr) := (t.getAppArgs[1]!.beta #[a]).headBeta
private partial def dropLets (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .letE _ _ v b _ => dropLets (b.instantiate1 v)
  | z => z
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "dimension-only metric {key}: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "dimension-only metric {key}: a free menu, history or unsupported operand survives"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  if let some path ← IO.getEnv "JANET_DIMENSION_METRIC_TRACE" then
    IO.FS.withFile path .append fun h => h.putStrLn s!"dimension-only original metric: kernel checking {key}/{p.size}"
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The same original metric coordinates, core/reference, source dilation and physical target interval, now with only dimension and the original metric as static inputs (main:prop:seed; main:eq:metric-two-errors). The actual uniform physical correction is not asserted."
  logInfo m!"dimension-only original metric: checked {key}/{p.size}"

/-- Static original target data. The physical namespace contains the genuine
measurement profile and interval; the dimension prefix has no free menu. -/
structure Input where
  native : Array Expr
  dimension : Array Expr
  metric : Array Expr
  a : Array Expr
  reg : Array Expr
  reduction : Expr
  result : Expr

def Input.fixed (d : Input) := d.dimension ++ d.metric
private def Input.coord (d : Input) := app (ns ++ `metricCoordinates) d.fixed
private def Input.rest (d : Input) := predAt d.result d.coord
private def Input.chartEx (d : Input) := tailType d.rest 2
private def Input.chartProof (d : Input) := tailProof (spec d.reduction d.result) 2
private def Input.chart (d : Input) := app (ns ++ `metricChartDilation) d.fixed

/-- The ONLY fixed inputs are `(d,hn,g,V,hV,h0,hg)`. The temporary original
history is used to recover the genuine measurement/reference application;
every saved output is checked to close independently of that history. -/
def withDimensionMetric (next : Input → MetaM Unit) : MetaM Unit :=
  withDimensionHistory fun params native _ _ => do
    let dh := params[:2].toArray
    let target ← bodyAt (forcing ++ `measured_target) native
    unless target.isAppOfArity (forcing ++ `measure_normalized_history) 13 do
      throwError "dimension-only metric: lost original measured target"
    let a := target.getAppArgs
    let reg := a[2]!.getAppArgs
    unless reg.size == 25 && a[2]! == (← bodyAt (selected ++ `Gref) dh) &&
        a[1]! == (← bodyAt (selected ++ `Dsmoothing) dh) && reg[23]! == app (selected ++ `sigma) dh do
      throwError "dimension-only metric: changed107 original reference/domain/dilation"
    let cm ← mkLambdaFVars dh a[3]!
    if cm.hasFVar || cm.hasLooseBVars then
      throwError "dimension-only metric: measurement budget varies with the target or history"
    let start := app (selected ++ `target_reduction) dh
    tel (← inferType start) 5 fun metric result => do
      unless result.isAppOfArity ``Exists 2 do throwError "dimension-only metric: not the original arbitrary-metric problem"
      next {native,dimension:=dh,metric,a,reg,reduction:=mkAppN start metric,result}

private def Input.normalized (d : Input) : MetaM (Array Expr) := do
  let g := d.metric
  let h := app (ns ++ `metricCoordinates_spec) d.fixed
  let t := app (ns ++ `pullback_domain_inputs) (#[d.a[0]!] ++ g ++ #[d.coord,part h 0])
  let V := (compType (← inferType t) 0).getAppArgs.back!
  let gg := app `JanetCartan.coordinatePullback #[d.a[0]!,g[0]!,d.coord]
  return #[gg,V,part t 0,part t 1,tailProof t 2,tailProof h 1]
private def Input.phys (d : Input) : MetaM Expr := do
  return app (forcing ++ `targetDilation) (d.native[:44].toArray ++ (← d.normalized))
private def Input.physicalArgs (d : Input) : MetaM (Array Expr) := do
  let raw ← bodyAt (forcing ++ `targetDilation) (d.native[:44].toArray ++ (← d.normalized))
  let h := raw.getAppArgs[2]!
  unless h.isAppOfArity (fc ++ `source_interval) 35 && h.getAppArgs[:25].toArray == d.reg do
    throwError "dimension-only metric: lost the SAME original35 physical interval"
  return h.getAppArgs

elab "prepare_original_dimension_metric " which:num : command => liftTermElabM do
  withTransparency .reducible <| withDimensionMetric fun d => do
    match which.getNat with
    | 0 => save `metricCoordinates d.fixed (witness d.reduction d.result) d.result.getAppArgs[0]! true
    | 1 =>
      let a := compType d.rest 0
      let b := compType d.rest 1
      let h := spec d.reduction d.result
      save `metricCoordinates_spec d.fixed (app ``And.intro #[a,b,part h 0,part h 1]) (mkApp2 (mkConst ``And) a b)
      save `metricChartDilation d.fixed (witness d.chartProof d.chartEx) (mkConst ``Real) true
    | 2 =>
      let t := predAt d.chartEx d.chart
      let h := spec d.chartProof d.chartEx
      save `metricChartDilation_pos d.fixed (part h 0) (compType t 0)
      save `metricChartDilation_reduction d.fixed (tailProof h 4) (tailType t 4)
    | 3 =>
      let phys ← d.phys
      save `metricCap d.fixed (app (ns ++ `preparationCap) #[phys,d.chart]) (mkConst ``Real) true
    | 4 =>
      let ng ← d.normalized
      let phys ← d.phys
      let hphys := app (forcing ++ `targetDilation_spec) (d.native[:44].toArray ++ ng)
      let h := app (ns ++ `preparationCap_spec) #[phys,d.chart,part hphys 0,app (ns ++ `metricChartDilation_pos) d.fixed]
      let old := app (ns ++ `preparationCap) #[phys,d.chart]
      let cap := app (ns ++ `metricCap) d.fixed
      save `metricCap_spec d.fixed h ((← inferType h).replace fun e => if e == old then some cap else none)
    | 5 =>
      let p ← d.physicalArgs
      let cap := app (ns ++ `metricCap) d.fixed
      let h := app (ns ++ `metricCap_spec) d.fixed
      let reducer := app (ns ++ `metricChartDilation_reduction) d.fixed
      let initial := app (selected ++ `Tref) d.dimension
      let reducerAtInitial := mkAppN reducer #[cap,part h 0,tailProof h 2,p[33]!,p[31]!,initial]
      tel (← inferType reducerAtInitial) 2 fun CT _ => do
        let gap := app (selected ++ `kMin_cubic) #[d.dimension[0]!]
        let v := mkApp (mkAppN reducerAtInitial CT) gap
        let t ← inferType v
        unless (t.find? (·.isAppOf `JanetCartan.RevisedGlobal.UniformHistoryCorrection)).isSome &&
            (t.find? (· == d.coord)).isSome && (t.find? (· == initial)).isSome do
          throwError "dimension-only metric: lost original metric, fixed initial reach or actual UHC contract"
        save `local_metric_of_original_history_step d.fixed (← mkLambdaFVars CT v) (← mkForallFVars CT t)
    | 6 =>
      let p ← d.physicalArgs
      let ng ← d.normalized
      let phys ← d.phys
      let v0 := app (forcing ++ `exists_prescribed_smoothing_reach)
        (#[d.a[0]!,d.a[1]!,d.a[2]!,d.reg[23]!,part d.reg[24]! 0] ++ ng ++ p[31:35].toArray ++ #[d.a[3]!])
      tel (← inferType v0) 2 fun kr t => do
        let val := mkAppN v0 kr
        let t := dropLets t
        unless t.isAppOfArity ``Exists 2 do throwError "dimension-only metric: stage reach is not constructed"
        let some actual := t.find? (fun e => e.isAppOfArity ``Exists.choose 3 &&
          e.getAppArgs[2]!.isAppOf `JanetCartan.PhysicalSmoothing.exists_original_target_history_smoothing) |
          throwError "dimension-only metric: changed physical interval"
        let orig := app (selected ++ `D) d.dimension
        let geom := app `JanetCartan.LocalDomain.core #[d.a[1]!,d.a[0]!]
        let statement := t.replace fun e => if e == actual then some phys else if e == geom then some orig else none
        unless (statement.find? (· == orig)).isSome && (statement.find? (· == phys)).isSome do
          throwError "dimension-only metric: lost original107 core/dilation"
        save `original_smoothing_plan (d.fixed ++ kr) val statement
    | _ => throwError "dimension-only metric: unknown publication mode"
end JanetCartan.RevisedUniform.OriginalMetricPreparationTemplate
end
