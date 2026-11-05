module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticRealization
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowActualBridge
public meta import Lean

/-!
# The single before-history quadratic dictionary

The low Picard constant and high quadratic source profile use these SAME
original geometric cutoffs and costs. The measured cost comes from the actual
measured row; the direction cost comes from the actual moment chart. Their
pointwise sum precedes R, all histories, samples, shifts and prefixes. The
full coordinate assembler reuses `staticFieldsAt` instead of rebuilding a
second geometry or sampling factory (`app:ch_mean_pairs:eq:block-bilinear`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual

/-- One common cost for the unchanged measured amplitude and trade direction.
It is a sum of two fixed original profiles, not a sum over samples or shells. -/
def joinedAdjointBudget (a d : ℕ → ℝ) (j : ℕ) : ℝ := a j + d j

theorem joinedAdjointBudget_nonneg (a d : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hd : ∀ j, 0 ≤ d j) : ∀ j, 0 ≤ joinedAdjointBudget a d j :=
  fun j => add_nonneg (ha j) (hd j)

theorem measured_le_joinedAdjointBudget (a d : ℕ → ℝ)
    (hd : ∀ j, 0 ≤ d j) : ∀ j, a j ≤ joinedAdjointBudget a d j :=
  fun j => le_add_of_nonneg_right (hd j)

theorem direction_le_joinedAdjointBudget (a d : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) : ∀ j, d j ≤ joinedAdjointBudget a d j :=
  fun j => le_add_of_nonneg_left (ha j)

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles
private def actual := root ++ `Actual
private def row := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def app (n : Name) (p : Array Expr) := mkAppN (mkConst n) p

private def save (name : Name) (p : Array Expr) (term : Expr) (data : Bool)
    (target : Option Expr := none) : MetaM Unit := do
  let t ← match target with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars p t)
  let value ← instantiateMVars (← mkLambdaFVars p term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "static quadratic: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then
      throwError "static quadratic: open declaration {name}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := actual ++ name
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "Before-history cost of the SAME original measured amplitude and trade direction; no sample cardinality, prefix or current data (app:ch_mean_pairs:eq:block-bilinear)."
  logInfo m!"checked original static quadratic {name}/{p.size}"

/-- Freeze one of the four exact static adjoint-cost fields. -/
elab "construct_actual_quadratic_adjoint_budget " mode:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitudeBudgetTotal)).type (some 44) fun p _ => do
    let a := app (row ++ `measuredAmplitudeBudget) p
    let d := app (actual ++ `directionBudgetTotal) p
    let ha := app (row ++ `measuredAmplitudeBudget_nonneg) p
    let hd := app (actual ++ `directionBudgetTotal.nonneg) p
    let joined := app (actual ++ `joinedAdjointBudget) #[a,d]
    if mode.getNat == 0 then
      save `adjointBudget p joined true
      return
    let (name,term) ← match mode.getNat with
      | 1 => pure (`adjointBudget_nonneg,app (actual ++ `joinedAdjointBudget_nonneg) #[a,d,ha,hd])
      | 2 => pure (`measuredBudget_le_adjointBudget,app (actual ++ `measured_le_joinedAdjointBudget) #[a,d,hd])
      | 3 => pure (`directionBudget_le_adjointBudget,app (actual ++ `direction_le_joinedAdjointBudget) #[a,d,ha])
      | _ => throwError "static quadratic: unknown adjoint cost field"
    let target := (← inferType term).replace fun e =>
      if e == joined then some (app (actual ++ `adjointBudget) p) else none
    save name p term false (some target)

/-- The one reusable static part of the shared actual dictionary. The full
coordinate assembler and both numerical publishers call this SAME function.
All inputs are the original before-history44, with no numeric moment guard. -/
def staticFieldsAt (p : Array Expr) : MetaM (Array (Name × Expr)) := do
  unless p.size == 44 do throwError "static quadratic: expected the original prehistory44"
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let N := app `JanetCartan.embeddingDimension #[n]
  let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
  let geo (k : Name) := app (root ++ `Geometry ++ k) sampler
  let measured := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
  let event := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
  return #[(`n,n),(`N,N),(`Rbox,geo `Rbox),(`hRbox,geo `Rbox_lt_half),
    (`χ,geo `χ),(`hχ,geo `χ_smooth),(`hχs,geo `χ_compact),(`hχcell,geo `χ_cell),
    (`K,geo `K),(`hK,geo `K_compact),(`hχK,geo `χ_one_on_K),(`hbox,geo `K_box),
    (`aC,app (measured ++ `CM) p),(`haC,app (measured ++ `CM_nonneg) p),
    (`aG,app (actual ++ `forwardAmplitudeBudgetTotal) p),
    (`haG,app (actual ++ `forwardAmplitudeBudgetTotal_nonneg) p),
    (`p,app (actual ++ `phaseBudgetTotal) p),(`hp,app (actual ++ `phaseBudgetTotal.nonneg) p),
    (`directionBudget,app (actual ++ `directionBudgetTotal) p),
    (`directionBudget_nonneg,app (actual ++ `directionBudgetTotal.nonneg) p),
    (`measuredAmplitudeBudget,app (row ++ `measuredAmplitudeBudget) p),
    (`measuredAmplitudeBudget_nonneg,app (row ++ `measuredAmplitudeBudget_nonneg) p),
    (`Badj,app (actual ++ `adjointBudget) p),(`hBadj,app (actual ++ `adjointBudget_nonneg) p),
    (`measuredBudget_le_Badj,app (actual ++ `measuredBudget_le_adjointBudget) p),
    (`directionBudget_le_Badj,app (actual ++ `directionBudget_le_adjointBudget) p),
    (`Cbare,app (event ++ `Cbare) p),(`Ctest,app (event ++ `Ctest) p),
    (`hCtest,app (actual ++ `testBudget_nonneg) p)]

/-- Expose exactly the static subset of the SAME actual primitive dictionary,
so fixed low/high numerical constants need not wait for dynamic hG. -/
def withActualQuadraticStaticPrimitives
    (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (actual ++ `forwardAmplitudeBudgetTotal)).type (some 44) fun p _ => do
    next p (← staticFieldsAt p)

end JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
end

construct_actual_quadratic_adjoint_budget 0
construct_actual_quadratic_adjoint_budget 1
construct_actual_quadratic_adjoint_budget 2
construct_actual_quadratic_adjoint_budget 3
