module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalGeometry
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrentSource
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.UniformProjected
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.ProjectedProtection
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.OriginalPatchSourceDomains
public meta import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.InitializedProofCache
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Protected sectors and full source cells on the actual original cover

The original response uses *independent* source label and spatial covector.
`Csrc` is the full union of the doubled original cells, not their diagonal or
an empty off-graph placeholder. `Xsrc` is one compact physical ball before any
source contraction, accuracy, or history. The signed protection is on the very
same incidence/patch groups as the strong measured inverse. Consumers: both
primary full-source envelopes and the signed correction on the original
terminal plateau (`app:ch_regular:thm:no-return`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 18000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalProtected
open PhysicalSeed OriginalBoundary ActualCarriers ActualCarriers.CurrentFullPhase

variable {n : ℕ}

/-- Every label AND independent initial covector in the doubled cell is part
of the fixed source set for this exact patch. -/
def Csrc (hn : 5 ≤ n) (a : OriginalPatchIndex hn) : Set (Euclidean 3 × Euclidean (n-1)) :=
  ⋃ j : OriginalBoundary.centers hn a, closedBall
    (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
    (2 * OriginalBoundary.σcover hn a j)

theorem Csrc_cell (hn : 5 ≤ n) (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a) :
    closedBall (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
      (2 * OriginalBoundary.σcover hn a j) ⊆ Csrc hn a :=
  subset_iUnion (fun j : OriginalBoundary.centers hn a ↦ closedBall
    (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
    (2 * OriginalBoundary.σcover hn a j)) j

/-- Original compact modulation domains obtained with the actual frozen cell
margin, before the regular solver or its source mask is picked. -/
theorem exists_source_radius (hn : 5 ≤ n) :
    ∃ r > (0 : ℝ), r < OriginalBoundary.b hn ∧
      closedBall (0 : Euclidean n) r ⊆ ball 0 (OriginalBoundary.b hn) ∧
      IsCompact (closedBall (0 : Euclidean n) r) ∧
      ∀ a : OriginalPatchIndex hn, IsCompact (Csrc hn a) ∧
        (∀ c ∈ Csrc hn a, c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (OriginalBoundary.T hn a))
          (OriginalBoundary.T hn a).family.radius) ∧
        closedBall (0 : Euclidean n) r ×ˢ Csrc hn a ⊆ LeadingWave.FullModulation.domain (OriginalBoundary.T hn a) ∧
        closedBall (0 : Euclidean n) r ⊆ ball 0 (OriginalBoundary.T hn a).physicalRadius :=
  CompatibleResponse.exists_original_patch_source_domains (OriginalBoundary.D hn) (OriginalBoundary.T hn)
    (OriginalBoundary.centers hn) (OriginalBoundary.σcover hn)
    (fun i j ↦ (OriginalBoundary.comparison_pos hn i j).2.2.2.2.2.2.2.2)
    (fun i j ↦ (OriginalBoundary.comparison_cover hn i j).2.2) (OriginalBoundary.b_pos hn)

/-- A single physical selector radius for all the independent full source cells. -/
def sourceRadius (hn : 5 ≤ n) : ℝ := (exists_source_radius hn).choose

def Xsrc (hn : 5 ≤ n) (_a : OriginalPatchIndex hn) : Set (Euclidean n) :=
  closedBall 0 (sourceRadius hn)

theorem sourceRadius_pos (hn : 5 ≤ n) : 0 < sourceRadius hn := (exists_source_radius hn).choose_spec.1

theorem sourceRadius_lt_b (hn : 5 ≤ n) : sourceRadius hn < OriginalBoundary.b hn :=
  (exists_source_radius hn).choose_spec.2.1

theorem source_domains (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    IsCompact (Xsrc hn a) ∧ IsCompact (Csrc hn a) ∧
    (∀ c ∈ Csrc hn a, c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (OriginalBoundary.T hn a))
      (OriginalBoundary.T hn a).family.radius) ∧
    Xsrc hn a ×ˢ Csrc hn a ⊆ LeadingWave.FullModulation.domain (OriginalBoundary.T hn a) ∧
    Xsrc hn a ⊆ ball 0 (OriginalBoundary.T hn a).physicalRadius :=
  ⟨(exists_source_radius hn).choose_spec.2.2.2.1, (exists_source_radius hn).choose_spec.2.2.2.2 a⟩

/-- Incidence × local patch: literally the index of the original measured
carrier, not a fresh Cartesian product of unrelated patches. -/
abbrev CellGroup (hn : 5 ≤ n) (cells : Finset (ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn))) :=
  (j : cells) × Fin ((OriginalBoundary.D hn).patchCount j.val.val.1)

def cellPatch (hn : 5 ≤ n) (cells : Finset (ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)))
    (g : CellGroup hn cells) : OriginalPatchIndex hn := ⟨g.1.val.val.1, g.2⟩

theorem extension_closedBall (hn : 5 ≤ n) (qext : BallExtension.Parameters (Euclidean n))
    (h0 : qext.center = 0) (hb : qext.radius = OriginalBoundary.b hn) :
    closedBall qext.center qext.radius ⊆ closedBall (0 : Euclidean n) (OriginalBoundary.b hn) := by
  rw [h0, hb]

theorem original_radius_lt_patch (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    OriginalBoundary.r hn < (OriginalBoundary.T hn a).physicalRadius := by
  have h := original_phase_radius_buffer hn a
  have hp := OriginalBoundary.r_pos hn
  linarith

/- The physical dimension is the actual embedding dimension; the extension is
on the original coefficient ball. No torus histories enter this construction. -/
proof_from protection_on_selected_centers {n : ℕ} (hn : 5 ≤ n)
    (cells : Finset (ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)))
    (qext : BallExtension.Parameters (Euclidean n)) (h0 : qext.center = 0)
    (hb : qext.radius = OriginalBoundary.b hn) :=
  ProtectedFlow.exists_projected_signed_uniform_protection (N := embeddingDimension n) hn
    (OriginalBoundary.hD hn) (OriginalBoundary.T hn) (CellGroup hn cells) (cellPatch hn cells)
    (isCompact_closedBall (0 : Euclidean n) (OriginalBoundary.b hn))
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)) (original_frameBall_subset hn)
    qext h0 (extension_closedBall hn qext h0 hb) (OriginalBoundary.r_pos hn) (original_radius_lt_patch hn)

/- The terminal finite-chain theorem needs a uniform lower and upper gradient
   bound and one derivative bound BEFORE the varying physical history. Retain
   these in the original choice, not from a second application after fixing f. -/
proof_from protection_on_selected_centers_with_graph_bounds {n : ℕ} (hn : 5 ≤ n)
    (cells : Finset (ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)))
    (qext : BallExtension.Parameters (Euclidean n)) (h0 : qext.center = 0)
    (hb : qext.radius = OriginalBoundary.b hn) :=
  ProtectedFlow.exists_projected_signed_uniform_protection_with_graph_bounds (N := embeddingDimension n) hn
    (OriginalBoundary.hD hn) (OriginalBoundary.T hn) (CellGroup hn cells) (cellPatch hn cells)
    (isCompact_closedBall (0 : Euclidean n) (OriginalBoundary.b hn))
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)) (original_frameBall_subset hn)
    qext h0 (extension_closedBall hn qext h0 hb) (OriginalBoundary.r_pos hn) (original_radius_lt_patch hn)

private theorem keep_chart {A : Type} {P Q R : A → Prop} (h : ∃ x, P x ∧ Q x ∧ R x) : ∃ x, R x :=
  h.imp fun _ hh => hh.2.2

end JanetCartan.PhysicalInitialization.OriginalProtected
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalProtected
open Lean Meta Elab Command OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalInitialization.OriginalProtected

/- Old fact ordinals are intentionally unchanged. Keep both the strong current
   graph witness and the weak API as a projection of THAT witness. -/
private partial def selectGraphs (params : Array Expr) (h : Expr) (index := 0) : MetaM Unit := do
  let t ← inferType h
  if let .letE name _ v body _ := t then
    let v ← store (ns ++ name) params v true
    let rest ← store (ns ++ Name.mkSimple s!"afterLet_{name}") params h false (some (body.instantiate1 v))
    selectGraphs params rest index
  else
    let t ← whnf t
    if t.isAppOfArity ``Exists 2 then
      let .lam name _ body _ := t.appArg! | throwError "missing original named graph witness"
      let v ← store (ns ++ name) params (← mkAppM ``Classical.choose #[h]) true
      let rest ← store (ns ++ Name.mkSimple s!"afterChoice_{name}") params (← mkAppM ``Classical.choose_spec #[h]) false (some (body.instantiate1 v))
      selectGraphs params rest index
    else if t.isAppOfArity ``And 2 then
      let i := if index < 25 then index else index-3
      let name := match index with
        | 25 => `cgraph_pos | 26 => `Cgraph_pos | 27 => `Lx_nonnegative
        | _ => Name.mkSimple s!"fact{i}"
      let restName := if 25 ≤ index && index < 28 then Name.mkSimple s!"after_{name}" else Name.mkSimple s!"afterFact{i}"
      discard <| store (ns ++ name) params (.proj ``And 0 h)
      let rest ← store (ns ++ restName) params (.proj ``And 1 h)
      selectGraphs params rest (index+1)
    else
      unless index == 33 do throwError "native graph packet: wanted existing thirty fields plus three bounds; got {index}"
      let quant ← store (ns ++ `quantitative_continuation) params h
      forallBoundedTelescope (← inferType quant) (some 1) fun fr _ => do
        let current := mkAppN quant fr
        let bounds := Expr.proj ``And 1 current
        let ex := Expr.proj ``And 1 bounds
        let et ← whnf (← inferType ex)
        unless et.isAppOfArity ``Exists 2 do throwError "missing native comparison charts"
        let pred := et.appArg!
        let α := et.getAppArgs[0]!
        let (p,q,r) ← withLocalDeclD `c α fun c => do
          let v ← whnf (pred.beta #[c])
          let bv := v.appArg!
          unless v.isAppOfArity ``And 2 && bv.isAppOfArity ``And 2 do throwError "missing native graph derivative and two-sided norm"
          pure (← mkLambdaFVars #[c] v.getAppArgs[0]!,← mkLambdaFVars #[c] bv.getAppArgs[0]!,← mkLambdaFVars #[c] bv.appArg!)
        let old := mkAppN (mkConst ``keep_chart) #[α,p,q,r,ex]
        let tail ← mkAppM ``And.intro #[.proj ``And 0 bounds,old]
        let weak ← mkAppM ``And.intro #[.proj ``And 0 current,tail]
        discard <| store (ns ++ `continuation) params (← mkLambdaFVars fr weak)

/- Reconstruct the old public existential from the named strong fields rather
   than making a second existential choice. -/
private partial def projectSelected (params : Array Expr) (type : Expr) (index := 0) : MetaM Expr := do
  if let .letE name _ _ body _ := type then
    return ← projectSelected params (body.instantiate1 (mkAppN (mkConst (ns ++ name)) params)) index
  let t ← whnf type
  if t.isAppOfArity ``Exists 2 then
    let .lam name _ body _ := t.appArg! | throwError "missing original choice label"
    let v := mkAppN (mkConst (ns ++ name)) params
    let rest ← projectSelected params (body.instantiate1 v) index
    return mkAppN (mkConst ``Exists.intro t.getAppFn.constLevels!) (t.getAppArgs ++ #[v,rest])
  if t.isAppOfArity ``And 2 then
    let f := mkAppN (mkConst (ns ++ Name.mkSimple s!"fact{index}")) params
    let rest ← projectSelected params t.appArg! (index+1)
    return mkAppN (mkConst ``And.intro) (t.getAppArgs ++ #[f,rest])
  unless index == 30 do throwError "original signed packet lost its thirty static facts: {index}"
  return mkAppN (mkConst (ns ++ `continuation)) params

run_cmd liftTermElabM do
  let native := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation
  forallBoundedTelescope (← getConstInfo native).type (some 21) fun x _ => do
    unless x.size == 21 do throwError "expected the original incidence21"
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[x[0]!,x[1]!,x[20]!]
    let cen := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.centers) (x.set! 20 cap)
    let fixed := #[x[0]!,x[1]!,cen]
    let groups ← store (ns ++ `Groups) x (mkAppN (mkConst (ns ++ `CellGroup)) fixed) true
    let assign ← store (ns ++ `assign) x (mkAppN (mkConst (ns ++ `cellPatch)) fixed) true
    let args := fixed ++ #[x[4]!,x[5]!,x[6]!]
    let surface (t : Expr) := t.replace fun e =>
      if e.isAppOf (ns ++ `CellGroup) && e.appArg! == cen then some groups
      else if e.isAppOf (ns ++ `cellPatch) && e.appArg! == cen then some assign else none
    let h := mkAppN (mkConst (ns ++ `protection_on_selected_centers_with_graph_bounds)) args
    let one ← store (ns ++ `signed_protection_with_graph_bounds) x h false (some (surface (← inferType h)))
    selectGraphs x one
    let weak := surface (← inferType (mkAppN (mkConst (ns ++ `protection_on_selected_centers)) args))
    discard <| store (ns ++ `signed_protection) x (← projectSelected x weak) false (some weak)
    logInfo "Original pre-reference selection: same full signed packet and legacy thirty facts; cgraph/Cgraph/Lx and graph derivatives before every history, weak continuation from the very same quantitative charts."

end JanetCartan.PhysicalInitialization.OriginalProtected
end
