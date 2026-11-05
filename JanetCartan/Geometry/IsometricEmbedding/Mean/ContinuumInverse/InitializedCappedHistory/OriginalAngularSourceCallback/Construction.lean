module

public meta import Lean

/-!
# Apply the angular source producer to the already chosen Mean reference

This command only instantiates the existing AngularRaw theorem on the actual
original21 callback inputs. It neither selects a row nor copies the prefix-cache
machinery. The output is an ordinary closed kernel-checked theorem with the
entire source/raw/inverse/target-gap continuation. The later SelectedBoundary
chooses once from this stronger existential (`new:sec:order-of-choices`,
`app:ch_background:defn:bg-row`, `new:eq:amplitude-test`).
-/

public meta section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalAngularSourceCallback.Construction
open Lean Meta Elab Command Term

private partial def withAliases (bindings : List (Name × Expr))
    (fvars values : Array Expr) (k : Array Expr → Array Expr → TermElabM Unit) : TermElabM Unit := do
  match bindings with
  | [] => k fvars values
  | (name, value) :: rest =>
    withLetDecl name (← inferType value) value fun x =>
      withAliases rest (fvars.push x) (values.push value) k

/-- Apply all 53 static AngularRaw arguments to the same Mean H/seed and
candidate cells, retaining the unchanged original21 input telescope. No old
selected-row data or independently cached physical reference is used. -/
elab "apply_original_angular_source_callback" : command => liftTermElabM do
  let base := `JanetCartan.ContinuumInverse.InitializedCappedHistory
  let source ← getConstInfo (base ++ `SeedBoundary.fact3)
  unless source.levelParams.isEmpty do
    throwError "original angular source: unexpected universe parameters"
  forallTelescopeReducing source.type fun params _ => do
    unless params.size == 21 do
      throwError "original angular source: expected original21, got {params.size}"
    let val (part field : Name) (count : Nat) :=
      mkAppN (mkConst (base ++ part ++ field)) params[:count]
    let bindings : List (Name × Expr) := [
      (`n, params[0]!), (`hn, params[1]!),
      (`incidenceCap, params[18]!), (`hincidenceCap, params[19]!), (`aExtra, params[20]!),
      (`D, val `OriginalBoundary `D 2), (`T, val `OriginalBoundary `T 2),
      (`H, val `ReferenceBoundary `H 18), (`hHdomain, val `ReferenceBoundary `fact5 18),
      (`seed, val `SeedBoundary `seed 18), (`hseed, val `SeedBoundary `fact2 18),
      (`hD, val `OriginalBoundary `hD 2), (`b, val `OriginalBoundary `b 2),
      (`R, val `OriginalBoundary `R 2), (`G₀, val `OriginalBoundary `G₀ 2),
      (`hbR, val `OriginalBoundary `b_lt_R 2), (`hR, val `OriginalBoundary `R_lt_chartRadius 2),
      (`hphysical, val `OriginalBoundary `stateDomain_subset_ball 2),
      (`hgeometryc, val `OriginalBoundary `transport_cells 2),
      (`hsourceGeometry, val `OriginalBoundary `cofactor_cells 2),
      (`hpositive, val `OriginalBoundary `comparison_pos 2),
      (`hproduct, val `OriginalBoundary `density_product_geometry 2),
      (`hcoverProduct, val `OriginalBoundary `density_product_cover 2),
      (`centers, val `OriginalBoundary `centers 2),
      (`row, val `OriginalBoundary `row 2), (`col, val `OriginalBoundary `col 2),
      (`Ωc, val `OriginalBoundary `Ωc 2), (`ρc, val `OriginalBoundary `ρc 2),
      (`Rc, val `OriginalBoundary `Rc 2), (`Bc, val `OriginalBoundary `Bc 2),
      (`τc, val `OriginalBoundary `τc 2), (`L, val `OriginalBoundary `L 2),
      (`Rproduct, val `OriginalBoundary `Rproduct 2),
      (`εcarrier, val `OriginalBoundary `εcarrier 2),
      (`Mproduct, val `OriginalBoundary `Mproduct 2)]
    withAliases bindings #[] #[] fun fvars values => do
      let code := "let Tm := fun b l => T ⟨b, l⟩; " ++
        "let Im := fun b l => ↥(centers ⟨b, l⟩); " ++
        "let Ωm := fun b l j => Ωc ⟨b, l⟩ j; " ++
        "let zCellm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) => j.val.val; " ++
        "let ρcm := fun b l j => ρc ⟨b, l⟩ j; " ++
        "let Rcm := fun b l j => Rc ⟨b, l⟩ j; " ++
        "let Mm := fun b l j => Bc ⟨b, l⟩ j; " ++
        "let τleadm := fun b l j => τc ⟨b, l⟩ j; " ++
        "let rowm := fun b l j => row ⟨b, l⟩ j; let colm := fun b l j => col ⟨b, l⟩ j; " ++
        "let c₀ := fun b l j => seed ⟨b, l⟩ j; " ++
        "let Rm := fun b l j => Rproduct ⟨b, l⟩ j; " ++
        "let Vm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) => ball (j.val.val 0, spectatorCenter j.val.val) (εcarrier ⟨b, l⟩ j); " ++
        "let Lm := fun b l j => L ⟨b, l⟩ j; " ++
        "JanetCartan.PhysicalSeed.AngularRaw.exists_source_raw_inverse_with_angular_cap hD hn H " ++
        "(by change ball (0 : Euclidean n) R ⊆ ball 0 H.domain.chartRadius; have hd : H.domain = G₀.domain := hHdomain; rw [hd]; exact ball_subset_ball hR.le) " ++
        "isBounded_ball Tm Im Ωm " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.2.2.1) zCellm ρcm Rcm Mm τleadm rowm colm " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.2.2.2.1) " ++
        "(fun b l j w hw => by have hh := (hgeometryc ⟨b,l⟩ j).2.2.2.2.2.1 hw; exact ⟨⟨closedBall_subset_ball hbR (interior_subset hh.1.2), hh.1.1⟩, hh.2⟩) " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.1.le) " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.2.2.2.2.2.2.2.1) " ++
        "(fun b l j => (hsourceGeometry ⟨b,l⟩ j).2.1) " ++
        "(fun b l j => (hpositive ⟨b,l⟩ j).2.2.2.1) " ++
        "(fun b l j => (hpositive ⟨b,l⟩ j).2.2.2.2.1) " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.2.2.2.2.2.2.2.2) " ++
        "(fun b l j => (hgeometryc ⟨b,l⟩ j).2.2.2.2.2.2.2.1) " ++
        "(fun b l => (frameBall_subset_of_stateDomain (T ⟨b,l⟩).data.localReference (hphysical ⟨b,l⟩)).trans (ball_subset_ball hbR.le)) " ++
        "c₀ (fun b l j => (hseed ⟨b,l⟩ j).2) Rm Vm " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.1) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.1) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.2.1) (fun _ _ _ => isOpen_ball) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.2.2.2.2.2.1) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.2.2.2.2.2.2.1) " ++
        "Lm (fun b l j => Mproduct ⟨b,l⟩ j) " ++
        "(fun b l j => (hpositive ⟨b,l⟩ j).2.1) (fun b l j => (hproduct ⟨b,l⟩ j).1) " ++
        "(fun b l j => ((hproduct ⟨b,l⟩ j).2.2.2.2.2.2.2.2.2.2.2.2 H.map (row ⟨b,l⟩ j) (col ⟨b,l⟩ j) (seed ⟨b,l⟩ j)).1) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.2.2.1) " ++
        "(fun b l j => (hproduct ⟨b,l⟩ j).2.2.2.2.2.2.2.2.2.2.1) " ++
        "(fun b l => hcoverProduct ⟨b,l⟩) hincidenceCap aExtra"
      let stx ← match Parser.runParserCategory (← getEnv) `term code with
        | .ok stx => pure stx
        | .error message => throwError "original angular source argument syntax: {message}"
      let value ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let value := (← instantiateMVars value).replaceFVars fvars values
      let head ← withTransparency .reducible <| whnf value
      unless head.getAppFn.isConstOf
          `JanetCartan.PhysicalSeed.AngularRaw.exists_source_raw_inverse_with_angular_cap &&
          head.getAppArgs.size == 53 do
        throwError "original angular source: the complete AngularRaw53 application changed"
      let type ← mkForallFVars params (← inferType value)
      let value ← mkLambdaFVars params value
      if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
          type.hasSorry || value.hasSorry || type.hasLevelMVar || value.hasLevelMVar then
        throwError "original angular source: not a closed ordinary theorem"
      let name := base ++ `OriginalAngularSourceCallback.initialized
      addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
      addDocStringCore name "The actual original21 angular-cap source callback on the already chosen Mean H, seed and candidate cells. The entire old row/raw/source/inverse/target-gap continuation is retained, with angularWidth ≤ aExtra appended before targetGap. Select rows once from this stronger existential; no earlier weak selected row or coefficient function is identified with its future witnesses (new:sec:order-of-choices, new:eq:amplitude-test)."

end JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalAngularSourceCallback.Construction
