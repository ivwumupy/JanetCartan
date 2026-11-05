module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-! Kernel-checked original-data specializations of the ordinary uncut classical
estimate and joint primary regularity. There is no parameter-window shrinkage
or change to the inverse, source, current or corrected atom. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalJointResponseRegularityTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity
private def op := `JanetCartan.PhysicalPrimary.OriginalObservedSolver
private def uncut := `JanetCartan.PhysicalPrimary.OriginalUncutSolver
private def native := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native
private def cur := `JanetCartan.PhysicalInitialization.OriginalRegular.Current
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def recn := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def cmp := `JanetCartan.PhysicalPrimary.OriginalComparisonResponse
private def compact := `JanetCartan.PhysicalPrimary.OriginalFullResponseCompact
private def support := `JanetCartan.PhysicalPrimary.OriginalSolverSupport
private def src := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def phy := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def coords := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
private def CAt := `JanetCartan.CorrectedAtoms
private def appl (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (proof : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let r ← store (ns ++ k) xs proof data t
  addDocStringCore (ns ++ k) "The ordinary classical or joint regularity of the native uncut weak38 response, with chi3 only after its own inverse, actual chi2 source, original entire doubled parameter window and original full geometry (app:ch_response:cor:current-atoms). No graded uniform history cost or parameter cutoff is assumed."
  return r

elab "derive_original_uncut_classical_bound" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (op ++ `native_inverse_eq)).type (some 38) fun w _ => do
    let fixed := w[:23].toArray
    let d := w[0]!
    let rawR ← bodyAt (cur ++ `R) w
    unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "original classical solver: native W changed"
    let hW := rawR.getAppArgs[3]!
    let W := (← inferType hW).appArg!
    let χ := appl (reg ++ `χ₃) fixed
    let x := (← inferType χ).appArg!
    let actualI := (← inferType (appl (op ++ `native_inverse_eq) w)).appArg!
    let bound := appl (ns ++ `classical_costs_of_uncut_solver) <|
      #[d,W,hW,x,χ,appl (uncut ++ `source_support) w,actualI,appl (native ++ `pairedSolver) w,
        appl (uncut ++ `uncut_solver) w,appl (uncut ++ `uncut_solver_smooth) w,appl (op ++ `smooth_solver_ae) w] ++
      #[`I.cost,`I.high,`S.cost,`S.high,`I.cost_nonneg,`I.high_nonneg,`S.cost_nonneg,`S.high_nonneg,`I.bound,`S.bound].map
        (fun k => appl (op ++ k) w)
    let bound ← emit `Weak.classical_costs w bound
    let D ← emit `Weak.D w (← mkAppM ``Classical.choose #[bound]) true
    let Dbody ← bodyAt (ns ++ `Weak.D) w
    let spec ← mkAppM ``Classical.choose_spec #[bound]
    for (j,k) in #[(0,`Weak.D_nonneg),(1,`Weak.classical_bound)] do
      let v := Expr.proj ``And j spec
      let t := (← inferType v).replace fun e => if e == Dbody then some D else none
      discard <| emit k w v false (some t)
    logInfo "same weak38 real inverse, chi3 source extension and full paired solver give ordinary cNorm bound on every positive-radius ball; no inner chi2 or output recut"

/-- Combine the raw source and the ordinary weak solver, sharing all original
fixed data, σ/R₀ and the SAME four finite-history inputs. The *only* extra
binders are the actual weak scale/order/reached admission proofs which both
Graph42 and the physical 13 spine already contain. No stronger signed or
quantitative inverse assumption is incurred on the ordinary-wave consumer. -/
private partial def withSourceWeak (go : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withSourcePrefix 53 fun s => do
    let known := (s[:24].toArray.mapIdx (fun j e => (j,e))) ++
      #[(25,s[26]!),(26,s[27]!),(27,s[28]!),(28,s[29]!),(31,s[31]!),(32,s[39]!),
        (34,s[41]!),(35,s[42]!),(36,s[43]!),(37,s[44]!)]
    let extra := #[(24,`hRegularScale),(29,`hRegularStar),(30,`hRegularOrder),(33,`hRegularReached)]
    let rec loop (t : Expr) (w p : Array Expr) : MetaM Unit := do
      if w.size == 38 then go p s w else
        let .forallE _ dom b _ := t | throwError "joint regularity: weak38 ended early at {w.size}"
        if let some (_,val) := known.find? (·.1 == w.size) then
          loop (b.instantiate1 val) (w.push val) p
        else if let some (_,key) := extra.find? (·.1 == w.size) then
          withLocalDeclD key dom fun val => loop (b.instantiate1 val) (w.push val) (p.push val)
        else throwError "joint regularity: unmapped weak38 input {w.size}"
    loop (← getConstInfo (recn ++ `B)).type #[] s

elab "retain_original_joint_solver_spine" : command => liftTermElabM do
  withSourceWeak fun p s w => do
    let rawF := appl (wave ++ `F) s
    let B := appl (recn ++ `B) w
    let nativeF := appl (recn ++ `F) w
    discard <| emit `B p B true
    discard <| emit `same_finite_map p (← mkEqRefl rawF) false (some (← mkEq nativeF rawF))
    let Qext := appl (cur ++ `Q) w
    let e ← mkAppM `JanetCartan.ProtectedFlow.extendedProjectedStress #[s[4]!,rawF]
    discard <| emit `same_extended_frame p (← mkEqRefl Qext) false (some (← mkEq Qext e))
    logInfo "Source53 shares the literal finite history, original24 scale, and extended frame with the ordinary weak38 full B; only the original admissions, not strong or analytic estimates, remain"

private def proofBy (name : Name) (goal : Expr) : MetaM Expr := do
  let g ← mkFreshExprMVar goal
  unless (← g.mvarId!.apply (← mkConstWithFreshMVarLevels name)).isEmpty do
    throwError "joint regularity: {name} did not close {goal.getAppFn}"
  instantiateMVars g

private def applyNamed (name : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let mut t := (← getConstInfo name).type
  let mut h := mkConst name
  while let .forallE k _ b _ := t do
    let some (_,v) := fields.find? (·.1 == k) | throwError "joint regularity: missing original input {k} of {name}"
    h := mkApp h v
    t := b.instantiate1 v
  return h

elab "identify_original_joint_tensor_frame" : command => liftTermElabM do
  withSourceWeak fun p s w => do
    let fixed := s[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) w[0]!
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let d := (← bodyAt (recn ++ `B) w).getAppArgs
    unless d.size == 14 do throwError "original joint proof: changed uncut source/solver spine"
    let vp := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let patch := vp[23]!
    let Xrect := appl (src ++ `Actual.chart_in_source) (fixed.push patch)
    let hSrect ← mkAppM `Set.Subset.trans #[appl (masks ++ `χ₂_support_chart) fixed,Xrect]
    let hS := appl (phy ++ `source_rectangle_in_chart) #[n,s[1]!,patch]
    let hSU ← emit `tensor_support_in_chart p (← mkAppM `Set.Subset.trans #[hSrect,hS])
    let rawQ := appl (wave ++ `Q) s
    let Q := Expr.proj ``Subtype 0 rawQ
    let F := appl (wave ++ `F) s
    let qproj ← mkAppM `JanetCartan.ProjectedStressFrame.projectedStress #[F]
    let rawEq ← emit `same_raw_frame p (← mkEqRefl Q) false (some (← mkEq Q qproj))
    let hframes := appl (phy ++ `frames_on_rectangle) #[n,N,s[1]!,patch,F,s[4]!,s[5]!,s[6]!,d[3]!,Q,
      appl (ns ++ `same_extended_frame) p,rawEq]
    let he ← emit `frames_on_tensor_support p (← mkAppM `Set.EqOn.mono #[hSrect,hframes])
    let hQ₀ := Expr.proj ``And 0 (.proj ``Subtype 1 rawQ)
    let U := (← inferType hQ₀).appArg!
    let hU ← proofBy `Metric.isOpen_ball (← mkAppM `IsOpen #[U])
    let hQ := appl (phy ++ `raw_components) #[n,U,Q,hQ₀]
    let ξ := appl (cmp ++ `proofCutoff) #[n,s[1]!,patch]
    let hOut := appl (src ++ `Actual.outputSupport_in_source) (fixed.push patch)
    let hSol := appl (compact ++ `uncut_solver_support) w
    let hSol ← forallBoundedTelescope (← inferType hSol) (some 1) fun v _ => do
      mkLambdaFVars v (← mkAppM `Set.Subset.trans #[mkAppN hSol v,hOut])
    let hSC ← mkAppM `Set.Subset.trans #[appl (support ++ `χ₂_support_output) fixed,hOut]
    let onNative ← mkAppM (cmp ++ `admitted_eq)
      #[F,d[3]!,Q,d[4]!,d[8]!,hU,d[9]!,hQ,d[10]!,d[11]!,hSU,he,d[12]!,d[13]!,ξ,hSol,hSC]
    let literalB ← bodyAt (recn ++ `B) w
    let actual := appl (ns ++ `B) p
    let t := (← inferType onNative).replace fun e => if e == literalB then some actual else none
    discard <| emit `on_admitted_tensors p onNative false (some t)
    logInfo "true raw tensor plus both canonical frames: original weak B and comparison map agree for all admitted chi2 tensors, as WHOLE functions in space, with native support and no change of solver"

elab "apply_original_joint_window_regularities" : command => liftTermElabM do
  withSourceWeak fun p s w => do
    let d := s[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let fixed := s[:23].toArray
    let mask (k : Name) := appl (masks ++ k) fixed
    let raw (k : Name) := appl (wave ++ k) s
    let dom (k : Name) := appl (geo ++ k) s
    let W := (← bodyAt (recn ++ `B) w).getAppArgs[7]!
    let tt := (← inferType (raw `T)).getAppArgs
    unless tt.size == 4 do throwError "joint regularity: bad leading patch family"
    let vp := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let patch := vp[23]!
    let ξ := appl (cmp ++ `proofCutoff) #[n,s[1]!,patch]
    let xi := (← inferType ξ).getAppArgs
    let chart := xi.back!
    let core := xi[xi.size-2]!
    let hchart ← proofBy `Metric.isOpen_ball (← mkAppM `IsOpen #[chart])
    let hchartU := appl (ns ++ `weak_chart_in_raw) #[n,s[1]!]
    let nativeBall ← bodyAt (src ++ `Actual.physical_closed_ball) fixed
    let ab := nativeBall.getAppArgs
    let x := ab[ab.size-2]!
    let R := ab.back!
    let f := appl (reg ++ `f) fixed
    let hR ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.physicalRadius_pos #[f]
    let xr ← bodyAt (masks ++ `chart) fixed
    let min := xr.getAppArgs.back!.getAppArgs
    let hXR := appl (ns ++ `source_chart_in_ball) #[n,x,min[min.size-2]!,R]
    let hK ← mkAppM `IsCompact.isClosed #[appl (support ++ `outputSupport_compact) fixed]
    let hη := mask `χsrc_smooth
    let hχ := mask `χ₂_smooth
    let data := #[(`d,d),(`N,N),(`P,tt[1]!),(`U,tt[2]!),(`hU,tt[3]!),(`T,raw `T),(`Q,raw `Q),(`F,raw `F),
      (`row,raw `row),(`col,raw `col),(`Φ,raw `Φ),(`Y,raw `Y),(`χ,(← inferType hχ).appArg!),(`η,(← inferType hη).appArg!),
      (`hη,hη),(`hχU,appl (ns ++ `tensor_support_in_chart) p),(`W,W),(`core,core),(`chart,chart),
      (`solver,appl (uncut ++ `uncut_solver) w),(`hsolver,appl (uncut ++ `uncut_solver_smooth) w),(`Ξ,ξ),
      (`hchart,hchart),(`hchartU,hchartU),(`x,x),(`R,R),(`hcore,appl (src ++ `Actual.physical_ball_in_source) (fixed.push patch)),
      (`D,appl (ns ++ `Weak.D) w),(`hD,appl (ns ++ `Weak.D_nonneg) w),(`hbound,appl (ns ++ `Weak.classical_bound) (w ++ #[x,R,hR])),
      (`Ω,(← inferType (dom `current_open)).appArg!),(`hΩ,dom `current_open),(`hspace,dom `current_space),(`hphase,dom `current_phase),
      (`hF,raw `current_map_smooth),(`hi,raw `current_immersion),(`hrank,raw `current_full_rank),(`hnonzero,raw `nullvectors_nonzero),
      (`X,mask `chart),(`K,(← inferType hK).appArg!),(`V,dom `parameter_window),(`hX,mask `chart_open),(`hV,appl (masks ++ `V_open) vp),
      (`hXV,dom `source_product_in_current),(`hXR,hXR),(`hK,hK),(`hKR,appl (support ++ `outputSupport_in_physical_ball) fixed),
      (`hχ,hχ),(`hc,mask `χ₂_compact),(`hχX,mask `χ₂_support_chart),(`B,appl (ns ++ `B) p),(`τ,s[47]!),(`hτ,← mkAppM `ne_of_gt #[s[48]!]),
      (`r,raw `scalar),(`hα,raw `scalar_smooth),(`_heAgree,appl (ns ++ `on_admitted_tensors) p),
      (`_hBK,appl (compact ++ `support) w),(`_hquad,raw `source_quadratures)]
    let all ← emit `joint_family p (← applyNamed (ns ++ `joint_of_classical_and_admitted_support) data)
    let rest := Expr.proj ``And 1 all
    let current := Expr.proj ``And 1 rest
    for (k,v) in #[(`full_response_smooth,Expr.proj ``And 0 all),(`source_chart_corrected,Expr.proj ``And 0 rest),
        (`corrected_atom_smooth,Expr.proj ``And 0 current),(`displacement_amplitude_smooth,Expr.proj ``And 0 (.proj ``And 1 current)),
        (`derivative_amplitude_smooth,Expr.proj ``And 1 (.proj ``And 1 current))] do
      discard <| emit k p v
    logInfo "original uncut fullPrimaryResponse jointly smooth on univ × doubled V; corrected atom and both physical amplitudes jointly smooth on the same source chart × V and actual current Ω over full doubled V; no theta or output cutoff in any conclusion"

end JanetCartan.PhysicalPrimary.OriginalJointResponseRegularityTemplate
