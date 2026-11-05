module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseReconstruction

/-! # The actual graded original full primary response
Apply the classical full inverse and uncontracted full matrix source, together
with the five native coefficient families, to the literal completed response.
Only their common prehistory threshold and the original sigma-scaled scalar
profile remain as input data. The conclusion uses the unchanged full B. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfiles

/-- The original strict frequency window implies precisely the reconstruction
scale comparison; it does not identify independent source and carrier rates. -/
theorem scale_le_physical_carrier {τ K ν : ℝ} (hρ : 1 ≤ τ⁻¹) (hν : 0 < ν)
    (hw : K ≤ (τ⁻¹)^(1-ν)) : K ≤ τ⁻¹ :=
  hw.trans (Real.rpow_le_self_of_one_le hρ (by linarith))

theorem joint_phase_and_slices {d : ℕ}
    {φ : (Euclidean 3 × Euclidean d) → Euclidean (d+1) → ℝ}
    (h : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦ φ q.2 q.1) ∧
      ∀ c, ContDiff ℝ ∞ (φ c) :=
  ⟨h.comp (contDiff_snd.prodMk contDiff_fst),fun _ ↦ h.comp (contDiff_const.prodMk contDiff_id)⟩

theorem joint_phase_on {d : ℕ}
    (Ω : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d)))
    {φ : (Euclidean 3 × Euclidean d) → Euclidean (d+1) → ℝ}
    (h : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiffOn ℝ ∞ (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦ φ q.2 q.1) Ω :=
  (joint_phase_and_slices h).1.contDiffOn

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfiles
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate OriginalPhysicalReducedProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfiles
private def input := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def recon := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstruction
private def red := `JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def phase := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def obs := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def comparison := `JanetCartan.PhysicalPrimary.OriginalComparisonResponse
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def can := `JanetCartan.CanonicalAtomRealization
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"actual graded primary: checked {k}"
  addDocStringCore (ns ++ k) "Actual original full primary response on the same history, raw source, complete inverse, positive parameter phase and globally uncut B. Uniform costs precede histories; original sigma-scaled scalar budget retained (app:ch_response:eq:current-atomic-amplitudes)."
  return h
private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k
private def named (name : Name) (v : Array (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo name
  let levels := ci.levelParams.map fun _ => Level.zero
  let mut t := ci.type.instantiateLevelParams ci.levelParams levels
  let mut r := mkConst name levels
  while let .forallE key dom b bi := t do
    let x ← if let some (_,x) := v.find? (·.1 == key) then pure x
      else if bi == .instImplicit then synthInstance dom
      else throwError "actual graded primary argument {key} of {name}"
    r := mkApp r x
    t := b.instantiate1 x
  return r
private def arguments (v : Expr) : MetaM (Array (Name × Expr)) := do
  let ci ← getConstInfo v.getAppFn.constName!
  let mut t := ci.type.instantiateLevelParams ci.levelParams v.getAppFn.constLevels!
  let mut out := #[]
  for x in v.getAppArgs do
    let .forallE key _ b _ ← whnf t | throwError "actual reconstruction: source envelope arity changed"
    out := out.push (key,x)
    t := b.instantiate1 x
  return out
private def smoothField (h : Expr) (arity : Nat) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some arity) fun xs _ => mkLambdaFVars xs (.proj ``And 0 (mkAppN h xs))
private def boundedField (h : Expr) (arity : Nat) (m : Expr) (isPair := true) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some arity) fun xs _ => do
    let hb := if isPair then Expr.proj ``And 1 (mkAppN h xs) else mkAppN h xs
    forallBoundedTelescope (← inferType hb) (some 1) fun r _ => do
      withLocalDeclD `hr (← mkAppM ``LE.le #[r[0]!,m]) fun hr =>
        mkLambdaFVars (xs ++ r ++ #[hr]) (mkAppN hb r)
private def restrictedReduced (h : Expr) (Ω sub : Expr) (m : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some 2) fun jr tail => do
    let .forallE _ qType _ _ := tail | throwError "actual reduced coordinate domain changed"
    withLocalDeclD `hr (← mkAppM ``LE.le #[jr[1]!,m]) fun hr => do
      withLocalDeclD `q qType fun q => do
        withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq =>
          mkLambdaFVars (jr ++ #[hr,q,hq]) (mkAppN h (jr ++ #[q,mkAppN sub #[q,hq]]))

elab "apply_actual_native_primary_reconstruction_part " st:num : command => liftTermElabM do
  let stage := st.getNat
  if stage == 0 then
    forallBoundedTelescope (← getConstInfo (input ++ `S)).type (some 44) fun fixed _ => do
      let n := mkApp (mkConst ``Nat.succ) fixed[0]!
      let N := app `JanetCartan.embeddingDimension #[n]
      let C := app (input ++ `C) fixed
      let B := app (input ++ `B) fixed
      discard <| emit `S fixed (app (input ++ `S) fixed) true
      discard <| emit `S_ge_two fixed (app (input ++ `S_ge_two) fixed)
      let D := app (can ++ `jointReconstructionDisplacementBudget) #[n,C,B]
      let E := app (can ++ `jointReconstructionPhysicalBudget) #[n,C,B]
      discard <| emit `displacement_coordinate_cost fixed D true
      discard <| emit `derivative_coordinate_cost fixed E true
      discard <| emit `displacement_cost_nonneg fixed
        (app (can ++ `jointReconstructionDisplacementBudget_nonneg) #[C,B,app (input ++ `C_nonneg) fixed,app (input ++ `B_nonneg) fixed,n])
      discard <| emit `derivative_cost_nonneg fixed
        (app (can ++ `jointReconstructionPhysicalBudget_nonneg) #[C,B,app (input ++ `C_nonneg) fixed,app (input ++ `B_nonneg) fixed,n])
      let _ := N
    return
  withNativePhysicalInputs fun xs p old s _pt => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let nat := mkConst ``Nat
    let fixed := s[:23].toArray
    let wc (k : Name) := app (wave ++ k) s
    let mask (k : Name) := app (masks ++ k) fixed
    let pp := old[:44].toArray.push (app (ind ++ `point) old)
    let phRaw ← bodyAt (family ++ `Point.φ) pp
    let ph := phRaw.getAppArgs[:33].toArray ++ #[s[39]!,phRaw.getAppArgs[34]!] ++ s[41:45].toArray
    let residual ← bodyAt (family ++ `Point.R) pp
    let weak := residual.getAppArgs[:32].toArray ++ #[s[39]!,residual.getAppArgs[33]!] ++ s[41:45].toArray
    let rawEnvelope ← bodyAt (red ++ `reduced) xs
    unless rawEnvelope.isAppOf (can ++ `fixedSolverParameterEnvelope) do throwError "same classical reduced envelope changed"
    let args ← arguments rawEnvelope
    let get (k : Name) : MetaM Expr := do
      let some (_,v) := args.find? (fun v => v.1 == k) | throwError "native reduced envelope argument {k}"
      return v
    let Z ← get `Z
    let V ← get `V
    let jointφ ← get `φ
    let φ := app (ind ++ `phase) old
    let jointType := (← inferType jointφ).bindingDomain!
    let Ω := app (input ++ `region) xs
    let region := app (input ++ `region_geometry_actual) xs
    let hΩ := part region 0
    let hΩV := part region 3
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let ws := app (cmp ++ `parameterComparisonWindow_spec) #[n,s[1]!,va[23]!,va[24]!]
    let hSub := part (.proj ``And 1 ws) 0
    let χ := (← inferType (mask `χ₂_smooth)).appArg!
    let ξ := app (comparison ++ `proofCutoff) #[n,s[1]!,ph[32]!]
    let ξa := (← inferType ξ).getAppArgs
    let hphase ← withLocalDeclD `q jointType fun q => do
      withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq =>
        mkLambdaFVars #[q,hq] (app (geo ++ `current_phase) (s ++ #[q,mkAppN (part region 2) #[q,hq]]))
    let phaseNative := app (ns ++ `joint_phase_and_slices) #[s[0]!,φ,app (phase ++ `joint_smooth) ph]
    let hjoint := app (ns ++ `joint_phase_on) #[s[0]!,Ω,φ,app (phase ++ `joint_smooth) ph]
    let hsp ← withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc =>
        mkLambdaFVars #[c,hc] (mkApp (.proj ``And 1 phaseNative) c)
    let hobs ← withLocalDeclD `q jointType fun q => do
      withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq => do
        let hXV := mkAppN (part region 1) #[q,hq]
        let c := Expr.proj ``Prod 1 q
        let hV' := mkAppN hSub #[c,.proj ``And 1 hXV]
        let hc := app (masks ++ `V_closure_Csrc) (fixed ++ #[va[23]!,va[24]!,c,← mkAppM `subset_closure #[hV']])
        let h := app (cmp ++ `Physical.phase_on_source_rectangle) (old ++ #[c,hc,.proj ``Prod 0 q,.proj ``And 0 hXV])
        mkLambdaFVars #[q,hq] h
    let nativeB := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B weak
    let fixedB := app (comparison ++ `fixed) old
    let response (b : Expr) := mkAppM `JanetCartan.CorrectedAtoms.fullPrimaryResponse
      ((#[`T,`Q,`F,`row,`col,`Φ,`Y].map wc) ++ #[χ,b,s[47]!,wc `scalar])
    let original ← response nativeB
    let fixedResponse ← response fixedB
    let hcomparison ← withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc =>
        mkLambdaFVars #[c,hc] (app (comparison ++ `whole_response_eq) (old ++ #[c,mkAppN hSub #[c,hc]]))
    withLocalDeclD `reserve nat fun res => do
      let rs := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) res n) (mkNatLit 1)
      withLocalDeclD `hSourceReserve (← mkEq rs s[37]!) fun hr => do
        let static := p ++ #[res,hr]
        let S := app (input ++ `S) static
        withLocalDeclD `hResponseReached (← mkAppM ``LE.le #[S,s[39]!]) fun hR => do
          let all := xs ++ #[res,hr,hR]
          let q (k : Name) := app (input ++ k) all
          let C := app (input ++ `C) static
          let B := app (input ++ `B) static
          let hC := app (input ++ `C_nonneg) static
          let hB := app (input ++ `B_nonneg) static
          let hK := app (family ++ `Point.hK) pp
          let hKτ ← mkAppM (ns ++ `scale_le_physical_carrier)
            #[app (family ++ `Point.hρ) pp,old[42]!,app (family ++ `Point.hwindow) pp]
          withLocalDeclD `m nat fun m => do
            let allm := all.push m
            let m1 := mkApp2 (mkConst ``Nat.add) m (mkNatLit 1)
            let m2 := mkApp2 (mkConst ``Nat.add) m (mkNatLit 2)
            let D := app (ns ++ `displacement_coordinate_cost) static
            let H := app (ns ++ `derivative_coordinate_cost) static
            let ha := app (recon ++ `strain_coordinate_smooth) all
            let hg := app (recon ++ `reduced_smooth) all
            let cutoff := q `cutoff_profile
            let gradient := q `gradient_profiles
            let value := q `value_entries
            let deriv := q `derivative_entries
            let source := q `source_entries
            let env := app `JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles.envelope s
            let more := #[( `N,N),(`F,wc `F),(`hsolver,app `JanetCartan.PhysicalPrimary.OriginalUncutSolver.uncut_solver_smooth weak),
              (`core,ξa[1]!),(`chart,ξa[2]!),(`Ξ,ξ),(`χ,χ),(`a,env),(`hsource,app (recon ++ `source_remodulation) xs),
              (`Ω,Ω),(`hΩ,hΩ),(`hΩcore,part region 1),(`hφjoint,hjoint),(`hφsp,hsp),(`hg,hg),(`ha,ha),
              (`hχ,.proj ``And 0 cutoff),(`hφ,← smoothField gradient 1),(`hV,← smoothField value 2),
              (`hD,← smoothField deriv 2),(`hS,← smoothField source 2),(`C,C),(`B,B),(`hC,hC),(`hB,hB),
              (`size,s[50]!),(`K,s[45]!),(`hsize,s[51]!),(`hτ,s[48]!),(`hK,hK),(`hKτ,hKτ),(`reserve,res),(`m,m),
              (`hχB,← boundedField cutoff 0 m1),(`hφB,← boundedField gradient 1 m1),
              (`hVB,← boundedField value 2 m1),(`hDB,← boundedField deriv 2 m1),(`hSB,← boundedField source 2 m1),
              (`hgB,← restrictedReduced (app (recon ++ `reduced_coordinate_bounds) all) Ω hΩV m2),
              (`haB,← boundedField (app (recon ++ `strain_coordinate_bounds) all) 1 m1 false)]
            if stage == 1 then
              let h ← named (can ++ `fixedSolverParameterResponse_joint_graded) (more ++ args)
              discard <| emit `fixed_coordinate_profiles allm h
              return
            let hfixed := app (ns ++ `fixed_coordinate_profiles) allm
            let huncut := app (recon ++ `native_coordinate_profiles)
              #[n,s[0]!,N,V,Ω,hΩ,hΩV,original,fixedResponse,hcomparison,jointφ,s[47]!,s[50]!,s[45]!,D,H,res,m,hfixed]
            let huncut ← emit `uncut_coordinate_profiles allm huncut
            let hd := part huncut 1
            let he := Expr.proj ``And 1 (.proj ``And 1 huncut)
            let primary ← named (can ++ `fullPrimaryResponse_amplitudes_of_coordinate_profiles)
              (#[( `n,n),(`N,N),(`P,(← inferType (wc `T)).getAppArgs[1]!),(`U,← get `U),(`hU,← get `hU),
                (`T,wc `T),(`Q,wc `Q),(`F,wc `F),(`row,wc `row),(`col,wc `col),(`Φ,wc `Φ),(`Y,wc `Y),
                (`χ,χ),(`B,nativeB),(`scalar,wc `scalar),(`τ,s[47]!),(`φ,jointφ),(`Ω,Ω),(`hΩ,hΩ),(`hphase,hphase),
                (`hφobs,hobs),(`hresponse,part huncut 0),(`D,D),(`E,H),(`hD,app (ns ++ `displacement_cost_nonneg) static),
                (`hE,app (ns ++ `derivative_cost_nonneg) static),(`size,s[50]!),(`K,s[45]!),(`hsize,s[51]!),(`hτ,s[48]!),
                (`hK,hK),(`reserve,res),(`m,m),(`hdisp,hd),(`hderiv,he)])
            discard <| emit `amplitude_profiles allm primary
            discard <| emit `response_smooth allm (part huncut 0)
            discard <| emit `derivative_amplitude_smooth allm (.proj ``And 0 primary)
            discard <| emit `on_sets allm (.proj ``And 1 primary)
  logInfo "literal original full B: same solver and source, quadratic displacement and linear full derivative-amplitude profiles from the native cubic bounds"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfilesTemplate
end
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
apply_actual_native_primary_reconstruction_part 0
apply_actual_native_primary_reconstruction_part 1
apply_actual_native_primary_reconstruction_part 2
