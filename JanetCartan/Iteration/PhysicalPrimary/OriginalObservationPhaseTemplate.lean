module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Close global observation-phase profiles on the literal original current.
Only the profile threshold is joined before histories; no phase is chosen. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalObservationPhaseTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary
private def current := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def gradient := `JanetCartan.PhysicalPrimary.OriginalWordGradient
private def ns := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def native := ns ++ `Native

private def retain (name : Name) (params : Array Expr) (proof : Expr)
    (isDef := false) (type : Option Expr := none) : MetaM Expr := do
  let name := ns ++ name
  let result ← store name params proof isDef type
  addDocStringCore name "Global observation profile of the SAME original full phase and physical cutoff, including every cutoff shoulder. Only profile thresholds are joined before histories; no phase/frame/operator is reselected (app:ch_regular:eq:inverse-remainder; app:ch_response:eq:response-graded-reduced)."
  return result

/-- Apply the physical Schwartz-history global phase theorem to the original
cutoff and reference, then close its frame input on the canonical current. -/
elab "construct_original_observation_phase_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `S)).type (some 32) fun base _ => do
    unless base.size == 32 do throwError "observation phase: expected native32 prehistory prefix"
    let fixed := base[:23].toArray
    let ref := base[:25].toArray
    let n := mkApp (mkConst ``Nat.succ) base[0]!
    let hn := base[1]!
    let originalArgs := #[n] ++ base[1:21].toArray
    let originalField (name : Name) := mkAppN (mkConst (original ++ name)) #[n,hn]
    let G := mkAppN (mkConst (current ++ `Gref)) ref
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) originalArgs[:18].toArray
    logInfo "observation: native prefix and source reference ready"
    let hR ← mkAppM (regular ++ `radius_lt_same_chart) #[same,originalField `R_lt_chartRadius]
    logInfo "observation: original chart-radius proof ready"
    let cutoff := mkAppN (mkConst (regular ++ `Phase.χ)) fixed
    forallBoundedTelescope (← inferType cutoff) (some 1) fun patch _ => do
      let params := base ++ patch
      let phase (name : Name) := mkAppN (mkConst (regular ++ `Phase ++ name)) (fixed ++ patch)
      let T := mkApp (originalField `T) patch[0]!
      logInfo m!"observation: original cutoff ready; domain proof type {← inferType (phase `fact2)}"
      let ta := (← inferType T).getAppArgs
      unless ta.size == 4 do throwError "observation phase: unexpected original patch telescope"
      let profile := mkAppN (mkConst `JanetCartan.PhysicalParameterRemainder.exists_physical_retainedPhaseExtension_joint_profiles)
        #[base[0]!,ta[1]!,ta[2]!,ta[3]!,T,
          phase `χ,phase `fact0,phase `fact1,phase `fact2,G,
          originalField `b,originalField `R,originalField `b_pos,originalField `b_lt_R,hR,
          base[4]!,base[5]!,base[6]!,base[25]!,base[26]!,base[27]!,base[28]!,base[29]!,base[31]!]
      logInfo "observation: fully explicit global phase application ready"
      let existsProfile ← store (native ++ `exists_profiles) params profile
      select native params existsProfile
      let get (name : Name) := mkAppN (mkConst (native ++ name)) params
      let oldS := mkAppN (mkConst (current ++ `S)) base
      let profileS := get `S
      let S ← retain `S params (← mkAppM ``Max.max #[oldS,profileS]) true
      let hnS ← retain `current_threshold params (← mkAppM `le_max_left #[oldS,profileS])
      let hpS ← retain `profile_threshold params (← mkAppM `le_max_right #[oldS,profileS])
      discard <| retain `hS params (← mkAppM `le_trans
        #[mkAppN (mkConst (current ++ `hS)) base,hnS])
      discard <| retain `H params (get `H) true
      discard <| retain `H_nonneg params (get `fact1)
      let compact := get `fact2
      let X ← retain `X params (← inferType compact).appArg! true
      discard <| retain `X_compact params compact false
        (some (mkApp (← inferType compact).appFn! X))
      logInfo "OBS: fixed phase profile, support and prehistory maximum retained"
      withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀]) fun hR₀ => do
          let hnR ← mkAppM `le_trans #[hnS,hR₀]
          let hpR ← mkAppM `le_trans #[hpS,hR₀]
          let frame := mkAppN (mkConst (current ++ `sourceFrame)) (base ++ #[R₀,hnR])
          forallBoundedTelescope (← inferType frame) (some 4) fun data _ => do
            unless data.size == 4 do throwError "observation phase: expected native n/u/ell/history"
            let now := params ++ #[R₀,hR₀] ++ data
            let cur := base ++ #[R₀,hnR] ++ data
            let Q := mkAppN frame (data ++ patch)
            let hQ := mkAppN (mkConst (current ++ `sourceFrame_val)) (cur ++ patch)
            logInfo "OBS: exact current frame telescope ready"
            let proof := mkAppN (get `continuation) (#[R₀,hpR] ++ data ++ #[Q,hQ])
            let smooth := Expr.proj ``And 0 proof
            let support := Expr.proj ``And 0 (.proj ``And 1 proof)
            let bounds := Expr.proj ``And 1 (.proj ``And 1 proof)
            logInfo "OBS: before joint smooth type"
            let joint := (← inferType smooth).appArg!
            logInfo "OBS: joint smooth type ready"
            unless joint.isAppOf `Function.uncurry do
              throwError "observation phase: expected parameter-first uncurry"
            let rawPhase := joint.appArg!
            let physical := mkAppN (mkConst (gradient ++ `φ)) (cur ++ patch)
            let expected ← forallBoundedTelescope (← inferType rawPhase) (some 2) fun q _ => do
              unless q.size == 2 do throwError "observation phase: expected parameter and physical point"
              mkLambdaFVars q (mkApp physical (← mkAppM ``Prod.mk #[q[1]!,q[0]!]))
            let φ ← retain `φ now expected true
            let equality := mkAppN (mkConst (ns ++ `canonical_phase_eq_retained))
              #[base[0]!,base[1]!,patch[0]!,phase `χ,Q]
            let equality ← retain `φ_eq_retained now equality false
              (some (← mkEq φ rawPhase))
            for (name,value) in [(`joint_smooth,smooth),(`support,support),(`joint_profiles,bounds)] do
              let originalType ← inferType value
              let predicate ← withLocalDeclD `ψ (← inferType rawPhase) fun ψ => do
                let type := originalType.replace fun e => if e == rawPhase then some ψ else none
                unless type != originalType do
                  throwError "observation phase: missing literal phase occurrence in {name}"
                mkLambdaFVars #[ψ] type
              let typeEquality ← mkAppM ``congrArg #[predicate,equality]
              let actual ← mkAppM ``Eq.mpr #[typeEquality,value]
              discard <| retain name now actual
  logInfo "same original39 observation phase: global all-point/all-order parameter-first jets including cutoff shoulders; exact canonical positive phase, native frame and prescribed cutoff; one prehistory maximum, no new phase/operator/source scale"

end JanetCartan.PhysicalPrimary.OriginalObservationPhaseTemplate
end
