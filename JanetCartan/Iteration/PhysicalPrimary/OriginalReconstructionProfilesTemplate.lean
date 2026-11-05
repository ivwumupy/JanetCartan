module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Native physical-history reconstruction coefficients, retained before every
history, for the actual uncut primary response. No torus history is used. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalReconstructionProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def root := `JanetCartan.PhysicalPrimary.OriginalReconstructionProfiles
private def current := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary

private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs

private def save (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) (type : Option Expr := none) : MetaM Expr := do
  let result ← store (root ++ name) params value isDef type
  addDocStringCore (root ++ name) "Same original physical-history value/derivative/source reconstruction coefficients. The common threshold and profile precede every finite history; only the primitive numerical reserve 2+reserve<=history is required (app:ch_response:eq:response-reconstruction-grading)."
  return result

elab "construct_original_physical_reconstruction_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `S)).type (some 32) fun base _ => do
    unless base.size == 32 do throwError "original reconstruction: changed native32 spine"
    let n := mkApp (mkConst ``Nat.succ) base[0]!
    let G := app (current ++ `Gref) base[:25].toArray
    let get (name : Name) := app (original ++ name) #[n,base[1]!]
    let sourceOriginal := #[n] ++ base[1:21].toArray
    let same := app `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5 sourceOriginal[:18].toArray
    let hR ← mkAppM (reg ++ `radius_lt_same_chart) #[same,get `R_lt_chartRadius]
    withLocalDeclD `reserve (mkConst ``Nat) fun reserve => do
      let lower := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) reserve
      withLocalDeclD `hreserve (← mkAppM ``LE.le #[lower,base[27]!]) fun hreserve => do
        let params := base ++ #[reserve,hreserve]
        let profile := app `JanetCartan.PhysicalPairs.exists_physical_history_reconstruction_entry_profiles
          #[n,G,get `b,get `R,get `b_pos,get `b_lt_R,hR,base[25]!,base[26]!,base[27]!,
            reserve,base[28]!,base[29]!,hreserve,base[31]!]
        let ex ← save `exists_profiles params profile
        let nativeS ← save `profile_threshold params (← mkAppM ``Classical.choose #[ex]) true
        let spec ← mkAppM ``Classical.choose_spec #[ex]
        let hNative ← save `profile_threshold_ge_two params (.proj ``And 0 spec)
        let exC := .proj ``And 1 spec
        let _C ← save `C params (← mkAppM ``Classical.choose #[exC]) true
        let cspec ← mkAppM ``Classical.choose_spec #[exC]
        discard <| save `C_nonneg params (.proj ``And 0 cspec)
        let profileContinuation := .proj ``And 1 cspec
        let oldS := app (current ++ `S) base
        let S ← save `S params (← mkAppM ``Max.max #[oldS,nativeS]) true
        let hCurrent ← save `current_threshold params (← mkAppM `le_max_left #[oldS,nativeS])
        let hProfile ← save `reconstruction_threshold params (← mkAppM `le_max_right #[oldS,nativeS])
        discard <| save `hS params (← mkAppM `le_trans #[hNative,hProfile])
        withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
          withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀]) fun hR₀ => do
            let hNative ← mkAppM `le_trans #[hCurrent,hR₀]
            let hRec ← mkAppM `le_trans #[hProfile,hR₀]
            let cp := base ++ #[R₀,hNative]
            let native := app (current ++ `normalized_solver) cp
            forallBoundedTelescope (← inferType native) (some 4) fun history _ => do
              unless history.size == 4 do throwError "original reconstruction: changed physical history spine"
              let now := params ++ #[R₀,hR₀] ++ history
              let strong := cp ++ history
              let some value := (← getConstInfo (current ++ `normalized_solver)).value? (allowOpaque := true)
                | throwError "original reconstruction: missing native solver body"
              let weak ← Core.betaReduce (value.beta strong)
              unless weak.isAppOfArity (reg ++ `Current.normalized_solver) 38 do
                throwError "original reconstruction: lost same weak38 current"
              let F := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.F weak.getAppArgs
              let physicalF ← mkAppM `JanetCartan.RevisedGlobal.finiteMap
                #[← mkAppM `JanetCartan.FlatReference.map #[G],history[1]!]
              unless ← isDefEq F physicalF do
                throwError "original reconstruction: finite-map producer differs from actual uncut response"
              let actual ← save `F now F true
              discard <| save `same_finite_map now (← mkEqRefl physicalF) false
                (some (← mkEq actual physicalF))
              let h := mkAppN profileContinuation (#[R₀,hRec] ++ history)
              let type ← inferType h
              let renamed := type.replace fun e => if e == physicalF then some actual else none
              let h ← save `profiles now h false (some renamed)
              for (label,jointLabel,proof) in #[
                  (`value_entries,`joint_value_entries,Expr.proj ``And 0 h),
                  (`derivative_entries,`joint_derivative_entries,Expr.proj ``And 0 (.proj ``And 1 h)),
                  (`source_entries,`joint_source_entries,Expr.proj ``And 1 (.proj ``And 1 h))] do
                let entry ← save label now proof
                let joint ← forallBoundedTelescope (← inferType entry) (some 2) fun indices _ => do
                  unless indices.size == 2 do throwError "original reconstruction: changed coefficient entry indices"
                  let certificate := mkAppN entry indices
                  let hjoint ← mkAppM
                    `JanetCartan.PhysicalPrimary.OriginalReconstructionJoint.spatial_reconstruction_joint_profile_with_reserve
                    #[.proj ``And 0 certificate,.proj ``And 1 certificate]
                  mkLambdaFVars indices hjoint
                discard <| save jointLabel now joint
  logInfo "actual original34 reconstruction profile: native physical Schwartz history, threshold/profile before history, same weak38 uncut finite map, all value/derivative/source entries with exact reserve; no torus history or response-success input"

end JanetCartan.PhysicalPrimary.OriginalReconstructionProfilesTemplate
end
