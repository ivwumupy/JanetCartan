module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Reuse the actual coefficient and physical phase profiles at one prehistory
maximum, with separate history, coefficient and phase reserves. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalWordProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def current := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def coeff := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def phase := `JanetCartan.PhysicalPrimary.OriginalPhaseProfiles
private def gradient := `JanetCartan.PhysicalPrimary.OriginalWordGradient
private def ns := `JanetCartan.PhysicalPrimary.OriginalWordProfiles

elab "retain_original_joint_word_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `S)).type (some 32) fun native _ => do
    unless native.size == 32 do throwError "native word profiles: original32 prehistory spine changed"
    let fixed := native[:23].toArray
    let ref := native[:25].toArray
    let regularScale := mkAppN (mkConst (current ++ `regular_scale)) ref
    let rr := fixed ++ #[native[23]!,regularScale]
    let cutoff := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalRegular.Phase.χ) fixed
    forallBoundedTelescope (← inferType cutoff) (some 1) fun patch _ => do
      let common := #[native[25]!,native[26]!,native[27]!]
      let coefficientBase := mkAppN (mkConst (coeff ++ `exists_profiles)) (rr ++ common)
      forallBoundedTelescope (← inferType coefficientBase) (some 1) fun reserveCoeff _ => do
        let coefficientBase := mkAppN coefficientBase (reserveCoeff ++ #[native[28]!,native[29]!])
        forallBoundedTelescope (← inferType coefficientBase) (some 1) fun hCoeff _ => do
          let cp := rr ++ common ++ reserveCoeff ++ #[native[28]!,native[29]!] ++ hCoeff ++ #[native[31]!]
          let phaseBase := mkAppN (mkConst (phase ++ `exists_profiles)) (rr ++ patch ++ common)
          forallBoundedTelescope (← inferType phaseBase) (some 1) fun reservePhase _ => do
            let phaseBase := mkAppN phaseBase (reservePhase ++ #[native[28]!,native[29]!])
            forallBoundedTelescope (← inferType phaseBase) (some 2) fun hPhase _ => do
              let pp := rr ++ patch ++ common ++ reservePhase ++ #[native[28]!,native[29]!] ++ hPhase ++ #[native[31]!]
              let params := native ++ patch ++ reserveCoeff ++ hCoeff ++ reservePhase ++ hPhase
              unless cp.size == 33 && pp.size == 35 && params.size == 38 do
                throwError "native word profiles: separate-reserve prefixes changed"
              let cg (name : Name) := mkAppN (mkConst (coeff ++ name)) cp
              let pg (name : Name) := mkAppN (mkConst (phase ++ name)) pp
              let Sc := cg `S
              let Sp := pg `S
              let Sn := mkAppN (mkConst (current ++ `S)) native
              let joined ← mkAppM ``Max.max #[Sc,Sp]
              let S ← store (ns ++ `S) params (← mkAppM ``Max.max #[Sn,joined]) true
              let hn ← store (ns ++ `current_threshold) params (← mkAppM `le_max_left #[Sn,joined])
              let hjoin ← mkAppM `le_max_right #[Sn,joined]
              let hc ← store (ns ++ `coefficient_threshold) params
                (← mkAppM `le_trans #[← mkAppM `le_max_left #[Sc,Sp],hjoin])
              let hp ← store (ns ++ `phase_threshold) params
                (← mkAppM `le_trans #[← mkAppM `le_max_right #[Sc,Sp],hjoin])
              discard <| store (ns ++ `hS) params (← mkAppM `le_trans
                #[mkAppN (mkConst (current ++ `hS)) native,hn])
              for (name,value) in [(`AQ,cg `AQ),(`AB,cg `AB),(`Aphase,pg `Aphase)] do
                discard <| store (ns ++ name) params value true
              for (name,value) in [(`AQ_nonneg,cg `fact1),(`AB_nonneg,cg `fact2),(`Aphase_nonneg,pg `fact1)] do
                discard <| store (ns ++ name) params value
              withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
                withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀]) fun hR₀ => do
                  let hnR ← mkAppM `le_trans #[hn,hR₀]
                  let hcR ← mkAppM `le_trans #[hc,hR₀]
                  let hpR ← mkAppM `le_trans #[hp,hR₀]
                  let frame := mkAppN (mkConst (current ++ `sourceFrame)) (native ++ #[R₀,hnR])
                  forallBoundedTelescope (← inferType frame) (some 4) fun data _ => do
                    unless data.size == 4 do throwError "native word profiles: changed literal physical history"
                    let now := params ++ #[R₀,hR₀] ++ data
                    let cur := native ++ #[R₀,hnR] ++ data
                    let fr := mkAppN frame (data ++ patch)
                    let hv := mkAppN (mkConst (current ++ `sourceFrame_val)) (cur ++ patch)
                    let coefficients := mkAppN (cg `continuation) (#[R₀,hcR] ++ data)
                    discard <| store (ns ++ `coefficient_profiles) now coefficients
                    let profiles := mkApp (pg `continuation) fr
                    let smooth := Expr.proj ``And 0 profiles
                    let germ := Expr.proj ``And 0 (.proj ``And 1 profiles)
                    let bounds := mkAppN (.proj ``And 1 (.proj ``And 1 profiles)) (#[R₀,hpR] ++ data ++ #[hv])
                    let rawφ := (← inferType smooth).appArg!
                    let φ ← store (ns ++ `φ) now (mkAppN (mkConst (gradient ++ `φ)) (cur ++ patch)) true
                    for (name,value) in [(`phase_smooth,smooth),(`phase_germ,germ),(`phase_profiles,bounds)] do
                      let ty := (← inferType value).replace fun e => if e == rawφ then some φ else none
                      discard <| store (ns ++ name) now value false (some ty)
                    let subset := mkAppN (mkConst (phase ++ `word_box_subset)) (fixed ++ patch)
                    let sets := (← inferType subset).getAppArgs
                    let small := sets[sets.size-2]!
                    let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R₀,data[0]!]
                    let restricted := mkAppN (mkConst (phase ++ `restrict_original_joint_profiles))
                      #[native[0]!,native[1]!,patch[0]!,small,subset,φ,pg `Aphase,scale,reservePhase[0]!,smooth,bounds]
                    let restricted ← store (ns ++ `word_profiles) now restricted
                    let physicalBall := small.getAppArgs[small.getAppArgs.size-2]!
                    let radius := physicalBall.appArg!
                    withLocalDeclD `index (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) native[0]!)) fun index => do
                      let coordinates := mkAppN (mkConst (phase ++ `original_coordinate_joint_profiles))
                        #[native[0]!,native[1]!,patch[0]!,index,radius,φ,pg `Aphase,scale,reservePhase[0]!,smooth,restricted]
                      discard <| store (ns ++ `coordinate_word_profiles) (now.push index) coordinates
  logInfo "one common prehistory S with SAME canonical current, full Q/B and positive physical phase profiles; separate history/coefficient/phase reserves; all coordinate profiles use same Aphase, no sector/default/phase choice"

end JanetCartan.PhysicalPrimary.OriginalWordProfilesTemplate
