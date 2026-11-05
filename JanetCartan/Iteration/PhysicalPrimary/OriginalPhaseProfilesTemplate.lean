module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the checked physical-history phase producer to the original25
source reference, prescribed extension and ONE already selected physical cutoff.
No phase, current frame, coefficient admission or regular inverse is reselected. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhaseProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhaseProfiles

/-- The same full physical phase receives one threshold and all-order profile
before any current coefficient field, physical history or source frequency. -/
elab "retain_original_whole_phase_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `Gref)).type (some 25) fun fixed _ => do
    unless fixed.size == 25 do throwError "original phase profiles: expected original25 reference"
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let source := #[n] ++ fixed[1:21].toArray
    let G := mkAppN (mkConst (regular ++ `Gref)) fixed
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) source[:18].toArray
    let orig (name : Name) := mkAppN (mkConst (original ++ name)) #[n,hn]
    let hR ← mkAppM (regular ++ `radius_lt_same_chart) #[same,orig `R_lt_chartRadius]
    let cutoff := mkAppN (mkConst (regular ++ `Phase.χ)) fixed[:23].toArray
    forallBoundedTelescope (← inferType cutoff) (some 1) fun patch _ => do
      let a := patch[0]!
      let phase (name : Name) := mkAppN (mkConst (regular ++ `Phase ++ name)) (fixed[:23].toArray.push a)
      let raw := mkAppN (mkConst (ns ++ `exists_prescribed_cutoff_phase_profiles))
        #[fixed[0]!,hn,a,phase `χ,phase `fact0,phase `fact2,phase `fact3,G,hR,
          fixed[4]!,fixed[5]!,fixed[6]!]
      forallBoundedTelescope (← inferType raw) (some 9) fun order _ => do
        unless order.size == 9 do throwError "original phase profiles: expected exact nine numeric inputs"
        let params := fixed ++ patch ++ order
        let actual ← store (ns ++ `exists_profiles) params (mkAppN raw order)
        select ns params actual
  logInfo "native original25 phase jets: SAME prescribed physical chi and extended current, full Xsrc x Csrc, exact zero coordinates, S/Aphase before every history"

/-- The exact future PDO box lies in the pre-existing whole source set. The
original physical radius and full parameter window are only restricted. -/
elab "retain_original_word_phase_box" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `f)).type (some 23) fun fixed _ => do
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let source := #[n] ++ fixed[1:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,source[20]!]
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (source.set! 20 capped)
    let hr := mkAppN (mkConst (protectedNS ++ `fact2)) source
    let screened ← mkAppM (regular ++ `screened_pos) #[hn,hr,hμ]
    let core ← mkAppM (regular ++ `core_spec) #[hn,screened]
    let coreAll := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 core))
    logInfo "phase-box native core radius closed"
    let χ := mkAppN (mkConst (regular ++ `Phase.χ)) fixed
    forallBoundedTelescope (← inferType χ) (some 1) fun patch _ => do
      let a := patch[0]!
      let f := mkAppN (mkConst (regular ++ `f)) fixed
      let hcore := .proj ``And 0 (mkApp coreAll a)
      let fa := (← inferType f).getAppArgs
      unless fa.size == 7 do throwError "original phase box: unexpected native family telescope"
      let h := mkAppN (mkConst (ns ++ `original_word_phase_box_subset))
        #[fixed[0]!,hn,a,fa[1]!,fa[3]!,fa[6]!,fa[4]!,fa[5]!,f,hcore]
      discard <| store (ns ++ `word_box_subset) (fixed ++ patch) h
  logInfo "original phase domain includes the unchanged closed3f-radius x closure wholeWindow; no source window or phase cutoff is shrunk"

/-- Use the SAME actual source frame, whose value is definitionally the native
extended projected stress. Only numeric phase reserves are added to the original
history spine; no phase estimate or frame admission remains as an input. -/
elab "apply_original_current_whole_phase_profiles" : command => liftTermElabM do
  let cur := regular ++ `Current
  let actual := ns ++ `Actual
  forallBoundedTelescope (← getConstInfo (cur ++ `sourceFrame)).type (some 32) fun native _ => do
    unless native.size == 32 do throwError "actual phase profiles: expected original32 prehistory inputs"
    let fixed := native[:25].toArray
    let cutoff := mkAppN (mkConst (regular ++ `Phase.χ)) native[:23].toArray
    forallBoundedTelescope (← inferType cutoff) (some 1) fun patch _ => do
      let rawPrefix := mkAppN (mkConst (ns ++ `exists_profiles))
        (fixed ++ patch ++ #[native[25]!,native[26]!,native[27]!])
      forallBoundedTelescope (← inferType rawPrefix) (some 1) fun reserve _ => do
        let rawPrefix := mkAppN rawPrefix (reserve ++ #[native[28]!,native[29]!])
        forallBoundedTelescope (← inferType rawPrefix) (some 2) fun inequalities _ => do
          let params := native ++ patch ++ reserve ++ inequalities
          let profileParams := fixed ++ patch ++ #[native[25]!,native[26]!,native[27]!,reserve[0]!,
            native[28]!,native[29]!,inequalities[0]!,inequalities[1]!,native[31]!]
          let get (name : Name) := mkAppN (mkConst (ns ++ name)) profileParams
          let Sphase := get `S
          let Scur := mkAppN (mkConst (regular ++ `History.S)) native
          let S ← store (actual ++ `S) params (← mkAppM ``max #[Scur,Sphase]) true
          let hcur ← store (actual ++ `current_threshold) params (← mkAppM `le_max_left #[Scur,Sphase])
          let hphase ← store (actual ++ `phase_threshold) params (← mkAppM `le_max_right #[Scur,Sphase])
          discard <| store (actual ++ `hS) params (← mkAppM `le_trans #[get `fact0,hphase])
          discard <| store (actual ++ `Aphase) params (get `Aphase) true
          discard <| store (actual ++ `Aphase_nonneg) params (get `fact1)
          withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
            withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S,R₀]) fun hR₀ => do
              let hncur ← mkAppM `le_trans #[hcur,hR₀]
              let hnphase ← mkAppM `le_trans #[hphase,hR₀]
              let frameBase := mkAppN (mkConst (cur ++ `sourceFrame)) (native ++ #[R₀,hncur])
              forallBoundedTelescope (← inferType frameBase) (some 4) fun history _ => do
                unless history.size == 4 do throwError "actual phase profiles: expected physical stage/u/ell/admissibility"
                let frameBase := mkAppN frameBase history
                forallBoundedTelescope (← inferType frameBase) (some 1) fun sector _ => do
                  let all := params ++ #[R₀,hR₀] ++ history ++ sector
                  let currentParams := native ++ #[R₀,hncur] ++ history ++ sector ++ patch
                  let frame := mkAppN frameBase (sector ++ patch)
                  let hframe := mkAppN (mkConst (cur ++ `sourceFrame_val)) currentParams
                  let phase := mkApp (get `continuation) frame
                  let hsmooth := .proj ``And 0 phase
                  let hgerm := .proj ``And 0 (.proj ``And 1 phase)
                  let bounds := .proj ``And 1 (.proj ``And 1 phase)
                  let bounds := mkAppN bounds (#[R₀,hnphase] ++ history ++ #[hframe])
                  let φ := (← inferType hsmooth).appArg!
                  discard <| store (actual ++ `φ) all φ true
                  let germBounds := mkAppN (mkConst ``And.intro)
                    #[← inferType hgerm,← inferType bounds,hgerm,bounds]
                  let both := mkAppN (mkConst ``And.intro)
                    #[← inferType hsmooth,← inferType germBounds,hsmooth,germBounds]
                  discard <| store (actual ++ `profiles) all both
                  let n := mkApp (mkConst ``Nat.succ) native[0]!
                  let hsubset := mkAppN (mkConst (ns ++ `word_box_subset)) (native[:23].toArray ++ patch)
                  let sets := (← inferType hsubset).getAppArgs
                  let small := sets[sets.size-2]!
                  let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R₀,history[0]!]
                  let restricted := mkAppN (mkConst (ns ++ `restrict_original_joint_profiles))
                    #[native[0]!,native[1]!,patch[0]!,small,hsubset,φ,get `Aphase,scale,reserve[0]!,hsmooth,bounds]
                  let restricted ← store (actual ++ `word_profiles) all restricted
                  let physicalBall := small.getAppArgs[small.getAppArgs.size-2]!
                  let radius := physicalBall.appArg!
                  withLocalDeclD `index (mkApp (mkConst ``Fin) n) fun index => do
                    let coordinates := mkAppN (mkConst (ns ++ `original_coordinate_joint_profiles))
                      #[native[0]!,native[1]!,patch[0]!,index,radius,φ,get `Aphase,scale,reserve[0]!,hsmooth,restricted]
                    discard <| store (actual ++ `coordinate_word_profiles) (all.push index) coordinates
                  let domains := mkAppN (mkConst (protectedNS ++ `source_domains)) #[n,native[1]!,patch[0]!]
                  let compact ← mkAppM `IsCompact.prod #[.proj ``And 0 domains,.proj ``And 0 (.proj ``And 1 domains)]
                  discard <| store (actual ++ `profile_domain_compact) params compact
  logInfo "actual original current phase profiles: original36 static inputs, max threshold BEFORE R0/history, literal sourceFrame value closes extended F by rfl, SAME phase and all-order reserve on full and word domains"

end JanetCartan.PhysicalPrimary.OriginalPhaseProfilesTemplate
