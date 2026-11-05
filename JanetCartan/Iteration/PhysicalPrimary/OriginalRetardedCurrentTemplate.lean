module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the existing graph/frame threshold to the actual common incidence
margin, retaining the original current and full normalized inverse. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedCurrentTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def inc := `JanetCartan.PhysicalPrimary.OriginalIncidence
private def ns := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent

/-- The strong scale/current hypotheses are conclusions of the original
construction. Only its already proved scalar thresholds are restricted. -/
elab "retain_original_current_at_incidence_margin" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (inc ++ `source_interval)).type (some 25) fun ref _ => do
    unless ref.size == 25 do throwError "native retarded current: expected original23 and strong source scale"
    let fixed := ref[:23].toArray
    let γ := mkAppN (mkConst (inc ++ `Common.γ)) fixed
    let hγ := mkAppN (mkConst (inc ++ `Common.fact0)) fixed
    let gx := fixed ++ #[γ,hγ] ++ ref[23:25].toArray
    let hσ ← store (ns ++ `regular_scale) ref
      (mkAppN (mkConst (regular ++ `Graph.regular_scale)) gx)
    let rr := fixed ++ #[ref[23]!,hσ]
    discard <| store (ns ++ `Gref) ref (mkAppN (mkConst (regular ++ `Gref)) rr) true
    let S := mkAppN (mkConst (regular ++ `Graph.S)) gx
    forallBoundedTelescope (← inferType S) (some 7) fun order _ => do
      unless order.size == 7 do throwError "native retarded current: expected seven original history-order parameters"
      let prior := ref ++ order
      let gb := gx ++ order
      let rb := rr ++ order
      let s ← store (ns ++ `S) prior (mkAppN S order) true
      discard <| store (ns ++ `hS) prior (mkAppN (mkConst (regular ++ `Graph.hS)) gb)
      withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[s,R₀]) fun hR₀ => do
          let gr := gb ++ #[R₀,hR₀]
          let hp ← store (ns ++ `regular_reached) (prior ++ #[R₀,hR₀])
            (mkAppN (mkConst (regular ++ `Graph.regular_reached)) gr)
          let actualPrefix := rb ++ #[R₀,hp]
          let solver := mkAppN (mkConst (regular ++ `Current.normalized_solver)) actualPrefix
          forallBoundedTelescope (← inferType solver) (some 4) fun data _ => do
            unless data.size == 4 do throwError "native retarded current: expected unchanged n/u/ell/history"
            let p := prior ++ #[R₀,hR₀] ++ data
            let cp := actualPrefix ++ data
            let gp := gr ++ data
            let get (name : Name) := mkAppN (mkConst (regular ++ `Current ++ name)) cp
            for name in [`Q,`B,`Φ,`C,`G,`Op,`W₁,`Inv] do
              discard <| store (ns ++ name) p (get name) true
            for name in [`hQ,`hB,`fact0,`fact1,`fact2,`fact3,`fact4] do
              discard <| store (ns ++ name) p (get name)
            discard <| store (ns ++ `normalized_solver) p (mkAppN solver data)
            let margin ← store (ns ++ `frame_margin) p
              (mkAppN (mkConst (regular ++ `Graph.current_frame_margin)) gp)
            let dim := mkApp (mkConst ``Nat.succ) ref[0]!
            let patchType := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalPatchIndex) #[dim,ref[1]!]
            withLocalDeclD `a patchType fun a => do
              let pa := p.push a
              let wa := #[ref[0]!,ref[1]!,a]
              let hwhole := mkApp (mkAppN (mkConst (inc ++ `Common.continuation)) fixed) a
              let hT := mkAppN (mkConst (inc ++ `Whole.fact3)) wa
              let hγT ← mkAppM `le_trans #[hwhole,hT]
              let frame := mkAppN (mkConst (regular ++ `frameInOriginalPatch))
                #[ref[0]!,ref[1]!,a,get `Q,get `hQ,γ,margin,hγT]
              let frame ← store (ns ++ `sourceFrame) pa frame true
              discard <| store (ns ++ `sourceFrame_val) pa (← mkEqRefl (get `Q)) false
                (some (← mkEq (← mkAppM `Subtype.val #[frame]) (get `Q)))
              let band := mkApp (mkAppN (mkConst (inc ++ `Whole.continuation)) wa) frame
              let .forallE _ needed _ _ ← whnf (← inferType band)
                | throwError "native full gradient band lost its coefficient tolerance input"
              let norm := needed.appFn!.appArg!
              let na := norm.getAppArgs
              unless norm.isAppOf `JanetCartan.cNorm && na.size ≥ 3 do
                throwError "native full gradient band coefficient norm changed"
              let K := na[na.size-3]!
              let low ← mkAppM `lt_of_lt_of_le #[mkApp margin K,hwhole]
              discard <| store (ns ++ `whole_gradient_range) pa (mkApp band low)
  logInfo "ONE common native incidence/graph/frame source interval and prehistory S; unchanged original current, complete inverse, sector-independent source frame and full original source gradient band"

end JanetCartan.PhysicalPrimary.OriginalRetardedCurrentTemplate
