module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Exact native support/footprint projections for the retarded constructor.
There is no new mask, flow, source interval, regular family or response bound. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedGeometryTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected
private def ns := `JanetCartan.PhysicalPrimary.OriginalRetardedGeometry

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

/-- Source support is the small native bump; the entire actual elapsed interval
is retained inside the critical window of radius maskRadius. -/
elab "retain_original_retarded_source_geometry" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `Sector.fact8)).type (some 24) fun x _ => do
    unless x.size == 24 do throwError "native retarded support: expected original23 and one original sector"
    let fixed := x[:23].toArray
    let sec (q : Name) := mkAppN (mkConst (regular ++ `Sector ++ q)) x
    let c := sec `chart
    let idx ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[c]
    let hs := mkAppN (mkConst (regular ++ `source_input_plateau)) fixed
    let box ← mkAppM (ns ++ `physical_source_preimage_subset) #[idx, hs, sec `fact8]
    discard <| store (ns ++ `source_in_box) x box
    let hr ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.maskRadius_pos #[c]
    let times ← mkAppM (ns ++ `native_mask_time_interval) #[hr, sec `fact0]
    discard <| store (ns ++ `full_elapsed_in_mask_window) x (.proj ``And 0 times)
    discard <| store (ns ++ `mask_window_in_original_stationary_window) x (.proj ``And 1 times)
  logInfo "native chi2 source in every actual physical retarded box; full elapsed interval unchanged and covered by the original stationary window"

/-- The original protection certificate puts the whole closed elapsed box in
both the original physical source compact and the original primary ball. -/
elab "retain_original_retarded_physical_footprints" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `Sector.fact8)).type (some 24) fun x _ => do
    let d := x[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := x[1]!
    let source := #[n] ++ x[1:21].toArray
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n, hn, source[20]!]
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (source.set! 20 cap)
    let hr := mkAppN (mkConst (protectedNS ++ `fact2)) source
    let screened ← mkAppM (regular ++ `screened_pos) #[hn, hr, hμ]
    let core ← mkAppM (regular ++ `core_spec) #[hn, screened]
    let coreAll := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 core))
    let sec (q : Name) := mkAppN (mkConst (regular ++ `Sector ++ q)) x
    let c := sec `chart
    let idx ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[c]
    let radius ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.rootRadius #[c]
    let protect := mkAppN (mkConst (regular ++ `fact11)) x
    let rootData := part protect 8
    let T := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.T) #[n, hn]
    forallBoundedTelescope (← inferType T) (some 1) fun patch _ => do
      let a := patch[0]!
      let params := x.push a
      let corePair := mkApp coreAll a
      for (label, sub) in [(Name.mkSimple "source", .proj ``And 0 corePair),
          (Name.mkSimple "primary", .proj ``And 1 corePair)] do
        forallBoundedTelescope (← inferType rootData) (some 2) fun w _ => do
          let physical := .proj ``And 0 (.proj ``And 1 (mkAppN rootData w))
          let physicalType ← inferType physical
          unless physicalType.isAppOfArity ``Membership.mem 5 do
            throwError "native root footprint: expected the actual physical membership certificate"
          let point := physicalType.appArg!
          let image := mkAppN sub #[point, physical]
          let hroot ← mkLambdaFVars w image
          let hroot ← store (ns ++ Name.mkSimple s!"root_in_{label}") params hroot
          let target := (← inferType image).getAppArgs[3]!
          let box := mkAppN (mkConst `JanetCartan.ResponseTransfer.RetainedFactors.retained_primary_physical_buffer)
            #[d, idx, sec `z, sec `εcarrier, radius, sec `fact3, target, hroot]
          discard <| store (ns ++ Name.mkSimple s!"box_in_{label}") params box
  logInfo "native protected whole-box footprints lie in the original source compact and primary ball for every sector and original patch"

end JanetCartan.PhysicalPrimary.OriginalRetardedGeometryTemplate
