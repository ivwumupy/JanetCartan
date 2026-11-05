module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! The actual original whole-box germ is the pullback of the single original
physical phase cutoff; its source is the checked native full-box footprint. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedWholeTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

elab "retain_original_whole_box_phase_germ" : command => liftTermElabM do
  let regular := `JanetCartan.PhysicalInitialization.OriginalRegular
  let geometry := `JanetCartan.PhysicalPrimary.OriginalRetardedGeometry
  let ns := `JanetCartan.PhysicalPrimary.OriginalRetardedWhole
  forallBoundedTelescope (← getConstInfo (geometry ++ `box_in_source)).type (some 25) fun x _ => do
    unless x.size == 25 do throwError "native whole phase germ: expected original23 + sector + original patch"
    let fixed := x[:23].toArray
    let s := fixed.push x[23]!
    let a := x[24]!
    let chart := mkAppN (mkConst (regular ++ `Sector.chart)) s
    let idx ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[chart]
    let foot := mkAppN (mkConst (geometry ++ `box_in_source)) x
    let ft := (← inferType foot).getAppArgs
    unless ft.size == 5 do throwError "native whole phase germ: full physical footprint is not MapsTo"
    let Y := ft[3]!
    let X := ft[4]!
    let original := #[mkApp (mkConst ``Nat.succ) x[0]!,x[1]!,a]
    let V := mkAppN (mkConst (regular ++ `wholeWindow)) original
    let χ := mkAppN (mkConst (regular ++ `Phase.χ)) (fixed.push a)
    let germ := mkAppN (mkConst (regular ++ `Phase.whole_germ)) (fixed.push a)
    let proof := mkAppN (mkConst (ns ++ `whole_germ_pullback)) #[x[0]!,idx,X,Y,V,χ,foot,germ]
    discard <| store (ns ++ `whole_χp_germ) x proof
  logInfo "actual single physical phase cutoff has germ ONE on the entire original carrier box times closure of the WHOLE original measurement window"

end JanetCartan.PhysicalPrimary.OriginalRetardedWholeTemplate
