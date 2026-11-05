module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphData

/-!
# The actual original graph coefficient price for primary strain

The native gain has offset `d+2` above `sectorLowOrder d`. Apply the existing
coefficient-price theorem to the full Q/B profiles on the original norm ball.
The fixed loss is paid by `OriginalTailPrice.inverse_tail`, not by raising the
history reserve or changing the inverse (`app:ch_regular:eq:inverse-remainder`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
open Lean Meta Elab Command

elab "price_original_primary_graph_coefficients " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "primary graph coefficients: unknown mode"
  withGraph fun x g weak coeff graph => do
    let fixed := g[:23].toArray
    let d := x[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let offset := mkApp2 (mkConst ``Nat.add) d (mkNatLit 2)
    let r := app (regular ++ `normRadius) fixed
    let R ← mkAppM ``HAdd.hAdd #[r,← mkNumeral (mkConst ``Real) 1]
    let f := app (regular ++ `f) fixed
    let center := (← inferType f).getAppArgs[2]!
    if mode.getNat == 0 then
      let price := app `JanetCartan.PhysicalPairs.OriginalTailPrice.coefficient_price
        #[n,center,r,R,app (native ++ `norm_radius_pos) fixed,← mkAppM ``lt_add_one #[r],
          app (operators ++ `AQ) coeff,app (operators ++ `AB) coeff,
          app (operators ++ `fact1) coeff,app (operators ++ `fact2) coeff,coeff[28]!,offset]
      discard <| save `coefficient_price x price
      return
    let price := app (root ++ `coefficient_price) x
    let D ← mkAppM ``Classical.choose #[price]
    if mode.getNat == 1 then
      discard <| save `Dcoeff x D true
      return
    if mode.getNat == 4 then
      let named := app (root ++ `Dcoeff) x
      let hD := part (← mkAppM ``Classical.choose_spec #[price]) 0
      discard <| save `Dcoeff_nonneg x hD false
        (some ((← inferType hD).replace fun e => if e == D then some named else none))
      return
    withLocalDeclD `originalHistory graph fun i => do
      let (w,L,_,data,window) ← currentAt g weak coeff i
      if mode.getNat == 3 then
        discard <| save `coefficient_window (x.push i) window
        return
      let cur (key : Name) := app (regular ++ `Current ++ key) w
      let pair := down (app (operators ++ `continuation)
        (coeff ++ #[w[32]!,part data 1] ++ w[34:].toArray)) 2
      let K ← mkAppM ``Metric.closedBall #[center,R]
      let profiles := mkAppN pair #[K,← mkAppM `ProperSpace.isCompact_closedBall #[center,R]]
      let proof := mkAppN (down (← mkAppM ``Classical.choose_spec #[price]) 1)
        #[cur `Q,cur `B,cur `hQ,cur `hB,L,part window 0,part profiles 0,down profiles 1]
      let named := app (root ++ `Dcoeff) x
      discard <| save `coefficient_bound (x.push i) proof false
        (some ((← inferType proof).replace fun e => if e == D then some named else none))

price_original_primary_graph_coefficients 0
price_original_primary_graph_coefficients 1
price_original_primary_graph_coefficients 4
price_original_primary_graph_coefficients 2
price_original_primary_graph_coefficients 3

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
end
