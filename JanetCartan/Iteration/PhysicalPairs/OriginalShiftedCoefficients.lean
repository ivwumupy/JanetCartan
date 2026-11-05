module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalTailPrice

/-! # The unchanged coefficient reserve, at the actual original inverse

Use the graph's actual `sectorLowOrder d` (not `sectorLowOrder d+d+2`).
Both full coefficient slots are those of its original strong normalized solver;
the extra fixed power is absorbed in `OriginalTailPrice.inverse_tail`.
Consumer: the actual signed Neumann remainder in `app:ch_regular:eq:inverse-remainder`.
-/
public meta section
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalShiftedCoefficients
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalShiftedCoefficients
private def tp := `JanetCartan.PhysicalPairs.OriginalTailPrice
private def sd := `JanetCartan.PhysicalPairs.OriginalSignedData
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def samples := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def par := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (h : Expr) : Nat → Expr | 0 => h | k+1 => down (.proj ``And 1 h) k
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
elab "pay_native_shifted_coefficients " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sd ++ `uncut)).type (some 49) fun p _ => do
    let b := p[:37].toArray
    let gf := (← inferType (a (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let raw := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily).value! (allowOpaque := true)).beta gf.getAppArgs
    let coeff := raw.getAppArgs.back!.getAppArgs
    let d := p[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let off := mkApp2 (mkConst ``Nat.add) d (mkNatLit 2)
    let fa := (← inferType (a (reg ++ `f) fix)).getAppArgs
    let r := a (reg ++ `normRadius) fix
    let R ← mkAppM ``HAdd.hAdd #[r,← mkNumeral (mkConst ``Real) 1]
    let reserve := coeff[28]!
    unless reserve.isAppOfArity `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder 1 do throwError "actual graph requires its unstrengthened finite sector baseline"
    if piece.getNat == 0 then
      let pf := a (tp ++ `coefficient_price) #[n,fa[2]!,r,R,a (par ++ `Native.norm_radius_pos) fix,← mkAppM `lt_add_one #[r],
        a (op ++ `AQ) coeff,a (op ++ `AB) coeff,a (op ++ `fact1) coeff,a (op ++ `fact2) coeff,reserve,off]
      discard <| store (ns ++ `original_price) b pf
      return
    let low := a (ns ++ `original_price) b
    let D ← mkAppM ``Classical.choose #[low]
    if piece.getNat == 1 then
      let name ← store (ns ++ `D) b D true
      let h := part (← mkAppM ``Classical.choose_spec #[low]) 0
      discard <| store (ns ++ `D_nonneg) b h false (some ((← inferType h).replace fun e => if e == D then some name else none))
      return
    let hi := a (hist ++ `measured_history) p
    let stat := b[:36].toArray ++ #[p[37]!,part hi 0] ++ p[39:43].toArray
    let now := ((← getConstInfo (samples ++ `projected)).value! (allowOpaque := true)).beta stat
    unless now.isAppOfArity (reg ++ `Current.projected) 38 do throwError "shifted coefficient source lost actual38 normalized current"
    let w := now.getAppArgs
    let L := a `JanetCartan.currentCoefficientScale #[p[37]!,p[39]!]
    let hL ← mkAppM (par ++ `coefficient_scale_one_le_of_two_le) #[← mkAppM ``le_trans #[a (op ++ `fact0) coeff,part hi 1],p[39]!]
    if piece.getNat == 2 then
      let hw := part (a (hist ++ `native_window) p) 0
      let gap ← mkAppM ``le_trans #[down hi 5,part hw 3]
      discard <| store (ns ++ `current_window) p (← mkAppM ``And.intro #[hL,gap])
      return
    let cur (k : Name) := a (reg ++ `Current ++ k) w
    let pair := down (a (op ++ `continuation) (coeff ++ #[p[37]!,part hi 1] ++ p[39:43].toArray)) 2
    let K ← mkAppM `Metric.closedBall #[fa[2]!,R]
    let profiles := mkAppN pair #[K,← mkAppM `ProperSpace.isCompact_closedBall #[fa[2]!,R]]
    let bound := mkAppN (down (← mkAppM ``Classical.choose_spec #[low]) 1) #[cur `Q,cur `B,cur `hQ,cur `hB,L,hL,part profiles 0,down profiles 1]
    let name := a (ns ++ `D) b
    discard <| store (ns ++ `actual_bound) p bound false (some ((← inferType bound).replace fun e => if e == D then some name else none))
pay_native_shifted_coefficients 0
pay_native_shifted_coefficients 1
pay_native_shifted_coefficients 2
pay_native_shifted_coefficients 3
end JanetCartan.PhysicalPairs.OriginalShiftedCoefficients
end
