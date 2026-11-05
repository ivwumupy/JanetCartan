module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtection
public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public meta import Lean

/-!
# The colored protection on the literal task-26 sampling index

The original22 sampling prefix passes ONLY `samplingCappedExtra` into the
ordinary original21 colored factory. Its retained OriginalProtected parent
then applies `strongCappedExtra` exactly once. The resulting index is checked
against the literal OriginalWeights.Index; the radii, weights and source
objects are not identified with any raw or independently selected choices.
All values below are aliases/projections of the SAME cached eta/k packet.
Consumers: the actual R(i,color) passed to OriginalRates and the native signed
family, `app:ch_waves:thm:sampling` and `app:rem:exhaustive-signed-pairs`.
The same explicit Ksource contains every beat-normalized colored pair vector;
it is not identified with the old angular compact. The parent still owes the
fixed-band validation and full-source chain compatibility.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
open Lean Meta Elab Command
open OriginalProtectedTemplate

/-- Keep the verified original22 sampling ABI, then expose the one ordinary
colored packet on its exact once-sampling/once-strong-capped original index. -/
elab "apply_retained_original_color_packet" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalInitialization.OriginalColoredProtection
  let old := `JanetCartan.PhysicalInitialization.OriginalProtected
  let ns := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
  let indexName := `JanetCartan.PhysicalSampling.OriginalWeights.Index
  let info ← getConstInfo indexName
  forallTelescope info.type fun all result => do
    unless all.size == 22 && result.isSort do
      throwError "sampling colored packet: expected exact original22 index ABI"
    let n := (← inferType all[1]!).getAppArgs.back!
    unless ← isDefEq n (mkApp (mkConst ``Nat.succ) all[0]!) do
      throwError "sampling colored packet: original physical dimension is not m+1"
    let merged := mkAppN (mkConst ``PhysicalSampling.samplingCappedExtra)
      #[all[0]!, all[1]!, all[2]!, all[21]!]
    let original := (#[n, all[1]!] ++ all[3:22].toArray).set! 20 merged
    unless original.size == 21 do
      throwError "sampling colored packet: original21 reconstruction failed"
    let params := original.push all[2]!
    let index := mkAppN (mkConst indexName) all
    let nativeIndex := mkAppN (mkConst (old ++ `Groups)) original
    unless ← isDefEq nativeIndex index do
      throwError "sampling colored packet: SAME once-capped original index mismatch"
    discard <| store (ns ++ `index_eq_original) all (← mkEqRefl index)
      false (some (← mkEq nativeIndex index))
    let C ← mkAppM ``OriginalColoredProtection.Color #[all[2]!]
    let groupType ← mkAppM ``Prod #[index, C]
    let nativeGroups := mkAppN (mkConst (source ++ `Groups)) params
    unless ← isDefEq nativeGroups groupType do
      throwError "sampling colored packet: colored index is not OriginalWeights.Index times Color"
    let groups ← store (ns ++ `Groups) all groupType true
    let mut replacements : Array (Expr × Expr) := #[(nativeGroups, groups)]
    for name in #[`eta, `k, `Rcolor, `Scolor, `family, `aColor, `AColor, `assign, `Ksource] do
      let value := mkAppN (mkConst (source ++ name)) params
      let target := (← inferType value).replace fun e =>
        replacements.findSome? fun pair => if e == pair.1 then some pair.2 else none
      let retained ← store (ns ++ name) all value true (some target)
      replacements := replacements.push (value, retained)
    for name in #[`eta_pos, `eta_le_quarter, `scale_ge_one, `scale_injective,
        `radial_ge_one, `radial_injective, `scale_separation, `protected_directions,
        `aColor_pos, `AColor_pos, `aColor_lt_AColor, `signed_bounds, `family_eq_currentGroup,
        `source_annulus, `source_compact, `source_normalized_interior, `normalized_pair_mem_source] do
      let proof := mkAppN (mkConst (source ++ name)) params
      let target := (← inferType proof).replace fun e =>
        replacements.findSome? fun pair => if e == pair.1 then some pair.2 else none
      discard <| store (ns ++ name) all proof false (some target)
    let Rcolor := mkAppN (mkConst (ns ++ `Rcolor)) all
    let k := mkAppN (mkConst (ns ++ `k)) all
    let oldR := mkAppN (mkConst (old ++ `R)) original
    withLocalDeclD `ic groups fun ic => do
      let lhs := mkApp Rcolor ic
      let rhs ← mkAppM ``HMul.hMul
        #[mkApp k (.proj ``Prod 1 ic), mkApp oldR (.proj ``Prod 0 ic)]
      let target ← mkEq lhs rhs
      let proof ← mkEqRefl lhs
      unless ← isDefEq (← inferType proof) target do
        throwError "sampling colored packet: Rcolor is not the literal k(color)*oldR(index)"
      discard <| store (ns ++ `radial_formula) all (← mkLambdaFVars #[ic] proof)
        false (some (← mkForallFVars #[ic] target))
  logInfo "original22 sampling coupling: sampling cap ONCE then original strong cap ONCE; exact OriginalWeights.Index, one shared color packet, native family and literal radial formula guards passed"

apply_retained_original_color_packet

end JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
end
