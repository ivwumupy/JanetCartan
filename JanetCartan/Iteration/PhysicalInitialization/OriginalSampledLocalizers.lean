module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledFactorData
public meta import Lean

/-!
# Measured signed leakage on every original physical history

Apply the fixed native transport/mask/cost construction to the actual full
matrix coefficients and to the genuine Fourier right/left realizations.
This is the signed-letter input of `app:ch_regular:lem:finite-chain`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledFactors
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def base := `JanetCartan.PhysicalInitialization.OriginalSampledFactors
private def termNS := `JanetCartan.PhysicalInitialization.OriginalSampledTerminal
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def app (k : Name) (x : Array Expr) := mkAppN (mkConst k) x
private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def field (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
private def named (key : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec opts : Expr → Array (Option Expr)
    | .forallE n _ body _ => #[(known.find? (·.1 == n)).map (·.2)] ++ opts body
    | .mdata _ e => opts e
    | _ => #[]
  mkAppOptM key (opts (← getConstInfo key).type)

run_cmd liftTermElabM <| withTransparency .reducible do
  let poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
  let op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
  let leak := `JanetCartan.PhysicalInitialization.OriginalSampledLeakage
  forallBoundedTelescope (← getConstInfo (termNS ++ `before_history)).type (some 37) fun x _ => do
    let factors ← factorsFor x
    let coeff := factors[:33].toArray
    let fixed := coeff[:23].toArray
    let d := x[0]!
    let g := fixed ++ x[24:26].toArray ++ x[27:36].toArray
    let weak := fixed ++ #[g[25]!,app (reg ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let hargs := #[d,coeff[25]!,coeff[29]!,app (reg ++ `Graph.S) g,app (op ++ `S) coeff]
    let I := app (poly ++ `Histories) hargs
    let stat (k : Name) := app (reg ++ k) fixed
    let fa := (← inferType (stat `f)).getAppArgs
    let KQ ← mkAppM `Metric.closedBall #[fa[2]!,fa[3]!]
    let hKQ ← mkAppM `ProperSpace.isCompact_closedBall #[fa[2]!,fa[3]!]
    withLocalDeclD `order (mkConst ``Nat) fun order => withLocalDeclD `i I fun i => do
      let raw ← mkAppM ``Subtype.val #[i]
      let idx (k : Name) := app (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
      let proof := app (poly ++ `admitted_data) (hargs ++ #[app (op ++ `fact0) coeff,i])
      let hGraph := field proof 0
      let hist := #[idx `length,idx `u,idx `ell,field proof 2]
      let tail := #[idx `R₀,hGraph] ++ hist
      let hreg := app (reg ++ `Graph.regular_reached) (g ++ #[idx `R₀,hGraph])
      let w := weak ++ #[idx `R₀,hreg] ++ hist
      let cur (name : Name) := app (reg ++ `Current ++ name) w
      let maskType ← inferType (app (termNS ++ `on_actual_history) (x ++ tail))
      unless maskType.isAppOfArity (termNS ++ `Packet.onCurrent) 66 do throwError "not the current's native reflected masks"
      let ms := maskType.getAppArgs
      let mask (z : Name) := app (base ++ `Masks ++ z) ms
      let mf (z : Name) := app (base ++ `MaskFacts ++ z) ms
      logInfo "Actual same-current reflected masks identified."
      let hQ := app (base ++ `NativeGeometry.Q_smooth) w
      let hB := app (base ++ `NativeGeometry.B_smooth) w
      let hmap := app (base ++ `NativeGeometry.range) w
      let low := mkAppN (cur `fact2) #[KQ,hKQ]
      let hp := app (leak ++ `current_coefficients) (coeff ++ #[idx `R₀,field proof 1] ++ hist ++ #[KQ,hKQ,idx `K,down proof 5])
      let now := factors ++ #[cur `Q,hQ,hmap,field low 0,cur `B,hB,field low 1,cur `Φ,cur `C,cur `G,cur `Op,cur `fact4,
        order,coeff[28]!,app ``sector_ge_ten #[d],idx `K,idx `lam,field proof 3,field proof 4,.proj ``And 0 hp,.proj ``And 1 hp]
      logInfo "Checking the complete native signed leakage on this current."
      discard <| store (base ++ `on_actual_history) (x ++ #[order,i]) (app (base ++ `Proven.at_current) now)
      logInfo "Native signed coefficient/phase input checked."
      let hiProp := Expr.proj ``Subtype 1 i
      let hρ := field hiProp 2
      logInfo "Actual frequency admission retained."
      let qr := ms ++ #[idx `lam,hρ]
      let ops (z : Name) := app (base ++ `Operators ++ z) qr
      let xi := x.push i
      discard <| store (base ++ `actual_masks) xi (mask `m) true
      discard <| store (base ++ `actual_right) xi (ops `right) true
      discard <| store (base ++ `actual_left) xi (ops `left) true
      logInfo "Actual right and left Fourier localizers retained."
      discard <| store (base ++ `actual_realization) xi (app (base ++ `Proven.realization) qr)
      logInfo "Actual Fourier realization and low norms checked."
      discard <| store (base ++ `actual_even) xi (mask `fact1)
      discard <| store (base ++ `actual_first_buffer) xi (mask `fact4)
      discard <| store (base ++ `actual_first_plateau) xi (mf `first_plateau)
      discard <| store (base ++ `actual_mask_jets) xi (mask `fact8)
      discard <| store (base ++ `actual_adjacent_and_terminal) xi
        (app (base ++ `Proven.quantization) (qr ++ #[idx `K,field proof 3,field proof 4]))
      logInfo "Actual localizers, first plateau and quantization checked."
end JanetCartan.PhysicalInitialization.OriginalSampledFactors
end
