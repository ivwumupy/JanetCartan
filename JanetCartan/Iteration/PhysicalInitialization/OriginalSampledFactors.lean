module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledLocalizers
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
  forallBoundedTelescope (← getConstInfo (base ++ `on_actual_history)).type (some 39) fun p _ => do
    unless p.size == 39 do throwError "changed actual signed-current spine"
    let x := p[:37].toArray
    let order := p[37]!
    let i := p[38]!
    let t ← inferType (app (base ++ `on_actual_history) p)
    unless t.isAppOfArity (base ++ `Packet.at_current) 95 do
      throwError "expected the checked original signed-current packet"
    let now := t.getAppArgs
    -- Open only our transparent operator alias, never a proof or a choice.
    let rightInfo ← getConstInfo (base ++ `actual_right)
    let right := (mkAppN rightInfo.value! (x.push i)).headBeta
    unless right.isAppOfArity (base ++ `Operators.right) 68 do
      throwError "expected the same checked Fourier right realization"
    let qr := right.getAppArgs
    let ms := qr[:66].toArray
    let mask (k : Name) := app (base ++ `Masks ++ k) ms
    let mf (k : Name) := app (base ++ `MaskFacts ++ k) ms
    let ops (k : Name) := app (base ++ `Operators ++ k) qr
    let fixed := now[:23].toArray
    let fa := (← inferType (app (reg ++ `f) fixed)).getAppArgs
    let E ← inferType fa[2]!
    let univ := mkApp (mkConst `Set.univ [.zero]) E
    let measurable ← synthInstance (mkApp (mkConst `MeasurableSpace [.zero]) E)
    let hUniv ← named `MeasurableSet.univ #[(`α,E),(`m,measurable)]
    let maskFun (k : Name) : MetaM Expr := do
      let sm := app (`JanetCartan.PhysicalPrimary.OriginalSourceMasks ++ k) fixed
      pure (← inferType sm).appArg!
    let χ₂ ← maskFun `χ₂_smooth
    let χ₃ ← maskFun `χ₃_smooth
    let hμ ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₂]]
    let hν ← mkAppM `Set.subset_univ #[← mkAppM `tsupport #[χ₃]]
    let ΓoutCompact := ms[13]!
    let N := ms[40]!
    withLocalDeclD `k (mkApp (mkConst ``Fin) N) fun k => do
      let k₀ := app ``Fin.castSucc #[N,k]
      let k₁ := app ``Fin.succ #[N,k]
      let atMasks := now ++ #[mask `Gext,mf `phase_smooth,mf `phase_agrees,mkApp (mask `m) k₀,mkApp (mask `m) k₁,
        mkApp (mf `inside) k₀,mkApp (mf `outside) k₀,mkApp (mf `inside) k₁,mkApp (mf `outside) k₁,
        mkApp (mask `fact3) k₀,mkApp (mask `fact3) k₁,mkApp (mask `fact1) k₀,mkApp (mask `fact1) k₁,
        mkApp (mf `support) k₀,mkApp (mf `support) k₁,mkApp (mask `fact8) k₀,mkApp (mask `fact8) k₁,
        mkApp (mf `diagonal) k,mkApp (mf `short_gap) k]
      let loss := mkApp (app (base ++ `loss) x) order
      forallBoundedTelescope (← inferType loss) (some 2) fun lb _ =>
        withLocalDeclD `reflected (mkConst ``Bool) fun reflected => do
          let all := atMasks ++ #[lb[0]!,reflected,lb[1]!,ΓoutCompact,univ,hUniv,hμ,hν,mkApp (ops `right) k₀,mkApp (ops `left) k₁,
            app (base ++ `MaskFacts.right_realization) (qr.push k₀),app (base ++ `MaskFacts.left_realization) (qr.push k₁)]
          unless all.size == 126 do throwError "changed native measured factor arity"
          logInfo "Checking every reflected and adjoint measured factor."
          discard <| store (base ++ `actual_between_masks) (x ++ #[order,i,k,lb[0]!,reflected,lb[1]!]) (app (base ++ `Proven.resolved) all)
end JanetCartan.PhysicalInitialization.OriginalSampledFactors
end
