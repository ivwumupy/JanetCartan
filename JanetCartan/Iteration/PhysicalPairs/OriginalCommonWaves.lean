module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedSum

/-! # A single original full-wave family before sign and ordered pair

The actual correction fixes all packets at the common sampled shift before
entering the plus or minus ledger. This is the projection from the external
signed labels to that very prefix; it is never inverted and need not be
injective. `app:ch_pairs:eq:pairs-exact-offself`.
-/
public meta section
set_option warningAsError true
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalCommonWaves
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalCommonWaves
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "share_waves_before_each_pair " piece:num : command => liftTermElabM do
  let sum := `JanetCartan.PhysicalPairs.OriginalSignedSum.correction
  forallBoundedTelescope (← getConstInfo sum).type (some 46) fun p _ => do
    let b := p[:37].toArray
    let dyn := p[37:45].toArray
    let Z := p[45]!
    if piece.getNat == 0 then
      discard <| store (ns ++ `Waves) b (← mkForallFVars dyn (← inferType Z)) true (some (mkSort .one))
      return
    withLocalDeclD `commonWaves (a (ns ++ `Waves) b) fun W => do
      let β := a (hist ++ `Labels) b
      if piece.getNat == 1 then
        let value ← withLocalDeclD `label β fun t => do
          let mut row := #[]
          let mut tl := t
          for _ in [:8] do
            row := row.push (.proj ``PSigma 0 tl)
            tl := .proj ``PSigma 1 tl
          mkLambdaFVars #[t] (mkAppN W row)
        discard <| store (ns ++ `onLabels) (b.push W) value true (some (a (fm ++ `Waves) b))
        return
      let labelW := a (ns ++ `onLabels) (b.push W)
      forallBoundedTelescope (← inferType (a (hist ++ `label) (b ++ dyn))) (some 4) fun sign _ => do
        let rhs := mkAppN W dyn
        let lhs := mkApp labelW (a (hist ++ `label) (b ++ dyn ++ sign))
        discard <| store (ns ++ `at_pair) (b ++ #[W] ++ dyn ++ sign) (← mkEqRefl rhs) false (some (← mkEq lhs rhs))
share_waves_before_each_pair 0
share_waves_before_each_pair 1
share_waves_before_each_pair 2
end JanetCartan.PhysicalPairs.OriginalCommonWaves
end
