module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the first-summand estimate to the actual positive-current carrier
witness.  No v=0 specialization, independent carrier choice, all-L² tail
estimate, or comparison/sampling estimate is used. -/

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTailTemplate
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTail
private def src := `JanetCartan.PhysicalNormalInverse.OriginalCarriers.exists_common_measured_carriers

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k

private def save (n : Name) (x : Array Expr) (proof : Expr) : MetaM Expr := do
  let v ← store (ns ++ n) x proof
  addDocStringCore (ns ++ n)
    "The source-only normal tail for the same original measured carriers, paired current positive-density estimate, uncut augmented normal inverse, and supplied smooth residual. No finite-transport or sampling estimate is assumed (new:sec:mean-source-equation)."
  return v

/-- Add the source-only tail to the ENTIRE native predicate and its original
common measurement on the same already-constructed carrier witness. -/
elab "retain_actual_original_normal_source_tail" : command => liftTermElabM do
  let info ← getConstInfo src
  forallBoundedTelescope info.type (some 44) fun x result => do
    unless x.size == 44 do throwError "normal source tail: missing original44"
    let existsNative := mkAppN (mkConst src) x
    let result ← whnf result
    unless result.isAppOfArity ``Exists 2 do throwError "normal source tail: native Vop existential lost"
    let pred := result.appArg!
    let continuation ← withLocalDeclD `Vop result.getAppArgs[0]! fun Vop => do
      let jt ← whnf (pred.beta #[Vop])
      unless jt.isAppOfArity ``And 2 do throwError "normal source tail: original common measurement lost"
      let deduce ← withLocalDeclD `hNative jt.getAppArgs[0]! fun hNative => do
        let ops := .proj ``And 1 hNative
        let hM := part ops 1
        let paired := part ops 8
        let regular := part ops 11
        let T ← inferType regular
        let p ← forallBoundedTelescope T (some 2) fun es out => do
          unless es.size == 2 do throwError "normal source tail: all smooth residual/order regularity not found"
          let e := es[0]!
          let q := es[1]!
          let some row := out.find? (·.isAppOf `JanetCartan.ContinuumRow.augmentedRow)
            | throwError "normal source tail: lost literal measured augmented row"
          let rows := row.getAppArgs
          let r := rows[rows.size-3:].toArray
          let toL2 := mkApp (mkConst `JanetCartan.CurrentMean.smoothResidualToL2) x[0]!
          let w := mkApp (← mkAppM `DFunLike.coe #[toL2]) e
          let hw ← mkAppM `JanetCartan.CurrentMean.smoothResidualToL2_mem #[e,q]
          let hp := .proj ``And 1 (mkAppN paired #[q,w,hw])
          withLocalDeclD `K (mkConst `Real) fun K => do
            let one ← mkAppOptM ``OfNat.ofNat #[some (mkConst `Real),some (mkNatLit 1),none]
            withLocalDeclD `hK (← mkAppM ``LE.le #[one,K]) fun hK => do
              let bound ← mkAppM (ns ++ `source_tail_from_native_pair)
                #[r[0]!,r[1]!,r[2]!,hM,hK,e,q,mkAppN regular es,hp]
              mkLambdaFVars (es ++ #[K,hK]) bound
        discard <| save `tail_of_native (x ++ #[Vop,hNative]) p
        return mkAppN (mkConst (ns ++ `tail_of_native)) (x.push Vop)
      withLocalDeclD `hJoint (pred.beta #[Vop]) fun hJoint => do
        let joint ← mkAppM ``And.intro #[hJoint,mkApp deduce (.proj ``And 0 hJoint)]
        let target ← mkLambdaFVars #[Vop] (← inferType joint)
        let hex ← mkAppOptM ``Exists.intro #[none,some target,some Vop,some joint]
        mkLambdaFVars #[Vop,hJoint] hex
    let proof ← mkAppM ``Exists.elim #[existsNative,continuation]
    discard <| save `exists_native_source_tail x proof

end JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTailTemplate
end
