module

public meta import Lean

/-! Apply the measured-history endpoint to the native uncorrected inverse
fields of the **same** `CurrentInverse` witness. The helper only assembles
proof terms; the caller stores and kernel-checks the resulting actual history
proof, with its original source, current chart, and current operator. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.NativeApplication
open Lean Meta Elab Term

private def domain (f : Expr) : MetaM Expr := do
  let t ← whnf (← inferType f)
  unless t.isForall do throwError "native current comparison: expected next original row input"
  return t.bindingDomain!

/-- Primitive projections avoid duplicating the entire finite current row
specification as explicit proposition arguments of every intermediate proof. -/
private def left (p : Expr) := Expr.proj ``And 0 p
private def right (p : Expr) := Expr.proj ``And 1 p
private def rights (p : Expr) (n : Nat) := (List.range n).foldl (fun q _ ↦ right q) p

/-- Rewrite only the genuinely zero initial scalar in the native specification.
In particular, do not run a general simplifier over the entire finite physical
family, its source selection proofs, or its normal-inverse constants. -/
private def zeroAmplitude (p : Expr) : MetaM Expr := do
  let t ← inferType p
  let name := `JanetCartan.positiveDensityAmplitude
  let some a := t.find? (·.isAppOfArity name 2) | return p
  let σ := a.getAppArgs[0]!
  unless σ.isFVar do throwError "native current comparison: expected the fixed original source contraction"
  let family ← withLocalDeclD `initialAmplitude (← inferType σ) fun v => do
    let t := t.replace fun e =>
      if e.isAppOfArity name 2 && e.getAppArgs[0]! == σ then some v else none
    mkLambdaFVars #[v] t
  let change ← mkAppM `JanetCartan.positiveDensityAmplitude_zero #[σ]
  let same ← mkAppM ``congrArg #[family, change]
  mkAppM ``Eq.mp #[same, p]

/-- `transfer` is the actual measured-history continuation after the history,
current chart, literal coefficient and its pointwise formula; `W` and
`native` are the operator and complete specification from the unchanged
current inverse at zero density. No new choice, gap, source or operator is
introduced. `s` is the actual high reserve `m+1`. -/
def closeNativeZero (transfer W native s : Expr) : TermElabM Expr := do
  let actions := left native
  let row := right native
  let gap := left (rights row 2)
  let adj := left (rights row 6)
  let pair := left (rights row 8)
  let zero := rights row 12
  let atW := mkApp transfer W
  let tests ← forallBoundedTelescope (← domain atW) (some 1) fun i _ => do
    mkLambdaFVars i (left (mkApp actions i[0]!))
  let atTests := mkApp atW tests
  let hAE ← forallBoundedTelescope (← domain atTests) (some 2) fun iw _ => do
    let atI := right (mkApp actions iw[0]!)
    let ae := right (mkApp atI iw[1]!)
    mkLambdaFVars iw (← zeroAmplitude ae)
  let hAdj ← zeroAmplitude (mkApp adj (mkNatLit 1))
  let atGap := mkAppN atTests #[hAE, hAdj, gap]
  let memGoal ← domain atGap
  let some e := memGoal.find? (·.isAppOf `JanetCartan.PhysicalBackground.measuredSourceToL2) |
    throwError "native current comparison: expected the original current measured datum"
  let he := mkAppN (mkConst `JanetCartan.PhysicalBackground.measuredSourceToL2_mem) (e.getAppArgs ++ #[s])
  let hRaw := left (mkAppN pair #[s, e, he])
  let eq ← domain zero
  unless eq.isAppOfArity ``Eq 3 do throwError "native current comparison: expected the true zero-density branch"
  let vZero ← mkEqRefl eq.getAppArgs[1]!
  let hZero := mkAppN zero #[vZero, s, e, he]
  return mkAppN atGap #[hRaw, hZero]

/-- Preserve the complete native zero-density row specification alongside the
new difference estimate. The operator is the witness of the original inverse,
not a newly solved or truncated row. -/
def joinNativeZero (transfer family s : Expr) : TermElabM Expr := do
  let t ← whnf (← inferType family)
  unless t.isAppOfArity ``Exists 2 do throwError "native current comparison: original operator family changed"
  let pred := t.appArg!
  let finish ← withLocalDeclD `nativeOperator t.getAppArgs[0]! fun W => do
    withLocalDeclD `nativeSpecification (pred.beta #[W]) fun spec => do
      let result ← closeNativeZero transfer W spec s
      let conjunction ← mkAppM ``And.intro #[spec, result]
      let predicate ← mkLambdaFVars #[W] (← inferType conjunction)
      let merged ← mkAppOptM ``Exists.intro #[none, some predicate, some W, some conjunction]
      mkLambdaFVars #[W, spec] merged
  mkAppM ``Exists.elim #[family, finish]

end JanetCartan.PhysicalInverseContinuity.NativeApplication
end
