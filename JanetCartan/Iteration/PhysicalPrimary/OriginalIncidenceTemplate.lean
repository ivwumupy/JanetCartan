module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the signed cutoff producer once to the SAME original pre-source
regular family. Only proof projections and named choices are retained; the
original sector, source phase, source window and masks are never selected anew. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalIncidenceTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary
private def protectedNS := `JanetCartan.PhysicalInitialization.OriginalProtected
private def ns := `JanetCartan.PhysicalPrimary.OriginalIncidence

/-- Retain the full independent source-domain band before any source contraction. -/
elab "retain_original_whole_source_band" : command => liftTermElabM do
  let name := ns ++ `exists_original_whole_source_gradient_band
  forallBoundedTelescope (← getConstInfo name).type (some 3) fun x _ => do
    select (ns ++ `Whole) x (mkAppN (mkConst name) x)

/-- Apply the proved source-gap producer to the actual signed capture field of
one original sector. The coefficient margin and angular gap precede every
source contraction, current field, derivative order and accuracy. -/
elab "retain_original_signed_incidence_cutoffs" : command => liftTermElabM do
  let capture := regular ++ `Incidence.fact4
  forallBoundedTelescope (← getConstInfo capture).type (some 26) fun x _ => do
    unless x.size == 26 do throwError "original incidence cutoff: expected fixed23, sector, source sign, original patch"
    let fixed := x[:23].toArray
    let d := x[0]!
    let hn := x[1]!
    let n := mkApp (mkConst ``Nat.succ) d
    let p := x[23]!
    let negative := x[24]!
    let a := x[25]!
    let T := mkAppN (mkConst (original ++ `T)) #[n,hn,a]
    let f := mkAppN (mkConst (regular ++ `f)) fixed
    let dom := mkAppN (mkConst (protectedNS ++ `source_domains)) #[n,hn,a]
    let hX := Expr.proj ``And 0 dom
    let hC := Expr.proj ``And 0 (.proj ``And 1 dom)
    let hsrc := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 dom)))
    let hXne := mkAppN (mkConst (ns ++ `original_source_nonempty)) #[n,hn,a]
    let hV := mkAppN (mkConst (regular ++ `Incidence.fact0)) x
    let margin := mkAppN (mkConst (regular ++ `sourceMargin)) fixed
    let hmargin := Expr.proj ``And 0
      (mkAppN (mkConst (regular ++ `afterChoice_sourceMargin)) fixed)
    let hcapture := mkAppN (mkConst capture) x
    let ta := (← inferType T).getAppArgs
    let fa := (← inferType f).getAppArgs
    unless ta.size == 4 && fa.size == 7 do
      throwError "original signed cutoff: unexpected patch/frame dimensions"
    let X := (← inferType hX).appArg!
    let Csrc := (← inferType hC).appArg!
    let V := (← inferType hV).appArg!
    let gap := mkAppN (mkConst `JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes.exists_selected_signed_incidence_cutoff_and_gap)
      #[d,ta[1]!,ta[2]!,ta[3]!,fa[1]!,fa[2]!,fa[3]!,fa[6]!,fa[4]!,fa[5]!,
        T,f,p,X,Csrc,V,hX,hXne,hC,hsrc,hV,negative,margin,hmargin,hcapture]
    let actual ← store (ns ++ `selected) x gap
    select ns x actual
    discard <| store (ns ++ `original_margin) x margin true
  logInfo "actual original signed incidence cutoff, positive pre-source coefficient margin, and angular separation for SAME selected multiplier and complete independent source window"

/-- Take one finite common margin for the actually selected cutoffs, then
reuse the SAME graph/frame cap chosen by the original regular family. -/
elab "retain_original_common_incidence_margin" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (ns ++ `δ)).type (some 23) fun fixed _ => do
    let δ := mkAppN (mkConst (ns ++ `δ)) fixed
    forallBoundedTelescope (← inferType δ) (some 3) fun tail _ => do
      unless tail.size == 3 do throwError "original incidence common margin: expected sector, source sign, patch"
      let all := fixed ++ tail
      let get (q : Name) := mkAppN (mkConst (ns ++ q)) all
      let base := #[fixed[0]!,fixed[1]!,tail[2]!]
      let getWhole (q : Name) := mkAppN (mkConst (ns ++ `Whole ++ q)) base
      let selected ← mkAppM (ns ++ `exists_original_signed_incidence_margin)
        #[← mkLambdaFVars tail (get `δ),← mkLambdaFVars tail (get `gap),
          ← mkLambdaFVars #[tail[2]!] (getWhole `δWhole),
          ← mkLambdaFVars tail (get `fact4),← mkLambdaFVars tail (get `fact7),
          ← mkLambdaFVars #[tail[2]!] (getWhole `fact2)]
      let common ← store (ns ++ `common_margin) fixed selected
      select (ns ++ `Common) fixed common
    let γ := mkAppN (mkConst (ns ++ `Common.γ)) fixed
    let hγ := mkAppN (mkConst (ns ++ `Common.fact0)) fixed
    let graphArgs := fixed ++ #[γ,hγ]
    discard <| store (ns ++ `sourceCap) fixed
      (mkAppN (mkConst (regular ++ `Graph.cap40)) graphArgs) true
    discard <| store (ns ++ `sourceCap_pos) fixed
      (mkAppN (mkConst (regular ++ `Graph.fact0)) graphArgs)
    discard <| store (ns ++ `source_interval) fixed
      (mkAppN (mkConst (regular ++ `Graph.continuation)) graphArgs)
  logInfo "one actual finite signed margin and the SAME original graph/frame source interval, all chosen before the final source contraction"

end JanetCartan.PhysicalPrimary.OriginalIncidenceTemplate
end
