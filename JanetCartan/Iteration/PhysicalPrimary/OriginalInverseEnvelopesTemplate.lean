module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Specialize the complete-inverse parameter identity on the actual admitted
source family. The finite powers and the uniform inverse remainder are distinct
inputs; there is no new inverse, representative history, or corrected source. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalInverseEnvelopesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes
private def fam := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs

/-- The concrete source53 forcing is a smooth curve in the actual local L²
space. Its scalar membership, joint smoothness and compact support have all
already been realized by the same canonical point; no source assumption follows
those of the original raw-family admission. -/
elab "retain_original_restricted_source_regularity" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fam ++ `Point.source)).type (some 45) fun xs _ => do
    unless xs.size == 45 do throwError "original inverse envelopes: expected source39+sigma/order+window3+point"
    let st (k : Name) := app (fam ++ `Static ++ k) xs[:41].toArray
    let pt (k : Name) := app (fam ++ `Point ++ k) xs
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let smooth := app (ns ++ `smooth_restricted_original_forcing)
      #[xs[0]!,n,st `W,st `x,st `χ₃,st `V,st `X,st `hV,st `hX,pt `ρ,pt `φ,pt `hφ,
        pt `f,pt `hf,pt `hs,pt `hmphysical,pt `source,pt `hsource]
    let hsource ← store (ns ++ `Point.source_smooth) xs smooth
    let args := #[xs[0]!,n,st `W,st `hW,st `x,st `χ₃,pt `R,pt `hR,pt `Op,pt `source,
      st `V,pt `ρ,pt `φ,pt `hφ]
    let curve ← store (ns ++ `Point.observed_solution) xs (app (ns ++ `fullObservedCurve) args) true
    let hcurve := app (ns ++ `contDiffOn_fullObservedCurve)
      (args ++ #[st `hV,st `Xφ,st `hXφ,pt `hsφ,hsource])
    let curveType ← inferType hcurve
    unless curveType.isAppOf `ContDiffOn do throwError "lost original norm-smooth full solution"
    let a := curveType.getAppArgs
    discard <| store (ns ++ `Point.observed_solution_smooth) xs hcurve false
      (some (mkAppN curveType.getAppFn (a.set! (a.size-2) curve)))
  logInfo "original norm-smooth source and uncut full solved L² curve: canonical Family.Point on the retained spatial-parameter window"
private def words := `JanetCartan.PhysicalPrimary.OriginalReservedWords
private def real := mkConst `Real

/-- Native consumer already specialized to the identical `Source.realization`,
`Rcomplex`, `hnorm` and `pairedSolver`. Its second returned term is the actual
native `N+s` tail, restricted to this subfamily with its two constants intact. -/
def actualReceiver (base : Array Expr) (I member : Expr) : MetaM (Expr × Expr) := do
  unless base.size == 44 do throwError "full inverse: expected the native fixed44 family"
  let st (k : Name) := app (fam ++ `Static ++ k) base[:41].toArray
  let ast := app (fam ++ `Point.source) base
  let remTy := (← inferType ast).bindingDomain!
  unless remTy.isAppOfArity ``Subtype 2 do throwError "lost original admitted subtype"
  let raw := remTy.getAppArgs[0]!
  let predicate := remTy.getAppArgs[1]!
  let n := mkApp (mkConst ``Nat.succ) base[0]!
  let receiver ← withLocalDeclD `i I fun i => do
    let p := base.push (mkApp member i)
    let pt (k : Name) := app (fam ++ `Point ++ k) p
    let pf (k : Name) := mkLambdaFVars #[i] (pt k)
    let smooth := app (ns ++ `Point.source_smooth) p
    let hst ← inferType smooth
    unless hst.isAppOf `ContDiffOn do throwError "missing norm-smoothness of the original forcing"
    let sd := hst.getAppArgs
    let params := #[n,n,I,sd[2]!,sd[3]!,sd[4]!,st `W,st `hW,st `x,st `χ₃,← pf `R,← pf `hR,
      ← pf `Op,← pf `source,st `V,st `hV,← mkLambdaFVars #[i] smooth,
      ← pf `ρ,← pf `A,← pf `K,← pf `hA,← pf `hK,base[37]!,← pf `φ,← pf `hφ,st `Xφ,st `hXφ,← pf `hsφ]
    return mkAppN (mkConst `JanetCartan.FixedDomainInverse.complex_inverse_parameter_envelopes_of_actual_finite_words [.zero]) params
  let rem := app (fam ++ `admitted_remainder) base
  let remProof ← forallBoundedTelescope (← inferType rem) (some 2) fun sk _ => do
    unless sk.size == 2 do throwError "expected all original orders before N and D"
    let Q := app (fam ++ `point_remainder_bound) (base ++ sk)
    mkLambdaFVars sk (app (ns ++ `retain_depth_and_cost) #[raw,I,predicate,member,Q,mkAppN rem sk])
  return (receiver,remProof)

private def emit (name : Name) (xs : Array Expr) (value : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let v ← store (ns ++ name) xs value data target
  addDocStringCore (ns ++ name) "The original complete-inverse family at its common finite-word/remainder threshold. Constants precede all admitted queries; exact restricted source, demodulated paired-solver solution and natural order reserve (app:ch_regular:eq:finite-neumann-identity; app:ch_response:eq:response-graded-reduced)."
  return v

private structure Joined where
  /-- The actual word41 prefix; no response data. -/
  word : Array Expr
  /-- Word41 and the original inverse history-order condition. -/
  params : Array Expr
  /-- The native task66 prefix including the strict frequency-window exponent. -/
  rem44 : Array Expr
  /-- The native task80 prefix at the shared maximum. -/
  word43 : Array Expr
  /-- The common admitted subtype of the original data-only raw index. -/
  I : Expr

private def withJoined (go : Joined → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (words ++ `S)).type (some 41) fun w _ => do
    unless w.size == 41 do throwError "full inverse: lost original word41 prefix"
    let wp := w[:40].toArray
    let .forallE _ hOrderType _ _ := (← inferType (app (fam ++ `S) wp))
      | throwError "full inverse: missing original tail reserve"
    withLocalDeclD `hInverseReserve hOrderType fun hr => do
      let p := w.push hr
      let rf := wp.push hr
      let S := app (ns ++ `S) p
      let wp := w ++ #[S,app (ns ++ `word_threshold) p]
      let rem44 := rf ++ [ `windowExponent, `windowExponent_pos, `windowExponent_lt_one ].toArray.map
        (fun k => mkConst (words ++ k))
      let I := (← inferType (app (words ++ `Point.source) wp)).bindingDomain!
      unless I.isAppOfArity ``Subtype 2 do throwError "full inverse: missing actual joint admitted subtype"
      go ⟨w,p,rem44,wp,I⟩

elab "choose_original_inverse_envelope_threshold" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (words ++ `S)).type (some 41) fun w _ => do
    let wp := w[:40].toArray
    let hOrderType := (← inferType (app (fam ++ `S) wp)).bindingDomain!
    withLocalDeclD `hInverseReserve hOrderType fun hr => do
      let p := w.push hr
      let a := app (words ++ `S) w
      let b := app (fam ++ `S) (wp.push hr)
      let S ← emit `S p (← mkAppM ``Max.max #[a,b]) true
      let hab ← emit `word_threshold p (← mkAppM `le_max_left #[a,b]) false (some (← mkAppM ``LE.le #[a,S]))
      discard <| emit `remainder_threshold p (← mkAppM `le_max_right #[a,b]) false (some (← mkAppM ``LE.le #[b,S]))
      discard <| emit `hS p (← mkAppM `le_trans #[app (words ++ `hS) w,hab])

elab "retain_original_envelope_points" : command => liftTermElabM do
  withJoined fun f => do
    let p := f.params
    let base := f.rem44
    let rt := (← inferType (app (fam ++ `Point.source) base)).bindingDomain!
    unless rt.isAppOfArity ``Subtype 2 do throwError "missing actual full-inverse source subtype"
    withLocalDeclD `point f.I fun y => do
      let i := Expr.proj ``Subtype 0 y
      let h := Expr.proj ``Subtype 1 y
      let under ← mkAppM (ns ++ `admit_at_smaller_threshold) #[app (ns ++ `remainder_threshold) p,h]
      let lift := mkAppN (mkConst ``Subtype.mk [.one]) #[rt.getAppArgs[0]!,rt.getAppArgs[1]!,i,under]
      let actual ← emit `remainder_point (p.push y) lift true
      let pt (k : Name) := app (fam ++ `Point ++ k) (base.push actual)
      for (key,native,data) in [(`phase,`φ,true),(`source,`source,true),(`solver,`Op,true),
          (`Rcomplex,`R,true),(`hnorm,`hR,false)] do
        discard <| emit key (p.push y) (pt native) data
      let sol ← emit `observed_solution (p.push y)
        (app (ns ++ `Point.observed_solution) (base.push actual)) true
      let hsol := app (ns ++ `Point.observed_solution_smooth) (base.push actual)
      let stype ← inferType hsol
      let a := stype.getAppArgs
      discard <| emit `observed_solution_smooth (p.push y) hsol false
        (some <| mkAppN stype.getAppFn (a.set! (a.size-2) sol))

private def withRaw {α : Type} (f : Joined) (go : Expr → Expr → Expr → MetaM α) : MetaM α := do
  withLocalDeclD `i f.I.getAppArgs[0]! fun i => do
    withLocalDeclD `hi (f.I.getAppArgs[1]!.beta #[i]) fun hi => do
      let point := mkAppN (mkConst ``Subtype.mk [.one]) #[f.I.getAppArgs[0]!,f.I.getAppArgs[1]!,i,hi]
      go i hi point

/-- Read the precise mathematical conclusion of the native theorem, at a
symbolic cost. Fold the complete curve, and display the original raw scalars in
the norm bound; the kernel checks all three representational replacements. -/
private def rawBoundAtVariable (fixed : Array Expr) (existsC C i point curve : Expr) : MetaM Expr := do
  unless C.isFVar do throwError "render cost only at a symbolic uniform constant"
  let pair ← whnf (existsC.appArg!.beta #[C])
  unless pair.isAppOfArity ``And 2 do throwError "full inverse: missing nonnegative uniform cost"
  let .forallE _ _ body _ := pair.getAppArgs[1]! | throwError "full inverse: missing admitted point"
  let atPoint := body.instantiate1 point
  let tied := atPoint.replace fun e => match e with
    | .letE `solution _ _ value _ => some (value.instantiate1 curve)
    | _ => none
  unless (tied.find? fun e => e == curve).isSome do
    throwError "full inverse lost the definitionally identical full observed curve"
  let payload := mkApp2 (mkConst ``Prod [.zero,.zero]) real (app (fam ++ `ScalarSpace) fixed)
  let fld (k : Name) := app (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k)
    #[fixed[0]!,payload,i]
  let budget ← mkAppM ``HMul.hMul #[← mkAppM ``HPow.hPow #[.proj ``Prod 0 (fld `datum),mkNatLit 3],fld `amplitude]
  let bound ← Core.betaReduce tied
  unless bound.getUsedConstants.contains (fam ++ `Point.A) && bound.getUsedConstants.contains (fam ++ `Point.K) do
    throwError "full inverse lost the original norm budget or admitted scale"
  return bound.replace fun e =>
    if e.isAppOfArity (fam ++ `Point.A) 45 then some budget
    else if e.isAppOfArity (fam ++ `Point.K) 45 then some (fld `K)
    else none

def renderRawBound (fixed : Array Expr) (existsC C i point curve : Expr) : MetaM Expr := do
  withLocalDeclD `uniformCost real fun z => do
    let t ← rawBoundAtVariable fixed existsC z i point curve
    return (← mkLambdaFVars #[z] t).beta #[C]

private def rawBound (f : Joined) (existsC C i point : Expr) : MetaM Expr :=
  renderRawBound f.params[:39].toArray existsC C i point (app (ns ++ `observed_solution) (f.params.push point))

/-- The two analytic fields come from already-proved, separate producers. In
particular this command does not introduce a free local proof of either field. -/
elab "apply_original_finite_words_and_inverse_remainder" : command => liftTermElabM do
  withJoined fun f => do
    let p := f.params
    let member := app (ns ++ `remainder_point) p
    let (receive,hrem) ← actualReceiver f.rem44 f.I member
    let hfinite := app (words ++ `local_reserved) f.word43
    let native := mkApp2 receive hfinite hrem
    let all ← emit `solution_envelope p native
    forallBoundedTelescope (← inferType all) (some 2) fun sk _ => do
      unless sk.size == 2 do throwError "full inverse solution lost the two response orders"
      let u := mkAppN all sk
      let choice ← mkAppM ``Classical.choose #[u]
      let C ← emit `cost (p ++ sk) choice true
      let spec ← mkAppM ``Classical.choose_spec #[u]
      let hC ← emit `cost_nonneg (p ++ sk) (.proj ``And 0 spec) false
        (some (← mkAppM ``LE.le #[← mkNumeral real 0,C]))
      let ex ← inferType u
      unless ex.isAppOfArity ``Exists 2 do throwError "missing native uniform C before histories"
      withRaw f fun i hi pt => do
        let H := mkApp (.proj ``And 1 spec) pt
        discard <| emit `on_admitted (p ++ sk ++ #[i,hi]) H false (some (← rawBound f ex C i pt))
      let existsPredicate ← withLocalDeclD `C real fun c => do
        let conclusion ← withRaw f fun i hi pt => do
          mkForallFVars #[i,hi] (← rawBound f ex c i pt)
        let nn ← mkAppM ``LE.le #[← mkNumeral real 0,c]
        mkLambdaFVars #[c] (mkApp2 (mkConst ``And) nn conclusion)
      let pair ← mkAppM ``And.intro #[hC,app (ns ++ `on_admitted) (p ++ sk)]
      let admitted ← mkAppOptM ``Exists.intro #[some real,some existsPredicate,some C,some pair]
      discard <| emit `admitted_envelope (p ++ sk) admitted
    logInfo "actual complete inverse: native finite powers and N+s full inverse remainder on the SAME original family, exact chi3 and uncut paired solver; uniform ordered jets for all admitted raw histories, including the vacuous empty family"

end JanetCartan.PhysicalPrimary.OriginalInverseEnvelopesTemplate
