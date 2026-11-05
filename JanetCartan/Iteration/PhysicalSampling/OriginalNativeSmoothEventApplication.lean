module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Apply the true source53/weak38 uncut response on the original sampled history

Use the actual source's own scalar subtype, unscaled shifted budget and
size-σ high profile. The original `rate` is the one in the measured corrected
kernel; the ordinary weak38 solver *is* the numerical graph42 B inside that
kernel. A single finite prehistory maximum reaches all source rows and all
original event/native thresholds (`app:ch_response:cor:current-atoms`,
`app:ch_waves:thm:sampling`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeSmoothEventApplication
open Lean Meta Elab Command OriginalNativeSourceRowsApplication
private def ps := `JanetCartan.PhysicalSampling
private def ns := ps ++ `OriginalNativeSmoothEvent
private def nr := ps ++ `OriginalNativeSourceRows
private def ni := ps ++ `OriginalNativeInitialEvent
private def br := ps ++ `OriginalBareEvent
private def pos := ps ++ `OriginalPositiveEvent
private def st := ps ++ `OriginalCommonStage
private def graph := ps ++ `OriginalGraphResponse
private def so := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def rawB := `JanetCartan.PhysicalPrimary.OriginalFullResponse.B
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo n).value? (allowOpaque := true) | throwError "native smooth event: missing {n} body"
  pure (body.beta xs).headBeta

private def save (q : Name) (xs : Array Expr) (e : Expr) (data := false) (goal : Option Expr := none) : MetaM Expr := do
  let y ← match goal with | none => inferType e | some t => pure t
  let type ← instantiateMVars (← mkForallFVars xs y)
  let value ← instantiateMVars (← mkLambdaFVars xs e)
  if type.hasMVar || type.hasFVar || value.hasMVar || value.hasFVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "native smooth event: open {q}"
  let name := ns ++ q
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked genuine source57 on one original sampler: {q} / {xs.size}"
  return mkAppN (mkConst name) xs

private def withFixed (k : Data → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withSourceData fun d => do
    let high := mkAppN (mkConst (ni ++ `S)) d.initial44
    forallBoundedTelescope (← inferType high) (some 3) fun resp _ =>
      k d (d.fixed ++ resp) (d.initial44 ++ resp)

elab "choose_original_native_smooth_threshold " which:num : command => liftTermElabM <| withTransparency .reducible <| withFixed fun d p high => do
  let a := mkAppN (mkConst (ni ++ `S)) high
  let b := mkAppN (mkConst (nr ++ `S)) d.fixed
  let S := mkAppN (mkConst (ns ++ `S)) p
  match which.getNat with
  | 0 => discard <| save `S p (← mkAppM ``Max.max #[a,b]) true
  | 1 => discard <| save `event_le p (← mkAppM `le_max_left #[a,b]) false (some (← mkAppM ``LE.le #[a,S]))
  | 2 => discard <| save `source_le p (← mkAppM `le_max_right #[a,b]) false (some (← mkAppM ``LE.le #[b,S]))
  | 3 => discard <| save `hS p (← mkAppM `le_trans #[mkAppN (mkConst (ni ++ `hS)) high,mkAppN (mkConst (ns ++ `event_le)) p])
  | _ => throwError "native smooth event: unknown threshold field"

/-- Open the *same* original positive event with its true high field already in
place. No auxiliary existential is used to define the density, solver or rates. -/
private def withStage (d : Data) (p high : Array Expr)
    (k : Array Expr → Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withLocalDeclD `R₀ (mkConst ``Real) fun R => do
    let S := mkAppN (mkConst (ns ++ `S)) p
    withLocalDeclD `hReached (← mkAppM ``LE.le #[S,R]) fun hR => do
      let hh ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `event_le)) p,hR]
      let hs ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `source_le)) p,hR]
      let hrow ← mkAppM `le_trans #[mkAppN (mkConst (nr ++ `source_le)) (d.fixed.push d.i),hs]
      let hn ← mkAppM `le_trans #[mkAppN (mkConst (ni ++ `native_le)) high,hh]
      let e := mkAppN (mkConst (ni ++ `exists_of_response_profiles)) (high ++ #[R,hh])
      forallBoundedTelescope (← inferType e) (some 4) fun hist _ =>
        k (p ++ #[R,hR] ++ hist) (mkAppN e hist) hist hh hrow hn

private def rateProof (high : Array Expr) (i c R stage hHigh : Expr) : MetaM Expr := do
  let h ← bodyAt (ni ++ `S) high
  let some bare := h.find? (·.isAppOfArity (br ++ `S) 46) | throwError "native smooth event: bare46 absent"
  let h ← bodyAt (br ++ `S) bare.getAppArgs
  let some p := h.find? (·.isAppOfArity (pos ++ `S) 47) | throwError "native smooth event: positive47 absent"
  let hb ← mkAppM `le_trans #[mkAppN (mkConst (ni ++ `event_le)) high,hHigh]
  let hp ← mkAppM `le_trans #[mkAppN (mkConst (br ++ `event_le)) bare.getAppArgs,hb]
  let ht ← mkAppM `le_trans #[mkAppN (mkConst (pos ++ `stage_le)) p.getAppArgs,hp]
  let rates := mkAppN (mkConst (st ++ `stage_rates)) (p.getAppArgs[:46].toArray ++ #[R,ht,stage])
  pure (part (mkAppN (tail rates 6) #[i,c]) 0)

/-- Produce the two original spines needed by the ordinary response and by the
subsequent graded calculation: `s53` and the identical `weak38`. -/
def trueSourceSpines (d : Data) (high hist : Array Expr) (R hHigh hrow hn c expected : Expr) : MetaM (Array Expr × Array Expr) := do
  let some tensor := expected.find? (·.isAppOfArity `JanetCartan.CorrectedAtoms.fullPrimaryResponse 18)
    | throwError "native smooth event: expected literal full `(x,c,z)` measured response"
  let α := tensor.getAppArgs[15]!
  let rate := tensor.getAppArgs[14]!
  let B := tensor.getAppArgs[13]!
  unless B.isAppOfArity (graph ++ `B) 42 do throwError "native smooth event: lost original uncut graph42 B"
  let weak ← bodyAt (graph ++ `B) B.getAppArgs
  unless weak.isAppOfArity rawB 38 do throwError "native smooth event: changed ordinary weak38 solver"
  let stage := hist[0]!
  let K := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R,stage]
  let hrate ← rateProof high d.i c R stage hHigh
  let native39 := d.native33 ++ #[R,hn] ++ hist
  let actualScalar := mkAppN (mkConst (ps ++ `OriginalNativeSourceScalar.scalar)) (native39.push d.i)
  let σ := d.native33[21]!
  let sign ← mkAppM `le_of_lt #[Expr.proj ``And 0 d.native33[23]!]
  let s52 := d.source39 ++ #[R,hrow] ++ hist ++ #[K,← mkAppM `le_refl #[K],rate,hrate,actualScalar,σ,sign]
  let needed := (← whnf (← inferType (mkAppN (mkConst (so ++ `full_source_profiles)) s52))).bindingDomain!
  let bound ← forallBoundedTelescope needed (some 1) fun _ t => do
    unless t.isAppOfArity ``LE.le 4 do throwError "native smooth event: source52 high has changed"
    let lhs := t.getAppArgs[2]!
    unless lhs.isAppOf `JanetCartan.cNorm do throwError "native smooth event: missing actual source label norm"
    let args := lhs.getAppArgs
    let C := mkAppN (mkConst (ni ++ `initialC)) (d.initial44.push d.i)
    let actual := mkAppN (mkConst (ni ++ `native_initial_profile)) (high ++ #[R,hHigh] ++ hist ++ #[d.i])
    -- The native full source span value and retained measured initial scalar
    -- agree by construction (same σ, native39 labels and original point).
    unless (α.find? (·.isAppOf `JanetCartan.PhysicalBackground.NativeAdmission.labels)).isSome do
      throwError "native smooth event: original native positive labels absent"
    mkAppM `JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication.after16
      #[args[args.size-3]!,args.back!,K,σ,C,d.source39[37]!,actual]
  pure (s52.push bound,weak.getAppArgs)

elab "supply_original_joint_uncut_smoothness" : command => liftTermElabM <| withTransparency .reducible <| withFixed fun d p high => withStage d p high fun args next hist hh hrow hn => do
  let wanted := (← whnf (← inferType next)).bindingDomain!
  let .forallE _ _ each _ ← whnf wanted | throwError "native smooth event: expected row family"
  let body := each.instantiate1 d.i
  let h ← forallBoundedTelescope body (some 1) fun colors expected => do
    let (s,w) ← trueSourceSpines d high hist args[47]! hh hrow hn colors[0]! expected
    let full := mkAppN (mkConst (ps ++ `OriginalResponseWindow.full_response_smooth_on_working_ball))
      (d.sampler22 ++ s[21:53].toArray ++ #[w[24]!,w[29]!,w[30]!,w[33]!])
    mkLambdaFVars (#[d.i] ++ colors) full
  discard <| save `uncut_response_smooth args h false (some wanted)

elab "apply_original_event_of_quantitative_uncut_jets" : command => liftTermElabM <| withTransparency .reducible <| withFixed fun d p high => withStage d p high fun args next _ _ _ _ => do
  let e := mkApp next (mkAppN (mkConst (ns ++ `uncut_response_smooth)) args)
  forallBoundedTelescope (← inferType e) (some 1) fun jet t => do
    unless jet.size == 1 && (← whnf t).isAppOfArity ``Exists 2 do throwError "native smooth event: lost original common shift"
    discard <| save `exists_of_quantitative_uncut_jets (args ++ jet) (mkAppN e jet)

end JanetCartan.PhysicalSampling.OriginalNativeSmoothEventApplication
end
