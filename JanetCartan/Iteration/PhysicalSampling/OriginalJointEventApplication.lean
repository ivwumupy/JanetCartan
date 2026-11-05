module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCommonStage
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernels
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarEventInputs
public meta import Lean

/-!
# Apply one joint sampling continuation at the original stage and color rates

The remaining analytic inputs are exactly the original positive density/initial
profile and the joint smoothness and whole-compact derivative estimates of the
literal uncut response. None is deduced from the local smoothness in the
physical variable alone. In particular the conditional theorem named here is
not the unconditional construction. It does not take kernel bounds, means,
probabilities, counts, a chosen shift, or an alternative response operator as
hypotheses (`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalJointEventApplication

private theorem retained_source_reserve {r rStar : ℕ} (h : 16+r ≤ rStar) :
    14+(r+2) ≤ rStar := by omega

private theorem retained_initial_reserve (r : ℕ) : 14+(r+2) ≤ 16+r := by omega

private theorem mesh_ne_of_stage {T₀ T : ℝ} (h₀ : 1 ≤ T₀) (h : T₀ ≤ T) :
    T ^ (-separationExponent) ≠ 0 := (Real.rpow_pos_of_pos (zero_lt_one.trans_le (h₀.trans h)) _).ne'

end JanetCartan.PhysicalSampling.OriginalJointEventApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalJointEventApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalSampling
private def ns := root ++ `OriginalJointEvent
private def scalar := root ++ `OriginalScalarFamily
private def measured := root ++ `OriginalMeasuredFamily
private def row := measured ++ `Row
private def stageNS := root ++ `OriginalCommonStage
private def event := root ++ `OriginalCommonThreshold

private def tail (h : Expr) (n : Nat) :=
  (List.range n).foldl (fun e _ => Expr.proj ``And 1 e) h
private def part (h : Expr) (n : Nat) := Expr.proj ``And 0 (tail h n)

private def save (short : Name) (xs : Array Expr) (v : Expr) (data := false) : MetaM Unit := do
  let t ← instantiateMVars (← mkForallFVars xs (← inferType v))
  let v ← instantiateMVars (← mkLambdaFVars xs v)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "actual joint event: open or recovered {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type := t, value := v, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type := t, value := v}) (forceExpose := true)
  logInfo m!"checked one original-stage event join: {name} with {xs.size} inputs"

/-- Reindex only the next actual premises by the original row. The fiber
can depend on the previously supplied row values, including the SAME v. -/
private def withFiber (i start : Expr) (names : List Name)
    (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let rec go (rest : List Name) (app : Expr) (all atRow : Array Expr) : MetaM Unit := do
    match rest with
    | [] => k all atRow
    | label :: next =>
      let .forallE _ dom _ _ ← whnf (← inferType app)
        | throwError "actual joint event: missing original input {label}"
      withLocalDeclD label (← mkForallFVars #[i] dom) fun f =>
        go next (mkApp app (mkApp f i)) (all.push f) (atRow.push (mkApp f i))
  go names start #[] #[]

/-- Bookkeeping only, never part of a mathematical hypothesis. -/
private structure Joined where
  fixed : Array Expr
  params : Array Expr
  i : Expr
  scalar46 : Array Expr
  measured64 : Array Expr
  measured66 : Array Expr
  dyadic : Expr
  clock : Expr
  hclock : Expr

private def withJoined (k : Joined → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (event ++ `T₀)).type (some 46) fun x _ => do
    unless x.size == 46 do throwError "actual joint event: changed static46"
    let n := (← inferType x[1]!).appArg!
    let rpar := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    let Rr ← mkAppM ``HAdd.hAdd #[mkNatLit 16, rpar]
    -- This actual source reserve is a numerical choice preceding every history.
    withLocalDeclD `hSharedReserve (← mkAppM ``LE.le #[Rr, x[31]!]) fun hReserve ↦ do
      let S := mkAppN (mkConst (stageNS ++ `S)) x
      withLocalDeclD `R₀ (mkConst ``Real) fun R => do
        withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S, R]) fun hR => do
          let hScalar ← mkAppM `le_trans #[mkAppN (mkConst (stageNS ++ `S_scalar)) x, hR]
          let sc39 := x[:36].toArray ++ #[x[40]!, R, hScalar]
          let native := mkAppN (mkConst (scalar ++ `kernel)) sc39
          forallBoundedTelescope (← inferType native) (some 4) fun hist _ => do
            unless hist.size == 4 do throwError "actual joint event: changed Schwartz history4"
            let rates := mkAppN (mkConst (stageNS ++ `stage_rates)) (x ++ #[R, hR, hist[0]!])
            let hclock := part rates 0
            let t ← inferType hclock
            unless t.isAppOfArity ``LE.le 4 do throwError "actual joint event: clock threshold missing"
            let clock := t.getAppArgs[3]!
            let allRates := tail rates 6
            forallBoundedTelescope (← inferType allRates) (some 2) fun ic _ => do
              unless ic.size == 2 do throwError "actual joint event: missing actual row/color"
              let i := ic[0]!
              let rateBounds := mkAppN allRates ic
              let hpos := part rateBounds 0
              let ht ← inferType hpos
              unless ht.isAppOfArity ``LT.lt 4 do throwError "actual joint event: missing positive native rate"
              let rate ← mkLambdaFVars ic ht.getAppArgs[3]!
              let hpos ← mkLambdaFVars ic hpos
              let hone ← mkLambdaFVars ic (part rateBounds 1)
              let dyadic := tail rateBounds 3
              let jt := (← whnf (← inferType dyadic)).bindingDomain!
              unless jt.isAppOfArity ``Fin 1 do throwError "actual joint event: expected the finite ceiling"
              let J := jt.appArg!
              let dyadic ← mkLambdaFVars ic dyadic
              let row43 := x[:40].toArray ++ #[i,mkApp x[41]! i,mkApp x[42]! i]
              let hCurrent ← mkAppM `le_trans #[mkAppN (mkConst (stageNS ++ `S_current)) (x.push i),hR]
              let row51 := row43 ++ #[mkApp x[43]! i,mkApp x[44]! i,R,hCurrent] ++ hist
              let b := mkConst (row ++ `amplitude_bound)
              withFiber i (mkAppN b row51) [`density,`density_smooth,`one_add_pos,`density_range,`density_low] fun low lowi => do
                let hStar ← mkAppM ``retained_source_reserve #[hReserve]
                let row59 := row51 ++ lowi ++ #[Rr,hStar,mkApp (mkConst ``retained_initial_reserve) rpar]
                withFiber i (mkAppN b row59) [`initial_profile] fun initial initiali => do
                  let row60 := row59 ++ initiali
                  let rawRates := #[J,mkApp rate i,mkApp hpos i]
                  let four := rawRates.push (mkApp hone i)
                  withFiber i (mkAppN b (row60 ++ four)) [`uncut_response_smooth,`uncut_response_jets] fun response resp => do
                    let params := x ++ #[hReserve,R,hR] ++ hist ++ low ++ initial ++ response
                    unless params.size == 61 && row60.size == 60 do throwError "actual joint event: lost SAME fixed scalar/response obligations"
                    k ⟨x, params, i, sc39 ++ hist ++ #[J,rate,hpos],
                      row60 ++ rawRates ++ #[resp[0]!], row60 ++ four ++ resp,
                      dyadic, clock, hclock⟩

/-- One on-stage row family. Its construction does not depend on the last
response-jets input. The original uncut B is already inside EACH native row. -/
elab "retain_original_event_measured_kernel" : command => liftTermElabM <| withTransparency .reducible <| withJoined fun a => do
  let D ← mkLambdaFVars #[a.i] (mkAppN (mkConst (row ++ `kernel)) a.measured64)
  save `measured_kernel a.params[:60].toArray D true

/-- Apply the actual simultaneous threshold once. The band estimates are
active-weight bounds at both refined radii, and the measured mean is summed by
the triangle inequality before it is compared to the static numerical maximum. -/
elab "apply_original_joint_event_of_profiles" : command => liftTermElabM <| withTransparency .reducible <| withJoined fun a => do
  let x := a.fixed
  let i := a.i
  let sc (f : Name) := mkAppN (mkConst (scalar ++ f)) a.scalar46
  let ms (f : Name) := mkAppN (mkConst (row ++ f)) a.measured64
  let row67 := a.measured66.push (mkApp a.dyadic i)
  let sb := x[:26].toArray ++ x[27:36].toArray ++ #[x[40]!]
  let mb := x[:22].toArray ++ #[x[27]!,x[36]!,x[37]!] ++ x[29:33].toArray ++ #[x[38]!,x[35]!,x[39]!] ++ x[41:45].toArray
  unless sb.size == 36 && mb.size == 36 do throwError "actual joint event: changed numerical budget36"
  let m (f : Name) := mkAppN (mkConst (measured ++ f)) mb
  let s (f : Name) := mkAppN (mkConst (scalar ++ f)) sb
  let hmesh ← mkAppM ``mesh_ne_of_stage #[mkAppN (mkConst (event ++ `T₀_ge_one)) x,a.hclock]
  let mesh := (← inferType hmesh).appFn!.appArg!
  let aux := mkAppN (mkConst (scalar ++ `original_inputs)) (a.scalar46 ++ #[a.dyadic,x[45]!,mesh,hmesh])
  let D := mkAppN (mkConst (ns ++ `measured_kernel)) a.params[:60].toArray
  let eventPrefix := mkAppN (mkConst (event ++ `continuation)) (x ++ #[a.clock,a.hclock,D,sc `kernel,
    ← mkLambdaFVars #[i] (ms `amplitude_support),sc `amplitude_support,
    ← mkLambdaFVars #[i] (mkAppN (mkConst (row ++ `amplitude_bound)) a.measured66),sc `amplitude_bound,
    ← mkLambdaFVars #[i] (ms `mask_bound),sc `mask_bound])
  let sharpDom := (← whnf (← inferType eventPrefix)).bindingDomain!
  let sharpDom := (← whnf sharpDom).bindingBody!.instantiate1 i
  let makeSharp (isMeasured : Bool) : MetaM Expr := do
    forallBoundedTelescope sharpDom (some 4) fun labels _ => do
      unless labels.size == 4 do throwError "actual joint event: expected refined/color/node/active"
      let ref := labels[0]!
      let (bound, increase) ← if isMeasured then do
        let j ← mkAppM ``Prod.fst #[ref]
        let b ← mkAppM ``Prod.snd #[ref]
        let native := mkAppN (mkConst (row ++ `sharp_bound)) (row67 ++ labels[1:4].toArray ++ #[j])
        let bigger ← mkAppM `le_trans #[mkApp (m `Csharp_le) i,← mkAppM `le_max_left #[m `Csharp,s `Csharp]]
        pure (mkApp (tail native 1) b, bigger)
      else do
        let bigger ← mkAppM `le_max_right #[m `Csharp,s `Csharp]
        pure (mkAppN (part aux 0) (#[i] ++ labels),bigger)
      let hrad ← mkAppM `le_of_lt #[← mkAppM `JanetCartan.RawInputPartition.refinedRadius_pos #[ref]]
      let h ← mkAppM `mul_le_mul_of_nonneg_right #[increase,hrad]
      mkLambdaFVars (#[i] ++ labels) (← mkAppM `le_trans #[bound,h])
  let rowMean := part (mkAppN (mkConst (row ++ `mean_bound)) (row67 ++ #[x[45]!,mesh,hmesh])) 0
  let mt ← inferType rowMean
  unless mt.isAppOfArity ``LE.le 4 do throwError "actual joint event: missing complex continuum mean bound"
  let means ← mkLambdaFVars #[i] mt.getAppArgs[2]!.appArg!
  let univ ← mkAppOptM `Finset.univ #[some (← inferType i),none]
  let member ← mkAppM `Finset.mem_univ #[i]
  let sum ← withLocalDeclD `hi (← inferType member) fun hi => do
    mkAppM `Finset.sum_le_sum #[← mkLambdaFVars #[i,hi] rowMean]
  let mean ← mkAppM `le_trans #[← mkAppM `norm_sum_le #[univ,means],sum]
  let mean ← mkAppM `le_trans #[mean,← mkAppM `le_max_left #[m `Cmean,s `Cmean]]
  let scalarMean ← mkAppM `le_trans #[tail aux 1,← mkAppM `le_max_right #[m `Cmean,s `Cmean]]
  let result := mkAppN eventPrefix #[← makeSharp true,← makeSharp false,mean,scalarMean]
  let t ← whnf (← inferType result)
  unless t.isAppOfArity ``Exists 2 do throwError "actual joint event: missing SINGLE original ξ"
  save `exists_of_initial_and_response_profiles a.params result

end JanetCartan.PhysicalSampling.OriginalJointEventApplication
