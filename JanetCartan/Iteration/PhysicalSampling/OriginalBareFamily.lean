module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareOuter
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarEventInputs
public import JanetCartan.Iteration.PhysicalSampling.OriginalColoredRates
public meta import Lean

/-!
# Native bare36 assembled with the actual scalar46 family

Fix all numerical constants before the single history. At its actual coarse,
fine and colored scales, recover the literal stress frame from the original
scalar row and instantiate the bare transverse theorem on the same map. This
is a construction for *every point*, including zero spatial mask. It does not
require an already successful sample (`app:ch_mean_pairs:eq:block-fields`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalBareFamily
theorem nonzero_on_plateau {a : ℝ} (ha : a = 1) : a ≠ 0 := by rw [ha]; exact one_ne_zero
end JanetCartan.PhysicalSampling.OriginalBareFamily
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalBareFamilyApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalSampling
private def dest := root ++ `OriginalBareFamily
private def bare := root ++ `OriginalBare
private def family := root ++ `OriginalScalarFamily
private def tail (e : Expr) (n : Nat) : Expr := Nat.rec (motive := fun _ ↦ Expr) e (fun _ p ↦ Expr.proj ``And 1 p) n
private def first (e : Expr) (n : Nat) := Expr.proj ``And 0 (tail e n)

private def save (short : Name) (xs : Array Expr) (e : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let t ← instantiateMVars (← mkForallFVars xs (target?.getD (← inferType e)))
  let v ← instantiateMVars (← mkLambdaFVars xs e)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "bare scalar46: open {short}"
  let name := dest ++ short
  if data then addDecl (.defnDecl {name,levelParams := [],type := t,value := v,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type := t,value := v}) (forceExpose := true)
  return mkAppN (mkConst name) xs

/-- Only the positive early frame margin is required of the original εframe;
`OriginalBare.exists_frame` proves exactly this before the callback. -/
private def withFixed (k : Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let D := mkConst (family ++ `kernel)
  forallBoundedTelescope (← inferType D) (some 22) fun p _ => do
    let user := mkAppN (mkConst (bare ++ `userCap)) #[p[0]!,p[1]!,p[21]!]
    let fixed := p.set! 21 user
    let b := mkAppN (mkConst (bare ++ `exists_on_history)) p
    withLocalDeclD `hEarlyFrame (← whnf (← inferType b)).bindingDomain! fun hf => do
      forallBoundedTelescope (← inferType (mkAppN D fixed)) (some 15) fun next _ => do
        let x := fixed ++ next
        let merged := mkAppN (mkConst (root ++ `samplingCappedExtra)) #[p[0]!,p[1]!,p[2]!,user]
        let original := (x[:2].toArray ++ x[3:24].toArray).set! 20 merged
        let q := original ++ x[24:26].toArray
        let upper ← mkAppM `le_trans #[Expr.proj ``And 1 x[28]!,mkAppN
          (mkConst `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.fact2) q]
        let cert := mkAppN b (#[hf,x[27]!,Expr.proj ``And 0 x[28]!,upper] ++ x[29:33].toArray ++ #[x[36]!,x[35]!])
        k (p ++ #[hf] ++ next) x cert

elab "fix_original_bare_scalar46_constants" : command => liftTermElabM <| withFixed fun p _ cert => do
  let sb ← save `Sbare p (← mkAppM ``Classical.choose #[cert]) true
  let bc ← mkAppM ``Classical.choose_spec #[cert]
  let cx := tail bc 1
  discard <| save `CbareSq p (← mkAppM ``Classical.choose #[cx]) true
  let spec ← mkAppM ``Classical.choose_spec #[cx]
  discard <| save `CbareSq_pos p (first spec 0)
  discard <| save `bare_on_history p (tail spec 1)
  discard <| save `Sbare_ge_two p (first bc 0) false (some (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 2,sb]))

elab "join_original_scalar46_rate_thresholds" : command => liftTermElabM <| withFixed fun p x _ => do
  let sb := mkAppN (mkConst (dest ++ `Sbare)) p
  let one ← mkNumeral (mkConst ``Real) 1
  let rates := mkAppN (mkConst (root ++ `OriginalColoredRates.exists_fine_threshold)) (x[:22].toArray.push one)
  let sr ← save `Srate p (← mkAppM ``Classical.choose #[rates]) true
  let rateSpec ← mkAppM ``Classical.choose_spec #[rates]
  discard <| save `rates p (tail rateSpec 1)
  let ss := mkAppN (mkConst (root ++ `OriginalScalarHistory.S)) (x[:26].toArray ++ x[27:37].toArray)
  let pair ← mkAppM ``Max.max #[ss,sr]
  let S ← save `S p (← mkAppM ``Max.max #[sb,pair]) true
  let b ← save `bare_le p (← mkAppM `le_max_left #[sb,pair]) false (some (← mkAppM ``LE.le #[sb,S]))
  let upper ← mkAppM `le_max_right #[sb,pair]
  for (short,v,inner) in #[(`scalar_le,ss,`le_max_left),(`rate_le,sr,`le_max_right)] do
    discard <| save short p (← mkAppM `le_trans #[← mkAppM inner #[ss,sr],upper]) false (some (← mkAppM ``LE.le #[v,S]))
  discard <| save `hS p (← mkAppM `le_trans #[mkAppN (mkConst (dest ++ `Sbare_ge_two)) p,b])

elab "bound_original_scalar46_rows_uniformly" : command => liftTermElabM <| withFixed fun p _ _ => do
  let C := mkAppN (mkConst (dest ++ `CbareSq)) p
  let I := (← whnf (← inferType C)).bindingDomain!
  withLocalDeclD `i I fun i => do
    let cb ← mkAppM ``Real.sqrt #[mkApp C i]
    let fi ← mkAppOptM `Finset.univ #[some I,none]
    let sum ← save `Cbare p (← mkAppM `Finset.sum #[fi,← mkLambdaFVars #[i] cb]) true
    let hi ← mkAppM `Finset.mem_univ #[i]
    let pos ← mkAppM ``Real.sqrt_nonneg #[mkApp C i]
    let h ← withLocalDeclD `hi (← inferType hi) fun hi' => mkLambdaFVars #[i,hi'] pos
    discard <| save `sqrt_le_Cbare (p.push i) (← mkAppM `Finset.single_le_sum #[h,hi]) false (some (← mkAppM ``LE.le #[cb,sum]))

/-- No dyadic or phase-admission premise. The true 46 cutoff, rate and map
are used even at an external label where the incident mask vanishes. -/
elab "instantiate_original_native36_at_scalar46" : command => liftTermElabM <| withFixed fun p x _ => do
  let field (q : Name) := mkAppN (mkConst (dest ++ q)) p
  withLocalDeclD `R₀ (mkConst ``Real) fun R => do
    withLocalDeclD `hR₀ (← mkAppM ``LE.le #[field `S,R]) fun hR => do
      let hb ← mkAppM `le_trans #[field `bare_le,hR]
      let hs ← mkAppM `le_trans #[field `scalar_le,hR]
      let hr ← mkAppM `le_trans #[field `rate_le,hR]
      let pre := x ++ #[R,hs]
      let sc := mkAppN (mkConst (family ++ `kernel)) pre
      forallBoundedTelescope (← inferType sc) (some 4) fun hist _ => do
        let ra := mkAppN (field `rates) #[R,hr,hist[0]!]
        let every := tail ra 5
        let rows := mkAppN (field `bare_on_history) (#[R,hb] ++ hist)
        forallBoundedTelescope (← inferType every) (some 2) fun ic _ => do
          let i := ic[0]!
          let c := ic[1]!
          let one := mkAppN every ic
          let positive := first one 0
          let dy := tail one 3
          let J := (← whnf (← inferType dy)).bindingDomain!.appArg!
          let rate ← mkLambdaFVars #[c] (← inferType positive).appArg!
          let hpos ← mkLambdaFVars #[c] positive
          let caps := mkAppN (mkConst (root ++ `OriginalMargins.ε_caps)) (x[:22].toArray.push i)
          let dyadic ← forallBoundedTelescope (← inferType dy) (some 1) fun jj _ => do
            mkLambdaFVars (#[c] ++ jj) (← mkAppM `le_trans #[mkAppN dy jj,Expr.proj ``And 0 caps])
          let row := pre ++ hist ++ #[i,J,rate,hpos]
          let pl := mkAppN (mkConst (family ++ `Row.carrier_plateau)) (row.push dyadic)
          let info ← getConstInfo (family ++ `Row.kernel)
          let some body := info.value? | throwError "bare scalar46: missing original row definition"
          let raw := body.beta row
          unless raw.isAppOfArity (root ++ `originalScalarKernelData) 22 do
            throwError "bare scalar46: changed literal native scalar kernel"
          let Q := raw.getAppArgs[7]!
          let qval := Expr.proj ``Subtype 0 Q
          let sameQ ← mkAppM ``Eq.refl #[qval]
          withLocalDeclD `z (mkConst `JanetCartan.SeparatedSampling.Point) fun z => do
            let localBare := mkAppN rows (ic.push z)
            let plateau := mkApp pl z
            let active ← withLocalDeclD `hm (← whnf (← inferType plateau)).bindingDomain! fun hm => do
              let isOne := mkApp plateau hm
              let nonz ← mkAppM ``OriginalBareFamily.nonzero_on_plateau #[isOne]
              mkLambdaFVars #[hm] (mkApp localBare nonz)
            let .forallE _ _ action _ ← whnf (← inferType active) | throwError "bare scalar46: missing native row"
            unless action.isAppOfArity (bare ++ `RowAction) 28 do throwError "bare scalar46: changed original row coordinates"
            let a := action.getAppArgs
            let use := mkAppN (mkConst (bare ++ `at_outer_point))
              (a[:22].toArray ++ #[i,J,a[22]!,Q,sameQ,z,a[26]!,a[27]!,active])
            discard <| save `at_point (p ++ #[R,hR] ++ hist ++ ic ++ #[z]) use
  logInfo "actual native36 on all original scalar46 points: identical low stress Q, both radial copies, full colored rate, χcoeff and literal spatial mask (zero included)"

end JanetCartan.PhysicalSampling.OriginalBareFamilyApplication
end

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
fix_original_bare_scalar46_constants
join_original_scalar46_rate_thresholds
bound_original_scalar46_rows_uniformly
