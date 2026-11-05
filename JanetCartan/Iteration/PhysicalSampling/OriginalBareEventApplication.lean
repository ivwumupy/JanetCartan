module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareCurrent
public meta import Lean

/-!
# The individual scalar row at the nodes of the one positive event

Choose the original frame and cap before the source. A single common starting
scale admits both the actual native36/scalar46 calculation and the positive
sampler. Its very same shift, node and color have the unweighted bare kernel
with the original spatial mask, including at inactive outer labels. No second
sample or comparison of two δ witnesses (`app:ch_mean_pairs:eq:block-fields`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalBareEvent
/-- The common sampled mesh at a reached original physical scale. -/
theorem mesh_bounds {T : ℝ} (h : 1 ≤ T) : 0 < T ^ (-separationExponent) ∧ T ^ (-separationExponent) ≤ 1 :=
  ⟨Real.rpow_pos_of_pos (zero_lt_one.trans_le h) _,
    Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num [separationExponent])⟩
/-- Remove the sampled `T^(-3/512)` from the aggregate tester constant. -/
theorem sqrt_tol_le {T : ℝ} (C : ℝ) (h : 1 ≤ T) :
    Real.sqrt (C + T ^ (-((3:ℝ)/512))) ≤ Real.sqrt (C+1) :=
  Real.sqrt_le_sqrt (add_le_add le_rfl (Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)))
/-- Use the already chosen prehistory uniform bound without changing the
individual tester or any component of its kernel action. -/
theorem uniform_bound {E : Type*} [Norm E] {P : E → Prop} {a b : ℝ}
    (h : a ≤ b) (e : ∃ u : E, ‖u‖ ≤ a ∧ P u) : ∃ u : E, ‖u‖ ≤ b ∧ P u := by
  obtain ⟨u,hu,hP⟩ := e
  exact ⟨u,hu.trans h,hP⟩
end JanetCartan.PhysicalSampling.OriginalBareEvent
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalBareEventApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalSampling
private def dest := root ++ `OriginalBareEvent
private def pos := root ++ `OriginalPositiveEvent
private def bare := root ++ `OriginalBare
private def family := root ++ `OriginalBareFamily
private def endpoint := pos ++ `exists_with_physical_amplitude_test
private def tail (e : Expr) (n : Nat) : Expr := Nat.rec (motive := fun _ ↦ Expr) e (fun _ p ↦ Expr.proj ``And 1 p) n
private def part (e : Expr) (n : Nat) := Expr.proj ``And 0 (tail e n)

private def save (q : Name) (p : Array Expr) (e : Expr) (data := false) (ty? : Option Expr := none) : MetaM Expr := do
  let t ← instantiateMVars (← mkForallFVars p (ty?.getD (← inferType e)))
  let v ← instantiateMVars (← mkLambdaFVars p e)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "original bare event: open {q}"
  let name := dest ++ q
  if data then addDecl (.defnDecl {name,levelParams := [],type := t,value := v,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type := t,value := v}) (forceExpose := true)
  return mkAppN (mkConst name) p

private def withStatic (k : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let e := mkConst (pos ++ `S)
  forallBoundedTelescope (← inferType e) (some 3) fun b _ => do
    withLocalDeclD `extraFrame (mkConst ``Real) fun r => do
      withLocalDeclD `extraFrame_pos (← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,r]) fun hr => do
        let frame ← mkAppM (bare ++ `exists_frame) #[b[1]!,hr]
        let eps ← mkAppM ``Classical.choose #[frame]
        let f ← mkAppM ``Classical.choose_spec #[frame]
        let a := b ++ #[eps,part f 0]
        forallBoundedTelescope (← inferType (mkAppN e a)) (some 17) fun fixed _ => do
          let ordinary := a ++ fixed
          let cap := mkAppN (mkConst (bare ++ `userCap)) #[b[0]!,b[1]!,fixed.back!]
          let chosen := ordinary.set! 21 cap
          forallBoundedTelescope (← inferType (mkAppN e chosen)) (some 17) fun order _ => do
            let pref := chosen ++ order ++ #[tail f 4]
            forallBoundedTelescope (← inferType (mkAppN e pref)) (some 7) fun low _ => do
              let x := pref ++ low
              unless x.size == 47 do throwError "original bare event: positive prehistory47 changed"
              k (b ++ #[r,hr] ++ fixed ++ order ++ low) x
                (ordinary ++ #[part f 2] ++ x[22:36].toArray ++ #[x[40]!])

elab "choose_original_bare_event_budget " which:num : command => liftTermElabM <| withTransparency .reducible <| withStatic fun p x b => do
  let sb := mkAppN (mkConst (family ++ `S)) b
  let sp := mkAppN (mkConst (pos ++ `S)) x
  let S := mkAppN (mkConst (dest ++ `S)) p
  match which.getNat with
  | 0 => discard <| save `S p (← mkAppM ``Max.max #[sb,sp]) true
  | 1 => discard <| save `Cbare p (mkAppN (mkConst (family ++ `Cbare)) b) true
  | 2 =>
    let cm := mkAppN (mkConst (root ++ `OriginalScalarFamily.Cmean)) (x[:26].toArray ++ x[27:36].toArray ++ #[x[40]!])
    let one ← mkNumeral (mkConst ``Real) 1
    discard <| save `Ctest p (← mkAppM ``Real.sqrt #[← mkAppM ``HAdd.hAdd #[cm,one]]) true
  | 3 => discard <| save `bare_le p (← mkAppM `le_max_left #[sb,sp]) false (some (← mkAppM ``LE.le #[sb,S]))
  | 4 => discard <| save `event_le p (← mkAppM `le_max_right #[sb,sp]) false (some (← mkAppM ``LE.le #[sp,S]))
  | 5 => discard <| save `hS p (← mkAppM `le_trans #[mkAppN (mkConst (family ++ `hS)) b,mkAppN (mkConst (dest ++ `bare_le)) p])
  | _ => throwError "original bare event: unknown static budget"
  logInfo m!"checked joined original bare prehistory budget {which.getNat}"

elab "apply_original_bare_positive_event" : command => liftTermElabM <| withStatic fun p x b => do
  let prior := mkAppN (mkConst endpoint) x
  let field (q : Name) := mkAppN (mkConst (dest ++ q)) p
  withLocalDeclD `hσbackground (← whnf (← inferType prior)).bindingDomain! fun hσ => do
    withLocalDeclD `R₀ (mkConst ``Real) fun R => do
      withLocalDeclD `hR₀ (← mkAppM ``LE.le #[field `S,R]) fun hR => do
        let hb ← mkAppM `le_trans #[field `bare_le,hR]
        let hp ← mkAppM `le_trans #[field `event_le,hR]
        let e := mkAppN prior #[hσ,R,hp]
        forallBoundedTelescope (← inferType e) (some 4) fun hist _ => do
          let rows := mkAppN (mkConst (family ++ `at_point)) (b ++ #[R,hb] ++ hist)
          let e := mkAppN e hist
          forallBoundedTelescope (← inferType e) (some 3) fun profiles ex => do
            let ex ← whnf ex
            unless ex.isAppOfArity ``Exists 2 do throwError "original bare event: missing single shift"
            let aa := ex.getAppArgs
            let result ← withLocalDeclD `ξ aa[0]! fun ξ => do
              withLocalDeclD `event ((mkApp aa[1]! ξ).headBeta) fun ev => do
                let norm := part (Expr.proj ``And 0 ev) 4
                let t ← inferType norm
                let some native := t.find? (·.isAppOf `JanetCartan.PhysicalSamplingShells.nativeScalarOperator)
                  | throwError "original bare event: missing the actual native sampled operator"
                let args := native.getAppArgs
                let sz := args.size
                let D := args[sz-2]!
                unless D.isAppOfArity (root ++ `OriginalScalarFamily.kernel) 46 do
                  throwError "original bare event: not the original scalar46"
                let sc := D.getAppArgs
                let I := (← whnf (← inferType rows)).bindingDomain!
                let allRows ← withLocalDeclD `i I fun i => do
                  withLocalDeclD `sample (mkConst `JanetCartan.SeparatedSampling.Sample) fun q => do
                    let color := mkAppN (mkConst `JanetCartan.SeparatedSampling.color) #[x[2]!,Expr.proj ``Prod 0 q]
                    let z := mkAppN (mkConst `JanetCartan.SeparatedSampling.node) #[args[sz-4]!,mkApp args[sz-3]! i,q]
                    let row := mkAppN rows #[i,color,z]
                    let ty ← inferType row
                    let some φ := ty.find? (·.isAppOf `JanetCartan.PhysicalForwardMean.singleRetainedForwardPhase)
                      | throwError "original bare event: lost full individual phase"
                    let ra := sc[:43].toArray ++ #[i,sc[43]!,mkApp sc[44]! i,mkApp sc[45]! i]
                    let info ← getConstInfo (root ++ `OriginalScalarFamily.Row.kernel)
                    let some body := info.value? | throwError "original bare event: missing native row body"
                    let raw := (body.beta ra).getAppArgs
                    let phase := φ.getAppArgs
                    unless phase.size == 12 && raw.size == 22 do throwError "original bare event: changed actual phase coordinates"
                    for (lhs,rhs) in #[(phase[1]!,raw[1]!),(phase[5]!,raw[6]!),(phase[6]!,raw[7]!),
                        (phase[7]!,raw[9]!),(phase[10]!,mkApp raw[20]! color)] do
                      unless ← isDefEq lhs rhs do throwError "original bare event: bare/aggregate frame, ceiling or rate differs"
                    let same ← mkAppM ``OriginalBareEvent.uniform_bound #[mkAppN (mkConst (family ++ `sqrt_le_Cbare)) (b.push i),row]
                    mkLambdaFVars #[i,q] same
                let rateReach ← mkAppM `le_trans #[mkAppN (mkConst (family ++ `rate_le)) b,hb]
                let actualRates := mkAppN (mkConst (family ++ `rates)) (b ++ #[R,rateReach,hist[0]!])
                let meshBounds ← mkAppM ``OriginalBareEvent.mesh_bounds #[part actualRates 0]
                let every := tail actualRates 5
                let dy ← forallBoundedTelescope (← inferType every) (some 2) fun ic _ =>
                  mkLambdaFVars ic (tail (mkAppN every ic) 3)
                let original := Expr.proj ``And 0 ev
                let dev := mkAppN (part original 2) #[sc[43]!,mkApp (mkConst ``Nat.le_refl) sc[43]!]
                let tol := (← inferType dev).appArg!
                let exteriorArgs := sc ++ #[dy,x[45]!,args[sz-4]!,part meshBounds 0,tail meshBounds 1,ξ,part original 0,tol,dev]
                let aggregate := mkAppN (mkConst (root ++ `OriginalOuterTester.of_common_deviation)) exteriorArgs
                let cm := mkAppN (mkConst (root ++ `OriginalScalarFamily.Cmean)) (x[:26].toArray ++ x[27:36].toArray ++ #[x[40]!])
                let fixedTolerance ← mkAppM ``OriginalBareEvent.sqrt_tol_le #[cm,part actualRates 0]
                let fixedBound ← mkAppM `le_trans #[part aggregate 0,fixedTolerance]
                let aggregate ← mkAppM ``And.intro #[fixedBound,tail aggregate 1]
                let outerBound := mkAppN (mkConst (root ++ `OriginalOuterTester.native_bound_of_common_deviation)) exteriorArgs
                let outerBound ← mkAppM `le_trans #[outerBound,fixedTolerance]
                let some outer := (← inferType outerBound).find? (·.isAppOf `JanetCartan.PhysicalSamplingShells.nativeScalarOperator)
                  | throwError "original bare event: missing actual exterior scalar operator"
                let outerTest ← mkAppOptM (root ++ `OriginalSobolevTest.native_physical_amplitude_test)
                  (outer.getAppArgs.map some ++ #[some (field `Ctest),some outerBound])
                let weights := sc[:22].toArray
                let outerBounds := mkAppN (mkConst (root ++ `OriginalOuterWeights.patchBounds)) weights
                let hw ← mkAppM (root ++ `OriginalWindow.window_bounds) #[x[45]!]
                let geo ← withLocalDeclD `i I fun i => do
                  let g ← mkAppM `JanetCartan.Sampling.Realization.sampleGeometry_of_admissible
                    #[hw,mkApp outerBounds i,part meshBounds 0,tail meshBounds 1,mkApp args[sz-3]! i,mkApp (part original 0) i]
                  mkLambdaFVars #[i] g
                let hBox ← mkAppM `le_of_lt #[mkAppN (mkConst (root ++ `OriginalOuterWeights.hB)) weights]
                let budgetI := mkAppN (mkConst (root ++ `OriginalWeights.Index)) weights
                let fi ← synthInstance (← mkAppM ``Fintype #[budgetI])
                let budgets ← withTransparency .default <| mkAppOptM `JanetCartan.UniformStep.sampled_weight_budgets_originalScale
                  #[some budgetI,some fi,some x[2]!,none,none,some hBox,none,none,none,
                    some hw,some outerBounds,none,some (part actualRates 0),some args[sz-3]!]
                let qp := mkAppN (mkConst (root ++ `OriginalOuterWeights.quadrature)) (weights.push x[45]!)
                let quadrature ← forallBoundedTelescope (← inferType qp) (some 5) fun data _ => do
                  let q := mkAppN qp (data ++ #[args[sz-4]!,part meshBounds 0,tail meshBounds 1,args[sz-3]!,part original 0])
                  mkLambdaFVars data q
                let exterior ← mkAppM ``And.intro #[geo,← mkAppM ``And.intro #[budgets,quadrature]]
                let both ← mkAppM ``And.intro #[ev,← mkAppM ``And.intro #[aggregate,
                  ← mkAppM ``And.intro #[allRows,← mkAppM ``And.intro #[outerTest,exterior]]]]
                let pred ← mkLambdaFVars #[ξ] (← inferType both)
                let one ← mkAppOptM ``Exists.intro #[none,some pred,some ξ,some both]
                mkAppM ``Exists.elim #[mkAppN e profiles,← mkLambdaFVars #[ξ,ev] one]
            discard <| save `exists_with_native_individual_rows (p ++ #[hσ,R,hR] ++ hist ++ profiles) result

end JanetCartan.PhysicalSampling.OriginalBareEventApplication
end

