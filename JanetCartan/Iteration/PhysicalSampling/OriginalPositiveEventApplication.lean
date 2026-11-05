module

public import JanetCartan.Iteration.PhysicalBackground.NativeAdmission
public import JanetCartan.Iteration.PhysicalSampling.OriginalJointEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalSourceGraphCaps
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Put the actual protected native positive density into the one sampler

The two numerical raw half-budgets already construct one original `NativeDensity.v`.
Use exactly its label pullback and four low-density facts, at a joint scale fixed
before the history. Only its all-order initial scalar profile and the two joint
uncut response conclusions for THAT scalar remain. Neither a free low density
nor a second inverse/shift is retained (`app:ch_background:prop:bg-current`,
`new:eq:amplitude-test`, `app:ch_response:cor:current-atoms`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalPositiveEventApplication

private theorem both_intervals {σ a b : ℝ} (h : σ ∈ Set.Ioc 0 (min a b)) :
    σ ∈ Set.Ioc 0 a ∧ σ ∈ Set.Ioc 0 b :=
  ⟨⟨h.1,h.2.trans (min_le_left _ _)⟩,⟨h.1,h.2.trans (min_le_right _ _)⟩⟩

private theorem positive_of_native_range {a : ℝ}
    (h : a ∈ Set.Icc (1/2 : ℝ) (3/2)) : 0 < a := by linarith [h.1]

/-- The fixed low density's native grade is already paid by the shared raw-row
reserve. This does not assert the stronger, separate all-order initial bound. -/
private theorem native_density_low_reserve {n rStar : ℕ} (hn : 5 ≤ n)
    (h : 16 + RawPrimary.SliceBounds.rawSliceParameterOrder n ≤ rStar) :
    ((2*(n+1)+14) + (3+(n-1)) + 2) + 1 +
      2*ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar := by
  simp only [RawPrimary.SliceBounds.rawSliceParameterOrder, RawPrimary.SliceBounds.rawSliceJetOrder] at h
  simp only [ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder]
  omega

end JanetCartan.PhysicalSampling.OriginalPositiveEventApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalPositiveEventApplication
open Lean Meta Elab Command Term
open PhysicalBackground.NativeReferenceSourceTemplate (termWith)

private def root := `JanetCartan.PhysicalSampling
private def ns := root ++ `OriginalPositiveEvent
private def admission := root ++ `OriginalSourceGraphAdmission
private def positive := `JanetCartan.PhysicalBackground.NativeAdmission
private def stage := root ++ `OriginalCommonStage
private def joint := root ++ `OriginalJointEvent.exists_of_initial_and_response_profiles

private def save (short : Name) (xs : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let target ← match target? with
    | some t => pure t
    | none => inferType value
  let t ← instantiateMVars (← mkForallFVars xs target)
  let v ← instantiateMVars (← mkLambdaFVars xs value)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "original positive event: open {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type := t, value := v, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type := t, value := v}) (forceExpose := true)
  return mkAppN (mkConst name) xs

private def original21 (x : Array Expr) : MetaM (Array Expr) := do
  let n := (← inferType x[1]!).appArg!
  let merged := mkAppN (mkConst (root ++ `samplingCappedExtra)) #[x[0]!, x[1]!, x[2]!, x[21]!]
  return #[n,x[1]!] ++ x[3:21].toArray ++ #[merged]

/-- The native background cap is not identified with a graph cap. BOTH are
positive on the same immutable selector; take their numerical minimum. -/
elab "admit_original_positive_event_scale" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (admission ++ `scaleCeiling)).type (some 26) fun p _ => do
    let native ← original21 p
    let left := mkAppN (mkConst (admission ++ `scaleCeiling)) p
    let right := mkAppN (mkConst (positive ++ `sourceCap)) native
    let cap ← save `scaleCeiling p (← mkAppM ``Min.min #[left,right]) true
    discard <| save `scaleCeiling_pos p (← mkAppM `lt_min
      #[mkAppN (mkConst (admission ++ `scaleCeiling_pos)) p,mkAppN (mkConst (positive ++ `sourceCap_pos)) native])
      false (some (← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,cap]))
    withLocalDeclD `σ (mkConst ``Real) fun σ => do
      let t ← termWith [(`sigma,σ),(`cap,cap)] "sigma ∈ Set.Ioc (0 : ℝ) cap"
      withLocalDeclD `hσ t fun hσ => do
        let both := mkAppN (mkConst ``both_intervals) #[σ,left,right,hσ]
        let four := mkAppN (mkConst (admission ++ `scale_admissions)) (p ++ #[σ,Expr.proj ``And 0 both])
        discard <| save `scale_admissions (p ++ #[σ,hσ]) (← mkAppM ``And.intro #[four,Expr.proj ``And 1 both])
  logInfo "one pre-source positive cap meets the actual native density, sampling/signed graphs and both native source admissions"

/-- The single R₀ reaches the original protected native density as well as all
actual event rows. The four density premises were about the supplied V itself,
not about an unrelated profile with a matching estimate. -/
private def withPositiveStatic (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (stage ++ `S)).type (some 46) fun p _ => do
    let n := (← inferType p[1]!).appArg!
    let r := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    let need ← mkAppM ``HAdd.hAdd #[mkNatLit 16,r]
    withLocalDeclD `hSharedReserve (← mkAppM ``LE.le #[need,p[31]!]) fun hReserve => do
      let x := p.push hReserve
      let fixed ← original21 x
      let native := fixed ++ #[x[27]!,x[36]!,x[37]!] ++ x[29:33].toArray ++ #[x[38]!,x[35]!,x[39]!]
      let low := mkAppN (mkConst ``native_density_low_reserve) #[fixed[0]!,x[31]!,x[1]!,hReserve]
      k x (native.push low)

elab "choose_original_positive_event_threshold " which:num : command => liftTermElabM <| withTransparency .reducible <| withPositiveStatic fun x p32 => do
    let bgS := mkAppN (mkConst (positive ++ `S)) p32
    let stS := mkAppN (mkConst (stage ++ `S)) x[:46].toArray
    let S := mkAppN (mkConst (ns ++ `S)) x
    match which.getNat with
    | 0 => discard <| save `S x (← mkAppM ``Max.max #[stS,bgS]) true
    | 1 => discard <| save `stage_le x (← mkAppM `le_max_left #[stS,bgS]) false (some (← mkAppM ``LE.le #[stS,S]))
    | 2 => discard <| save `native_le x (← mkAppM `le_max_right #[stS,bgS]) false (some (← mkAppM ``LE.le #[bgS,S]))
    | 3 => discard <| save `hS x (← mkAppM `le_trans #[mkAppN (mkConst (stage ++ `hS)) x[:46].toArray,mkAppN (mkConst (ns ++ `stage_le)) x])
    | _ => throwError "original positive event: unknown prehistory threshold field"
    logInfo m!"checked native positive and original sampler threshold field {which.getNat} before the physical history"

elab "put_native_positive_labels_in_original_event" : command => liftTermElabM <| withTransparency .reducible <| withPositiveStatic fun x p32 => do
    let S := mkAppN (mkConst (ns ++ `S)) x
    let hstage := mkAppN (mkConst (ns ++ `stage_le)) x
    let hbg := mkAppN (mkConst (ns ++ `native_le)) x
    let scaleT := (← whnf (← inferType (mkAppN (mkConst (positive ++ `labels)) p32))).bindingDomain!
    withLocalDeclD `hσbackground scaleT fun hσ => withLocalDeclD `R₀ (mkConst ``Real) fun R => do
      withLocalDeclD `hReached (← mkAppM ``LE.le #[S,R]) fun hR => do
        let hs ← mkAppM `le_trans #[hstage,hR]
        let hb ← mkAppM `le_trans #[hbg,hR]
        let atR := mkAppN (mkConst joint) (x ++ #[R,hs])
        forallBoundedTelescope (← inferType atR) (some 4) fun hist _ => do
          let p39 := p32 ++ #[hσ,R,hb] ++ hist
          let bg (name : Name) := mkAppN (mkConst (positive ++ name)) p39
          let mut applied := mkAppN atR (hist.push (bg `labels))
          for j in [:4] do
            let .forallE _ domain _ _ ← whnf (← inferType applied)
              | throwError "original positive event: changed native four low obligations"
            let p ← match j with
              | 0 => forallBoundedTelescope domain (some 1) fun v t => do
                let s := mkApp (bg `labels_smooth) v[0]!
                let st ← inferType s
                unless st.isAppOfArity ``ContDiff 10 && t.isAppOf ``ContDiffOn do
                  throwError "original positive event: changed native label smoothness target"
                let a := st.getAppArgs
                let arg := mkAppN (mkConst ``ContDiff.contDiffOn st.getAppFn.constLevels!)
                  (a[:8].toArray ++ #[t.appArg!,a[9]!,a[8]!,s])
                mkLambdaFVars v arg
              | 1 | 2 => forallBoundedTelescope domain (some 3) fun w _ => do
                let hr := mkAppN (bg `labels_range) w[:2].toArray
                let result ← if j == 1 then mkAppM ``positive_of_native_range #[hr] else pure hr
                mkLambdaFVars w result
              | _ => pure (bg `labels_C15)
            applied := mkApp applied p
            logInfo m!"assembled original positive-density field {j} on the same native history"
          forallBoundedTelescope (← inferType applied) (some 3) fun high _ => do
            unless high.size == 3 do throwError "original positive event: expected true high scalar and two response inputs"
            let publicParams := x ++ #[hσ,R,hR] ++ hist ++ high
            let proof := mkAppN applied high
            unless (← whnf (← inferType proof)).isAppOfArity ``Exists 2 do
              throwError "original positive event: lost the actual one common shift"
            discard <| save `exists_of_high_initial_and_response_profiles publicParams proof
    logInfo "same actual NativeAdmission.labels and all four low clauses consumed; only high initial profile and joint uncut response smoothness/jets remain at the original physical history"

end JanetCartan.PhysicalSampling.OriginalPositiveEventApplication
