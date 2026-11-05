module

public meta import Lean

/-! Specialization and assembly of the original strong source, arbitrary tested
normal comparison, fixed-vector adjoint comparison, and finite high reserve.
All cached terms below are closed ordinary declarations checked by the kernel;
selectors are recovered from the *same* `StrongSource` proof and never changed. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.HistoryApplication
open Lean Meta Elab Term Command

private def sourceNS := `JanetCartan.PhysicalNormalInverse.StrongSource
private def rawNS := `JanetCartan.PhysicalInverseContinuity.StrongRaw
private def cacheNS := `JanetCartan.PhysicalInverseContinuity.StrongRaw.History
private def normalNS := `JanetCartan.PhysicalNormalInverse.StrongSource.NormalTolerance

private def term (s : String) (expected : Option Expr := none) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term s | throwError "cannot parse raw history term: {s}"
  Term.withoutErrToSorry do
    let out ← elabTermEnsuringType stx expected
    synthesizeSyntheticMVarsNoPostponing
    let out ← instantiateMVars out
    if out.hasSorry || out.hasMVar then throwError "unresolved raw history term: {s}"
    return out

private partial def withAliases (pairs : List (Name × Expr)) (act : TermElabM Expr) : TermElabM Expr := do
  match pairs with
  | [] => act
  | (name, value) :: tail =>
    withLetDecl name (← inferType value) value fun x => do
      let t ← withAliases tail act
      return t.replaceFVar x value

private def store (name : Name) (xs : Array Expr) (value : Expr) (data := false) : TermElabM Expr := do
  let name := cacheNS ++ name
  let type ← instantiateMVars (← mkForallFVars xs (← inferType value))
  let value ← instantiateMVars (← mkLambdaFVars xs value)
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar || type.hasFVar || value.hasFVar ||
      type.hasSorry || value.hasSorry then throwError "open or recovered history proof: {name}"
  if data then
    addDecl (.defnDecl {name, type, value, levelParams := [], hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, type, value, levelParams := []}) (forceExpose := true)
  return mkAppN (mkConst name) xs

private def splitChoice (name specName hName tailName : Name) (xs : Array Expr) (value : Expr) :
    TermElabM (Expr × Expr × Expr) := do
  let type ← whnf (← inferType value)
  unless type.isAppOfArity ``Exists 2 do throwError "history choice {name} is not existential"
  let chosen ← store name xs (← mkAppM ``Classical.choose #[value]) true
  let spec := (← mkAppM ``Classical.choose_spec #[value])
  let specType := type.appArg!.beta #[chosen]
  let proofType ← instantiateMVars (← mkForallFVars xs specType)
  let proof ← instantiateMVars (← mkLambdaFVars xs spec)
  if proofType.hasFVar || proofType.hasMVar || proofType.hasSorry || proof.hasFVar || proof.hasMVar || proof.hasSorry then
    throwError "open history choice specification {specName}"
  addDecl (.thmDecl {name := cacheNS ++ specName, type := proofType, value := proof, levelParams := []}) (forceExpose := true)
  let actualSpec := mkAppN (mkConst (cacheNS ++ specName)) xs
  let h ← store hName xs (← mkAppM ``And.left #[actualSpec])
  let tail ← store tailName xs (← mkAppM ``And.right #[actualSpec])
  return (chosen, h, tail)

private def actualArgs (xs : Array Expr) : MetaM (Array Expr) := do
  let info ← getConstInfo (sourceNS ++ `exists_history_coercivity)
  let proof := (info.value! (allowOpaque := true)).beta xs
  unless proof.isAppOfArity `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity 134 do
    throwError "raw history: original134 physical source arguments changed"
  return proof.getAppArgs

private def staticArg (args : Array Expr) (wanted : Name) : MetaM Expr := do
  let info ← getConstInfo `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity
  forallBoundedTelescope info.type (some 134) fun xs _ => do
    for x in xs, arg in args do
      if (← x.fvarId!.getDecl).userName == wanted then return arg
    throwError "raw history: missing original selector {wanted}"

private def zeroArgs (xs : Array Expr) : MetaM (Array Expr) := do
  let v := ((← getConstInfo (rawNS ++ `referenceCarrier)).value! (allowOpaque := true)).beta xs
  unless v.isAppOfArity `JanetCartan.PhysicalNormalInverse.StrongSourceGap.Vop 28 do
    throwError "raw history: zero source carrier is not the original Vop"
  return v.getAppArgs

private def budgetContext : TermElabM Expr :=
  term "∀ (m : ℕ) (_hreserve : m + 1 + 2 * canonicalCarrierLowOrder n ≤ rStar) (Cadj Czero : ℝ) (_hCadj : 0 ≤ Cadj) (_hCzero : 0 ≤ Czero) (e₀ : OutputL2 n) (_he₁ : e₀ ∈ periodicSobolevLevel n (Euclidean n) 1) (_heHigh : e₀ ∈ periodicSobolevLevel n (Euclidean n) (m + 1)) (δ : ℝ) (_hδ : 0 < δ), True"

/-- Fix the actual low tolerance and both the normal and physical-jet
frequency thresholds *before* the first history. The perturbation transfers
at the original gap/half-gap pair, not a gap reselected from the accuracy. -/
elab "prepare_actual_source_raw_history" : command => liftTermElabM do
  let info ← getConstInfo (sourceNS ++ `exists_history_coercivity)
  forallBoundedTelescope info.type (some 29) fun source _ => do
    let args ← actualArgs source
    let fixed := source[:23].toArray
    let vArgs ← zeroArgs fixed
    let raw := mkAppN (mkConst (rawNS ++ `reference_uncorrected)) fixed
    let sourceGap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongSourceGap.augmented_adjoint_gap) vArgs
    let some normal := (← inferType raw).find? (·.isAppOf `JanetCartan.CoerciveInverse.normalOperator) |
      throwError "raw history: original reference estimate lost the normal operator"
    let Aref ← store `referenceRow fixed normal.appArg! true
    let hGlobal ← staticArg args `hglobalGap
    let H ← staticArg args `H
    let scale := source[21]!
    let G ← store `referenceMap fixed (← mkAppM `JanetCartan.sourceDilation #[← mkAppM `JanetCartan.FlatReference.map #[H], scale]) true
    let hG ← withAliases [(`sourceReference, H), (`referenceMap, G)] <| term
      "(show ContDiff ℝ ∞ referenceMap from contDiff_sourceDilation sourceReference.contDiff)"
    discard <| store `reference_smooth fixed hG
    forallTelescope (← budgetContext) fun x _ => do
      unless x.size == 11 do throwError "raw history: expected eleven budget and datum arguments"
      let full := source ++ x
      let primitive ← withAliases [(`referenceRow, Aref), (`sourceRaw, raw), (`sourceGap, sourceGap),
          (`hGlobal, hGlobal)] <| term
        "exists_raw_grade_perturbation_tolerance (m := m) (rStar := rStar) (Bcan := canonicalCarrierLowOrder n) (Czero := Czero) (Be := (periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) e₀ + 1) referenceRow e₀ (half_pos (half_pos hGlobal)) (half_pos hGlobal) sourceGap (by omega) _hCzero (add_nonneg ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg _ _) zero_le_one) ((sourceRaw.2 (m + 1) e₀ _heHigh).1) _hδ"
      let (η, hη, _) ← splitChoice `η `η_spec `hη `perturbation full primitive
      let strong := mkAppN (mkConst (rawNS ++ `exists_source_adjoint_tolerance))
        (fixed ++ #[x[6]!, x[7]!, x[2]!, x[4]!, η, hη])
      let (_d, hd, _) ← splitChoice `jetRadius `jet_spec `jet_pos `physical_adjoint full strong
      let near ← withAliases [(`actualBand, source[24]!), (`actualOrder, source[28]!), (`radiusPos, hd)] <| term
        "PhysicalHistory.exists_initialScale_for_prefix_neighborhood (N := embeddingDimension n) actualBand actualOrder radiusPos"
      let (SF, hSF, _) ← splitChoice `SF `SF_spec `hSF `physical_prefix full near
      let SN := mkAppN (mkConst (normalNS ++ `S)) (source ++ #[η, hη])
      let S ← store `S full (← mkAppM ``max #[SF, SN]) true
      let hS ← withAliases [(`SFseed, SF), (`SNseed, SN), (`hSFseed, hSF), (`Sseed, S)] <| term
        "(show 2 ≤ Sseed from hSFseed.trans (le_max_left SFseed SNseed))"
      discard <| store `hS full hS
    logInfo "fixed actual half-gap, perturbation tolerance and joint prehistory frequency before all histories"

private def existsWith (value certificate : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  let predicate ← withLocalDeclD `bound (← inferType value) fun a =>
    mkLambdaFVars #[a] (type.replace fun e => if e == value then some a else none)
  mkAppOptM ``Exists.intro #[none, some predicate, some value, some certificate]

/-- Derive the fixed-grade difference on every actual admissible prefix.
The remaining primitive current clauses are precisely the native current row
outputs (tests, adjoint realization, order-one adjoint, coercivity, raw
membership and zero-density high bound). Neither normal nor strong-vector
convergence is an input; both are proved on this same history and operator. -/
elab "apply_actual_source_raw_history" : command => liftTermElabM do
  let info ← getConstInfo (cacheNS ++ `S)
  forallBoundedTelescope info.type (some 40) fun full _ => do
    unless full.size == 40 do throwError "raw history: expected 29 + 11 inputs"
    let source := full[:29].toArray
    let fixed := full[:23].toArray
    let density := (← zeroArgs fixed)[23:].toArray
    let cache (field : Name) := mkAppN (mkConst (cacheNS ++ field)) full
    let η := cache `η
    let hη := cache `hη
    let S := cache `S
    let SF := cache `SF
    let SN := mkAppN (mkConst (normalNS ++ `S)) (source ++ #[η, hη])
    let normalAll := mkAppN (mkConst (normalNS ++ `continuation)) (source ++ #[η, hη] ++ density)
    let F₀ := mkAppN (mkConst (cacheNS ++ `referenceMap)) fixed
    let hF₀ := mkAppN (mkConst (cacheNS ++ `reference_smooth)) fixed
    let b := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b) source[:2]
    let hb ← withAliases [(`actualRadius, mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b_lt_R) source[:2])] <|
      term "actualRadius.le"
    let out ← forallBoundedTelescope (← inferType normalAll) (some 1) fun r _ => do
      let R₀ := r[0]!
      withLocalDeclD `hReached (← mkAppM ``LE.le #[S, R₀]) fun hReached => do
        let hN ← withAliases [(`physThreshold, SF), (`normThreshold, SN), (`reached, hReached)] <|
          term "(le_max_right physThreshold normThreshold).trans reached"
        let hF ← withAliases [(`physThreshold, SF), (`normThreshold, SN), (`reached, hReached)] <|
          term "(le_max_left physThreshold normThreshold).trans reached"
        let normalAt := mkAppN normalAll #[R₀, hN]
        let family ← forallBoundedTelescope (← inferType normalAt) (some 9) fun z _ => do
          unless z.size == 9 do throwError "raw history: expected nine true prefix/current-row arguments"
          let j := z[0]!
          let hist := z[1]!
          let ell := z[2]!
          let hu := z[3]!
          let normalNow := mkAppN normalAt z
          let some normal := (← inferType normalNow).find? (fun t ↦
            t.isAppOf `JanetCartan.ContinuumRow.augmentedNormal && t.containsFVar z[7]!.fvarId!) |
            throwError "raw history: expected the actual tested current normal"
          let A := mkAppN (mkConst `JanetCartan.ContinuumRow.augmentedRow normal.getAppFn.constLevels!) normal.getAppArgs
          let F ← mkAppM `JanetCartan.RevisedGlobal.finiteMap #[F₀, hist]
          let hsm ← withAliases [(`actualPrefix, hist), (`sourceSmooth, hF₀), (`actualF, F)] <| term
            "(show ContDiff ℝ ∞ actualF from sourceSmooth.add (ContDiff.sum (fun i _ ↦ (actualPrefix i).smooth')))"
          let physical := mkAppN (cache `physical_adjoint) #[F, hsm]
          let nearType := (← whnf (← inferType physical)).bindingDomain!
          let some jet := nearType.find? (·.isAppOf `JanetCartan.cNorm) |
            throwError "raw history: expected actual immersion jets in the strong-vector tolerance"
          let ja := jet.getAppArgs
          let K := ja[ja.size - 3]!
          let hK ← term "isCompact_closedBall _ _" (some (← mkAppM `IsCompact #[K]))
          let prefixNear := mkAppN (cache `physical_prefix) #[R₀, hF, K, F₀, hK, j, hist, ell, hu]
          let near ← withAliases [(`nearPrefix, prefixNear), (`radiusPos, cache `jet_pos)] <| term
            "(cNorm_mono_order (show 1 + canonicalCarrierLowOrder n ≤ rStar by omega)).trans_lt (nearPrefix.trans (half_lt_self radiusPos))" (some nearType)
          let actualAdj := mkAppN physical #[near, z[4]!, z[5]!, z[6]!, z[7]!]
          let v ← forallBoundedTelescope (← inferType actualAdj) (some 1) fun actions _ => do
            let adjAt := mkAppN actualAdj (actions ++ #[b, hb])
            let v ← forallBoundedTelescope (← inferType adjAt) (some 1) fun regularity _ => do
              let adjNow := mkAppN adjAt regularity
              let tr := mkApp (cache `perturbation) A
              let v ← forallBoundedTelescope (← inferType tr) (some 1) fun e _ => do
                let T ← mkAppM `JanetCartan.currentCoefficientScale #[R₀, j]
                let atDatum := mkAppN tr (e ++ #[T])
                let result ← forallBoundedTelescope (← inferType atDatum) (some 5) fun native _ => do
                  unless native.size == 5 do throwError "raw history: expected native gap, high datum and raw clauses"
                  let atSmall := mkAppN atDatum native
                  let result ← forallBoundedTelescope (← inferType atSmall) (some 1) fun small _ => do
                    let result := mkAppN atSmall (small ++ #[normalNow, adjNow])
                    mkLambdaFVars small (← instantiateMVars result)
                  mkLambdaFVars native result
                mkLambdaFVars e result
              mkLambdaFVars regularity v
            mkLambdaFVars actions v
          mkLambdaFVars z v
        mkLambdaFVars #[R₀, hReached] family
    let cont ← store `continuation full out
    let scale ← existsWith S (← mkAppM ``And.intro #[cache `hS, cont])
    let budget ← existsWith η (← mkAppM ``And.intro #[hη, scale])
    discard <| store `exists_history_raw_grade_tolerance full budget
    logInfo "actual original29: derived tested normal, fixed-vector raw adjoint and high-reserve transfer on one physical history"

end JanetCartan.PhysicalInverseContinuity.HistoryApplication
end
