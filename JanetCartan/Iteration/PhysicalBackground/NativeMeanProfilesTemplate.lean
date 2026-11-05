module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Apply the whole protected-weight mean profile to the actual current

This specializes existing real fixed-pullback and weighted-mean estimates.
The original whole product, full leading cell and protected outer chi are
retained. No successful principal/mean estimate is a hypothesis.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeMeanProfilesTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

private def targetNS := `JanetCartan.PhysicalBackground.NativeMeanProfiles

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do throwError "native mean profiles: target mismatch {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasFVar || type.hasFVar || value.hasMVar || type.hasMVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native mean profiles: open or history-dependent choice {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  let t ← whnf (← inferType proof)
  if t.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

private def carrierEqualityCode : String :=
  "(by\n" ++
  "  intro p hp\n" ++
  "  have hc := retainedTransportMatrix_eq_fullPrincipal_on_graph current Phi Y initial hCompat (hCoordinates (hSProduct hp))\n" ++
  "  ext i j\n" ++
  "  apply Complex.ofReal_injective\n" ++
  "  exact congrArg (fun A : Matrix (Fin N) (Fin n) ℂ ↦ A i j) hc\n" ++
  "  : Set.EqOn D (fullPrincipal ∘ graph) S)"

private def carrierProfileCode : String :=
  "(by\n" ++
  "  intro s\n" ++
  "  have he : cNorm J s D = cNorm J s (fullPrincipal ∘ graph) := by\n" ++
  "    apply GeometricProfile.cNorm_eq_of_eventuallyEq\n" ++
  "    intro p hp\n" ++
  "    exact eventuallyEq_of_mem (hS.mem_nhds (hJS hp)) (fun q hq ↦ hEq hq)\n" ++
  "  rw [he]\n" ++
  "  have hp := hPull fullPrincipal (fun w hw ↦ hFullSmooth.contDiffAt (hO.mem_nhds (hJO hw))) s\n" ++
  "  have hp' : cNorm J s (fullPrincipal ∘ graph) ≤ Cpull s * cNorm Jfull s fullPrincipal := hp\n" ++
  "  have hf : cNorm Jfull s fullPrincipal ≤ Cfull s * scale ^ (s - reserve) := hFullProfile s\n" ++
  "  change cNorm J s (fullPrincipal ∘ graph) ≤ (Cpull s * Cfull s) * scale ^ (s - reserve)\n" ++
  "  exact hp'.trans ((mul_le_mul_of_nonneg_left hf (hPullPos s).le).trans_eq (mul_assoc _ _ _).symm)\n" ++
  "  : HasDerivativeProfile J D reserve scale Ccarrier)"

elab "realize_native_whole_weight_mean_profiles" : command => liftTermElabM do
  let admission := `JanetCartan.PhysicalBackground.NativeAdmission
  let native := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let density := `JanetCartan.PhysicalBackground.NativeDensity
  let source := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let outer := `JanetCartan.PhysicalBackground.OriginalOuterCutoff
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let leaf := `JanetCartan.PhysicalBackground.NativeLeadingProfiles
  let cellNS := `JanetCartan.PhysicalPrimary.LeadingCell
  let rawInfo ← getConstInfo (admission ++ `raw)
  forallBoundedTelescope rawInfo.type (some 39) fun all _ => do
    unless all.size == 39 do throwError "native mean profiles: expected actual admission39"
    let raw := ((rawInfo.value! (allowOpaque := true)).beta all).headBeta
    unless raw.isAppOfArity (native ++ `rawCurrent) 47 do
      throwError "native mean profiles: changed same native raw47"
    let nativeArgs := raw.getAppArgs
    let fixed := all[:31].toArray
    let original := all[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let src (name : Name) := mkAppN (mkConst (source ++ name)) selected
    let out (name : Name) := mkAppN (mkConst (outer ++ name)) selected
    let datum := ((← getConstInfo (native ++ `measuredDatum)).value! (allowOpaque := true)).beta nativeArgs
    let some mean := datum.find? (·.isAppOfArity `JanetCartan.PositiveBackground.physicalDensityMean 7) |
      throwError "native mean profiles: no literal physical mean in native datum"
    let meanArgs := mean.getAppArgs
    let n := meanArgs[0]!
    let N := meanArgs[1]!
    let index := meanArgs[2]!
    let fin := meanArgs[3]!
    let d := mkAppN (mkConst (density ++ `carrier)) nativeArgs
    unless ← isDefEq meanArgs[5]! (src `χ) do
      throwError "native mean profiles: the actual outer chi was replaced"
    let mu := src `r
    let hr := src `hr
    let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[all[33]!, all[35]!]
    let hScale ← termWith [(`R0, all[33]!), (`stage, all[35]!),
        (`hThreshold, mkAppN (mkConst (admission ++ `hS)) all[:32].toArray), (`hReached, all[34]!)]
      "(one_le_currentCoefficientScale (by linarith [hThreshold.trans hReached]) stage : 1 ≤ currentCoefficientScale R0 stage)"
    withLocalDeclD `rSource (mkConst ``Nat) fun reserve => do
      let hReserveType ← termWith [(`reserve, reserve), (`rStar, fixed[26]!)] "reserve + 14 ≤ rStar"
      withLocalDeclD `hReserve hReserveType fun hReserve => do
        let publicParams := all[:33].toArray ++ #[reserve, hReserve] ++ all[33:].toArray
        let (smooth, profiles, normalSmooth, covectorSmooth) ← withLocalDeclD `i index fun i => do
          let static := fixed.push i
          let mut current := mkApp (mkAppN (mkConst (admission ++ `current)) all) i
          for _ in [:8] do
            if current.isAppOfArity (leading ++ `Selected.current) 38 then break
            let some name := current.getAppFn.constName? |
              throwError "native mean profiles: current alias is not a constant application"
            let some body := (← getConstInfo name).value? (allowOpaque := true) |
              throwError "native mean profiles: current alias body unavailable {name}"
            current := (body.beta current.getAppArgs).headBeta
          unless current.isAppOfArity (leading ++ `Selected.current) 38 do
            throwError "native mean profiles: current left the unchanged selected leading cell"
          let leadingArgs := current.getAppArgs
          for j in [:31] do
            unless ← isDefEq fixed[j]! leadingArgs[j]! do
              throwError "native mean profiles: changed native leading input {j}"
          unless ← isDefEq i leadingArgs[37]! do
            throwError "native mean profiles: changed selected index"
          let currentBody := ((← getConstInfo (leading ++ `Selected.current)).value!
            (allowOpaque := true)).beta leadingArgs
          let currentBody := currentBody.headBeta
          unless currentBody.isAppOfArity (cellNS ++ `current) 36 do
            throwError "native mean profiles: changed leading current36"
          let cellArgs := currentBody.getAppArgs
          let cell (name : Name) := mkAppN (mkConst (cellNS ++ name)) cellArgs
          let stable (name : Name) := mkAppN (mkConst (leaf ++ name)) static
          let actual (name : Name) := mkAppN (mkConst (leaf ++ name)) leadingArgs
          let T := cellArgs[4]!
          let P := cellArgs[1]!
          let chi := mkApp (src `χ) i
          let window := mkApp (out `window) i
          let hChiWindow := mkApp (out `support_window) i
          let hChiCompact := mkApp (src `χ_compact) i
          let hP := mkApp (src `hP) i
          let J ← store `J static (← termWith [(`n, n), (`mu, mu), (`chi, chi)]
            "Metric.closedBall (0 : Euclidean n) (5 * mu) ×ˢ tsupport chi") true
          let S ← store `carrier_open_set static (← termWith [(`n, n), (`mu, mu), (`window, window)]
            "Metric.ball (0 : Euclidean n) (6 * mu) ×ˢ window") true
          let bindings := [(`n, n), (`N, N), (`mu, mu), (`hr, hr), (`chi, chi),
            (`window, window), (`Vold, mkApp (src `Voriginal) i), (`P, P), (`T, T),
            (`J, J), (`S, S), (`hChiWindow, hChiWindow), (`hChiCompact, hChiCompact),
            (`hWindow, mkApp (out `hwindow) i), (`hP, hP),
            (`hProduct, mkApp (src `hproduct) i), (`hOldGraph, stable `graph_into_full),
            (`Eold, stable `outer_product), (`Jfull, stable `Jfull)]
          let hJ ← store `J_compact static (← termWith bindings
            "((isCompact_closedBall _ _).prod hChiCompact.isCompact : IsCompact J)")
          let hS ← store `carrier_open static (← termWith bindings
            "(isOpen_ball.prod hWindow : IsOpen S)")
          let hJS ← store `J_subset_open static (← termWith bindings
            "(by intro p hp; exact ⟨closedBall_subset_ball (by linarith only [(show 0 < mu from hr)]) hp.1, hChiWindow hp.2⟩ : J ⊆ S)")
          let hSProduct ← termWith bindings
            "(by intro p hp; exact hProduct (q := p) ⟨ball_subset_closedBall hp.1, hp.2⟩ : S ⊆ Eold)"
          let hGraphJ ← termWith bindings
            "(by intro p hp; apply hOldGraph; exact hProduct (q := p) ⟨closedBall_subset_closedBall (show 5 * mu ≤ 6 * mu by linarith only [(show 0 < mu from hr)]) hp.1, hChiWindow hp.2⟩ : MapsTo (carrierGraph T) J Jfull)"
          let hPsi ← termWith bindings
            ("(by\n" ++
             "  apply (carrierGraph_smooth T hP).mono\n" ++
             "  intro p hp\n" ++
             "  refine ⟨Set.mem_univ _, ?_⟩\n" ++
             "  have hz : p.2 ∈ originalOuterWindow Vold P.radius := hp.2\n" ++
             "  intro j\n" ++
             "  exact (hz.2 j).trans_le (by change P.radius ≤ 2 * P.radius; linarith only [(show 0 < P.radius from hP.1)])\n" ++
             "  : ContDiffOn ℝ ∞ (carrierGraph T) S)")
          let pullExists ← termWith (bindings ++ [(`hJ, hJ), (`hS, hS), (`hJS, hJS),
              (`hPsi, hPsi), (`hGraphJ, hGraphJ), (`hJfull, stable `Jfull_compact)])
            ("ActualCarriers.ConstructedCarrierJets.exists_cNorm_fixed_pullback_le " ++
             "(G := Matrix (Fin N) (Fin n) ℝ) hJ hJfull " ++
             "(fun p hp ↦ hPsi.contDiffAt (hS.mem_nhds (hJS hp))) hGraphJ")
          let Cpull ← store `pullbackC static (← mkAppM ``Classical.choose #[pullExists]) true
          let pullSpec ← mkAppM ``Classical.choose_spec #[pullExists]
          let hPullPos ← store `pullbackC_pos static (.proj ``And 0 pullSpec)
          let hPull ← store `pullback_bound static (.proj ``And 1 pullSpec)
          let Cfull := stable `C
          let Ccarrier ← store `carrierC static (← termWith [(`Cpull, Cpull), (`Cfull, Cfull)]
            "fun s : ℕ ↦ Cpull s * Cfull s") true
          discard <| store `carrierC_pos static (← termWith
            [(`Ccarrier, Ccarrier), (`hPullPos, hPullPos), (`hFullPos, stable `C_pos)]
            "(fun s ↦ mul_pos (hPullPos s) (hFullPos s) : ∀ s, 0 < Ccarrier s)")
          let geometry := actual `geometry
          let hO ← component geometry 0
          let O := (← inferType hO).appArg!
          let hJO ← termWith [(`Jfull, stable `Jfull), (`O, O),
              (`hTwo, ← component geometry 3), (`hRadius, stable `Jfull_radius_pos)]
            "(by exact (closedBall_subset_closedBall (by linarith [hRadius])).trans hTwo : Jfull ⊆ O)"
          let initial ← termWith [(`n, n), (`sigma, fixed[21]!)]
            "fun _ : Euclidean (n - 1) × Euclidean 3 ↦ sigma"
          let fullPrincipal := actual `full_principal
          let Q := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingData.Q) cellArgs.pop
          let proofBindings := bindings ++ [(`current, current), (`Q, Q), (`F, cellArgs[30]!),
            (`row, cell `row), (`col, cell `col), (`Phi, cell `Φ), (`Y, cell `Y),
            (`initial, initial), (`O, O), (`hO, hO), (`hx, ← component geometry 1),
            (`hDomain, ← component geometry 2), (`hF, cellArgs[31]!), (`hi, cellArgs[32]!),
            (`hrank, cellArgs[33]!), (`hNull, actual `null_smooth),
            (`hCompat, actual `constant_compatible), (`hCoordinates, ← component geometry 6),
            (`fullPrincipal, fullPrincipal), (`graph, stable `graph), (`hSProduct, hSProduct)]
          let hFullNormal := mkAppN (mkConst `JanetCartan.ContinuumRow.LeadingPrimitive.fullNormal_smooth)
            #[n, N, cellArgs[1]!, cellArgs[2]!, cellArgs[3]!, cellArgs[4]!, Q, cellArgs[30]!,
              cell `row, cell `col, cell `Φ, cell `Y, initial, O, hO,
              ← component geometry 1, ← component geometry 2, cellArgs[31]!, cellArgs[32]!,
              cellArgs[33]!, actual `null_smooth]
          let hFullCovector ← termWith proofBindings
            "(phaseGradient_joint_smooth T Q).mono hDomain"
          let hFullSmooth ← termWith
            (proofBindings ++ [(`hFullNormal, hFullNormal), (`hFullCovector, hFullCovector)])
            "(contDiff_principalMatrix_pair.comp_contDiffOn (hFullNormal.prodMk hFullCovector) : ContDiffOn ℝ ∞ fullPrincipal O)"
          let D ← store `carrier_principal (all.push i) (← termWith [(`n, n), (`di, mkApp d i)]
            "fun p : Euclidean n × CarrierParameter ↦ principalMatrix (di.normalField p.1 p.2) (di.covector p.1 p.2)") true
          let hEq ← termWith (proofBindings ++ [(`D, D)]) carrierEqualityCode
          let hGraphO ← mkAppM `Set.MapsTo.mono_left #[← component geometry 5, hSProduct]
          let fieldBindings := proofBindings ++ [(`di, mkApp d i), (`hPsi, hPsi), (`hGraphO, hGraphO), (`hFullNormal, hFullNormal)]
          let hNormal ← termWith fieldBindings
            ("(by\n" ++
             "  apply (hFullNormal.comp hPsi hGraphO).congr\n" ++
             "  intro p hp\n" ++
             "  exact normalField_eq_fullNormal_on_graph T Q F row col Phi Y current.forward current.inverse initial hCompat (hCoordinates (hSProduct hp))\n" ++
             "  : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ di.normalField p.1 p.2) S)")
          let hNormal ← store `normal_smooth (all.push i) hNormal
          let hCovector ← termWith fieldBindings
            ("(by\n" ++
             "  have hx := ((phaseGradient_joint_smooth T Q).mono hDomain).comp hPsi hGraphO\n" ++
             "  apply hx.congr\n" ++
             "  intro p _\n" ++
             "  change T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2) = phaseGradient T Q (carrierGraph T p).1 (carrierGraph T p).2.2\n" ++
             "  simp only [carrierGraph, phaseGradient_on_carrier]\n" ++
             "  : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ di.covector p.1 p.2) S)")
          let hCovector ← store `covector_smooth (all.push i) hCovector
          let hSmooth ← termWith [(`hFullSmooth, hFullSmooth), (`hPsi, hPsi),
              (`hGraphO, hGraphO), (`hEq, hEq)] "(hFullSmooth.comp hPsi hGraphO).congr hEq"
          let hSmooth ← store `carrier_smooth (all.push i) hSmooth
          let hFullProfile := mkAppN (mkConst (leaf ++ `profile))
            (leadingArgs[:31].toArray ++ #[reserve, hReserve] ++ leadingArgs[31:].toArray)
          let hProfile ← termWith (proofBindings ++ [(`D, D), (`hEq, hEq), (`hS, hS),
              (`hJS, hJS), (`hJO, hJO), (`hFullSmooth, hFullSmooth), (`hPull, hPull),
              (`hPullPos, hPullPos), (`hFullProfile, hFullProfile), (`Cpull, Cpull),
              (`Cfull, Cfull), (`Ccarrier, Ccarrier), (`scale, scale), (`reserve, reserve)])
            carrierProfileCode
          let hProfile ← store `carrier_profile (publicParams.push i) hProfile
          pure (← mkLambdaFVars #[i] hSmooth, ← mkLambdaFVars #[i] hProfile,
            ← mkLambdaFVars #[i] hNormal, ← mkLambdaFVars #[i] hCovector)
        let J := mkAppN (mkConst (targetNS ++ `J)) fixed
        let hJ := mkAppN (mkConst (targetNS ++ `J_compact)) fixed
        let A := mkAppN (mkConst (targetNS ++ `carrierC)) fixed
        let hA := mkAppN (mkConst (targetNS ++ `carrierC_pos)) fixed
        let hJW := mkAppN (mkConst (targetNS ++ `J_subset_open)) fixed
        let meanBindings := [(`n, n), (`N, N), (`Index, index), (`fin, fin), (`mu, mu),
          (`hr, hr), (`chi, src `χ), (`hChi, src `χ_smooth), (`hChiCompact, src `χ_compact),
          (`V, out `window), (`hV, out `hwindow), (`hChiV, out `support_window),
          (`J, J), (`hJ, hJ), (`hJW, hJW), (`A, A), (`hA, hA)]
        let hMeanSmooth ← termWith (meanBindings ++ [(`d, d),
            (`normalSmooth, normalSmooth), (`covectorSmooth, covectorSmooth)])
          ("by\n" ++
           "  letI : Fintype Index := fin\n" ++
           "  exact contDiffOn_physicalDensityMean_zero d chi hChi hChiCompact\n" ++
           "    (W := ball (0 : Euclidean n) (6 * mu)) isOpen_ball V hV hChiV normalSmooth covectorSmooth")
        let smoothType ← inferType hMeanSmooth
        unless smoothType.isAppOf `ContDiffOn do
          throwError "native mean profiles: changed whole-buffer mean smoothness"
        let smoothArgs := smoothType.getAppArgs
        unless ← isDefEq smoothArgs[smoothArgs.size - 2]! mean do
          throwError "native mean profiles: smooth mean is not the native uncorrected mean"
        let zeroMean ← store `zero_mean all mean true
        let smoothTarget := mkAppN smoothType.getAppFn
          (smoothArgs.set! (smoothArgs.size - 2) zeroMean)
        discard <| store `smooth all hMeanSmooth false (some smoothTarget)
        let meanExists ← termWith meanBindings
          ("by\n" ++
           "  letI : Fintype Index := fin\n" ++
           "  exact exists_physicalDensityMean_zero_profile (n := n) (N := N)\n" ++
           "    (K := closedBall (0 : Euclidean n) (4 * mu)) (U := ball 0 (5 * mu)) (W := ball 0 (6 * mu))\n" ++
           "    (isCompact_closedBall _ _) isOpen_ball isOpen_ball\n" ++
           "    (closedBall_subset_ball (by linarith only [(show 0 < mu from hr)])) (ball_subset_ball (by linarith only [(show 0 < mu from hr)]))\n" ++
           "    chi hChi hChiCompact V hV hChiV J hJ hJW\n" ++
           "    (fun i p hp ↦ ⟨ball_subset_closedBall hp.1, hp.2⟩) A (fun i s ↦ (hA i s).le)")
        let C ← store `C fixed (← mkAppM ``Classical.choose #[meanExists]) true
        let meanSpec ← mkAppM ``Classical.choose_spec #[meanExists]
        discard <| store `C_nonneg fixed (.proj ``And 0 meanSpec)
        let hMean := mkAppN (.proj ``And 1 meanSpec) #[d, smooth, reserve, scale, hScale, profiles]
        let hMeanType ← Core.betaReduce (← zetaReduce (← inferType hMean))
        unless hMeanType.isAppOf `JanetCartan.HasDerivativeProfile do
          throwError "native mean profiles: weighted integral profile changed its result"
        let hMeanArgs := hMeanType.getAppArgs
        unless ← isDefEq hMeanArgs.back! C do
          throwError "native mean profiles: weighted integral lost its prehistory constant"
        let target := mkAppN hMeanType.getAppFn (hMeanArgs.set! (hMeanArgs.size - 1) C)
        discard <| store `profile publicParams hMean false (some target)
  logInfo "actual whole-chi current mean profile: same carrier/raw/current, fixed prehistory C, original graph, no angular-support truncation"

end JanetCartan.PhysicalBackground.NativeMeanProfilesTemplate
end
