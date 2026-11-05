module

public import JanetCartan.Iteration.PhysicalPairs.SampledInput
public import JanetCartan.Iteration.PhysicalPairs.SampledQuadrature
public import JanetCartan.Iteration.PhysicalPairs.OriginalInverse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredSupport
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! # Original signed data for the measured finite-chain application

On the original external pair and full primary waves, form the uncut smooth
stress of the actual broad `χsrc` tensor *before* the inner measurement. The
initial local datum of `OriginalSampledObserved` is `bumpL2 χ₂` of that source,
so the native measured correction is its Neumann inverse without another χ₂.
The original `Zcorr` and solver continue to act on the uncut smooth source.
The real zero extension of the measured datum agrees globally with the
previously computed true-frequency quadrature. No new plateau is required.
`app:ch_regular:eq:source-tail`, `app:ch_pairs:eq:pairs-exact-offself`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalSignedData
open PhysicalSeed PhysicalInitialization FixedDomainInverse LocalSobolev SmallSupport
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic PhysicalSampling FullPhaseCharts.ActualComparison

theorem original_source_support {m p : ℕ} (hn : 5 ≤ m+1)
    (q : IncidenceCenter (OriginalBoundary.D hn)) (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1,l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0,spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1,l⟩ j))
    {μ : ℝ} (hμ : 0 < μ)
    (hs : tsupport (OriginalRegular.measuredSourceCutoff (n := m+1) hμ) ⊆
      closedBall 0 (OriginalChoices.Band.a (p := p) hn q l j hroot / 8)) :
    HasCompactSupport (OriginalRegular.measuredSourceCutoff (n := m+1) hμ) ∧
    tsupport (OriginalRegular.measuredSourceCutoff (n := m+1) hμ) ⊆ ball 0 (OriginalBoundary.R hn) := by
  refine ⟨(FixedCutoffs.physical hμ (2:Fin 3)).hasCompactSupport,hs.trans <| (closedBall_subset_closedBall ?_).trans <|
    (originalSamplingRadius_spec hn q l j hroot).2.2.1.trans <| (original_frameBall_subset hn ⟨q.1.1,l⟩).trans <|
    closedBall_subset_ball (OriginalBoundary.b_lt_R hn)⟩
  linarith [OriginalChoices.Band.ha_radius (p := p) hn q l j hroot,OriginalChoices.Band.ha (p := p) hn q l j hroot,
    (originalSamplingRadius hn q l j).2]

theorem smooth_frame_rows {n : ℕ} {Q : Euclidean n → Fin n → MetricTensor n} {U : Set (Euclidean n)}
    (h : ContDiffOn ℝ ∞ Q U) : ∀ j, ContDiffOn ℝ ∞ (fun x ↦ Q x j) U := contDiffOn_pi.mp h

def innerDatum {n : ℕ} {W : Set (Euclidean n)} {c : Euclidean n} (χ₂ : ContDiffBump c)
    (v : smoothSource W (Euclidean n)) : LocalL2 W (Euclidean n) := bumpL2 (p := 2) le_rfl χ₂ v.val

theorem apply_once {n : ℕ} {W : Set (Euclidean n)} {c : Euclidean n}
    (M : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n)) (χ₂ : ContDiffBump c) (v : smoothSource W (Euclidean n)) :
    (M.comp (bumpL2 (p := 2) le_rfl χ₂)) v.val = M (innerDatum χ₂ v) := rfl

def onSpace {n : ℕ} {W : Set (Euclidean n)} (hW : MeasurableSet W) (v : LocalL2 W (Euclidean n)) :
    Euclidean n → Euclidean n := zeroExtend hW v

theorem actual_quadrature_ae {n : ℕ} (v g h : Euclidean n → Euclidean n)
    (hg : v =ᵐ[volume] g) (he : g=h) : v =ᵐ[volume] h := he ▸ hg
end JanetCartan.PhysicalPairs.OriginalSignedData
end

public meta section
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalSignedData
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSignedData
private def src := `JanetCartan.PhysicalPairs.SampledInput
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def inverse := `JanetCartan.PhysicalPairs.OriginalInverse
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def samples := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def orig := `JanetCartan.PhysicalSeed.OriginalBoundary
private def selected := `JanetCartan.PhysicalSeed.SelectedBoundary
private def meas := `JanetCartan.PhysicalInitialization.OriginalSampledObserved
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def a (q : Name) (xs : Array Expr) := mkAppN (mkConst q) xs
private partial def lets (e : Expr) : Expr := match e.headBeta with
  | .letE _ _ v b _ => lets (b.instantiate1 v)
  | z => z

elab "construct_signed_native_datum " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p family => do
    let fixed := family.getAppArgs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let hn := p[1]!
    let dim := a `JanetCartan.embeddingDimension #[n]
    let fix := #[n] ++ fixed[1:21].toArray
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,fix[20]!]
    let sel := fix.set! 20 cap
    let ηsmooth := a (mask ++ `χsrc_smooth) fixed
    let η := (← inferType ηsmooth).appArg!
    if piece.getNat == 0 then
      let two ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 2
      let row := Expr.proj ``Sigma 0 p[46]!
      let hband := a `JanetCartan.PhysicalSampling.OriginalMeasuredSupport.physical_support_in_original_sharp_ball
        (p[:22].toArray ++ #[row,two])
      let band := (← inferType hband).getAppArgs.back!
      let some width := band.find? (fun e => e.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Band.a 7)
        | throwError "actual native sharp support theorem lost its original sampling row"
      let hgeom := a (ns ++ `original_source_support) (width.getAppArgs ++ #[a (selected ++ `rMeasure) sel,
        a (selected ++ `hrMeasure) sel,hband])
      discard <| store (ns ++ `source_chart) p[:47].toArray hgeom
      logInfo "original χsrc support via the actual first sampled row's sharp band and working ball"
      return
    let hgeom := a (ns ++ `source_chart) p[:47].toArray
    let χ₂ := a (reg ++ `χ₂) fixed
    let center := (← inferType χ₂).getAppArgs.back!
    let W := a (world ++ `W) fixed
    let hW := a (world ++ `W_measurable) fixed
    let hχ ← mkAppM `Set.Subset.trans #[a (mask ++ `χ₂_support_chart) fixed,a (reg ++ `hUW) fixed]
    let reached := Expr.proj ``And 0 (a (hist ++ `measured_history) p)
    let now := p[:36].toArray ++ #[p[37]!,reached] ++ p[39:43].toArray
    let current := ((← getConstInfo (samples ++ `projected)).value! (allowOpaque := true)).beta now
    unless current.isAppOfArity (reg ++ `Current.projected) 38 do throwError "lost native38 smooth inverse"
    let weak := current.getAppArgs
    let Q := a (quad ++ `Q) now
    let cg := ((← getConstInfo (quad ++ `group_phase)).value! (allowOpaque := true)).beta now
    unless cg.isAppOfArity (quad ++ `radialCarrier) 11 do throwError "lost original raw phase family"
    let U := cg.getAppArgs[2]!
    let hU := cg.getAppArgs[3]!
    let rows := a (ns ++ `smooth_frame_rows) #[n,Q,U,a (quad ++ `Q_smooth) now]
    let red := a (quad ++ `reduced_on_original_sample) p
    forallBoundedTelescope (← inferType red) (some 1) fun ws raw => do
      let eq := lets raw
      unless eq.isAppOfArity ``Eq 3 do throwError "missing native real equality for supplied Schwartz family"
      let some term := eq.getAppArgs[1]!.find? (fun e => e.isAppOf `JanetCartan.ProductSum.minusSource && e.getAppNumArgs ≥ 5)
        | throwError "missing the actual unweighted signed tensor"
      let minusArgs := term.getAppArgs
      if piece.getNat == 1 then
        discard <| store (ns ++ `angles) p minusArgs[minusArgs.size-5]! true
        logInfo "same external sampler's full-derivative angles"
        return
      let θ := a (ns ++ `angles) p
      let I ← inferType p[46]!
      let label := p ++ ws
      let args := #[n,dim,I,ws[0]!,θ,p[45]!,p[46]!,p[47]!,U,W,η,hU,Q,rows,ηsmooth,
        .proj ``And 0 hgeom,.proj ``And 1 hgeom]
      if piece.getNat == 2 then
        let uncut ← store (ns ++ `uncut) label (a (src ++ `uncut) args) true
        let measured ← store (ns ++ `measured) label (a (ns ++ `innerDatum) #[n,W,center,χ₂,uncut]) true
        discard <| store (ns ++ `complex_input) label (a (meas ++ `complexSource) #[p[0]!,W,hW,measured]) true
        logInfo "uncut original broad signed stress and native single-gated local and complex inputs"
        return
      let uncut := a (ns ++ `uncut) label
      let measured := a (ns ++ `measured) label
      if piece.getNat == 3 then
        let ae := a (src ++ `zeroExtend_measured) (args ++ #[hW,center,χ₂,hχ])
        let v := a (ns ++ `onSpace) #[n,W,hW,measured]
        let exactAE := a (ns ++ `actual_quadrature_ae) #[n,v,eq.getAppArgs[1]!,eq.appArg!,ae,mkApp red ws[0]!]
        discard <| store (ns ++ `realization) label exactAE
        logInfo "native measured input zero-extends to the full real stress quadrature at the true external beat"
        return
      let corr := a (inverse ++ `Corr) weak
      let body := lets (((← getConstInfo (inverse ++ `Corr)).value! (allowOpaque := true)).beta weak)
      unless body.isAppOf ``ContinuousLinearMap.comp && body.appArg!.isAppOf `JanetCartan.SmallSupport.bumpL2 do
        throwError "native inverse lost its original measured CLM composition"
      let ops := body.getAppArgs
      let inv := ops[ops.size-2]!
      let applied := a (ns ++ `apply_once) #[n,W,center,inv,χ₂,uncut]
      let ct ← inferType applied
      let old := ct.getAppArgs[1]!.replace fun e => if e.isAppOf ``ContinuousLinearMap.comp && e.getAppArgs.back!.isAppOf `JanetCartan.SmallSupport.bumpL2 then some corr else none
      let target := ct.appArg!.replace fun e => if e.isAppOfArity (ns ++ `innerDatum) 5 then some measured else none
      if piece.getNat == 4 then
        discard <| store (ns ++ `native_correction) label applied false (some (← mkEq old target))
        logInfo "original inverse of the measured source equals the native correction on the UNCUT smooth source"
        return
      for (name,key) in [(`corrector_representation,`corrector_ae),(`solver_representation,`solver_ae)] do
        let pf := mkApp (a (inverse ++ key) weak) uncut
        let ty ← inferType pf
        let some native := ty.find? (fun e => e.isApp && e.getAppNumArgs ≥ 2 && (e.getAppArgs[e.getAppNumArgs-2]!).isAppOfArity (inverse ++ `Corr) 38)
          | throwError "missing original measured correction in {key}"
        discard <| store (ns ++ name) label pf false (some (ty.replace fun e => if e == native then some target else none))
      logInfo "smooth original corrector and actual retarded solver represent the SAME singly measured inverse"
construct_signed_native_datum 0
construct_signed_native_datum 1
construct_signed_native_datum 2
construct_signed_native_datum 3
construct_signed_native_datum 4
construct_signed_native_datum 5
end JanetCartan.PhysicalPairs.OriginalSignedData
end
