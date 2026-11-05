module
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskGeometry
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedData

/-! # Original cutoff and stress-row prices for the native first-mask kernel

The fixed bump and the broad physical stress cutoff are measured on the actual
immutable compact.  The *raw* projected frame inherits the original full
operator profile by a spatial germ on this SAME compact, at the already admitted
fine scale. The reserve is the existing `sectorLowOrder`, not a new threshold.
`app:ch_pairs:prop:pairs-lag-sum`, `app:ch_response:eq:response-graded-reduced`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 420000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius ComplexConjugate
namespace JanetCartan.PhysicalPairs.OriginalMaskRows
open PhysicalInitialization PhysicalSeed ProtectedFlow ActualCarriers ProjectedStressFrame CurrentCoefficientProfiles
open ResponseTransfer.RetainedFactors GeometricProfile UniformStep PrimarySourceAdmission
open FrozenMenu CurrentFullPhase CanonicalRowComparison SeparatedSampling InitialSourceLocalization

/-- Fixed on the whole buffered chart, independently of every current history. -/
def cutoffPrice {n : ℕ} (S : Set (Euclidean n)) (χ : Euclidean n → ℝ) (j : ℕ) : ℝ := cNorm S j χ

theorem cutoffPrice_nonneg {n : ℕ} (S : Set (Euclidean n)) (χ : Euclidean n → ℝ) (j : ℕ) : 0 ≤ cutoffPrice S χ j := by
  exact cNorm_nonneg _ _ _

theorem cutoff_jets {n : ℕ} {S U : Set (Euclidean n)} (hS : IsCompact S) (hUS : U ⊆ S)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 1 ≤ M) :
    ∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j χ y‖ ≤ cutoffPrice S χ j * M^j := by
  intro y hy j
  exact (norm_iteratedFDeriv_le_cNorm hS (hχ.of_le (by simp)) (hUS hy) le_rfl).trans
    (le_mul_of_one_le_right (cutoffPrice_nonneg S χ j) (one_le_pow₀ hM))

/-- Exact raw spatial row on the chart, using the original affine-frame germ,
not a global equality between raw and extended projected stress. -/
theorem raw_rows {n : ℕ} (hn : 5 ≤ n) {r : ℝ} (hr : 0 < r) {U : Set (Euclidean n)}
    (hUV : U ⊆ closedBall 0 (OriginalRegular.coreRadius hn r))
    (ext : BallExtension.Parameters (Euclidean n)) (h0 : ext.center = 0) (hb : ext.radius = OriginalBoundary.b hn)
    (F : Euclidean n → Euclidean (embeddingDimension n)) (hQ : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (OriginalBoundary.R hn)))
    {reserve : ℕ} {L M : ℝ} (hL : 1 ≤ L) (hLM : L ≤ M) (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m)
    (hsm : ContDiff ℝ ∞ (extendedProjectedStress ext F))
    (hp : ∀ K : Set (Euclidean n), IsCompact K → HasDerivativeProfile K (extendedProjectedStress ext F) reserve L AQ) :
    ContDiffOn ℝ ∞ (projectedStress F) U ∧
      ∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ j (projectedStress F) y‖ ≤ AQ j*M^j := by
  have hUb := hUV.trans (OriginalRegular.core_spec hn hr).2.2.1
  refine ⟨hQ.mono (hUb.trans (ball_subset_ball (OriginalBoundary.b_lt_R hn).le)),?_⟩
  intro y hy j
  have hphys : y ∈ ball (0 : Euclidean n) ext.radius := by rw [hb]; exact hUb hy
  have he : projectedStress F =ᶠ[𝓝 y] extendedProjectedStress ext F := eventuallyEq_of_mem (isOpen_ball.mem_nhds hphys)
    (fun z hz ↦ (affineFrameExtension_eqOn ext (projectedStress F) (by rw [h0];exact ball_subset_closedBall hz)).symm)
  rw [((he.iteratedFDeriv ℝ j).eq_of_nhds)]
  let V := closedBall (0 : Euclidean n) (OriginalRegular.coreRadius hn r)
  have hv : IsCompact V := isCompact_closedBall _ _
  apply (norm_iteratedFDeriv_le_cNorm hv (hsm.of_le (by simp)) (hUV hy) le_rfl).trans
  apply (hp V hv j).trans
  exact mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hL (Nat.sub_le j reserve)).trans
    (pow_le_pow_left₀ (zero_le_one.trans hL) hLM _)) (hAQ j)

/-- Membership of each ORIGINAL sampled node in the whole unshrunk parameter cube. -/
theorem node_cube {J : Type} {p : ℕ} {B h : ℝ} {weights : J → Point → ℝ} {w : ℝ → ℝ} {shifts : J → Lattice → Point}
    (rad : J → ℝ) (hw : ∀ g z, weights g z ≠ 0 → WithLp.toLp 2 z ∈ parameterInterior (rad g))
    (i : SampleIndex p B weights w h shifts) : WithLp.toLp 2 (node h (shifts i.1) i.2) ∈ parameterCube (rad i.1) :=
  original_sample_node_mem_parameterCube rad (fun g z hz a ↦ (hw g z hz a).le) i

/-- The signed full derivative amplitudes are smooth on the physical chart
for every supplied full Schwartz wave, even when the underlying carrier was
only defined classically outside that chart. -/
theorem amplitude_smooth {n N : ℕ} {I G : Type} {Z : G → Set (Euclidean 3)} {S U : Set (Euclidean n)}
    (hUS : U ⊆ S) (Φ : G → Euclidean n × Euclidean 3 → ℝ) (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g) ∧ HasCompactSupport (Φ g))
    (raw : G → Euclidean 3 → Euclidean n → ℝ)
    (hg : ∀ g v, v ∈ S ×ˢ Z g → Φ g =ᶠ[𝓝 v] fun p ↦ raw g p.2 p.1)
    (g : I → G) (z : I → Euclidean 3) (lam : ℝ) (W : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (i : I) (hz : z i ∈ Z (g i)) :
    ContDiffOn ℝ ∞ (sampledDerivativeAmplitude (fun j ↦ (W j : Euclidean n → EuclideanSpace ℂ (Fin N)))
      (fun j x ↦ lam*raw (g j) (z j) x) i) U := by
  have htheta : ContDiffOn ℝ ∞ (fun x ↦ lam * raw (g i) (z i) x) U := by
    have hs : ContDiff ℝ ∞ (fun x : Euclidean n ↦ Φ (g i) (x,z i)) := (hΦ _).1.comp (contDiff_id.prodMk contDiff_const)
    apply contDiffOn_const.mul
    apply hs.contDiffOn.congr
    intro y hy
    exact ((hg (g i) (y,z i) ⟨hUS hy,hz⟩).eq_of_nhds).symm
  have hd : ContDiffOn ℝ ∞ (sampledDerivative (fun j ↦ (W j : Euclidean n → EuclideanSpace ℂ (Fin N))) i) univ := by
    let L : (Fin N → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ := LinearMap.id
    let J : (Fin N → Fin n → ℂ) →L[ℝ] Matrix (Fin N) (Fin n) ℂ := ⟨L,L.continuous_of_finiteDimensional⟩
    apply J.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro b
    exact (contDiffOn_piLp 2).mp (((W i).smooth'.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single b (1:ℝ)))) a
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn htheta.neg).mul contDiffOn_const).cexp).smul (hd.mono (subset_univ _))
/-- Replace the raw scalar by the same-pair smooth representative inside the
actual source. Nothing is asserted about either scalar outside its physical chart. -/
theorem measured_phase {n : ℕ} {U : Set (Euclidean n)} (g : Euclidean n → Euclidean n)
    (χ raw φ : Euclidean n → ℝ) (a : Euclidean n → EuclideanSpace ℂ (Fin n)) (ρ : ℝ)
    (hχ : tsupport χ ⊆ U) (he : ∀ x ∈ U, φ =ᶠ[𝓝 x] raw)
    (h : g =ᵐ[MeasureTheory.volume] fun y ↦ euclideanRealPart (ResponseTransfer.SourceNegative.modulatedSource χ raw a ρ y)) :
    g =ᵐ[MeasureTheory.volume] fun y ↦ euclideanRealPart (ResponseTransfer.SourceNegative.modulatedSource χ φ a ρ y) := by
  refine h.trans <| Filter.Eventually.of_forall ?_
  intro y
  by_cases hy : y ∈ tsupport χ
  · simp only [ResponseTransfer.SourceNegative.modulatedSource,ResponseTransfer.carrier,(he y (hχ hy)).eq_of_nhds]
  · simp only [ResponseTransfer.SourceNegative.modulatedSource,image_eq_zero_of_notMem_tsupport hy,zero_smul]
end JanetCartan.PhysicalPairs.OriginalMaskRows
end

public meta section
set_option maxHeartbeats 900000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalMaskRows
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def geo := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def frames := `JanetCartan.PhysicalPairs.OriginalSignedFrames
private def src := `JanetCartan.PhysicalPairs.OriginalSignedData
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (pf : Expr) : Nat → Expr
  | 0 => pf
  | i+1 => down (.proj ``And 1 pf) i
private def part (pf : Expr) (i : Nat) := Expr.proj ``And 0 (down pf i)

elab "construct_original_mask_rows " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p gf => do
    if piece.getNat == 5 || piece.getNat == 6 then
      let spec := a (ns ++ `row_spec) p
      if piece.getNat == 5 then discard <| store (ns ++ `row_smooth) p (part spec 0)
      else discard <| store (ns ++ `row_jets) p (down spec 1)
      return
    let fixed := gf.getAppArgs[:23].toArray
    let d := p[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let hn := p[1]!
    let orig := #[n] ++ fixed[1:21].toArray
    let cap := a `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,orig[20]!]
    let sel := orig.set! 20 cap
    let r := a `JanetCartan.PhysicalInitialization.OriginalProtected.r orig
    let μ := a `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure sel
    let f := a (reg ++ `f) fixed
    let fa := (← inferType f).getAppArgs
    let hUS := a (geo ++ `chart_buffer) #[d,hn,r,μ,fa[fa.size-2]!,fa.back!,f,a (reg ++ `r) fixed]
    let va := (← inferType hUS).getAppArgs
    let V := va[va.size-2]!
    let S := va.back!
    let χsm := a (mask ++ `χ₂_smooth) fixed
    let ηsm := a (mask ++ `χsrc_smooth) fixed
    let χ := (← inferType χsm).appArg!
    let η := (← inferType ηsm).appArg!
    let static := p[:37].toArray
    if piece.getNat == 0 then
      for (k,kpos,cut) in [(`bumpProfile,`bumpProfile_nonneg,χ),(`sourceProfile,`sourceProfile_nonneg,η)] do
        let cost := a (ns ++ `cutoffPrice) #[n,S,cut]
        let named ← store (ns ++ k) static cost true
        let pos := a (ns ++ `cutoffPrice_nonneg) #[n,S,cut]
        discard <| store (ns ++ kpos) static pos false (some ((← inferType pos).replace fun e => if e == cost then some named else none))
      return
    let window := part (a (hist ++ `native_window) p) 0
    let hL := part window 0
    let hle := part window 1
    let la := (← inferType hle).getAppArgs
    let L := la[la.size-2]!
    let M := la.back!
    if piece.getNat == 1 then
      let sa := S.getAppArgs
      let compact ← mkAppM ``isCompact_closedBall #[sa[sa.size-2]!,sa.back!]
      let hM ← mkAppM ``le_trans #[hL,hle]
      for (name,price,cut,sm) in [(`bump_jets,`bumpProfile,χ,χsm),(`source_jets,`sourceProfile,η,ηsm)] do
        let pf := a (ns ++ `cutoff_jets) #[n,S,V,compact,hUS,cut,sm,M,hM]
        let named := a (ns ++ price) static
        let cost := a (ns ++ `cutoffPrice) #[n,S,cut]
        discard <| store (ns ++ name) p pf false (some ((← inferType pf).replace fun e => if e == cost then some named else none))
      return
    let history := a (hist ++ `measured_history) p
    let now := p[:36].toArray ++ #[p[37]!,part history 0] ++ p[39:43].toArray
    if piece.getNat == 2 then
      let qnamed := a (quad ++ `Q) now
      let q := ((← getConstInfo (quad ++ `Q)).value! (allowOpaque := true)).beta now
      let actual := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily).value! (allowOpaque := true)).beta gf.getAppArgs
      let coeff := actual.getAppArgs.back!.getAppArgs
      let cont := a (op ++ `continuation) (coeff ++ #[p[37]!,part history 1] ++ p[39:43].toArray)
      let ps := down cont 2
      let pe ← forallBoundedTelescope (← inferType ps) (some 2) fun K _ => mkLambdaFVars K (.proj ``And 0 (mkAppN ps K))
      let hr := a (reg ++ `screened_pos) #[n,hn,r,μ,a `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 orig,
        a `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure sel]
      let pf := a (ns ++ `raw_rows) #[n,hn,(← inferType hr).appArg!,hr,V,hUS,fixed[4]!,fixed[5]!,fixed[6]!,q.appArg!,
        a (quad ++ `Q_smooth) now,coeff[28]!,L,M,hL,hle,a (op ++ `AQ) coeff,a (op ++ `fact1) coeff,part cont 0,pe]
      discard <| store (ns ++ `row_spec) p pf false (some ((← inferType pf).replace fun e => if e == q then some qnamed else none))
      return
    forallBoundedTelescope (← inferType (a (src ++ `uncut) p)) (some 1) fun ws _ => do
      let args := p ++ ws
      if piece.getNat == 3 then
        let th := ((← getConstInfo (src ++ `angles)).value! (allowOpaque := true)).beta p
        let N := a `JanetCartan.embeddingDimension #[n]
        let I ← inferType p[46]!
        let safe := p[:43].toArray
        let phase := ((← getConstInfo (geo ++ `phase)).value! (allowOpaque := true)).beta p
        let fa := phase.getAppArgs
        unless fa.size == 5 do throwError "lost the supplied pair's named normalized phase"
        lambdaTelescope th fun z body => do
          unless z.size == 2 do throwError "native angle no longer uses one original sample and one spatial point"
          let some carrier := body.find? (fun e => e.isAppOfArity (quad ++ `group_phase) 45)
            | throwError "lost the original colored radial phase of the native angle"
          let ca := carrier.getAppArgs
          let group ← mkLambdaFVars #[z[0]!] ca[42]!
          let node ← mkLambdaFVars #[z[0]!] ca[43]!
          let lam := body.getAppArgs[body.getAppNumArgs-2]!
          for (name,sm,i) in [(`leftAmplitude,`left_smooth,p[46]!),(`rightAmplitude,`right_smooth,p[47]!)] do
            let hi ← mkAppM (ns ++ `node_cube) #[a (outer ++ `parameterRadius) p[:22].toArray,a (outer ++ `nonzero_parameter) p[:22].toArray,i]
            let pf := a (ns ++ `amplitude_smooth) #[n,N,I,fa[1]!,fa[2]!,S,V,hUS,fa[4]!,a (frames ++ `smooth) safe,
              a (quad ++ `group_phase) now,a (frames ++ `original_germ) safe,group,node,lam,ws[0]!,i,hi]
            let st ← inferType pf
            let A := st.getAppArgs[st.getAppNumArgs-2]!
            let Anew ← store (ns ++ name) args A true
            discard <| store (ns ++ sm) args pf false (some (st.replace fun e => if e == A then some Anew else none))
        return
      let hr := a (src ++ `realization) args
      let rt := (← inferType hr).getAppArgs
      let some w := rt.back!.find? (fun e => e.isAppOf `JanetCartan.ResponseTransfer.SourceNegative.modulatedSource && e.getAppNumArgs ≥ 5)
        | throwError "lost the full real sampled reduced source"
      let b := w.getAppArgs
      let pf := a (ns ++ `measured_phase) #[n,V,rt[rt.size-2]!,χ,b[b.size-4]!,a (geo ++ `phase) p,b[b.size-3]!,b[b.size-2]!,
        a (mask ++ `χ₂_support_chart) fixed,a (geo ++ `germ) p,hr]
      discard <| store (ns ++ `represented_realization) args pf
construct_original_mask_rows 0
construct_original_mask_rows 1
construct_original_mask_rows 2
construct_original_mask_rows 5
construct_original_mask_rows 6
construct_original_mask_rows 3
construct_original_mask_rows 4
end JanetCartan.PhysicalPairs.OriginalMaskRows
end
