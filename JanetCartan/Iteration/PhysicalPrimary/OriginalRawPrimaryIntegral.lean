module
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MatrixRepresentation
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawSourceProfile
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
/-! The before-B raw matrix representation on the existing Fourier-shifted
chart. This is only a coordinate adapter for the original raw superposition;
it changes neither the Hilbert density nor the carrier/scale (main:eq:primary-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase RawInputPartition
private theorem shifted_window_data {d : ℕ} (ζ : Euclidean d) {τ : ℝ} (hτ : τ ≠ 0)
    {V : Set (Euclidean d)} (hV : IsOpen V) (hzero : (0 : Euclidean d) ∈ V) :
    let W := (fun ξ : Euclidean d ↦ τ⁻¹ • (ξ-ζ)) ⁻¹' V
    IsOpen W ∧ ζ ∈ W ∧ (∀ η ∈ V, ζ+τ • η ∈ W) ∧
      (∀ ξ ∈ W, ζ+τ • (τ⁻¹ • (ξ-ζ)) = ξ) := by
  dsimp only
  refine ⟨hV.preimage (by fun_prop), ?_, ?_, ?_⟩
  · simpa only [mem_preimage, sub_self, smul_zero] using hzero
  · intro η hη
    change τ⁻¹ • ((ζ+τ • η)-ζ) ∈ V
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ, one_smul] using hη
  · intro ξ _
    rw [smul_smul, mul_inv_cancel₀ hτ, one_smul]
    abel

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (τ : ℝ) (hτ : τ ≠ 0) (z : Euclidean 3)
    {X : Set (Euclidean n)} {V : Set (Euclidean (n-1))}
    (hX : IsOpen X) (hV : IsOpen V)
    (hVceil : closedBall 0 ((2 : ℝ)^J) ⊆ V)
    (hshift : ∀ p ∈ X ×ˢ V, (p.1,(z,T.reference.spatialPatch z+τ • p.2)) ∈ Ω)

include hΩ hspace hphase hF hi hrank hα hnonzero hτ hX hV hVceil hshift

private theorem raw_matrix_integral_on_shifted_chart
    {d : Euclidean (n-1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ X) :
    Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
        RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
          (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y τ r z d v) x) =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y,(z,ξ)))
        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x := by
  let ζ := T.reference.spatialPatch z
  let W := (fun ξ : Euclidean (n-1) ↦ τ⁻¹ • (ξ-ζ)) ⁻¹' V
  have hzero : (0 : Euclidean (n-1)) ∈ V := hVceil (by
    simp only [mem_closedBall, dist_self]
    positivity)
  have hw := shifted_window_data ζ hτ hV hzero
  have hproduct : ∀ p ∈ X ×ˢ W, (p.1,(z,p.2)) ∈ Ω := by
    intro p hp
    have hs := hshift (p.1,τ⁻¹ • (p.2-ζ)) ⟨hp.1,hp.2⟩
    change (p.1,(z,ζ+τ • (τ⁻¹ • (p.2-ζ)))) ∈ Ω at hs
    rw [hw.2.2.2 p.2 hp.2] at hs
    exact hs
  have hA := CorrectedAtoms.contDiffOn_retainedDerivativeAmplitude T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ
  exact fullPrimaryWave_differentialMatrix_representation T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hA z hX hw.1 hw.2.1
    hproduct (fun η hη ↦ hw.2.2.1 η (hVceil hη)) hd hM hb v hx

omit hX in
private theorem raw_demodulated_kernel_smooth_on_shifted_chart :
    ContDiffOn ℝ ∞
      (rawPrimaryDemodulatedAtom (fun y ξ ↦ phase T Q y ξ)
        (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y,(z,ξ)))
        (T.reference.spatialPatch z) τ) (X ×ˢ V) := by
  let ζ := T.reference.spatialPatch z
  let W := (fun ξ : Euclidean (n-1) ↦ τ⁻¹ • (ξ-ζ)) ⁻¹' V
  have hzero : (0 : Euclidean (n-1)) ∈ V := hVceil (by
    simp only [mem_closedBall, dist_self]
    positivity)
  have hw := shifted_window_data ζ hτ hV hzero
  have hproduct : ∀ p ∈ X ×ˢ W, (p.1,(z,p.2)) ∈ Ω := by
    intro p hp
    have hs := hshift (p.1,τ⁻¹ • (p.2-ζ)) ⟨hp.1,hp.2⟩
    change (p.1,(z,ζ+τ • (τ⁻¹ • (p.2-ζ)))) ∈ Ω at hs
    rw [hw.2.2.2 p.2 hp.2] at hs
    exact hs
  have hmap : ContDiffOn ℝ ∞
      (fun p : Euclidean n × Euclidean (n-1) ↦ (p.1,(z,p.2))) (X ×ˢ W) :=
    contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (fun y ξ ↦ phase T Q y ξ)) (X ×ˢ W) :=
    (contDiffOn_fullPhase T Q hphase).comp hmap hproduct
  have hA := CorrectedAtoms.contDiffOn_retainedDerivativeAmplitude T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry
      (fun y ξ ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ (y,(z,ξ)))) (X ×ˢ W) :=
    hA.comp hmap hproduct
  exact contDiffOn_rawPrimaryDemodulatedAtom hS hA' hw.2.1 hw.2.2.1
#print axioms raw_matrix_integral_on_shifted_chart
#print axioms raw_demodulated_kernel_smooth_on_shifted_chart
end JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealizationApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private partial def head (e : Expr) : Expr :=
  match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | value => value
private def progress (s : String) : MetaM Unit := do
  let out ← liftM IO.getStderr
  liftM <| out.putStrLn s
  liftM <| out.flush
private def bodyAt (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let some body := info.value? (allowOpaque := true) |
    throwError "raw native matrix: unavailable original body"
  return head ((body.instantiateLevelParams info.levelParams value.getAppFn.constLevels!).beta value.getAppArgs)
private def get (p : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let some (_,value) := p.find? (·.1 == key) | throwError "raw native matrix: missing original {key}"
  return value
private def arguments (value : Expr) : MetaM (Array (Name × Expr)) := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  let mut result := #[]
  for arg in value.getAppArgs do
    let .forallE key _ rest _ := head type | throwError "raw native matrix: named original spine changed"
    result := result.push (key.eraseMacroScopes,arg)
    type := rest.instantiate1 arg
  return result
private partial def applyNamedBody (known : Array (Name × Expr)) (stop : Option Name)
    (value type : Expr) : MetaM Expr := do
  match head type with
  | .forallE key _ rest _ =>
    let key := key.eraseMacroScopes
    let arg ← get known key
    let result := mkApp value arg
    if stop == some key then return result
    applyNamedBody known stop result (rest.instantiate1 arg)
  | _ => return value
private def applyNamed (name : Name) (known : Array (Name × Expr))
    (stop : Option Name := none) : MetaM Expr := do
  let info ← getConstInfo name
  let levels := info.levelParams.map fun _ => Level.zero
  applyNamedBody known stop (mkConst name levels)
    (info.type.instantiateLevelParams info.levelParams levels)
private def save (key : Name) (p : Array Expr) (proof : Expr) : MetaM Unit := do
  progress s!"raw native matrix: preparing {key}/{p.size}"
  let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "raw native matrix: missing metadata {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw native matrix: unresolved original chart or Fourier datum"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  progress s!"raw native matrix: checking {key}/{p.size}"
  addDecl (.thmDecl {name := ns ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (ns ++ key) "Part of the literal BEFORE-B raw whole-wave calculus on the original selected chart: the matrix integral identity, joint raw-kernel smoothness and exact refined annular identity retain the SAME raw derivative amplitude, phase, positive scalar, detector, wide/refined input and Lebesgue normalization. No corrected output G is relabeled (main:eq:primary-strain; app:ch_waves:eq:individual-representation)."
  progress s!"raw native matrix: checked {key}/{p.size}"

elab "check_actual_raw_native_matrix " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 3 do throwError "raw native matrix: unknown field"
  let source := wave ++ `Whole.raw_on_selected_cell
  progress s!"raw native matrix: opening native67, mode {mode}"
  forallBoundedTelescope (← getConstInfo source).type (some 67) fun all _ => do
    unless all.size == 67 do throwError "raw native matrix: native67 changed"
    progress s!"raw native matrix: opened native67, mode {mode}"
    let raw ← bodyAt (app source all)
    unless raw.isAppOf `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave do
      throwError "raw native matrix: expected original raw superposition proof, got {raw.getAppFn.constName?}"
    let known ← arguments raw
    let T ← get known `T
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "raw native matrix: same source53 current was lost"
    let hτ ← mkAppM ``ne_of_gt #[T.getAppArgs[48]!]
    let known := #[(`hτ,hτ),(`hceil,← get known `hVceil)] ++ known
    let params := all.pop
    if mode == 1 then
      let proof ← applyNamed ``OriginalRawPrimaryRealization.raw_demodulated_kernel_smooth_on_shifted_chart known
      save `raw_kernel_smooth params proof
      return
    let n ← get known `n
    let J ← get known `J
    let X ← get known `X
    let eucl := app `JanetCartan.Euclidean #[n]
    withLocalDeclNoLocalInstanceUpdate `x .default eucl fun x => do
      let membership ← mkAppM ``Membership.mem #[X,x]
      withLocalDeclNoLocalInstanceUpdate `hx .default membership fun hx => do
        let known := #[(`x,x),(`hx,hx)] ++ known
        if mode == 0 then
          let proof ← applyNamed ``OriginalRawPrimaryRealization.raw_matrix_integral_on_shifted_chart known
          let target ← inferType proof
          unless target.isAppOfArity ``Eq 3 &&
              target.getAppArgs[2]!.isAppOf `JanetCartan.rawPrimaryDemodulatedIntegral do
            throwError "raw native matrix: literal demodulated raw integral changed"
          save `raw_matrix_integral (all ++ #[x,hx]) proof
          return
        let smooth := app (ns ++ `raw_kernel_smooth) params
        let st ← inferType smooth
        unless st.isAppOfArity ``ContDiffOn 11 do
          throwError "raw native matrix: actual joint raw kernel type changed"
        let sections ← applyNamed
          ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.original_smooth_annular_sections
          (#[(`K,st.getAppArgs[9]!),(`hK,smooth)] ++ known) (some `hx)
        let refined := app `JanetCartan.RawInputPartition.RefinedInput #[n,J]
        withLocalDeclNoLocalInstanceUpdate `w .default refined fun w => do
          let wide ← bodyAt (app ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.original_refined_input #[n,J,w])
          let first := app (ns ++ `raw_matrix_integral) (params ++ #[wide,x,hx])
          let firstType ← inferType first
          unless firstType.isAppOfArity ``Eq 3 do
            throwError "raw native matrix: exact original integral equality changed"
          let fa := firstType.getAppArgs
          let integral ← arguments fa[2]!
          let second ← applyNamed ``PhysicalMean.OriginalMeanQuadraticProfilesTemplate.raw_integral_refined_annuli
            (#[(`v,w),(`hA,sections)] ++ integral ++ known)
          let secondType ← inferType second
          unless secondType.isAppOfArity ``Eq 3 do
            throwError "raw native matrix: unchanged annular expansion ceased to be equality"
          let sa := secondType.getAppArgs
          let proof := mkAppN (mkConst ``Eq.trans [.one]) #[fa[0]!,fa[1]!,fa[2]!,sa[2]!,first,second]
          save `raw_matrix_annuli (params ++ #[w,x,hx]) proof
check_actual_raw_native_matrix 0
check_actual_raw_native_matrix 1
check_actual_raw_native_matrix 2
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native.raw_matrix_integral
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native.raw_kernel_smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Native.raw_matrix_annuli
end JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealizationApplication
end
