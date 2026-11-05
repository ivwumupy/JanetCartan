module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceInput
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.IntegratedSourceDecay.PhysicalJets

/-! Actual baseline and whole-shifted sharp jets from the original graded stage.
The original finite-band rate margins are PROVED by the stage producer, not
passed as new hypotheses. These are independent of the still-external actual
fixed-K Picard input and its uniform Fourier-mass specialization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
open RawPrimary RawInputPartition CanonicalAtomRealization

/-- The actual whole-source response and its original corrected-atom integral
have identical physical jets on the SAME open chart. The original-data command
below supplies `heq` from the already checked whole-response producer, rather
than assuming an interchange or a different physical field
(`app:ch_lag:eq:lag-recurrence`, `main:eq:primary-fixed-scales`). -/
theorem whole_physical_jet_integral {n N J : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hX : IsOpen X) (hV : IsOpen V) (hceil : closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin N)}
    (hA : ContDiffOn ℝ ∞ A (X ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) (f : Euclidean n → EuclideanSpace ℂ (Fin N))
    (heq : EqOn f (wideSuperposition A d v) X)
    (q : ℕ) {x : Euclidean n} (hx : x ∈ X) :
    iteratedFDeriv ℝ q f x =
      ∫ η, weightedWideDensity d v η • iteratedFDeriv ℝ q (fun y ↦ A (y, η)) x := by
  have he : f =ᶠ[𝓝 x] wideSuperposition A d v := by
    filter_upwards [hX.mem_nhds hx] with y hy
    exact heq hy
  rw [(he.iteratedFDeriv ℝ q).self_of_nhds]
  exact iteratedFDeriv_wideSuperposition_eq_integral hX hV hceil hA hd hM hb q v hx

/-- Sharp atomwise jets incur only the SAME literal Fourier L¹ mass. Neither
band count nor the number of Picard updates enters the cost. The actual final
input is14's unweighted fixed-prefix component adjoint, and the sample weight
is left outside the complete baseline-plus-correction wave
(`main:eq:primary-fixed-scales`). -/
theorem whole_physical_jet_le_mass {n N J : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hX : IsOpen X) (hV : IsOpen V) (hceil : closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin N)}
    (hA : ContDiffOn ℝ ∞ A (X ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n J) (f : Euclidean n → EuclideanSpace ℂ (Fin N))
    (heq : EqOn f (wideSuperposition A d v) X)
    (q : ℕ) {x : Euclidean n} (hx : x ∈ X) {C : ℝ}
    (hbound : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ J),
      ‖iteratedFDeriv ℝ q (fun y ↦ A (y, η)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ q f x‖ ≤ C * ∫ η, ‖weightedWideDensity d v η‖ := by
  have he : f =ᶠ[𝓝 x] wideSuperposition A d v := by
    filter_upwards [hX.mem_nhds hx] with y hy
    exact heq hy
  rw [(he.iteratedFDeriv ℝ q).self_of_nhds]
  exact norm_iteratedFDeriv_wideSuperposition_le_integral hX hV hceil hA hd hM hb q v hx hbound

/-- The unchanged original sample label already carries its outer-weight
nonvanishing certificate. This says nothing about the possibly zero angular
factor in the source correction (`main:eq:primary`). -/
theorem original_sample_weight_ne_zero {ι : Type*} {p : ℕ}
    (B : ℝ) (ψ : ι → SeparatedSampling.Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → SeparatedSampling.Lattice → SeparatedSampling.Point)
    (i : CanonicalRowComparison.SampleIndex p B ψ w h U) :
    SeparatedSampling.weight (ψ i.1) w h (U i.1) i.2 ≠ 0 :=
  (Finset.mem_filter.mp i.2.property).2

/-- The original full angular factor costs at most one, including its zero
case where the unweighted inner wave need not be admitted. This is the exact
baseline-plus-whole-source step before the external sqrt-weight synthesis;
`whole_physical_jet_le_mass` supplies its SAME-density inner estimate
(`main:eq:primary`, `main:eq:primary-fixed-scales`). -/
theorem baseline_add_whole_angular_physical_jet {n N : ℕ}
    {Z₀ W : Euclidean n → EuclideanSpace ℂ (Fin N)} {b C mass : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1) (hC : 0 ≤ C) (hmass : 0 ≤ mass)
    (q : ℕ) (x : Euclidean n) (hZ₀ : ContDiffAt ℝ q Z₀ x)
    (hW : b ≠ 0 → ContDiffAt ℝ q W x)
    (hbase : ‖iteratedFDeriv ℝ q Z₀ x‖ ≤ C)
    (hwhole : b ≠ 0 → ‖iteratedFDeriv ℝ q W x‖ ≤ C * mass) :
    ‖iteratedFDeriv ℝ q (Z₀ + b • W) x‖ ≤ C * (1 + mass) := by
  by_cases hb₀ : b = 0
  · simp only [hb₀, zero_smul, add_zero]
    exact hbase.trans (by nlinarith [mul_nonneg hC hmass])
  · change ‖iteratedFDeriv ℝ q (Z₀ + fun y ↦ b • W y) x‖ ≤ C * (1 + mass)
    rw [iteratedFDeriv_add_apply hZ₀ ((hW hb₀).const_smul b)]
    change ‖iteratedFDeriv ℝ q Z₀ x + iteratedFDeriv ℝ q (b • W) x‖ ≤ C * (1 + mass)
    rw [iteratedFDeriv_const_smul_apply (hW hb₀)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ q Z₀ x‖ + ‖b • iteratedFDeriv ℝ q W x‖ := norm_add_le _ _
      _ = ‖iteratedFDeriv ℝ q Z₀ x‖ + b * ‖iteratedFDeriv ℝ q W x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb.1]
      _ ≤ C + C * mass := add_le_add hbase
        ((mul_le_mul_of_nonneg_left (hwhole hb₀) hb.1).trans
          (mul_le_of_le_one_left (mul_nonneg hC hmass) hb.2))
      _ = C * (1 + mass) := by ring

end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesTemplate
open Lean Meta Elab Command
open OriginalCorrectedWaveEnvelopeTemplate
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def envelope := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)
private def emit (field : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual sampled primary: unresolved declaration {field}"
  let name := ns ++ field
  liftM <| IO.eprintln s!"actual sampled primary: checking {field}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original native stage and unchanged whole response on the old Dsmooth chart, with original scalar, source, cutoff, sample and rates (main:eq:primary-fixed-scales). Quantitative completion still requires the actual fixed-K Picard mass bound."
  logInfo m!"actual original physical wave: checked {field} / {xs.size}"

/-- Recover the SAME published graph/source family61 without changing any
callback, scalar or dynamic history field. These are precisely the source
positions not already present in graph42. -/
def originalWaveFamily (color : NativeResponseColor) : Array Expr :=
  color.graph42 ++ #[24,25,30,32,33,34,35,36,37,38,40,45,46,47,48,49,50,51,52].map
    (fun j => color.source53[j]!)

elab "publish_original_native_baseline_sharp_jets" : command => liftTermElabM do
  withPublishedNativeStage fun g => withNativeResponseColor g fun color => do
    let closed := app (geo ++ `outer_weight_closed_cell) color.source53
    forallBoundedTelescope (← inferType closed) (some 5) fun sample _ => do
      unless sample.size == 5 do throwError "actual baseline sharp: original window/mesh/shift/node/weight changed"
      let hc := mkAppN closed sample
      let membership ← Core.betaReduce (← zetaReduce (← inferType hc))
      unless membership.isAppOfArity `Membership.mem 5 do
        throwError "actual baseline sharp: lost SAME closed parent cell"
      let parameter := membership.getAppArgs[4]!
      let h := app (envelope ++ `atom_sharp_spatial_jets)
        (g.args50 ++ #[g.data.i,color.color,parameter,hc])
      emit `baseline_sharp_spatial_jets (g.args50 ++ #[g.data.i,color.color] ++ sample) h

elab "publish_original_native_shifted_sharp_jets" : command => liftTermElabM do
  withPublishedNativeStage fun g => withNativeResponseColor g fun color => do
    let family := originalWaveFamily color
    unless family.size == 61 do throwError "actual shifted sharp: original source/graph61 changed"
    let rates := app (envelope ++ `stage_rates) g.args50
    let hΛ := part rates 1
    let Λ := (← inferType hΛ).appArg!
    let byColor := mkAppN (tail rates 6) #[g.data.i,color.color]
    let margin := tail byColor 3
    let closed := app (wave ++ `Whole.shifted_parameter_in_closed_cell)
      (family ++ #[Λ,hΛ,margin])
    forallBoundedTelescope (← inferType closed) (some 4) fun shifted _ => do
      unless shifted.size == 4 do throwError "actual shifted sharp: carrier/frequency admission changed"
      let hc := mkAppN closed shifted
      let membership ← Core.betaReduce (← zetaReduce (← inferType hc))
      unless membership.isAppOfArity `Membership.mem 5 do
        throwError "actual shifted sharp: lost original shifted closed-cell parameter"
      let parameter := membership.getAppArgs[4]!
      let h := app (envelope ++ `atom_sharp_spatial_jets)
        (g.args50 ++ #[g.data.i,color.color,parameter,hc])
      emit `shifted_sharp_spatial_jets (g.args50 ++ #[g.data.i,color.color] ++ shifted) h

private abbrev NativeArgs := Array (Name × Expr)

private def nativeAt (xs : NativeArgs) (key : Name) : MetaM Expr := do
  let some (_,value) := xs.find? (·.1 == key) |
    throwError "actual primary integral: missing native operand {key}"
  return value

private def nativeArguments (name : Name) (value : Expr) : MetaM NativeArgs := do
  let value := value.headBeta
  unless value.isAppOf name do
    throwError "actual primary integral: expected producer {name}, found {value.getAppFn}"
  let mut type := (← getConstInfo name).type
  let mut xs := #[]
  for value in value.getAppArgs do
    let .forallE key _ rest _ := type.consumeMData |
      throwError "actual primary integral: changed producer telescope {name}"
    xs := xs.push (key,value)
    type := rest
  return xs

private def applyNativeThrough (name last : Name) (xs : NativeArgs) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut value := mkConst name
  while let .forallE key _ rest _ := type.consumeMData do
    value := mkApp value (← nativeAt xs key)
    if key == last then return value
    type := rest
  throwError "actual primary integral: missing final native operand {last}"

private def nativeType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "actual primary integral: changed published declaration arity"
    type := rest.instantiate1 arg
  return type

private def withNativeIntegral (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Whole.derivative_integral
  let some body := info.value? (allowOpaque := true) |
    throwError "actual primary integral: native whole-response proof unavailable"
  openBinders 69 info.type #[] fun args => go args (body.beta args)
where
  openBinders : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,args,go => go args
    | remaining+1,type,args,go => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary integral: native69 ended at {args.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        openBinders remaining (body.instantiate1 x) (args.push x) go

/-- Reuse the actual whole-response continuity, unchanged shift window and exact
Fourier density already present in89's native69 proof. This is a physical-field
identity, not a new successful-source or Fourier-mass hypothesis. -/
elab "publish_original_native_whole_physical_jets" : command => liftTermElabM do
  withNativeIntegral fun all value => do
    let whole := `JanetCartan.CanonicalAtomRealization
    let vals ← nativeArguments (whole ++ `wholeSourceCorrectedDerivative_eq_integral) value
    let derivativeType ← nativeType value
    unless derivativeType.isAppOfArity ``Eq 3 do
      throwError "actual primary integral: native derivative result changed"
    let raw ← nativeArguments `JanetCartan.rawPrimaryDemodulatedIntegral derivativeType.appArg!
    let ζ ← nativeAt raw `ζ
    let waveEq ← applyNativeThrough (whole ++ `wholeSourceCorrectedWave_eq_correctedWideWave) `hx vals
    let waveType ← nativeType waveEq
    unless waveType.isAppOfArity ``Eq 3 do
      throwError "actual primary integral: whole displacement identity changed"
    let f := waveType.getAppArgs[1]!.appFn!
    let heq ← mkLambdaFVars all[67:].toArray waveEq
    let hA ← applyNativeThrough (whole ++ `contDiffOn_shiftedCorrectedAtom) `hshift
      (#[(`O,← nativeAt vals `X),(`ζ,ζ)] ++ vals)
    let smoothType ← nativeType hA
    unless smoothType.isAppOfArity ``ContDiffOn 11 do
      throwError "actual primary integral: shifted corrected atom smoothness changed"
    let A := smoothType.getAppArgs[9]!
    let known := #[(`A,A),(`hA,hA),(`f,f),(`heq,heq)] ++ vals
    let params := all[:67].toArray
    emit `Whole.corrected_displacement_integral all waveEq false (some waveType)
    let jets ← applyNativeThrough (ns ++ `whole_physical_jet_integral) `heq known
    emit `Whole.physical_jet_integral params jets false (some (← nativeType jets))
    let mass ← applyNativeThrough (ns ++ `whole_physical_jet_le_mass) `heq known
    emit `Whole.physical_jet_mass params mass false (some (← nativeType mass))

private def originalBodyAt (name : Name) (args : Array Expr)
    (levels : List Level := []) : MetaM Expr := do
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) |
    throwError "actual primary field: unavailable original producer {name}"
  unless info.levelParams.length == levels.length do
    throwError "actual primary field: native producer universe arguments changed"
  return ((body.instantiateLevelParams info.levelParams levels).beta args).headBeta

private def withFrozenInput (name : Name) (count : Nat)
    (next : Array Expr → MetaM Unit) : MetaM Unit := do
  bindNative count (← getConstInfo name).type #[] next
where
  bindNative : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,params,go => go params
    | remaining+1,type,params,go => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary input: frozen telescope ended at {params.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        bindNative remaining (body.instantiate1 x) (params.push x) go

/-- The physical field uses14's literal UNWEIGHTED final component input. The
positive baseline stays unscaled, the source correction keeps its zero-safe
original angular factor, and sqrt of the sample weight remains external. This
constructs the field and its old-chart smoothness, not its yet-pending Picard
norm bound (`main:eq:primary`, `main:eq:primary-fixed-scales`). -/
elab "publish_original_native_final_combined_wave" : command => liftTermElabM do
  let inputName := `JanetCartan.PhysicalMean.OriginalCanonicalSource.finalWideInput
  withFrozenInput inputName 54 fun params => do
    let sampled := `JanetCartan.PhysicalMean.OriginalCanonicalSampled
    let actual := `JanetCartan.PhysicalMean.OriginalCanonicalActual
    let xs := params[:50].toArray
    let ξ := params[50]!
    let i := params[53]!
    let I ← inferType i
    unless I.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual primary field: final input lost its literal OUTER sample index"
    let outerSample := I.getAppArgs
    let packed ← originalBodyAt (sampled ++ `G) (xs ++ #[ξ,i])
    unless packed.isAppOf (sampled ++ `sampledDerivative) do
      throwError "actual primary field: original sampled derivative wrapper changed"
    let unpacked ← originalBodyAt (sampled ++ `sampledDerivative) packed.getAppArgs
      packed.getAppFn.constLevels!
    unless unpacked.isAppOfArity (actual ++ `G) 53 do
      throwError "actual primary field: original native53 G changed"
    let literal ← originalBodyAt (actual ++ `G) unpacked.getAppArgs
    unless literal.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G 65 do
      throwError "actual primary field: original source53/graph42 join changed"
    let native := literal.getAppArgs
    let row := Expr.proj ``Sigma 0 i
    let node := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 1 i)
    let sample := #[outerSample[4]!,outerSample[5]!,mkApp outerSample[6]! row,node]
    let v := app inputName params
    let args := native[:64].toArray ++ sample
    let field := app (wave ++ `Combined.field) (args.push v)
    emit `finalCombinedWave params field true (some (← nativeType field))
    let hweight := mkAppN (mkConst (ns ++ `original_sample_weight_ne_zero) [.zero])
      (outerSample.push i)
    let hSmooth := app (wave ++ `Combined.active_smooth) (args ++ #[hweight,v])
    let smoothType ← nativeType hSmooth
    unless smoothType.isAppOfArity ``ContDiffOn 11 do
      throwError "actual primary field: old cutoff chart smoothness changed"
    let target := mkAppN smoothType.getAppFn
      (smoothType.getAppArgs.set! 9 (app (ns ++ `finalCombinedWave) params))
    emit `finalCombinedWave_smooth params hSmooth false (some target)

/-- Choose only the already fixed event shift used by14's
`selectedFinalWideInput`; this is not another selection or sampler. -/
elab "publish_original_native_selected_combined_wave" : command => liftTermElabM do
  let inputName := `JanetCartan.PhysicalMean.OriginalCanonicalSource.selectedFinalWideInput
  withFrozenInput inputName 52 fun params => do
    let original ← originalBodyAt inputName params
    unless original.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.finalWideInput 53 do
      throwError "actual selected physical field: original single chosen shift changed"
    let field := app (ns ++ `finalCombinedWave) original.getAppArgs
    emit `selectedFinalCombinedWave params field true (some (← nativeType field))
    let smooth := app (ns ++ `finalCombinedWave_smooth) original.getAppArgs
    emit `selectedFinalCombinedWave_smooth params smooth false (some (← nativeType smooth))

/-- Read the physical family on14's ONE selected shift together with the literal
`d, M, hd, hM, hb` already present in its native whole-wave smoothness proof.
The callback returns selected53, its unweighted input, the unchanged complete
physical field, the SAME source-family/rate64, and the detector dictionary. It
does not construct a new mask, source, scalar, sample, or norm assumption. -/
def withActualSelectedFinalWave
    (next : Array Expr → Expr → Expr → Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  let inputName := `JanetCartan.PhysicalMean.OriginalCanonicalSource.selectedFinalWideInput
  let type := (← getConstInfo inputName).type
  bindNative 53 type #[] fun params => do
    let input := app inputName params
    let actualInput ← originalBodyAt inputName params
    unless actualInput.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.finalWideInput 54 do
      throwError "actual primary detector: selected input lost the SAME chosen shift"
    let field := app (ns ++ `finalCombinedWave) actualInput.getAppArgs
    let literal ← originalBodyAt (ns ++ `finalCombinedWave) actualInput.getAppArgs
    unless literal.isAppOfArity (wave ++ `Combined.field) 69 do
      throwError "actual primary detector: final field lost the original whole-wave family"
    let native64 := literal.getAppArgs[:64].toArray
    let rawBody ← originalBodyAt (wave ++ `Whole.raw_on_selected_cell) native64
    let rawName := `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave
    let some raw := rawBody.find? (·.isAppOf rawName) |
      throwError "actual primary detector: original whole-wave smoothness producer missing"
    let known ← nativeArguments rawName raw
    let mut detector := #[]
    for key in #[`d,`M,`hd,`hM,`hb] do
      let value ← nativeAt known key
      if value.hasLooseBVars then
        throwError "actual primary detector: {key} depends on an unchosen carrier or Hilbert datum"
      detector := detector.push (key,value)
    next params input field native64 detector
where
  bindNative : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,params,go => go params
    | remaining+1,type,params,go => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary detector: selected53 ended at {params.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        bindNative remaining (body.instantiate1 x) (params.push x) go

/-- On14's one selected shift, integrate86's unchanged sharp corrected atoms,
then add the unscaled positive baseline and the original zero-safe angular
factor. The right side is the L¹ mass of the ACTUAL finalWideInput, not a free
WideInput or a claimed Picard bound. External sqrtμ is still absent here. -/
elab "publish_original_selected_final_wave_mass_jets" : command => liftTermElabM do
  withActualSelectedFinalWave fun params input field native64 detector => do
    let literal ← originalBodyAt (ns ++ `finalCombinedWave) field.getAppArgs
    let combinedArgs := literal.getAppArgs
    let combined ← originalBodyAt (wave ++ `Combined.field) combinedArgs
    unless combined.isAppOfArity ``HAdd.hAdd 6 do
      throwError "actual final physical jets: changed baseline-plus-full-angular sum"
    let base := combined.getAppArgs[4]!
    let sample := combinedArgs[64:68].toArray
    let i := params[52]!
    let index ← inferType i
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual final physical jets: original outer sample changed"
    let sa := index.getAppArgs
    let row := Expr.proj ``Sigma 0 i
    let sampleValue := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 1 i)
    let color := app `JanetCartan.SeparatedSampling.color #[sa[1]!,Expr.proj ``Prod 0 sampleValue]
    let hweight := mkAppN (mkConst (ns ++ `original_sample_weight_ne_zero) [.zero]) (sa.push i)
    let atomic := params[:50].toArray ++ #[row,color]
    let baseline := app (ns ++ `baseline_sharp_spatial_jets) (atomic ++ sample.push hweight)
    let baselineType ← nativeType baseline
    unless baselineType.isAppOfArity ``And 2 do
      throwError "actual final physical jets: baseline sharp conjunction changed"
    let smoothType := baselineType.getAppArgs[0]!
    let X := smoothType.getAppArgs[10]!
    let hX ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[X]))
    let node := app `JanetCartan.SeparatedSampling.node sample[1:4].toArray
    let factorEq := app (wave ++ `Whole.full_angular_factor.corrected) (native64 ++ #[node,input])
    let factorType ← nativeType factorEq
    unless factorType.isAppOfArity ``Eq 3 && factorType.appArg!.isAppOfArity ``HSMul.hSMul 6 do
      throwError "actual final physical jets: full-angular factor identity changed"
    let b := factorType.appArg!.getAppArgs[4]!
    let W := factorType.appArg!.getAppArgs[5]!
    unless b.isAppOfArity `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.factor 24 do
      throwError "actual final physical jets: not the original zero-safe angular factor"
    let hb := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.factor_range b.getAppArgs
    let d ← nativeAt detector `d
    let mass ← termWith [(`d,d),(`v,input)]
      "(∫ η, ‖JanetCartan.RawInputPartition.weightedWideDensity d v η‖)" (some (mkConst ``Real))
    let zero ← mkNumeral (mkConst ``Real) 0
    let hmass ← termWith [] "(by exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))"
      (some (← mkAppM ``LE.le #[zero,mass]))
    let rawBody ← originalBodyAt (wave ++ `Whole.raw_on_selected_cell) native64
    let rawName := `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave
    let some raw := rawBody.find? (·.isAppOf rawName) |
      throwError "actual final physical jets: native source admission disappeared"
    let rawKnown ← nativeArguments rawName raw
    let T ← nativeAt rawKnown `T
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "actual final physical jets: original source53 changed"
    let source := T.getAppArgs
    let hcut := app (geo ++ `smoothing_chart_in_source_chart) source[:23].toArray
    let support := app (wave ++ `Whole.inner_factor_support) (native64[:61].toArray.push node)
    let supportType ← nativeType support
    let .forallE supportLabel supportDomain _ supportBi := supportType.consumeMData |
      throwError "actual final physical jets: original factor support implication missing"
    let withSupport (next : Expr → Array Expr → MetaM Expr) : MetaM Expr := do
      withLocalDeclNoLocalInstanceUpdate supportLabel supportBi supportDomain fun nonzero => do
        let hp := mkApp support nonzero
        let hpType ← nativeType hp
        unless hpType.isAppOfArity ``Membership.mem 5 do
          throwError "actual final physical jets: native inner carrier support changed"
        let carrier := hpType.getAppArgs[4]!
        let whole := native64 ++ #[carrier,hp,input]
        mkLambdaFVars #[nonzero] (← next nonzero whole)
    let jetsType := baselineType.getAppArgs[1]!
    forallBoundedTelescope jetsType (some 3) fun point result => do
      unless point.size == 3 && result.isAppOfArity ``LE.le 4 do
        throwError "actual final physical jets: original jet/point/chart tail changed"
      let q := point[0]!
      let x := point[1]!
      let hx := point[2]!
      let C := result.getAppArgs[3]!
      let hbase := mkAppN (tail baseline 1) point
      let hC ← termWith [(`h,hbase)] "(by exact (norm_nonneg _).trans h)"
        (some (← mkAppM ``LE.le #[zero,C]))
      let known := #[(`n,← nativeAt rawKnown `n),(`N,← nativeAt rawKnown `N),
        (`Z₀,base),(`W,W),(`b,b),(`C,C),(`mass,mass),(`hb,hb),(`hC,hC),(`hmass,hmass),(`q,q),(`x,x)]
      let partialProof ← applyNativeThrough (ns ++ `baseline_add_whole_angular_physical_jet) `x known
      let .forallE _ hBaseType _ _ := (← nativeType partialProof).consumeMData |
        throwError "actual final physical jets: zero-safe baseline smoothness input changed"
      let hbaseSmooth ← termWith [(`h,part baseline 0),(`hX,hX),(`hx,hx)]
        "((h.contDiffAt (hX.mem_nhds hx)).of_le (by simp))" (some hBaseType)
      let afterBase := mkApp partialProof hbaseSmooth
      let .forallE _ hWholeType _ _ := (← nativeType afterBase).consumeMData |
        throwError "actual final physical jets: zero-safe whole smoothness input changed"
      let hwholeSmooth ← withSupport fun _ whole => do
        let smooth := app (wave ++ `Whole.corrected_on_cutoff_chart) whole
        let expected := hWholeType.bindingBody!
        termWith [(`h,smooth),(`hX,hX),(`hx,hx)]
          "((h.contDiffAt (hX.mem_nhds hx)).of_le (by simp))" (some expected)
      let afterSmooth := mkAppN afterBase #[hwholeSmooth,hbase]
      let hwhole ← withSupport fun _ whole => do
        let sourceSmooth ← originalBodyAt (wave ++ `Whole.corrected_on_source_chart) whole
        unless sourceSmooth.isAppOf ``ContDiffOn.mono do
          throwError "actual final physical jets: original source-chart inclusion changed"
        let inCell := sourceSmooth.getAppArgs.back!
        let hxCell := mkAppN inCell #[x,mkAppN hcut #[x,hx]]
        let massProof := app (ns ++ `Whole.physical_jet_mass) (whole ++ #[q,x,hxCell,C])
        let .forallE _ boundType _ _ := (← nativeType massProof).consumeMData |
          throwError "actual final physical jets: actual atomic-integral bound changed"
        let bound ← forallBoundedTelescope boundType (some 2) fun freq _ => do
          unless freq.size == 2 do throwError "actual final physical jets: original Fourier ceiling changed"
          let inWindow := mkAppN (← nativeAt rawKnown `hVceil) freq
          let shifted := app (ns ++ `shifted_sharp_spatial_jets)
            (atomic ++ whole[64:66].toArray ++ #[freq[0]!,inWindow])
          mkLambdaFVars freq (mkAppN (tail shifted 1) point)
        return mkApp massProof bound
      let proof := mkApp afterSmooth hwhole
      let resultType ← nativeType proof
      let summed := factorType.appArg!
      let combinedTarget ← mkAppM ``HAdd.hAdd #[base,summed]
      let target := resultType.replace fun e => if e == combinedTarget then some field else none
      unless (target.find? (· == field)).isSome do
        throwError "actual final physical jets: result did not retain the literal selected final field"
      let actual ← termWith [(`h,proof),(`heq,factorEq)]
        "(by simpa only [← heq] using h)" (some target)
      emit `selectedFinalCombinedWave_mass_jets (params ++ point) actual false (some target)

end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesTemplate
end
