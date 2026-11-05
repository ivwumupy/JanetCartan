module

public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredSupport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.WholeSource
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-!
# Realize the original whole-wave derivative without changing the physical wave

The local linear map and local smoothness are supplied by the actual original53/
graph42 whole-wave construction. Differentiation is local on that same chart.
Only its auxiliary torus representative is multiplied by the prescribed source
cutoff, which has a genuine one-germ on the ENTIRE measurement support. This is
not a new physical output cutoff or another factor on the source before B.

Consumers: the actual `CanonicalSource.fixedSourceLinear_toL2` raw action and
`app:ch_mean_pairs:eq:mean-current-canonical`. Quantitative profiles and the
actual fixed-K Picard run remain separate parent obligations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate
open RawInputPartition CurrentMean AmplitudeBound ContinuumRow

variable {n N J : ℕ} {X : Set (Euclidean n)} (hX : IsOpen X)
    (W : WideInput n J →ₗ[ℝ] (X → EuclideanSpace ℂ (Fin N)))
    (f : WideInput n J → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hW : ∀ v x, W v x = f v x)
    (hf : ∀ v, ContDiffOn ℝ ∞ (f v) X)
    (phase : Euclidean n → ℂ)

private def nativeDerivative (v : WideInput n J) (x : Euclidean n) :
    Matrix (Fin N) (Fin n) ℂ :=
  phase x • RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ (f v) x)

private def nativeDerivativeAt (x : X) :
    WideInput n J →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ := by
  have hd (v : WideInput n J) : DifferentiableAt ℝ (f v) x :=
    ((hf v).contDiffAt (hX.mem_nhds x.property)).differentiableAt (by simp)
  refine { toFun := fun v ↦ nativeDerivative f phase v x, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    have he : f (v+w) =ᶠ[𝓝 x.val] f v + f w := by
      filter_upwards [hX.mem_nhds x.property] with y hy
      simpa only [hW, Pi.add_apply] using congrFun (W.map_add v w) ⟨y,hy⟩
    unfold nativeDerivative
    rw [he.fderiv_eq, fderiv_add (hd v) (hd w), map_add, smul_add]
  · intro a v
    have he : f (a • v) =ᶠ[𝓝 x.val] a • f v := by
      filter_upwards [hX.mem_nhds x.property] with y hy
      simpa only [hW, Pi.smul_apply, RingHom.id_apply] using congrFun (W.map_smul a v) ⟨y,hy⟩
    unfold nativeDerivative
    rw [he.fderiv_eq, fderiv_const_smul (hd v) a, map_smul]
    exact smul_comm _ _ _

variable (hphase : ContDiffOn ℝ ∞ phase X)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1/2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

include hX hf hphase in
private theorem nativeDerivative_smooth (v : WideInput n J) :
    ContDiffOn ℝ ∞ (nativeDerivative f phase v) X := by
  exact hphase.smul
    ((RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).contDiff.comp_contDiffOn
      ((hf v).fderiv_of_isOpen hX (m := ∞) (by simp)))

include hX hf hphase hψ hψX hcell hbox in
private theorem nativeDerivative_periodic (v : WideInput n J) :
    IsSmoothPeriodic (fun z ↦ ψ (centeredTorusRepresentative z) •
      nativeDerivative f phase v (centeredTorusRepresentative z)) := by
  have hD := nativeDerivative_smooth hX f hf phase hphase v
  have hh := preparationMatrixExtension_regular ψ hψ hX hψX hcell hbox
    (fun p ↦ nativeDerivative f phase v p.1)
    (hD.comp contDiffOn_fst (fun _ hp ↦ hp.1))
  exact ⟨hh.1.comp (continuous_id.prodMk (continuous_const (y := 0))),
    hh.2.comp (contDiff_id.prodMk (contDiff_const (c := 0)))⟩

/-- Differentiate the same locally linear raw field, then use the supplied
chart extension. The actual application supplies W, f and all local certificates
from the original whole wave, not an assumed canonical G
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def nativePeriodicDerivative :
    WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) where
  toFun v := ⟨fun z _ ↦ ψ (centeredTorusRepresentative z) •
    (phase (centeredTorusRepresentative z) •
      RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
        (fderiv ℝ (f v) (centeredTorusRepresentative z))),
    fun _ ↦ by exact nativeDerivative_periodic hX f hf phase hphase ψ hψ hψX hcell hbox v⟩
  map_add' v w := by
    apply Subtype.ext
    funext z u
    by_cases hz : centeredTorusRepresentative z ∈ tsupport ψ
    · let D := nativeDerivativeAt hX W f hW hf phase ⟨centeredTorusRepresentative z,hψX hz⟩
      change ψ _ • D (v+w) = ψ _ • D v + ψ _ • D w
      rw [map_add, smul_add]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  map_smul' a v := by
    apply Subtype.ext
    funext z u
    by_cases hz : centeredTorusRepresentative z ∈ tsupport ψ
    · let D := nativeDerivativeAt hX W f hW hf phase ⟨centeredTorusRepresentative z,hψX hz⟩
      change ψ _ • D (a • v) = a • (ψ _ • D v)
      rw [map_smul]
      exact smul_comm _ _ _
    · simp [image_eq_zero_of_notMem_tsupport hz]

/-- The periodization uses the literal derivative on every plateau point;
no response is moved through the integral or re-solved. -/
theorem nativePeriodicDerivative_apply (v : WideInput n J) (z : Torus n) :
    (nativePeriodicDerivative hX W f hW hf phase hphase ψ hψ hψX hcell hbox v).val z () =
      ψ (centeredTorusRepresentative z) •
        (phase (centeredTorusRepresentative z) •
          RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
            (fderiv ℝ (f v) (centeredTorusRepresentative z))) := rfl

open scoped JanetCartan.TensorFrobenius
open ActualCarriers CurrentFullPhase FrozenMenu RawPrimary LeadingWave.FullModulation

private theorem originalDemodulation_smooth {n J : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    {X : Set (Euclidean n)} {V : Set (Euclidean (n-1))} {τ : ℝ} {z : Euclidean 3}
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hshift : ∀ p ∈ X ×ˢ V, (p.1,(z,T.reference.spatialPatch z+τ • p.2)) ∈ Ω)
    (hceil : closedBall (0 : Euclidean (n-1)) ((2 : ℝ)^J) ⊆ V) :
    ContDiffOn ℝ ∞ (fun x ↦ Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ))) X := by
  have hzero : (0 : Euclidean (n-1)) ∈ V := hceil (mem_closedBall_self (by positivity))
  have hp : ContDiffOn ℝ ∞ (fun x ↦ T.carrier Q x z) X := by
    have hm : ContDiffOn ℝ ∞
        (fun x : Euclidean n ↦ (x,(z,T.reference.spatialPatch z))) X :=
      contDiffOn_id.prodMk contDiffOn_const
    have hs : ∀ x ∈ X, (x,(z,T.reference.spatialPatch z)) ∈ Ω := by
      intro x hx
      simpa only [smul_zero,add_zero] using hshift (x,0) ⟨hx,hzero⟩
    simpa only [Function.comp_def,fullPrimaryPhase_on_carrier] using
      (contDiffOn_fullPhase T Q hphase).comp hm hs
  exact (contDiffOn_const.mul
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (hp.div_const τ))).cexp

private def sourceObservation {n : ℕ} {μ : ℝ} (hμ : 0 < μ) : Euclidean n → ℝ :=
  FixedCutoffs.physical hμ 2

private theorem sourceObservation_smooth {n : ℕ} {μ : ℝ} (hμ : 0 < μ) :
    ContDiff ℝ ∞ (sourceObservation (n := n) hμ) :=
  (FixedCutoffs.physical hμ 2).contDiff

private theorem source_cutoff_box {n : ℕ} {μ : ℝ} (hμ : 0 < μ) :
    ∀ x ∈ tsupport (FixedCutoffs.physical (n := n) hμ 2), ∀ i, |x i| ≤ 4*μ := by
  intro x hx i
  exact (PiLp.norm_apply_le x i).trans
    (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hμ 2 hx))

private theorem observation_support_in_selected_cell {n : ℕ}
    {ψ : Euclidean n → ℝ} {a ρ σ : ℝ}
    {zRoot zCell : Euclidean 3} {ηRoot ηCell : Euclidean (n-1)}
    (hψ : tsupport ψ ⊆ closedBall (0 : Euclidean n) (a/8))
    (hA : 4*a ≤ ρ/2) (hρ : 0 < ρ)
    (hparent : closedBall ((0 : Euclidean n),(zRoot,ηRoot)) (2*ρ) ⊆
      ball ((0 : Euclidean n),(zCell,ηCell)) σ) :
    tsupport ψ ⊆ ball (0 : Euclidean n) σ := by
  intro x hx
  have hx' : x ∈ closedBall (0 : Euclidean n) (2*ρ) :=
    closedBall_subset_closedBall (by linarith : a/8 ≤ 2*ρ) (hψ hx)
  have hp : (x,(zRoot,ηRoot)) ∈
      closedBall ((0 : Euclidean n),(zRoot,ηRoot)) (2*ρ) := by
    rw [← closedBall_prod_same]
    exact ⟨hx',mem_closedBall_self (by positivity)⟩
  have hs := hparent hp
  rw [← ball_prod_same] at hs
  exact hs.1

private theorem whole_derivative_factor {n N : ℕ} {a : ℝ}
    {full bare : Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hfield : full = a • bare) (phase : ℂ) (x : Euclidean n) :
    phase • RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N (fderiv ℝ full x) =
      a • (phase • RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
        (fderiv ℝ bare x)) := by
  rw [hfield,congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := bare) a) x,
    Pi.smul_apply,map_smul,smul_comm]

private theorem full_derivative_apply {n N J : ℕ} (a : ℝ)
    (G : a ≠ 0 → WideInput n J →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (ψ : Euclidean n → ℝ)
    (full bare : WideInput n J → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hfactor : ∀ v x, full v x = a • bare v x)
    (hG : ∀ h v z, (G h v).val z () =
      ψ (centeredTorusRepresentative z) • bare v (centeredTorusRepresentative z))
    (v : WideInput n J) (z : Torus n) :
    (let _ := Classical.propDecidable
     ((if h : a = 0 then (0 : WideInput n J →ₗ[ℝ]
       SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) else a • G h) v).val z ()) =
      ψ (centeredTorusRepresentative z) • full v (centeredTorusRepresentative z) := by
  classical
  dsimp only
  by_cases ha : a = 0
  · rw [dite_eq_left ha]
    change (0 : Matrix (Fin N) (Fin n) ℂ) = _
    rw [hfactor,ha,zero_smul,smul_zero]
  · rw [dite_eq_right ha]
    change a • (G ha v).val z () = _
    rw [hG,hfactor,smul_comm]

private theorem source_germ_on_measurement_support {d : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (x : Euclidean d) (hx : x ∈ tsupport (FixedCutoffs.physical (n := d) hμ 1)) :
    (FixedCutoffs.physical (n := d) hμ 2 : Euclidean d → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := by
  have hs := FixedCutoffs.physical_tsupport hμ 1 hx
  have hs' : x ∈ closedBall (0 : Euclidean d) (((2 : Fin 3).val+1 : ℝ)*μ) := by
    convert ball_subset_closedBall hs using 1; norm_num
  exact mem_interior_iff_mem_nhds.mp (FixedCutoffs.physical_plateau hμ 2 hs')

end JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def progress (message : String) : MetaM Unit := do
  logInfo message
  if let some path ← IO.getEnv "JANET_G_TRACE" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn message
      h.flush

private def bodyAtOpaque (name : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "original derivative: unavailable definition {name}"
  return (value.beta xs).headBeta

/-- Retain the original common source cutoff as the auxiliary observation
extension. No additional cutoff or admissibility condition is selected. -/
elab "construct_original_derivative_observation" : command => liftTermElabM do
  let inner := `JanetCartan.PhysicalSampling.OriginalWeights
  let selected := `JanetCartan.PhysicalSeed.SelectedBoundary
  let ns := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative
  forallTelescope (← getConstInfo (inner ++ `Index)).type fun all result => do
    unless all.size == 22 && result.isSort do
      throwError "original derivative: expected same original22 index"
    let n := mkApp (mkConst ``Nat.succ) all[0]!
    let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
      #[all[0]!,all[1]!,all[2]!,all[21]!]
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n,all[1]!,merged]
    let native := (#[n,all[1]!] ++ all[3:22].toArray).set! 20 capped
    let sel (field : Name) := mkAppN (mkConst (selected ++ field)) native
    let two ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 2
    let μ := sel `rMeasure
    let hμ := sel `hrMeasure
    let χ := mkAppN (mkConst `JanetCartan.ContinuumRow.FixedCutoffs.physical) #[n,μ,hμ,two]
    discard <| store (ns ++ `observationCutoff) all χ true
    discard <| store (ns ++ `observationFunction) all
      (mkAppN (mkConst ``sourceObservation) #[n,μ,hμ]) true
    discard <| store (ns ++ `observation_smooth) all
      (mkAppN (mkConst ``sourceObservation_smooth) #[n,μ,hμ])
    discard <| store (ns ++ `observation_cell) all (sel `hMeasureCell)
    discard <| store (ns ++ `observation_support) all
      (mkAppN (mkConst `JanetCartan.ContinuumRow.FixedCutoffs.physical_tsupport_four) #[n,μ,hμ,two])
    discard <| store (ns ++ `observation_germ_on_measurement) all
      (mkAppN (mkConst ``source_germ_on_measurement_support) #[n,μ,hμ])
  logInfo "original22 canonical derivative: SAME common physical source cutoff; true one-germ on entire measurement support, exact native 4mu cell bound; no chi2/source recut"

private def declaredForalls : Expr → Nat
  | .forallE _ _ body _ => 1 + declaredForalls body
  | .mdata _ body => declaredForalls body
  | _ => 0

private def nativeTelescope (type : Expr) (count : Nat)
    (k : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  go count type #[]
where
  go : Nat → Expr → Array Expr → MetaM Unit
    | 0, result, xs => k xs result
    | remaining + 1, type, xs => do
      let .forallE name domain body bi := type.consumeMData
        | throwError "original derivative: native telescope ended at {xs.size}"
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => go remaining (body.instantiate1 x) (xs.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
          go remaining (body.instantiate1 x) (xs.push x)

private def namedArguments (name : Name) (value : Expr) : MetaM (Array (Name × Expr)) := do
  unless value.isAppOf name do
    throwError "original derivative: expected literal producer {name}, obtained {value.getAppFn}"
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  for arg in value.getAppArgs do
    let .forallE label _ body _ := type.consumeMData
      | throwError "original derivative: producer binder changed at {name}"
    result := result.push (label,arg)
    type := body
  return result

private def knownArgument (known : Array (Name × Expr)) (label : Name) : MetaM Expr := do
  let some (_,value) := known.find? (fun p => p.1 == label)
    | throwError "original derivative: missing actual producer argument {label}"
  return value

private def applyOriginalByName (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec options : Expr → Array (Option Expr)
    | .forallE label _ body _ =>
      #[(known.find? (fun p => p.1 == label)).map Prod.snd] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  mkAppOptM name (options (← getConstInfo name).type)

private def applyKnownExact (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut args : Array Expr := #[]
  while type.isForall do
    let .forallE label _ body _ := type
      | break
    let some (_,value) := known.find? (fun p => p.1 == label)
      | throwError "original derivative: exact producer argument missing {name}.{label}"
    args := args.push value
    type := body
  return mkAppN (mkConst name) args

/-- Build G on the exact native inner carrier, using the original whole source
and response. All geometry, smoothness, support and phase certificates are
read from their actual original producers; no successful G is a binder. -/
elab "construct_original_whole_source_derivative" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative
  let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
  let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let whole := `JanetCartan.CanonicalAtomRealization
  let rawName := wave ++ `Whole.raw_on_selected_cell
  let correctedName := wave ++ `Whole.corrected_on_selected_cell
  let info ← getConstInfo correctedName
  progress "original derivative G: corrected metadata loaded"
  let count := declaredForalls info.type
  logInfo m!"original derivative G: declared count {count}"
  nativeTelescope info.type count fun all result => do
    unless all.size == 67 && result.isAppOf `ContDiffOn do
      throwError "original derivative: expected native67 ending in literal ContDiffOn, got {all.size}/{result.getAppFn}"
    progress "original derivative G: native67 boundary passed"
    let v := all.back!
    let params := all.pop
    let rawProof ← bodyAtOpaque rawName all
    progress "original derivative G: raw body extracted"
    let rawArgs ← namedArguments `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave rawProof
    progress "original derivative G: raw args named"
    let field ← bodyAtOpaque (wave ++ `Whole.corrected) all
    progress "original derivative G: corrected body extracted"
    let fieldArgs ← namedArguments (whole ++ `wholeSourceCorrectedWave) field
    progress "original derivative G: corrected args named"
    let known := (fieldArgs ++ rawArgs).push
      (`hceil,← knownArgument rawArgs `hVceil)
    let T ← knownArgument known `T
    progress "original derivative G: known source arguments"
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "original derivative: whole wave lost its literal original53 current"
    let source := T.getAppArgs
    let current ← PhysicalPrimary.OriginalLocalWaveGeometryTemplate.sourceCurrent source
    progress "original derivative G: source current extracted"
    let nativeSource := mkAppN (mkConst (masks ++ `χ₂_support_chart)) source[:23].toArray
    let nativeCell := mkAppN (mkConst (masks ++ `chart_in_cell))
      (source[:23].toArray ++ #[current.patch,current.cell])
    let hsrc ← mkAppM `Set.Subset.trans #[nativeSource,nativeCell]
    progress "original derivative G: native source support assembled"
    let known := known.push (`hsrc,hsrc)
    let W ← applyKnownExact (whole ++ `wholeSourceCorrectedWaveLinearMap) known
    progress "original derivative G: corrected wave linear map applied"
    let f ← mkLambdaFVars #[v] field
    let hf ← mkLambdaFVars #[v] (mkAppN (mkConst correctedName) all)
    let X ← knownArgument known `X
    let xType ← mkAppM ``Subtype #[X]
    let hW ← withLocalDeclNoLocalInstanceUpdate `x .default xType fun x => do
      let proof ← applyKnownExact (whole ++ `wholeSourceCorrectedWaveLinearMap_apply)
        (known.push (`x,x))
      mkLambdaFVars #[v,x] proof
    progress "original derivative G: hW original identity applied"
    let hphase := mkAppN (mkConst ``originalDemodulation_smooth) #[(← knownArgument known `n),
      (← knownArgument known `J), (← knownArgument known `P), (← knownArgument known `U),
      (← knownArgument known `hU), (← knownArgument known `T), (← knownArgument known `Q),
      (← knownArgument known `Ω), (← knownArgument known `X), (← knownArgument known `V),
      (← knownArgument known `τ), (← knownArgument known `z), (← knownArgument known `hphase),
      (← knownArgument known `hshift), (← knownArgument known `hceil)]
    progress "original derivative G: hphase applied"
    let n0 ← knownArgument known `n
    let T0 ← knownArgument known `T
    let Q0 ← knownArgument known `Q
    let τ0 ← knownArgument known `τ
    let z0 ← knownArgument known `z
    let xType0 ← mkAppM ``Euclidean #[n0]
    let phase ← withLocalDeclD `phase_x xType0 fun x => do
      let P0 ← knownArgument known `P
      let U0 ← knownArgument known `U
      let hU0 ← knownArgument known `hU
      let carrier := mkAppN (mkConst `JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily.carrier)
        #[n0,P0,U0,hU0,T0,Q0,x,z0]
      progress "original derivative G: phase carrier assembled"
      let quotient ← mkAppM ``HDiv.hDiv #[carrier,τ0]
      progress "original derivative G: phase quotient assembled"
      let ofReal ← mkAppM ``Complex.ofReal #[quotient]
      let negI ← mkAppM ``Neg.neg #[mkConst ``Complex.I]
      progress "original derivative G: phase neg assembled"
      let argument ← mkAppM ``HMul.hMul #[negI,ofReal]
      let value ← mkAppM ``Complex.exp #[argument]
      mkLambdaFVars #[x] value
    progress "original derivative G: phase constructed"
    let fixed := all[:22].toArray
    let ψ := mkAppN (mkConst (ns ++ `observationFunction)) fixed
    let hψ := mkAppN (mkConst (ns ++ `observation_smooth)) fixed
    progress "original derivative G: observation smoothness applied"
    let physical ← bodyAtOpaque (ns ++ `observationCutoff) fixed
    unless physical.isAppOfArity `JanetCartan.ContinuumRow.FixedCutoffs.physical 4 do
      throwError "original derivative: observation cutoff is not the same native source cutoff"
    let cutArgs := physical.getAppArgs
    let n := cutArgs[0]!
    let hbox := mkAppN (mkConst ``source_cutoff_box) cutArgs[:3].toArray
    let hcell := mkAppN (mkConst (ns ++ `observation_cell)) fixed
    let two ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 2
    let hsharp := mkAppN
      (mkConst `JanetCartan.PhysicalSampling.OriginalMeasuredSupport.physical_support_in_original_sharp_ball)
      (fixed ++ #[source[34]!,two])
    let q := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 0 source[34]!)
    let l := Expr.proj ``Sigma 1 source[34]!
    progress "original derivative G: original row projected"
    let hroot := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.root_mem)
      (fixed ++ #[q,l])
    let bandArgs := #[fixed[0]!,fixed[2]!,fixed[1]!,q,l,current.cell,hroot]
    let hA := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalChoices.Band.ha_radius) bandArgs
    let shiftedProof ← knownArgument known `hshift
    let shifted ← namedArguments
      `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.shifted_source_product
      (← bodyAtOpaque shiftedProof.getAppFn.constName! shiftedProof.getAppArgs)
    let hparent ← knownArgument shifted `hparent
    let parentType ← inferType hparent
    unless parentType.isAppOfArity ``LE.le 4 do
      throwError "original derivative: retained parent is not its literal set order: {parentType.getAppFn}"
    let fromBall := parentType.getAppArgs[2]!
    let toBall := parentType.getAppArgs[3]!
    unless fromBall.isAppOf ``Metric.closedBall && toBall.isAppOf ``Metric.ball do
      throwError "original derivative: retained parent balls changed"
    let fromCenter := fromBall.getAppArgs[fromBall.getAppArgs.size-2]!
    let toCenter := toBall.getAppArgs[toBall.getAppArgs.size-2]!
    let ηRoot := fromCenter.appArg!.appArg!
    let ηCell := toCenter.appArg!.appArg!
    let a := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalChoices.Band.a) bandArgs
    let hψX := mkAppN (mkConst ``observation_support_in_selected_cell)
      #[n,ψ,a,← knownArgument shifted `ρ,← knownArgument shifted `σ,
        ← knownArgument shifted `zRoot,← knownArgument shifted `zCell,ηRoot,ηCell,
        hsharp,hA,← knownArgument shifted `hρ,hparent]
    progress "original derivative G: observation cell support assembled"
    let cellType ← inferType hcell
    unless cellType.isAppOfArity ``LT.lt 4 do
      throwError "original derivative: original observation-cell bound changed"
    let b := cellType.getAppArgs[2]!
    let constructor := #[n,← knownArgument known `N,← knownArgument known `J,X,
      ← knownArgument known `hX,W,f,hW,hf,phase,hphase,ψ,hψ,hψX,b,hcell,hbox]
    progress "original derivative G: exact native constructor assembled"
    let G ← store (ns ++ `Whole.G) params
      (mkAppN (mkConst ``nativePeriodicDerivative) constructor) true
    progress "original derivative G: inner map stored"
    withLocalDeclNoLocalInstanceUpdate `zTorus .default
        (mkApp (mkConst `JanetCartan.Torus) n) fun zTorus => do
      let proof := mkAppN (mkConst ``nativePeriodicDerivative_apply)
        (constructor ++ #[v,zTorus])
      let center := mkAppN (mkConst ``AmplitudeBound.centeredTorusRepresentative) #[n,zTorus]
      let native ← applyKnownExact (whole ++ `wholeSourceCorrectedDerivative)
        (known.push (`x,center))
      let equality ← inferType proof
      unless equality.isAppOfArity ``Eq 3 do
        throwError "original derivative: native application lost pointwise equality"
      let nativeMap := mkAppN (mkConst ``nativePeriodicDerivative) constructor
      let lhs := equality.getAppArgs[1]!.replace fun e => if e == nativeMap then some G else none
      let rhs := equality.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSMul.hSMul 6 do
        throwError "original derivative: native observation factor changed"
      let rhs := mkAppN rhs.getAppFn (rhs.getAppArgs.set! 5 native)
      let target := mkAppN equality.getAppFn #[equality.getAppArgs[0]!,lhs,rhs]
      discard <| store (ns ++ `Whole.G_native) (all.push zTorus) proof false (some target)
  logInfo "original53/graph42 inner whole-source G constructed from SAME raw linear map and full corrected derivative; original common observation only, no G/response-bound premise"

/-- Restore the actual incidence/spectator factor on every original node.
The inactive branch is exactly zero for the correction alone; it makes no
claim that the independent positive baseline vanishes. -/
elab "construct_original_full_angular_derivative" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative
  let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
  let whole := `JanetCartan.CanonicalAtomRealization
  let info ← getConstInfo (ns ++ `Whole.G)
  let factorInfo ← getConstInfo (wave ++ `Whole.inner_factor)
  let familyCount := declaredForalls factorInfo.type - 1
  nativeTelescope info.type (declaredForalls info.type) fun original _ => do
    progress "original full G: native family opened"
    unless original.size == familyCount + 5 do
      throwError "original full G: changed family/rate/carrier argument order"
    let params := original[:original.size-2].toArray
    let family := params[:familyCount].toArray
    let factor := mkAppN (mkConst (wave ++ `Whole.inner_factor)) family
    let support := mkAppN (mkConst (wave ++ `Whole.inner_factor_support)) family
    withLocalDeclD `node (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
      let a := mkApp factor node
      let innerAt := mkApp support node
      let .forallE _ nonzero membership _ ← whnf (← inferType innerAt)
        | throwError "original full G: missing actual nonzero-factor implication"
      unless !membership.hasLooseBVars && membership.isAppOfArity ``Membership.mem 5 do
        throwError "original full G: changed actual native carrier membership"
      let p := membership.getAppArgs[4]!
      let Gfamily ← withLocalDeclD `ha nonzero fun ha => do
        let hp := mkApp innerAt ha
        mkLambdaFVars #[ha] (mkAppN (mkConst (ns ++ `Whole.G)) (params ++ #[p,hp]))
      let fullName := wave ++ `Whole.full_angular.corrected
      let fullHead := mkAppN (mkConst fullName) (params.push node)
      let .forallE _ input _ _ ← whnf (← inferType fullHead)
        | throwError "original full G: missing SAME native raw input"
      withLocalDeclNoLocalInstanceUpdate `v .default input fun v => do
        let physicalParams := params ++ #[node,v]
        let fullField ← bodyAtOpaque fullName physicalParams
        let fullArgs ← namedArguments (whole ++ `wholeSourceCorrectedWave) fullField
        progress "original full G: literal whole field extracted"
        let n ← knownArgument fullArgs `n
        let hfield := mkAppN (mkConst (wave ++ `Whole.full_angular_factor.corrected)) physicalParams
        let fieldType ← inferType hfield
        unless fieldType.isAppOfArity ``Eq 3 do
          throwError "original full G: missing exact original whole-wave factor identity"
        let scaled := fieldType.getAppArgs[2]!
        unless scaled.isAppOfArity ``HSMul.hSMul 6 do
          throwError "original full G: factor identity no longer scales the whole physical field"
        let bareField := scaled.getAppArgs.back!
        let bareArgs ← namedArguments (whole ++ `wholeSourceCorrectedWave) bareField
        let (fullDerivative,bareDerivative,hfactor) ←
            withLocalDeclD `x (mkApp (mkConst `JanetCartan.Euclidean) n) fun x => do
          let fullD ← applyKnownExact (whole ++ `wholeSourceCorrectedDerivative)
            (fullArgs.push (`x,x))
          let bareD ← applyKnownExact (whole ++ `wholeSourceCorrectedDerivative)
            (bareArgs.push (`x,x))
          let body ← bodyAtOpaque
            (whole ++ `wholeSourceCorrectedDerivative) fullD.getAppArgs
          unless body.isAppOfArity ``HSMul.hSMul 6 do
            throwError "original full G: changed literal native demodulated derivative"
          let phase := body.getAppArgs[4]!
          let proof := mkAppN (mkConst ``whole_derivative_factor)
            #[n,← knownArgument fullArgs `N,a,fullField,bareField,hfield,phase,x]
          return (← mkLambdaFVars #[v,x] fullD,← mkLambdaFVars #[v,x] bareD,
            ← mkLambdaFVars #[v,x] proof)
        progress "original full G: physical derivative factor assembled"
        let torus := mkApp (mkConst `JanetCartan.Torus) n
        let hG ← withLocalDeclD `ha nonzero fun ha => do
          withLocalDeclD `zTorus torus fun zTorus => do
            let hp := mkApp innerAt ha
            let proof := mkAppN (mkConst (ns ++ `Whole.G_native))
              (params ++ #[p,hp,v,zTorus])
            mkLambdaFVars #[ha,v,zTorus] proof
        let ψ := mkAppN (mkConst (ns ++ `observationFunction)) params[:22].toArray
        withLocalDeclD `zTorus torus fun zTorus => do
          let proof := mkAppN (mkConst ``full_derivative_apply)
            #[n,← knownArgument fullArgs `N,← knownArgument fullArgs `J,
              a,Gfamily,ψ,fullDerivative,bareDerivative,hfactor,hG,v,zTorus]
          let equality ← zetaReduce (← inferType proof)
          unless equality.isAppOfArity ``Eq 3 do
            throwError "original full G: malformed pointwise realization"
          let left ← Core.betaReduce (← zetaReduce equality.getAppArgs[1]!)
          let some data := left.find? (fun e => e.isAppOf ``dite)
            | throwError "original full G: missing exact zero-safe native linear map"
          progress "original full G: zero-safe native constructor assembled"
          let G ← store (ns ++ `G) (params.push node) data true
          progress "original full G: map stored"
          let lhs := left.replace fun e => if e == data then some G else none
          let rhs ← Core.betaReduce equality.getAppArgs[2]!
          let target := mkAppN equality.getAppFn #[equality.getAppArgs[0]!,lhs,rhs]
          discard <| store (ns ++ `G_native) (physicalParams.push zTorus)
            proof false (some target)
  logInfo "original53/graph42 full-angular G: actual incidence/spectator mask, SAME entire uncut corrected derivative, zero-safe all original nodes; independent positive baseline unchanged"

end JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate
end
