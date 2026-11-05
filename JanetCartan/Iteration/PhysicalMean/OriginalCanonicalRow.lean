module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowTemplate
public import JanetCartan.Iteration.PhysicalMean.GroupedInput
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.WideBandIntegral
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightBridge
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BandIdentification
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivative
public meta import Lean

/-!
# Native annular components of the unchanged sampled raw row

Construct the bounded complex component on the literal original disjoint
annular measure, retaining the fixed inverse Fourier scalar. Its real output
is exactly the existing bounded raw component after the original annular
isometry. This supplies the `hArep` interface of
`PhysicalMean.fixedSourceQuadratic_low_bound` without a boundedness or desired
row-equality premise. All sample labels, colors, rates and prefix projections
are those of the supplied original measured family, including zero weights.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition Sampling SamplingKernelBounds SeparatedSampling
open CanonicalRowComparison PhysicalSamplingShells PeriodicLocalL2

variable {ι : Type*} [Fintype ι] {n J p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The existing measured prefix on one sample's SAME native shell input.
The fixed inverse Fourier scalar is explicit and no weight enters the measure
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def sampledAnnularComponent (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ)
    (h : ℝ) (U : ι → Lattice → Point) (D : ι → BandKernelData (Fin J × CP) n)
    (L : ℕ) (i : SampleIndex p B ψ w h U) :
    Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ] Output n :=
  ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
    (refinedKernelPrefix (D i.1) L (color p i.2.val.1, node h (U i.1) i.2)).comp
      (annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fintype ι] in
/-- The actual bounded raw component and its native annular realization agree
on every raw datum, not only on active weights. This is the literal `hArep`
input used in the original quadratic/current estimates; no Fourier scaling of
the physical derivative G occurs. -/
theorem raw_component_eq_sampledAnnularComponent
    (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → Lattice → Point) (D : ι → BandKernelData (Fin J × CP) n)
    (L : ℕ) (i : SampleIndex p B ψ w h U) (v : RefinedInput n J) :
    rawIntegralSampledComponent B ψ w h U
      (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)) i v =
      transferOutputOperator (realQuadratureChannel (sampledAnnularComponent B ψ w h U D L i))
        ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).symm v) := by
  simp only [rawIntegralSampledComponent, periodicSampledComponent, sampledComponent,
    sampledAnnularComponent, transferOutputOperator, realQuadratureChannel_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, map_smul]
  exact smul_comm _ _ _

/-- Reassemble the SAME weighted adjoint column on its original unweighted
native input. The current inverse may be substituted for `q` without changing
this identity; this is the actual-input compatibility used by
`canonicalSourceIterate` and the native weighted adjoint mass estimate. -/
theorem sampled_native_adjoint_input
    (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → Lattice → Point) (D : ι → BandKernelData (Fin J × CP) n) (L : ℕ)
    (q : ContinuumRow.OutputL2 n) :
    (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U) n J).symm
      ((CanonicalRow.weightedRow (sampleWeight B ψ w h U)
        (rawIntegralSampledComponent B ψ w h U
          (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)))).adjoint q) =
      (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • transferOutputOperator
        (realQuadratureChannel ((sampledRefinedRow B ψ w h U D L).comp
          (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U)
            n J).toContinuousLinearEquiv.toContinuousLinearMap))).adjoint q := by
  rw [← sampled_raw_row_native_input]
  let e := nativeInputEquiv (n := n) (J := J) (p := p) B ψ w h U
  change e.symm ((CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U
        (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)))).adjoint q) =
    ((CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U
        (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)))).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap).adjoint q
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, e.adjoint_eq_symm]
  rfl

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped InnerProductSpace
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open SamplingKernelBounds RawInputPartition RawInputRealization Sampling Sampling.MeanNormalBound
open Sampling.ColoredNormalComparison Sampling.ColoredNormalComparison.EuclideanDisintegration
open Pseudodifferential NormalComparison
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n : ℕ}

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Literal annular integrability for the measured native component, used by
its `hAn` realization in `fixedSourceQuadratic_low_bound`. No component norm
or successful operator-action premise is supplied. -/
theorem integrable_original_annular_kernel (D : BandKernelData P n) (R : ℝ) (p : P)
    (f : AnnularL2 n R) (x : Euclidean n) :
    Integrable (fun η ↦ f η • D.kernel p η x) (annularMeasure n R) := by
  have hK : IsCompact (annulus n R) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hc : Continuous (fun η ↦ D.kernel p η x) :=
    D.continuous_kernel.comp (f := fun η : Euclidean (n-1) ↦ ((p,η),x)) (by fun_prop)
  exact memLp_one_iff_integrable.mp ((Lp.memLp f).smul
    (memLp_restrict_compact_column hc hK))

/-- The SAME original annular operator has its complete vector-valued
kernel, on the unchanged Lebesgue annulus. A compact auxiliary frequency
cutoff is used only inside the proof and disappears from both sides. This
closes the annular action input of the actual `hAn` construction; neither a
replacement kernel nor a successful raw-component equality is assumed. -/
theorem original_annular_operator_ae_kernel (D : BandKernelData P n) (R : ℝ) (p : P)
    (f : AnnularL2 n R) :
    D.operator R p f =ᵐ[volume] fun x ↦ ∫ η, f η • D.kernel p η x ∂annularMeasure n R := by
  let χ : ContDiffBump (0 : Euclidean (n-1)) :=
    ⟨|R| + 1, |R| + 2, by linarith [abs_nonneg R], by linarith⟩
  let t : Fin n → Euclidean n → Euclidean (n-1) → ℂ :=
    fun i x η ↦ (χ η : ℂ) * D.kernel p η x i
  have ht (i : Fin n) : Continuous (Function.uncurry (t i)) :=
    (Complex.continuous_ofReal.comp (χ.continuous.comp continuous_snd)).mul
      ((PiLp.continuous_apply 2 _ i).comp
        (D.continuous_kernel.comp
          (f := fun q : Euclidean n × Euclidean (n-1) ↦ ((p,q.2),q.1)) (by fun_prop)))
  have hs (i : Fin n) (x : Euclidean n) (η : Euclidean (n-1))
      (h : (x,η) ∉ D.physicalSupport ×ˢ tsupport χ) : t i x η = 0 := by
    by_cases hx : x ∈ D.physicalSupport
    · have hη : η ∉ tsupport χ := fun hη ↦ h ⟨hx,hη⟩
      simp [t, image_eq_zero_of_notMem_tsupport hη]
    · simp [t, D.kernel_eq_zero p η x hx]
  have hae : ∀ᵐ η ∂annularMeasure n R, χ η = 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_annulus n R)] with η hη
    apply χ.one_of_mem_closedBall
    apply Metric.closedBall_subset_closedBall (show R ≤ χ.rIn by
      dsimp [χ]
      linarith [le_abs_self R]) hη.1
  let hc := fun i ↦ HasCompactSupport.intro
    (D.physicalSupport_compact.prod χ.hasCompactSupport) (fun q hq ↦ hs i q.1 q.2 hq)
  let A := compactVectorKernelOperator (annulus n R) ht hc
  have hA : toSamplingOutput A = D.operator R p := by
    apply ContinuousLinearMap.adjoint.injective
    rw [toSamplingOutput_adjoint]
    ext1 v
    apply Lp.ext
    have hAc : A = kernelSynthesis
        (memLp_compactCoordinateColumn t ht D.physicalSupport_compact χ.hasCompactSupport hs
          (annulus n R)) :=
      compactVectorKernelOperator_eq_synthesis t ht D.physicalSupport_compact χ.hasCompactSupport
        hs (annulus n R)
    change A.adjoint (finiteL2CoordinateIsometry volume v) =ᵐ[annularMeasure n R] _
    rw [hAc]
    filter_upwards [kernelSynthesis_hasAdjointKernel
        (memLp_compactCoordinateColumn t ht D.physicalSupport_compact χ.hasCompactSupport hs
          (annulus n R)) (finiteL2CoordinateIsometry volume v),
      D.operator_hasAdjointKernel R p v, hae] with η ha hb hχ
    have hcolumn : compactCoordinateColumn t ht D.physicalSupport_compact hs η =
        finiteL2CoordinateIsometry volume (D.column p η) := by
      apply PiLp.ext
      intro i
      apply Lp.ext
      filter_upwards [compactCoordinateColumn_coe t ht D.physicalSupport_compact hs η i,
        finiteL2Coordinates_apply_ae volume (D.column p η) i, D.column_coe p η] with x hx hy hz
      refine hx.trans ?_
      change _ = ((finiteL2Coordinates volume (D.column p η)) i) x
      rw [hy,hz]
      simp only [t,hχ,Complex.ofReal_one,one_mul]
    exact ha.trans ((congrArg (fun a ↦ inner ℂ a ((finiteL2CoordinateIsometry volume) v)) hcolumn).trans
      (((finiteL2CoordinateIsometry volume).inner_map_map _ _).trans hb.symm))
  rw [← hA]
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  have h := compactVectorKernelOperator_ae_integral (annulus n R) ht hc f i
  change (finiteL2CoordinateIsometry volume ((finiteL2CoordinateIsometry volume).symm
    (A f))) i =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine h.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  have hi := integrable_original_annular_kernel D R p f x
  have he := (PiLp.proj 2 (fun _ : Fin n ↦ ℂ) i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
    |>.integral_comp_comm hi
  change _ = (∫ η, f η • D.kernel p η x ∂annularMeasure n R) i
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [hae] with η hη
  change (χ η : ℂ) * D.kernel p η x i * f η = f η * D.kernel p η x i
  rw [hη,Complex.ofReal_one,one_mul,mul_comm]

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open Lean Meta Elab Command

private def actualNS := `JanetCartan.PhysicalMean.OriginalCanonicalRow

private def storeOuter (short : Name) (params : Array Expr) (term : Expr) (data : Bool)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with
    | some t => pure t
    | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual outer row {short}: unresolved or extra analytic input"
  let name := actualNS ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked actual outer row {short}: native{params.size}, SAME original outer weights/kernel/extended shift"

private def withOriginalSample
    (k : Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let event := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.exists_on_original_history
  forallBoundedTelescope (← getConstInfo event).type (some 50) fun xs result => do
    unless xs.size == 50 do throwError "actual outer row: native50 changed"
    let some bare := result.find? (·.isAppOfArity `JanetCartan.PhysicalSampling.OriginalScalarFamily.kernel 46)
      | throwError "actual outer row: original scalar46 missing"
    let J := bare.getAppArgs[43]!
    let e ← whnf result
    unless e.isAppOfArity ``Exists 2 do throwError "actual outer row: SAME original shift type missing"
    lambdaTelescope e.getAppArgs[1]! fun ξ body => do
      unless ξ.size == 1 do throwError "actual outer row: changed original shift input"
      let some si := body.find? (·.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7)
        | throwError "actual outer row: original sample index7 missing"
      let some dev := body.find? (·.isAppOfArity `JanetCartan.Sampling.Realization.familyDeviation 17)
        | throwError "actual outer row: original family deviation17 missing"
      let some fI ← dev.getAppArgs.findM? (fun arg => do
        if arg.hasLooseBVars then return false
        return (← inferType arg).isAppOfArity ``Fintype 1)
        | throwError "actual outer row: original finite-index instance missing"
      unless ← isDefEq (← inferType fI).getAppArgs[0]! si.getAppArgs[0]! do
        throwError "actual outer row: different original finite index"
      k xs ξ si.getAppArgs J fI

private def applyOuterKnown (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec options : Expr → Array (Option Expr)
    | .forallE label domain body bi =>
      let key := if domain.isAppOfArity ``Fintype 1 then `originalFintype else label.eraseMacroScopes
      let value := (known.find? (fun p ↦ p.1 == key)).map Prod.snd
      if value.isNone && bi == .default then #[] else #[value] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  mkAppOptM name (options (← getConstInfo name).type)

private def replaceActualRoots (e : Expr) (pairs : Array (Expr × Expr)) : Expr :=
  pairs.foldl (fun a pair ↦ a.replace (fun x ↦ if x == pair.1 then some pair.2 else none)) e

/-- Specialize the checked original native row, not a second sampler. `A` and
`An` are bounded by their explicit existing operator constructions. The physical
sample mask is the original outer χ², the restored carrier factor occurs once
in each component, and the unchanged extended ξ remains an input. Consumers:
`canonicalSourceIterate`, `fixedSourceQuadratic_low_bound`, and
`app:ch_mean_pairs:defn:mean-canonical`. The G/hraw join is a separate proof. -/
elab "construct_actual_outer_canonical_row " which:num : command => liftTermElabM do
  withOriginalSample fun xs ξ sa J fI => do
    let I := sa[0]!
    unless I.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
      throwError "actual outer row: original static22 index missing"
    let fixed := I.getAppArgs
    let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
    let Bo := mkAppN (mkConst (outer ++ `B)) fixed
    let ψo := mkAppN (mkConst (outer ++ `ψ)) fixed
    let w := sa[4]!
    let h := sa[5]!
    let U := sa[6]!
    if which.getNat == 0 then
      let Dout ← withLocalDeclNoLocalInstanceUpdate `i .default I fun i => do
        let Di := mkAppN (mkConst (actualNS ++ `D)) (xs.push i)
        mkLambdaFVars #[i] (mkAppN
          (mkConst `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.scalarKernel)
          (fixed ++ #[i,J,Di]))
      storeOuter `Dout xs Dout true
    else
      let Dout := mkAppN (mkConst (actualNS ++ `Dout)) xs
      let shiftParams := xs ++ ξ
      withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
        let params := shiftParams.push L
        let known := #[(`ι,I),(`J,J),(`p,sa[1]!),(`B,Bo),(`ψ,ψo),(`w,w),(`h,h),
          (`U,U),(`D,Dout),(`L,L),(`originalFintype,fI)]
        let hrow ← applyOuterKnown ``sampled_raw_row_eq known
        let rowType ← inferType hrow
        unless rowType.isAppOfArity ``Eq 3 do throwError "actual outer row: sampled row equality changed"
        let weighted := rowType.getAppArgs[1]!
        unless weighted.getAppFn.isConstOf `JanetCartan.CanonicalRow.weightedRow do
          throwError "actual outer row: original weighted row lost"
        let wa := weighted.getAppArgs
        let μ := wa[wa.size-2]!
        let A := wa.back!
        let An ← applyOuterKnown ``sampledAnnularComponent known
        let hnrow ← applyOuterKnown ``sampled_raw_row_native_input known
        let nrType ← inferType hnrow
        unless nrType.isAppOfArity ``Eq 3 do throwError "actual outer row: native row equality changed"
        let R := nrType.getAppArgs[2]!
        let named (field : Name) := mkAppN (mkConst (actualNS ++ field)) params
        let wNamed := mkAppN (mkConst (actualNS ++ `weights)) shiftParams
        match which.getNat with
        | 1 => storeOuter `A params A true
        | 2 => storeOuter `An params An true
        | 3 =>
          let dt ← whnf (← inferType (mkAppN (mkConst (actualNS ++ `D)) xs))
          unless dt.isForall do throwError "actual outer row: original row family type changed"
          let dbody := dt.bindingBody!
          unless dbody.isAppOfArity `JanetCartan.SamplingKernelBounds.BandKernelData 3 do
            throwError "actual outer row: original band-data type changed"
          let n := dbody.getAppArgs.back!
          let e ← applyOuterKnown ``nativeInputEquiv (known.push (`n,n))
          storeOuter `inputEquiv shiftParams e true
        | 4 => storeOuter `weights shiftParams μ true
        | 5 => storeOuter `R params R true
        | 6 =>
          let target := replaceActualRoots nrType #[(A,named `A),(μ,wNamed),(R,named `R)]
          unless target.getUsedConstants.contains (actualNS ++ `A) &&
              target.getUsedConstants.contains (actualNS ++ `R) do
            throwError "actual outer row: native row did not retain the same A/R"
          storeOuter `hrow_native params hnrow false (some target)
        | 7 =>
          let proof ← applyOuterKnown ``raw_component_eq_sampledAnnularComponent known
          let target := replaceActualRoots (← inferType proof) #[(A,named `A),(An,named `An)]
          unless target.getUsedConstants.contains (actualNS ++ `A) &&
              target.getUsedConstants.contains (actualNS ++ `An) do
            throwError "actual outer row: hArep did not retain the same A/An"
          storeOuter `hArep params proof false (some target)
        | 8 =>
          let proof ← applyOuterKnown ``sampled_native_adjoint_input known
          let target := replaceActualRoots (← inferType proof) #[(A,named `A),(μ,wNamed),(R,named `R)]
          unless target.getUsedConstants.contains (actualNS ++ `A) &&
              target.getUsedConstants.contains (actualNS ++ `R) do
            throwError "actual outer row: adjoint input did not retain the same A/R"
          storeOuter `adjoint_input params proof false (some target)
        | _ => throwError "actual outer row: unknown retained field"

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32000
set_option backward.isDefEq.respectTransparency false

construct_actual_outer_canonical_row 0
construct_actual_outer_canonical_row 1
construct_actual_outer_canonical_row 2
construct_actual_outer_canonical_row 3
construct_actual_outer_canonical_row 4
construct_actual_outer_canonical_row 5
construct_actual_outer_canonical_row 6
construct_actual_outer_canonical_row 7
construct_actual_outer_canonical_row 8

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open Sampling Sampling.RawKernel Sampling.MeanNormalBound SamplingKernelBounds
open RawInputPartition RawPrimary RawPrimary.SliceBounds AmplitudeBound CanonicalRowComparison
variable {n N : ℕ}
local instance : ContinuousENorm (Matrix (Fin N) (Fin n) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin N) (Fin n) ℂ) inferInstance).toContinuousENorm
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] {bands : ℕ}
variable
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (V : P → Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (background : P → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦ S q.1.1 q.1.2 q.2))
    (hV : ∀ p x, Continuous (V p x))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (background q.1.1 q.1.2) (V q.1.1 q.1.2 q.2)))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K → complexCrossMeasurement (C x) (background p x) (V p x η) = 0)
    (M bound : ℝ) (hM : 0 ≤ M) (hbound : 0 ≤ bound)
    (hAM : ∀ p x η, ‖complexCrossMeasurement (C x) (background p x) (V p x η)‖ ≤ M)
    (hdB : ∀ η, ‖d η‖ ≤ bound)
include hV

/-- Independent `hraw` implication for the actual zero-safe full-angular G.
The positive baseline is unchanged even when `a=0`; its original Row64
comparison is required only on the active branch. The actual baseline/Cper
application remains the original parent construction's obligation. The
representation premise is the literal raw integral supplied by `G_native`
and `Whole.derivative_integral`, not a G/A equality. Consumers:
`completeCanonicalCorrection_toL2`, `app:ch_mean_pairs:defn:mean-canonical`. -/
theorem zero_safe_hraw_of_original_integral
    (L : ℕ) (p : P) (a : ℝ)
    (base : CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (G : a ≠ 0 → RefinedInput n bands →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hbackground : a ≠ 0 → ∀ z, Cper z ≠ 0 →
      base.val z () = background p (centeredTorusRepresentative z))
    (hmeasurement : ∀ z, Cper z = C (centeredTorusRepresentative z))
    (hG : ∀ ha v z, Cper z ≠ 0 →
      (G ha v).val z () = rawPrimaryDemodulatedIntegral (S p) (V p) (ζ p) (τ p) volume
        (weightedWideDensity d (widePrefix n bands L ((wideRefinement n bands).symm v)))
        (centeredTorusRepresentative z))
    (v : RefinedInput n bands) :
    let D := bandKernelData (J := bands) S
      (fun p x η ↦ complexCrossMeasurement (C x) (background p x) (V p x η))
      ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
    let _ := Classical.propDecidable
    let Gfull := if ha : a = 0 then
      (0 : RefinedInput n bands →ₗ[ℝ]
        CurrentMean.SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
      else a • G ha
    CurrentMean.smoothResidualToL2 n
      (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
        base Cper hCper (fun _ ↦ Gfull) () v) =
      a • (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
        PeriodicLocalL2.transferOutputOperator (realQuadratureChannel (refinedKernelPrefix D L p)) v) := by
  classical
  dsimp only
  by_cases ha : a = 0
  · simp [ha, CanonicalChange.smoothRawCrossResponse]
  · rw [dite_eq_right ha]
    have h := smoothRawCrossResponse_toL2_eq_rawIntegral_component S V C background ζ τ d
      hS hV hA hζ hτ hτ₀ hd K hK hAK M bound hM hbound hAM hdB
      L p base Cper hCper (G ha) (hbackground ha) hmeasurement (hG ha) v
    calc
      _ = a • CurrentMean.smoothResidualToL2 n
          (CanonicalChange.smoothRawCrossResponse (Raw := fun _ : Unit ↦ RefinedInput n bands)
            base Cper hCper (fun _ ↦ G ha) () v) := by
        simp only [CanonicalChange.smoothRawCrossResponse, LinearMap.smul_apply,
          LinearMap.comp_apply, map_smul]
        exact smul_comm _ _ _
      _ = _ := congrArg (fun w ↦ a • w) h
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

