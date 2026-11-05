module

public import Lean.Elab.Command
public meta import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackgroundTemplate
import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRow
public import JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.CrossProfiles
public meta import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import Lean

import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
import JanetCartan.Iteration.PhysicalMean.OriginalWeightBridge
import Lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
private def actualNS := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def bridge := `JanetCartan.PhysicalMean.OriginalWeightBridge.Original
private partial def applyKnown (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec go (type : Expr) (args : Array Expr) : MetaM Expr := do
    match type.consumeMData with
    | .forallE label domain body bi =>
      let key := label.eraseMacroScopes
      if let some value := (known.find? (fun pair => pair.1 == key)).map Prod.snd then
        go (body.instantiate1 value) (args.push value)
      else if bi == .instImplicit then
        let value ← synthInstance domain
        go (body.instantiate1 value) (args.push value)
      else if bi == .implicit || bi == .strictImplicit then
        let value ← mkFreshExprSyntheticOpaqueMVar domain
        go (body.instantiate1 value) (args.push value)
      else
        throwError "normal bridge: missing explicit argument {key}"
    | _ => instantiateMVars (mkAppN (mkConst name) args)
  go (← getConstInfo name).type #[]
private def eventGeometry (xs : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let some dv := (← getConstInfo (actualNS ++ `D)).value? (allowOpaque := true)
    | throwError "normal bridge: missing D50"
  let dm := (dv.beta xs).headBeta
  unless dm.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60 do
    throwError "normal bridge: lost measured60"
  let m := dm.getAppArgs
  let fixed := m[:46].toArray
  let rates := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalCommonStage.stage_rates)
    (fixed ++ #[m[47]!,m[48]!,m[49]!])
  let h₀ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalCommonThreshold.T₀_ge_one) fixed
  let hT ← mkAppM `le_trans #[h₀,Expr.proj ``And 0 rates]
  let mesh ← mkAppM `JanetCartan.PhysicalSampling.OriginalBareEvent.mesh_bounds #[hT]
  let hw ← mkAppM `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[m[45]!]
  return (hw, Expr.proj ``And 0 mesh, Expr.proj ``And 1 mesh)
private def save (name : Name) (params : Array Expr) (term : Expr) : MetaM Unit := do
   let env ← getEnv
   let missingValue := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
   unless missingValue.isEmpty do
     throwError "normal bridge: missing value producers {missingValue.toList}"
   let target ← inferType term
   let missingType := target.getUsedConstants.filter (fun n => (env.find? n).isNone)
   unless missingType.isEmpty do
     throwError "normal bridge: missing type producers {missingType.toList}"
   let type ← instantiateMVars (← mkForallFVars params target)
   let value ← instantiateMVars (← mkLambdaFVars params term)
   for closed in #[type,value] do
     let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)
     unless missing.isEmpty do
       throwError "normal bridge: missing closed-telescope producers {missing.toList}"
   if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
       value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
     throwError "normal bridge: open generated declaration"
   let nm := `JanetCartan.PhysicalMean.OriginalCanonicalRow ++ name
   addDecl (.thmDecl {name := nm, levelParams := [], type, value}) (forceExpose := true)
   logInfo m!"generated {nm}"
elab "probe_concrete_normal_bridge" : command => liftTermElabM do
  JanetCartan.PhysicalMean.OriginalPeriodicBackgroundTemplate.withActualCanonicalSample
    (fun xs _ξ si _J _fI _hU _hξ => do
      let siArgs := si.getAppArgs
      let ITypeExpr := siArgs[0]!
      let static := ITypeExpr.getAppArgs
      let m := static[0]!
      let fixed := static[1:].toArray
      let w := siArgs[4]!
      let h := siArgs[5]!
      let Uall := siArgs[6]!
      let (hw,hh,hh₁) ← eventGeometry xs
      withLocalDeclNoLocalInstanceUpdate `i .default ITypeExpr fun i => do
        let D0 := mkAppN (mkConst (actualNS ++ `D)) (xs.push i)
        let U_i := mkApp Uall i
        let utype := (← inferType Uall).consumeMData
        let lattice := utype.bindingBody!.bindingDomain!
        let fin3 := mkApp (mkConst ``Fin) (mkNatLit 3)
        let zero ← mkNumeral (mkConst ``Real) 0
        let hUiType ← withLocalDeclNoLocalInstanceUpdate `q .default lattice fun q =>
          withLocalDeclNoLocalInstanceUpdate `c .default fin3 fun c => do
            let u := mkAppN U_i #[q,c]
            let lo ← mkAppM ``LE.le #[zero,u]
            let hi ← mkAppM ``LT.lt #[u,h]
            mkForallFVars #[q,c] (← mkAppM ``And #[lo,hi])
        let hwType ← inferType hw
        let hhType ← inferType hh
        let hh₁Type ← inferType hh₁
        let DType ← inferType D0
        withLocalDeclNoLocalInstanceUpdate `DParam .default DType fun DParam => do
          withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
            withLocalDeclNoLocalInstanceUpdate `hUi .default hUiType fun hUi => do
              withLocalDeclNoLocalInstanceUpdate `hwP .default hwType fun hwP => do
                withLocalDeclNoLocalInstanceUpdate `hhP .default hhType fun hhP => do
                  withLocalDeclNoLocalInstanceUpdate `hh₁P .default hh₁Type fun hh₁P => do
                   let colors ← mkArrow (mkApp (mkConst ``Fin) (mkNatLit 3))
                     (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) fixed[1]!))
                   let point := mkConst `JanetCartan.SeparatedSampling.Point
                   let Ti ← withLocalDeclNoLocalInstanceUpdate `c .default colors fun c => do
                     withLocalDeclNoLocalInstanceUpdate `z .default point fun z => do
                       let pair ← mkAppM ``Prod.mk #[c,z]
                       let v ← mkAppM `JanetCartan.Sampling.refinedKernelPrefix #[DParam,L,pair]
                       mkLambdaFVars #[c,z] v
                   let tTy ← inferType Ti
                   let tBody := tTy.bindingBody!.bindingBody!
                   let E := tBody.getAppArgs[5]!
                   let H := tBody.getAppArgs[8]!
                   let names : Array Name := #[`hn,`pOrder,`εframe,`hεframe,`qext,`hqcenter,`hqradius,`k,`hk,`hkD,`p,`orders,
                     `margin,`extendedMargin,`hmargin,`hextendedMargin,`cap,`hcap,`incidenceCap,`hincidenceCap,`userExtra,`i]
                   let fixedKnown := names.zip (fixed.push i)
                   let wTy ← inferType hwP
                   let W := (wTy.getAppArgs)[2]!
                   let known := fixedKnown ++ #[(`m,m),(`E,E),(`H,H),(`w,w),(`W,W),(`h,h),(`hw,hwP),(`hh,hhP),(`hh₁,hh₁P),
                     (`T,Ti),(`U,U_i),(`hU,hUi)]
                   let proof ← applyKnown (bridge ++ `normal_sample_eq) known
                   let proof ← instantiateMVars proof
                   let pty ← inferType proof
                   unless pty.isAppOfArity ``Eq 3 do throwError "normal bridge: result not equality"
                   save `normal_sample_actual (xs.push i |>.push DParam |>.push L |>.push hUi |>.push hwP |>.push hhP |>.push hh₁P) proof)
probe_concrete_normal_bridge
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.normal_sample_actual

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial Sampling.CorrectedMean

/-- Literal adjoint coordinate of the measured coefficient, with only the fixed
inverse Fourier scalar; its carrier slice is the original one.
Consumer: `fixedSourceQuadratic_low_bound.hAn` and `.haj`. -/
def measuredAdjointSlice {n : ℕ}
    (H : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n))
    (z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ)
    (a : Fin n) (η : Euclidean (n-1)) (x : Euclidean n) : ℂ :=
  star (((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) * H (x,z,ζ + τ • η) a)

/-- Real-linear coordinate map retaining the exact inverse Fourier factor. -/
def measuredCoordinate (n : ℕ) (a : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
    ((((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) •
      PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) a).restrictScalars ℝ)

private theorem measuredCoordinate_norm_le (n : ℕ) (a : Fin n) :
    ‖measuredCoordinate n a‖ ≤ ‖(((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖star (((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) * v a)‖ ≤ _
  rw [norm_star, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v a) (norm_nonneg _)

/-- Joint smoothness of the SAME affine slice. -/
theorem measuredAdjointSlice_contDiff {n : ℕ}
    {H : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n)}
    (hH : ContDiff ℝ ∞ H) (z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ) (a : Fin n) :
    ContDiff ℝ ∞ (Function.uncurry (measuredAdjointSlice H z ζ τ a)) := by
  exact (measuredCoordinate n a).contDiff.comp
    (hH.comp (show ContDiff ℝ ∞ (fun w : Euclidean (n-1) × Euclidean n ↦
      (w.2,z,ζ + τ • w.1)) by fun_prop))

/-- Conjugation and coordinate projection cost no variable scale. -/
theorem measuredAdjointSlice_jets {n rK rpar : ℕ}
    {H : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → EuclideanSpace ℂ (Fin n)}
    (hH : ContDiff ℝ ∞ H) {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    {T : ℝ} (hT : 1 ≤ T) (hr : rK ≤ rpar)
    (hHj : ∀ w j, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * T ^ (j-rpar))
    (z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ)
    (a : Fin n) (η : Euclidean (n-1)) (x : Euclidean n) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (measuredAdjointSlice H z ζ τ a η) x‖ ≤
      ‖(((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ))‖ * D j * T ^ (j-rK) := by
  let f : Euclidean n → EuclideanSpace ℂ (Fin n) := fun y ↦ H (y,z,ζ + τ • η)
  have hf : ContDiff ℝ ∞ f := hH.comp (contDiff_id.prodMk contDiff_const)
  have hfj : ‖iteratedFDeriv ℝ j f x‖ ≤ D j * T ^ (j-rK) :=
    ((norm_iteratedFDeriv_physical_slice_le isOpen_univ hH.contDiffOn
      (mem_univ (x,z,ζ + τ • η)) j).trans (hHj _ j)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hD j))
  have hp := (measuredCoordinate n a).norm_iteratedFDeriv_comp_left
    (x := x) hf.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (measuredAdjointSlice H z ζ τ a η) x‖ ≤ _ at hp
  exact hp.trans ((mul_le_mul (measuredCoordinate_norm_le n a) hfj
    (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))

/-- The measured adjoint coefficient is supported in the SAME physical
measurement; its carrier cutoff need not be compared with the output compact. -/
theorem measuredAdjointSlice_cross_support {n N : ℕ}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (z : Euclidean 3) (ζ : Euclidean (n-1)) (τ : ℝ) (a : Fin n) (η : Euclidean (n-1)) :
    tsupport (measuredAdjointSlice (fun w ↦ CanonicalRowComparison.complexCrossMeasurement
      (C w.1) (B w) (G w)) z ζ τ a η) ⊆ tsupport C := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hc
  have hz : C x = 0 := image_eq_zero_of_notMem_tsupport hc
  apply hx
  simp [measuredAdjointSlice,CanonicalRowComparison.complexCrossMeasurement,hz]

/-- Only the fixed original patch family is summed in the common measured
budget, before the history, sampling window, sample index and band count. -/
def measuredFamilyBudget {ι : Type*} [Fintype ι] (n : ℕ) (D : ι → ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖(((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ))‖ * ∑ i, D i j

theorem measuredFamilyBudget_nonneg {ι : Type*} [Fintype ι] (n : ℕ)
    {D : ι → ℕ → ℝ} (hD : ∀ i j, 0 ≤ D i j) (j : ℕ) :
    0 ≤ measuredFamilyBudget n D j :=
  mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ hD i j))

theorem measuredFamilyBudget_row_le {ι : Type*} [Fintype ι] (n : ℕ)
    {D : ι → ℕ → ℝ} (hD : ∀ i j, 0 ≤ D i j) (i : ι) (j : ℕ) :
    ‖(((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ))‖ * D i j ≤ measuredFamilyBudget n D j := by
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.single_le_sum (fun k _ ↦ hD k j) (Finset.mem_univ i)

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open MeasureTheory Filter
open scoped BigOperators
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open Sampling SamplingKernelBounds RawInputPartition RawInputRealization
open PhysicalSamplingShells Pseudodifferential CanonicalRowComparison

/-- The literal measured annular coordinate of the retained band operator.
Consumer: the SAME `hAn` in `fixedSourceQuadratic_low_bound`. -/
theorem original_annular_coordinate_ae {n : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData P n) (R : ℝ) (p : P)
    (f : Lp ℂ 2 (annularMeasure n R)) (a : Fin n) :
    finiteL2CoordinateIsometry volume (D.operator R p f) a =ᵐ[volume]
      fun x ↦ ∫ η, D.kernel p η x a * f η ∂annularMeasure n R := by
  have hv := (finiteL2CoordinateIsometry_ae_iff volume _ _).mp
    (original_annular_operator_ae_kernel D R p f) a
  refine hv.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  have he := (PiLp.proj 2 (fun _ : Fin n ↦ ℂ) a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
    |>.integral_comp_comm (integrable_original_annular_kernel D R p f x)
  refine he.symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η ↦ by simp only [PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,mul_comm]

/-- The original complex prefix retains both refined shell copies, before any
sample is packed or any outer quadrature weight is inserted. -/
theorem original_prefix_coordinate_ae {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (p : P) (f : RefinedInput n J) (a : Fin n) :
    finiteL2CoordinateIsometry volume (refinedKernelPrefix D L p f) a =ᵐ[volume]
      fun x ↦ ∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
        ∫ η, D.kernel (i.1,p) η x a * f i η ∂annularMeasure n (refinedRadius i) := by
  simp only [refinedKernelPrefix,prefixRow_apply,map_sum,WithLp.ofLp_sum,Finset.sum_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have he := eventuallyEq_sum
    (s := Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L))
    (fun i _ ↦ original_annular_coordinate_ae D (refinedRadius i) (i.1,p) (f i) a)
  filter_upwards [he] with x hx
  simpa only [Finset.sum_apply] using hx

/-- Exact prefixed physical coordinate kernel on the unchanged shell measure. -/
def originalMeasuredShellKernel {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (p : P) (a : Fin n)
    (x : Euclidean n) (u : RefinedIndex J × Euclidean (n-1)) : ℂ :=
  if u.1.1.val < L then D.kernel (u.1.1,p) u.2 x a else 0

/-- Integrability is inherited from the original annular operator, not assumed. -/
theorem integrable_originalMeasuredShellKernel {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (p : P) (a : Fin n)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) (x : Euclidean n) :
    Integrable (fun u ↦ originalMeasuredShellKernel D L p a x u * f u)
      (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  change Integrable _ (Measure.sum (fun i : RefinedIndex J ↦
    (annularMeasure n (refinedRadius i)).map (Prod.mk i)))
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply (measurableEmbedding_prodMk_left i).integrable_map_iff.mpr
  change Integrable (fun η ↦ originalMeasuredShellKernel D L p a x (i,η) * f (i,η))
    (annularMeasure n (refinedRadius i))
  by_cases hi : i.1.val < L
  · let pr := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) a
    have h := pr.integrable_comp (integrable_original_annular_kernel D (refinedRadius i) (i.1,p)
      (annularShellEquiv (n := n) (refinedRadius (J := J)) f i) x)
    apply h.congr
    filter_upwards [annularShellEquiv_ae (n := n) (refinedRadius (J := J)) f i] with η hη
    simp only [pr,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,
      originalMeasuredShellKernel,hi,ite_true,hη,mul_comm]
  · simp only [originalMeasuredShellKernel,hi,ite_false,zero_mul]
    exact integrable_const (0 : ℂ)

/-- The exact shell-space representation of the original measured complex
prefix, with no weight factors or quantitative operator hypotheses. -/
theorem original_native_prefix_coordinate_ae {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (p : P) (a : Fin n)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) :
    finiteL2CoordinateIsometry volume
      (refinedKernelPrefix D L p (annularShellEquiv (n := n) (refinedRadius (J := J)) f)) a =ᵐ[volume]
        fun x ↦ ∫ u, originalMeasuredShellKernel D L p a x u * f u
          ∂annularShellMeasure (n := n) (refinedRadius (J := J)) := by
  refine (original_prefix_coordinate_ae D L p _ a).trans
    (Filter.Eventually.of_forall fun x ↦ ?_)
  symm
  change (∫ u, originalMeasuredShellKernel D L p a x u * f u
    ∂Measure.sum (fun i : RefinedIndex J ↦
      (annularMeasure n (refinedRadius i)).map (Prod.mk i))) = _
  simp only
  rw [integral_sum_measure (integrable_originalMeasuredShellKernel D L p a f x),
    tsum_fintype,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  by_cases hi : i.1.val < L
  · simp only [originalMeasuredShellKernel,hi,ite_true]
    apply integral_congr_ae
    filter_upwards [annularShellEquiv_ae (n := n) (refinedRadius (J := J)) f i] with η hη
    rw [hη]
  · simp only [originalMeasuredShellKernel,hi,ite_false,zero_mul,integral_zero]
/-- The actual sampled component has the same native measured kernel, including
its one fixed inverse Fourier normalization and no outer sample weight. -/
theorem sampledAnnularComponent_ae_originalKernel {ι : Type*} [Fintype ι] {n J p : ℕ}
    (B : ℝ) (ψ : ι → SeparatedSampling.Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → SeparatedSampling.Lattice → SeparatedSampling.Point)
    (D : ι → BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × SeparatedSampling.Point)) n)
    (L : ℕ) (i : SampleIndex p B ψ w h U)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) (a : Fin n) :
    finiteL2CoordinateIsometry volume (sampledAnnularComponent B ψ w h U D L i f) a =ᵐ[volume]
      fun x ↦ ∫ u,
        (((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
          originalMeasuredShellKernel (D i.1) L
            (SeparatedSampling.color p i.2.val.1, SeparatedSampling.node h (U i.1) i.2) a x u) * f u
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)) := by
  let c : ℝ := ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹
  let g := refinedKernelPrefix (D i.1) L
    (SeparatedSampling.color p i.2.val.1, SeparatedSampling.node h (U i.1) i.2)
    (annularShellEquiv (n := n) (refinedRadius (J := J)) f)
  have hbase := original_native_prefix_coordinate_ae (D i.1) L
    (SeparatedSampling.color p i.2.val.1, SeparatedSampling.node h (U i.1) i.2) a f
  have hc := finiteL2Coordinates_apply_ae volume g a
  have hsc := finiteL2Coordinates_apply_ae volume (c • g) a
  have hs := Lp.coeFn_smul c g
  filter_upwards [hbase,hc,hsc,hs] with x hb hc hsc hs
  change (finiteL2CoordinateIsometry volume (c • g) a) x = _
  change (finiteL2CoordinateIsometry volume (c • g) a) x = (c • g) x a at hsc
  change (finiteL2CoordinateIsometry volume g a) x = g x a at hc
  rw [hsc,hs,Pi.smul_apply,PiLp.smul_apply,Complex.real_smul,← hc]
  rw [hb,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by ring

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

open Lean Meta Elab Command
@[expose] public noncomputable section
private theorem actual_cut_factor_zero {n N : ℕ}
    (κ : JanetCartan.Euclidean n × (JanetCartan.Euclidean 3 × JanetCartan.Euclidean (n-1)) → ℝ)
    (F : JanetCartan.Euclidean n × (JanetCartan.Euclidean 3 × JanetCartan.Euclidean (n-1)) →
      Matrix (Fin N) (Fin n) ℂ) :
    ∀ w, κ w = 0 → κ w • F w = 0 := by
  intro w hw
  rw [hw,zero_smul]
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow.MeasuredGenerator
open OriginalBackgroundHermitianTemplate
private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalRow
private def mp := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
private def cp := `JanetCartan.PhysicalMean.OriginalBackgroundMeasurementProfiles
private def app (f : Name) (xs : Array Expr) := mkAppN (mkConst f) xs
private def store (label : Name) (params : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let env ← getEnv
  for e in #[term] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual measured cross missing value {missing.toList}"
  let t ← match target with | some t => pure t | none => inferType term
  let missingTarget := t.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missingTarget.isEmpty do
    throwError "actual measured cross missing target {missingTarget.toList}"
  let type ← instantiateMVars (← mkForallFVars params t)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual measured cross missing closed {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual measured cross open declaration {label}"
  let name := ns ++ label
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual measured {label}/{params.size}"
  return app name params

private def crossExistence (d : ActualRow) : MetaM Expr := do
  let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
  unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData 45 do
    throwError "actual measured cross: changed corrected kernel45"
  let a := raw.getAppArgs
  let static := d.parameters[:44].toArray
  let rowStatic := static.push d.row
  return app `JanetCartan.Sampling.CorrectedMean.exists_carrierCrossCoefficient_budgets_of_measurement_profiles
    #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[31]!,a[32]!,a[33]!,a[34]!,a[35]!,a[36]!,a[37]!,
      d.initial62[28]!,d.initial62[30]!,d.initial62[33]!,d.initial62[36]!,
      app (cp ++ `CM) static,app (cp ++ `CM_nonneg) static,
      app (mp ++ `cutAmplitudeBudget) rowStatic,app (mp ++ `cutAmplitudeBudget_nonneg) rowStatic]

elab "publish_actual_measured_cross_budget " which:num : command => liftTermElabM do
  withActualRow fun d => do
    let ex ← crossExistence d
    let p := d.parameters[:44].toArray.push d.row
    if which.getNat == 0 then
      let D ← mkAppM ``Classical.choose #[ex]
      discard <| store `measuredCrossBudget p D true
    else
      let spec ← mkAppM ``Classical.choose_spec #[ex]
      discard <| store `measuredCrossBudget_nonneg p (mkProj ``And 0 spec)

publish_actual_measured_cross_budget 0
publish_actual_measured_cross_budget 1

private def crossProof (d : ActualRow) (color : Expr) : MetaM Expr := do
  let ex ← crossExistence d
  let spec ← mkAppM ``Classical.choose_spec #[ex]
  let hall := mkProj ``And 1 spec
  let C := d.mean70[37]!
  let f := mkApp (app (mp ++ `cutAmplitude) d.parameters) color
  let τ := mkApp d.native64[61]! color
  let hzero ← mkAppM ``actual_cut_factor_zero #[d.initial62[33]!,mkApp (nativeAmplitude d) τ]
  let jets := mkApp (app (mp ++ `cutAmplitude_jets_global) d.parameters) color
  let jets ← forallBoundedTelescope (← inferType jets) (some 2) fun jw _ =>
    mkLambdaFVars #[jw[1]!,jw[0]!] (mkAppN jets jw)
  return mkAppN hall #[C,app (cp ++ `smooth) d.parameters,f,
    mkApp (app (mp ++ `cutAmplitude_contDiff) d.parameters) color,hzero,
    d.mean70[60]!,d.mean70[61]!,d.mean70[62]!,jets,
    mkApp (app (cp ++ `joint_profile) d.parameters) d.initial62[28]!]

elab "publish_actual_measured_cross_control" : command => liftTermElabM do
  withActualRow fun d => do
    forallBoundedTelescope (← inferType d.native64[61]!) (some 1) fun c _ => do
      discard <| store `measuredCrossControl (d.parameters ++ c) (← crossProof d c[0]!)

publish_actual_measured_cross_control

elab "publish_actual_measured_cross_field " which:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (ns ++ `measuredCrossControl)).type (some 52) fun p _ => do
    let h := app (ns ++ `measuredCrossControl) p
    let hc := mkProj ``And 0 h
    let t ← inferType hc
    unless t.isAppOf ``ContDiff do throwError "actual measured cross lost joint smoothness"
    let H := t.appArg!
    match which.getNat with
    | 0 => discard <| store `measuredCross p H true
    | 1 =>
      let t := t.replace fun e => if e == H then some (app (ns ++ `measuredCross) p) else none
      discard <| store `measuredCross_contDiff p hc false (some t)
    | 2 =>
      let hj := mkProj ``And 1 h
      let tj ← inferType hj
      let tj := tj.replace fun e => if e == H then some (app (ns ++ `measuredCross) p) else none
      discard <| store `measuredCross_jets_global p hj false (some tj)
    | _ => throwError "unknown measured cross field"

publish_actual_measured_cross_field 0
publish_actual_measured_cross_field 1
publish_actual_measured_cross_field 2

elab "publish_actual_measured_amplitude_budget " which:num : command => liftTermElabM do
  withActualRow fun d => do
    let p := d.parameters[:44].toArray
    let n := mkApp (mkConst ``Nat.succ) d.parameters[0]!
    if which.getNat == 0 then
      let B ← mkAppM ``measuredFamilyBudget #[n,app (ns ++ `measuredCrossBudget) p]
      discard <| store `measuredAmplitudeBudget p B true
    else
      let h ← mkAppM ``measuredFamilyBudget_nonneg #[n,app (ns ++ `measuredCrossBudget_nonneg) p]
      discard <| store `measuredAmplitudeBudget_nonneg p h

publish_actual_measured_amplitude_budget 0
publish_actual_measured_amplitude_budget 1
end JanetCartan.PhysicalMean.OriginalCanonicalRow.MeasuredGenerator
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.measuredCrossBudget_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.sampledAnnularComponent_ae_originalKernel
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.measuredAdjointSlice_jets

public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
elab "publish_actual_native_measured_kernel" : command => liftTermElabM do
  OriginalPeriodicBackgroundTemplate.withActualCanonicalSample fun xs ξ _si _J fI _hU _hξ => do
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      let p := xs.push ξ |>.push L
      let name := `JanetCartan.PhysicalMean.OriginalCanonicalRow.An
      let body ← OriginalBackgroundHermitianTemplate.bodyAt name p
      unless body.isAppOfArity ``sampledAnnularComponent 11 do
        throwError "actual measured native kernel: changed sampled component {body.getAppFn} arity{body.getAppNumArgs}"
      let a := body.getAppArgs
      let proof := mkAppN (mkConst ``sampledAnnularComponent_ae_originalKernel [.zero])
        (#[a[0]!,fI] ++ a[1:].toArray)
      let t ← inferType proof
      let named := mkAppN (mkConst name) p
      let t := t.replace fun e => if e == body then some named else none
      let params := xs.push L
      let type ← instantiateMVars (← mkForallFVars params t)
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[proof,t,type,value] do
        let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
        unless missing.isEmpty do throwError "actual measured native kernel missing {missing.toList}"
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "actual measured native kernel retained open proof data"
      let nm := `JanetCartan.PhysicalMean.OriginalCanonicalRow.hAn_originalKernel
      addDecl (.thmDecl {name := nm, levelParams := [],type,value}) (forceExpose := true)
      logInfo "checked SAME selected measured hAn_originalKernel51"
publish_actual_native_measured_kernel
end JanetCartan.PhysicalMean.OriginalCanonicalRow
end
#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.hAn_originalKernel

#print axioms JanetCartan.PhysicalMean.OriginalCanonicalRow.measuredCross_jets_global
