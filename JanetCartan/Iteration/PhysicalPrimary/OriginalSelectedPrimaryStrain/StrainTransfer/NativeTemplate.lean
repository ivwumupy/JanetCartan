module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.Graph
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.RawSource
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Both actual original source discrepancies control the primary node

The literal native primary supplies its complete raw atom, both compact
tensor quadratures, the same uncut response and the original graph tolerance.
This leaf applies the graph tensor comparison twice, then the exact negative
corrected-atom identity. Its conclusion compares the actual node strain to
the two original smooth source discrepancies; no source decay or response
success is assumed (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate

open CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission

private theorem real_quadrature_eq {n : ℕ}
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    tensorFieldRealPart (quadratureScalar false • H) = tensorFieldRealPart H := by
  simp only [quadratureScalar, Bool.false_eq_true, ite_false, one_smul]

private theorem imaginary_quadrature_eq {n : ℕ}
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    tensorFieldRealPart (quadratureScalar true • H) = tensorFieldImagPart H := by
  ext x i j
  change (-Complex.I * H x i j).re = (H x i j).im
  simp

private theorem source_quadrature_symmetric {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N)) (q : Bool) :
    ∀ x, (tensorFieldRealPart (quadratureScalar q • complexAtomicSource F χ Z) x).IsSymm := by
  intro x
  exact ((complexAtomicSource_isSymm F χ Z x).smul (quadratureScalar q)).map Complex.re

private theorem differentiable_on_original_core {n N : ℕ}
    (χ : ContDiffBump (0 : Euclidean n))
    {X : Set (Euclidean n)} (hX : IsOpen X)
    (hs : tsupport (χ : Euclidean n → ℝ) ⊆ X)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N)) (hZ : ContDiffOn ℝ ∞ Z X)
    {x : Euclidean n} (hx : x ∈ closedBall 0 (χ.rIn / 2)) :
    DifferentiableAt ℝ Z x :=
  (hZ.contDiffAt (hX.mem_nhds (PhysicalPairs.OriginalPacketEquation.inner_subset χ hs
    (PhysicalPairs.OriginalTensorLag.original_inner χ hx)))).differentiableAt (by simp)

private theorem response_differentiable_on_original_core {n N : ℕ} (hn : 5 ≤ n)
    (χ : ContDiffBump (0 : Euclidean n))
    (hcore : closedBall (0 : Euclidean n) (χ.rIn / 2) ⊆
      ball 0 (PhysicalSeed.OriginalBoundary.b hn))
    (V : Euclidean n → Euclidean N)
    (hV : ContDiffOn ℝ ∞ V (ball 0 (PhysicalSeed.OriginalBoundary.R hn)))
    {x : Euclidean n} (hx : x ∈ closedBall 0 (χ.rIn / 2)) :
    DifferentiableAt ℝ V x :=
  (hV.contDiffAt (isOpen_ball.mem_nhds
    (ball_subset_ball (PhysicalSeed.OriginalBoundary.b_lt_R hn).le (hcore hx)))).differentiableAt (by simp)

private theorem from_named_quadrature_errors {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (HR HI : MetricField n)
    (hRe : HR = tensorFieldRealPart (complexAtomicSource F χ Z))
    (hIm : HI = tensorFieldImagPart (complexAtomicSource F χ Z))
    {x : Euclidean n} (hχ : χ x = 1) (hZ : DifferentiableAt ℝ Z x)
    (hR : DifferentiableAt ℝ (B HR) x) (hI : DifferentiableAt ℝ (B HI) x)
    (C εR εI : ℝ)
    (heR : ‖linearizedMetric F (B HR) x - HR x‖ ≤ C * εR)
    (heI : ‖linearizedMetric F (B HI) x - HI x‖ ≤ C * εI) :
    ‖WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B Z) x‖ ≤ C * (εR + εI) := by
  subst HR HI
  exact corrected_atom_strain_le_quadrature_errors F χ B Z hχ hZ hR hI C εR εI heR heI

private theorem strain_bound_of_same_atom {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N)) (hZ : Z = W)
    (x : Euclidean n) (price : ℝ)
    (h : ‖WKB.complexLinearizedMetric F W x‖ ≤ price) :
    ‖WKB.complexLinearizedMetric F Z x‖ ≤ price := by
  simpa only [hZ] using h

private theorem from_named_quadrature_norms {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (HR HI : MetricField n)
    (hRe : HR = tensorFieldRealPart (complexAtomicSource F χ Z))
    (hIm : HI = tensorFieldImagPart (complexAtomicSource F χ Z))
    {x : Euclidean n} (hχ : χ x = 1) (hZ : DifferentiableAt ℝ Z x)
    (hR : DifferentiableAt ℝ (B HR) x) (hI : DifferentiableAt ℝ (B HI) x) :
    ‖WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B Z) x‖ ≤
      ‖linearizedMetric F (B HR) x - HR x‖ +
      ‖linearizedMetric F (B HI) x - HI x‖ := by
  simpa only [one_mul] using
    (from_named_quadrature_errors F χ B Z HR HI hRe hIm hχ hZ hR hI
      1 ‖linearizedMetric F (B HR) x - HR x‖
      ‖linearizedMetric F (B HI) x - HI x‖ (by simp) (by simp))

private theorem combine_quadrature_bounds (L eR eI C εR εI : ℝ)
    (h : L ≤ eR + eI) (hR : eR ≤ C * εR) (hI : eI ≤ C * εI) :
    L ≤ C * (εR + εI) := by
  calc
    L ≤ eR + eI := h
    _ ≤ C * εR + C * εI := add_le_add hR hI
    _ = _ := (mul_add C εR εI).symm

private theorem admitted_tensor_symmetry {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N)) (q : Bool)
    (H : MetricField n)
    (he : H = tensorFieldRealPart (quadratureScalar q • complexAtomicSource F χ Z)) :
    ∀ x, (H x).IsSymm := by
  subst H
  exact source_quadrature_symmetric F χ Z q

private theorem tensor_error_bound_transport {n N : ℕ}
    (F G : Euclidean n → Euclidean N) (hFG : F = G)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (H : MetricField n)
    (f g : Euclidean n → Euclidean n) (hgf : g = f) (x : Euclidean n) (C : ℝ)
    (h : ‖linearizedMetric F (B H) x - H x‖ ≤ C * ‖f x‖) :
    ‖linearizedMetric G (B H) x - H x‖ ≤ C * ‖g x‖ := by
  simpa only [hFG,hgf] using h

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
private def dataRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def response := `JanetCartan.PhysicalSampling.OriginalGraphResponse
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private def termWith (p : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith p code)

private def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "actual primary strain transfer: missing original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

private def withPublishedSource := NativeContext.withSource

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (description : String) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "actual primary strain transfer: unresolved source/geometry/quadrature field {key}"
    let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
    unless missing.isEmpty do throwError "actual primary strain transfer: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual original primary strain transfer {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name description
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary strain transfer: nonstandard axioms {ax}"
  logInfo m!"PASS actual original primary strain transfer {key}/{p.size}: {ax}"

elab "derive_original_native_strain_data " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "native strain data: invalid mode"
  withPublishedSource fun c => do
    let p := c.params
    let node := p[:53].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let input := app (dataRoot ++ `input) p
    let mapper ← mkAppM ``DFunLike.coe
      #[app `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy.tensor_input c.weak]
    let originalInput := mkApp mapper c.tensor
    if mode.getNat == 0 then
      let original := app (response ++ `same_finite_map) c.graph
      let same ← inferType original
      let body ← bodyAt c.tensorField
      let target ← mkEq same.getAppArgs[1]! body.getAppArgs[2]!
      save `native_current_eq node original target
        "The actual original raw source uses the SAME finite current as the full graph response. This is the existing original same_finite_map identity at native53 (main:eq:lag-strain)."
      return
    if mode.getNat == 1 then
      save `native_input_eq p (← mkEqRefl originalInput) (← mkEq input originalInput)
        "The named original source input is exactly the original tensor_input of the SAME named tensor54, with its single source cutoff (main:eq:lag-strain)."
      return
    if mode.getNat == 2 then
      let solver ← mkAppM ``DFunLike.coe
        #[app `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy.discrepancy c.weak]
      let original := mkApp solver originalInput
      let named := app (dataRoot ++ `discrepancy) p
      let inputEq := app (root ++ `native_input_eq) p
      let proof ← mkAppM ``congrArg #[solver,inputEq]
      save `native_discrepancy_eq p proof (← mkEq named original)
        "The named actual smooth discrepancy is the original positive source-minus-identity discrepancy at the SAME tensor input. The original full uncut inverse is retained (main:eq:lag-strain)."
      return
    let fixed := c.weak[:23].toArray
    let chi := app `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂ fixed
    let hSupport := app (masks ++ `χ₂_support_chart) fixed
    let hDb ← mkAppM `JanetCartan.PhysicalPairs.OriginalTensorLag.original_frame_ball
      #[chi,hSupport,app (masks ++ `chart_in_coefficient_ball) fixed]
    forallBoundedTelescope (← inferType hDb) (some 2) fun point _ => do
      unless point.size == 2 do throwError "native strain data: original point/core changed"
      let x := point[0]!
      let hx := point[1]!
      if mode.getNat == 3 then
        let rawField := app `JanetCartan.PhysicalPrimary.OriginalRawSourceField.raw node
        let hRaw := app `JanetCartan.PhysicalPrimary.OriginalRawSourceField.raw_smooth node
        let chart := (← inferType hRaw).getAppArgs.back!
        let proof := app ``differentiable_on_original_core
          #[n,dim,chi,chart,app (masks ++ `chart_open) fixed,hSupport,rawField,hRaw,x,hx]
        save `native_raw_differentiable (node ++ point) proof (← inferType proof)
          "The SAME original actual53 raw primary is differentiable throughout the original closed inner core, using its already checked source-chart smoothness (main:eq:lag-strain)."
      else
        let B := app (response ++ `B) c.graph
        let hB := app (response ++ `smoothOn) (c.graph.push c.tensor)
        let value ← mkAppM ``Subtype.val #[c.tensor]
        let BF ← mkAppM ``DFunLike.coe #[B]
        let V := mkApp BF value
        let proof := app ``response_differentiable_on_original_core
          #[n,dim,p[1]!,chi,hDb,V,hB,x,hx]
        save `native_response_differentiable (p ++ point) proof (← inferType proof)
          "The SAME original full uncut response to the named source tensor54 is differentiable on the original closed inner core. The actual graph response smoothness supplies this fact (main:eq:lag-strain)."

elab "derive_original_native_tensor_strain_transfer" : command => liftTermElabM do
  withPublishedSource fun c => do
    let p := c.params
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let sourceBody ← bodyAt c.tensorField
    let a := sourceBody.getAppArgs
    let F := a[2]!
    let graphF := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.F c.weak
    let atFrame ← inferType (app (root ++ `graph_tensor_strain_le_discrepancy) c.graph)
    unless atFrame.isForall do throwError "actual tensor quadrature: original frame slot changed"
    withLocalDeclD `hFrameTolerance atFrame.bindingDomain! fun hGamma => do
      let symmetry := app ``source_quadrature_symmetric #[n,dim,F,a[3]!,a[4]!,p[53]!]
      let bound := app (root ++ `graph_tensor_strain_le_discrepancy)
        (c.graph ++ #[hGamma,c.tensor,symmetry])
      forallBoundedTelescope (← inferType bound) (some 2) fun point target => do
        unless point.size == 2 && target.isAppOfArity ``LE.le 4 do
          throwError "actual tensor quadrature: original point/core bound changed"
        let err := mkApp (app (dataRoot ++ `discrepancy) p) point[0]!
        let eps ← mkAppM ``Norm.norm #[err]
        let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,p[1]!]
        let right ← mkAppM ``HMul.hMul #[C,eps]
        let args := target.getAppArgs
        let left := args[2]!.replace fun e => if e == graphF then some F else none
        let conclusion := mkAppN target.getAppFn ((args.set! 2 left).set! 3 right)
        save `native_tensor_strain_le_discrepancy (p ++ #[hGamma] ++ point)
          (mkAppN bound point) conclusion
          "The original admitted tensor quadrature has full tensor strain bounded by its SAME named smooth source discrepancy. The actual full uncut graph response, tensor symmetry and geometry are supplied internally; the original numerical frame tolerance is explicit. Consumer: native_node_strain_le_discrepancies (main:eq:lag-strain; main:eq:primary-strain)."

elab "derive_original_native_node_tensor_norms" : command => liftTermElabM do
  withPublishedSource fun c => do
    let p := c.params[:53].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let fixed := c.weak[:23].toArray
    let chi := app `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂ fixed
    let sourceBody ← bodyAt c.tensorField
    let sourceArgs := sourceBody.getAppArgs
    let F := sourceArgs[2]!
    let chiFn := sourceArgs[3]!
    let Zraw := sourceArgs[4]!
    let B := app (response ++ `B) c.graph
    let realParams := p.push (mkConst ``Bool.false)
    let imaginaryParams := p.push (mkConst ``Bool.true)
    let tR := app (dataRoot ++ `tensor) realParams
    let tI := app (dataRoot ++ `tensor) imaginaryParams
    let HR ← mkAppM ``Subtype.val #[tR]
    let HI ← mkAppM ``Subtype.val #[tI]
    let hRe := app ``real_quadrature_eq #[n,c.tensorField]
    let hIm := app ``imaginary_quadrature_eq #[n,c.tensorField]
    let hBR := app (response ++ `smoothOn) (c.graph.push tR)
    let hBI := app (response ++ `smoothOn) (c.graph.push tI)
    let hRaw := app (raw ++ `raw_smooth) c.rawSmoothArgs
    let hOpen := app (masks ++ `chart_open) fixed
    let hSupport := app (masks ++ `χ₂_support_chart) fixed
    let hDb ← mkAppM `JanetCartan.PhysicalPairs.OriginalTensorLag.original_frame_ball
      #[chi,hSupport,app (masks ++ `chart_in_coefficient_ball) fixed]
    let rawChart := (← inferType hRaw).getAppArgs.back!
    let identity := app (raw ++ `combined_eq_corrected_raw) c.rawSmoothArgs
    let eq ← inferType identity
    unless eq.isAppOfArity ``Eq 3 && eq.getAppArgs[2]!.isAppOfArity
        `JanetCartan.CorrectedAtoms.complexCorrectedAtom 6 do
      throwError "actual primary tensor norms: literal corrected raw identity changed"
    let Z := app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
    let corrected := eq.getAppArgs[2]!
    forallBoundedTelescope (← inferType hDb) (some 2) fun point _ => do
      unless point.size == 2 do throwError "actual primary tensor norms: original inner core changed"
      let x := point[0]!
      let hx := point[1]!
      let hχ ← termWith [(`chi,chi),(`x,x),(`hx,hx)]
        "chi.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (half_le_self chi.rIn_pos.le) hx)"
      let hZ := app ``differentiable_on_original_core
        #[n,dim,chi,rawChart,hOpen,hSupport,Zraw,hRaw,x,hx]
      let actualBR ← mkAppM ``DFunLike.coe #[B]
      let actualBI := mkApp actualBR HI
      let actualBR := mkApp actualBR HR
      let hR := app ``response_differentiable_on_original_core
        #[n,dim,p[1]!,chi,hDb,actualBR,hBR,x,hx]
      let hI := app ``response_differentiable_on_original_core
        #[n,dim,p[1]!,chi,hDb,actualBI,hBI,x,hx]
      let rawBound := app ``from_named_quadrature_norms
        #[n,dim,F,chiFn,B,Zraw,HR,HI,hRe,hIm,x,hχ,hZ,hR,hI]
      let price := (← inferType rawBound).getAppArgs.back!
      let proof := app ``strain_bound_of_same_atom #[n,dim,F,Z,corrected,identity,x,price,rawBound]
      save `native_node_strain_le_tensor_errors (p ++ point) proof (← inferType proof)
        "The SAME original primary node is bounded by the sum of its two full tensor residual norms. The actual raw identity, both named source quadratures and original raw/response differentiability are instantiated. The corrected-atom residual has its exact negative sign before norm_neg. Consumer: native_node_strain_le_discrepancies (main:eq:lag-strain; main:eq:primary-strain)."

elab "derive_original_native_primary_strain_transfer" : command => liftTermElabM do
  withPublishedSource fun c => do
    let p := c.params[:53].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let realParams := p.push (mkConst ``Bool.false)
    let imaginaryParams := p.push (mkConst ``Bool.true)
    let quadR := app (root ++ `native_tensor_strain_le_discrepancy) realParams
    let quadI := app (root ++ `native_tensor_strain_le_discrepancy) imaginaryParams
    let atFrame ← inferType quadR
    unless atFrame.isForall do throwError "actual primary strain transfer: numerical frame slot changed"
    let triangle := app (root ++ `native_node_strain_le_tensor_errors) p
    withLocalDeclD `hFrameTolerance atFrame.bindingDomain! fun hGamma => do
      forallBoundedTelescope (← inferType triangle) (some 2) fun point target => do
        unless point.size == 2 && target.isAppOfArity ``LE.le 4 do
          throwError "actual primary strain transfer: original point/core changed"
        let args := target.getAppArgs
        let sum := args[3]!
        unless sum.isAppOfArity ``HAdd.hAdd 6 do
          throwError "actual primary strain transfer: the two tensor norm sum changed"
        let errors := sum.getAppArgs
        let errR := mkApp (app (dataRoot ++ `discrepancy) realParams) point[0]!
        let errI := mkApp (app (dataRoot ++ `discrepancy) imaginaryParams) point[0]!
        let epsR ← mkAppM ``Norm.norm #[errR]
        let epsI ← mkAppM ``Norm.norm #[errI]
        let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,p[1]!]
        let proof := app ``combine_quadrature_bounds
          #[args[2]!,errors[4]!,errors[5]!,C,epsR,epsI,mkAppN triangle point,
            mkAppN (mkApp quadR hGamma) point,mkAppN (mkApp quadI hGamma) point]
        save `native_node_strain_le_discrepancies (p ++ #[hGamma] ++ point) proof (← inferType proof)
          "The SAME original native primary node has full complex strain bounded by the sum of its exact real and imaginary smooth source-minus-identity discrepancies, times the dimension-only projected-stress residual constant. After its explicit numerical frame tolerance, the original uncut response, source admission, full tensor equation and negative corrected-atom sign are supplied internally. The actual selected-data application discharges the tolerance separately. No quantitative source decay or response-success premise (main:eq:primary-strain; main:eq:lag-strain)."

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
end
