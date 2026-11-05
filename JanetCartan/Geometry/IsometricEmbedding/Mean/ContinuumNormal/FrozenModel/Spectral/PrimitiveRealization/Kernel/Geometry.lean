module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Inverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelGeometry

/-!
# Literal frozen slice geometry

The kernel adapter for `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
uses the zero-scale transport and its literal absolute Jacobian. The measurable
slice differential is extended by zero outside the original input cone. Its
value at the zero-extended inverse still gives the literal Jacobian, because
that Jacobian vanishes at zero frequency.

Sources: `new:lem:scaling`, `app:ch_background:eq:bg-Psi`, and
`app:ch_background:eq:bg-jacobian`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol TransportKernel

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The literal frozen determinant is zero at zero input frequency. This is
also needed outside the inverse image, where the retained inverse is zero
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenKernelJacobian_zero_frequency (hn : 0 < n) (p : InputVariables n)
    (hη : p.2.2 = 0) :
    transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q 0) p = 0 := by
  let c := adaptedSliceCoordinates T
  let Y := normalizedTransportPosition T Q 0
  by_cases hd : DifferentiableAt ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, p.2.2))
  · have hd' : DifferentiableAt ℝ (transportSliceForward c Y p)
        (c.equiv.symm (p.2.1.1, (2 : ℝ) • p.2.2)) := by simpa [hη] using hd
    have hh := transportAbsoluteJacobian_pos_smul c hn Y p (by norm_num : (0 : ℝ) < 2) hd hd'
    have he : scaleInput 2 p = p := by
      change (p.1, p.2.1, 2 • p.2.2) = p
      rw [hη, smul_zero, ← hη]
    rw [he] at hh
    change transportAbsoluteJacobian c Y p = 0
    linarith
  · change |(fderiv ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, p.2.2))).det| = 0
    rw [fderiv_zero_of_not_differentiableAt hd]
    change |LinearMap.det (0 : Euclidean n →ₗ[ℝ] Euclidean n)| = 0
    simp [LinearMap.det_zero, ne_of_gt hn]

/-- The frozen inverse is literally zero off its constructed image
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolInverse_zero_outside {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a : ℝ} {p : Variables n × Euclidean 2}
    (hp : p ∉ frozenSymbolDomain T Q z₀ ηb r a) :
    frozenSymbolInverse T Q z₀ ηb r a p = 0 := by
  change (supportedOutput T Q z₀ ηb r a).indicator
    (localConicInverse T Q z₀ ηb r) (symbolOutputCoordinates T (originOutput p)) = 0
  exact indicator_of_notMem (s := supportedOutput T Q z₀ ηb r a)
    (a := symbolOutputCoordinates T (originOutput p)) hp (localConicInverse T Q z₀ ηb r)

/-- The actual frozen slice map in the volume-preserving kernel coordinates
(`app:ch_background:eq:bg-Psi`). -/
def frozenKernelForward (x y : Euclidean n) (v : Euclidean 2) (t : Euclidean n) : Euclidean n :=
  transportAveragedGradient (normalizedTransportPosition T Q 0) (kernelInput T x y v t)

/-- Only the physical positions are unrestricted in the frozen input cone
(`new:lem:scaling`). -/
def frozenKernelDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
    (x y : Euclidean n) (v : Euclidean 2) : Set (Euclidean n) :=
  kernelInput T x y v ⁻¹' frozenInputDomain z₀ ηb r a

/-- The same frozen inverse in Euclidean integration coordinates
(`app:ch_background:eq:bg-Psi`). -/
def frozenKernelInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
    (x y : Euclidean n) (v : Euclidean 2) (k : Euclidean n) : Euclidean n :=
  (adaptedSliceCoordinates T).equiv.symm (frozenSymbolInverse T Q z₀ ηb r a ((x, y, k), v))

/-- Measurable extension of the actual slice differential on the input cone.
This supplies `ChartInputs.derivative`; no Jacobian is substituted in the
symbol (`app:ch_background:eq:bg-jacobian`). -/
def frozenKernelDifferential (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    InputVariables n → Euclidean n →L[ℝ] Euclidean n :=
  (frozenInputDomain z₀ ηb r a).indicator
    (fun p ↦ transportDifferentialRestriction (adaptedSliceCoordinates T)
      (fderiv ℝ (transportAveragedGradient (normalizedTransportPosition T Q 0)) p))

/-- Global determinant measurability for the literal substitution
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenKernelDeterminant_measurable (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a : ℝ) : Measurable (fun p ↦ (frozenKernelDifferential T Q z₀ ηb r a p).det) :=
  NormalComparison.contDiff_normalJacobianDet.continuous.measurable.comp
    (((transportDifferentialRestriction (adaptedSliceCoordinates T)).continuous.measurable.comp
      (measurable_fderiv ℝ _)).indicator (frozenInputDomain_open z₀ ηb r a).measurableSet)

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}

/-- Openness of the original frozen integration domain (`bg-Psi`). -/
theorem frozenKernelDomain_open (x y : Euclidean n) (v : Euclidean 2) :
    IsOpen (frozenKernelDomain T z₀ ηb r a x y v) :=
  (frozenInputDomain_open z₀ ηb r a).preimage
    ((kernelInput_smooth T x y).continuous.comp (continuous_const.prodMk continuous_id))

variable {c C : ℝ} (hP : P.IsValid c C) (hηb : ηb ≠ 0) (hr : 0 < r)
    (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))

include hP hηb hr har hcarrier hf in
/-- Smoothness of the actual frozen forward map, obtained by restricting the
retained chart to zero physical positions (`new:lem:scaling`, `bg-Psi`). -/
theorem frozenKernelGradient_smooth :
    ContDiffOn ℝ ∞ (transportAveragedGradient (normalizedTransportPosition T Q 0))
      (frozenInputDomain z₀ ηb r a) := by
  apply ((transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).comp
    originInput_smooth.contDiffOn (fun _ hp ↦ hp)).congr
  exact fun _ hp ↦ frozenForward_eq_origin T Q hP hr har hcarrier hp

include hP hηb hr har hcarrier hf in
/-- On the cone the measurable differential has exactly the literal frozen
absolute determinant (`app:ch_background:eq:bg-jacobian`). -/
theorem frozenKernelDifferential_det {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    |(frozenKernelDifferential T Q z₀ ηb r a p).det| =
      transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0) p := by
  have hd := ((frozenKernelGradient_smooth T Q hP hηb hr har hcarrier hf).contDiffAt
    ((frozenInputDomain_open z₀ ηb r a).mem_nhds hp)).differentiableAt (by simp)
  rw [frozenKernelDifferential, indicator_of_mem hp]
  exact congrArg (fun D : Euclidean n →L[ℝ] Euclidean n ↦ |D.det|)
    (transportSliceDifferential_eq_restriction (adaptedSliceCoordinates T) _ hd).symm

include hP hηb hr har hcarrier hf in
/-- The actual frozen slice has the derivative used by the substitution
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenKernelForward_hasFDerivAt (x y : Euclidean n) (v : Euclidean 2)
    {t : Euclidean n} (ht : t ∈ frozenKernelDomain T z₀ ηb r a x y v) :
    HasFDerivAt (frozenKernelForward T Q x y v)
      (frozenKernelDifferential T Q z₀ ηb r a (kernelInput T x y v t)) t := by
  have hd := ((frozenKernelGradient_smooth T Q hP hηb hr har hcarrier hf).contDiffAt
    ((frozenInputDomain_open z₀ ηb r a).mem_nhds ht)).differentiableAt (by simp)
  change kernelInput T x y v t ∈ frozenInputDomain z₀ ηb r a at ht
  rw [frozenKernelDifferential, indicator_of_mem ht]
  exact hd.hasFDerivAt.comp t
    ((hasFDerivAt_const (x, y) t).prodMk
      ((((adaptedSliceCoordinates T).equiv.hasFDerivAt.fst).prodMk
        (hasFDerivAt_const v t)).prodMk (adaptedSliceCoordinates T).equiv.hasFDerivAt.snd))

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hP hηb hr har hcarrier hInv htrans in
/-- The original integration image is exactly the frozen symbol domain
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenKernel_image_iff (x y : Euclidean n) (v : Euclidean 2) (k : Euclidean n) :
    k ∈ frozenKernelForward T Q x y v '' frozenKernelDomain T z₀ ηb r a x y v ↔
      ((x, y, k), v) ∈ frozenSymbolDomain T Q z₀ ηb r a := by
  rw [frozenSymbolDomain_eq_image T Q hP hηb hr har hcarrier hInv htrans]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨kernelInput T x y v t, ht, rfl⟩
  · rintro ⟨p, hp, he⟩
    have hx := congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.1) he
    have hy := congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.1) he
    have hv := congrArg (fun q : Variables n × Euclidean 2 ↦ q.2) he
    have hk := congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) he
    have hin : kernelInput T x y v ((adaptedSliceCoordinates T).equiv.symm (p.2.1.1, p.2.2)) = p := by
      simp only [kernelInput, ContinuousLinearEquiv.apply_symm_apply]
      change p.1.1 = x at hx
      change p.1.2 = y at hy
      change p.2.1.2 = v at hv
      rw [← hx, ← hy, ← hv]
    refine ⟨(adaptedSliceCoordinates T).equiv.symm (p.2.1.1, p.2.2), ?_, ?_⟩
    · change kernelInput T x y v _ ∈ frozenInputDomain z₀ ηb r a
      rwa [hin]
    · change transportAveragedGradient _ (kernelInput T x y v _) = k
      rw [hin]
      exact hk

include hP hηb hr har hcarrier hInv htrans in
/-- Left inversion of the actual frozen slice (`app:ch_background:eq:bg-Psi`). -/
theorem frozenKernelInverse_forward (x y : Euclidean n) (v : Euclidean 2)
    {t : Euclidean n} (ht : t ∈ frozenKernelDomain T z₀ ηb r a x y v) :
    frozenKernelInverse T Q z₀ ηb r a x y v (frozenKernelForward T Q x y v t) = t := by
  have he := frozenInverse_augmentedGradient T Q hP hηb hr har hcarrier hInv htrans ht
  have hs := congrArg (fun p : InputVariables n ↦ (p.2.1.1, p.2.2)) he
  apply (adaptedSliceCoordinates T).equiv.injective
  simpa only [frozenKernelInverse, frozenKernelForward, kernelInput, inverseCoordinates,
    augmentedTransportGradient, ContinuousLinearEquiv.apply_symm_apply] using hs

include hP hηb hr har hcarrier hInv htrans in
/-- Injectivity on the full frozen integration cone (`bg-Psi`). -/
theorem frozenKernelForward_injective (x y : Euclidean n) (v : Euclidean 2) :
    InjOn (frozenKernelForward T Q x y v) (frozenKernelDomain T z₀ ηb r a x y v) := by
  intro t ht u hu he
  rw [← frozenKernelInverse_forward T Q hP hηb hr har hcarrier hInv htrans x y v ht,
    ← frozenKernelInverse_forward T Q hP hηb hr har hcarrier hInv htrans x y v hu, he]

include hηb hr hInv htrans in
/-- Measurability of the retained frozen kernel inverse (`bg-full-complex-amplitude`). -/
theorem frozenKernelInverse_measurable (hV : IsOpen V) (hLV : L ⊆ V) (x y : Euclidean n) :
    Measurable (fun p : Euclidean 2 × Euclidean n ↦
      frozenKernelInverse T Q z₀ ηb r a x y p.1 p.2) :=
  (adaptedSliceCoordinates T).equiv.symm.continuous.measurable.comp
    ((frozenSymbolInverse_measurable T Q hηb hr hInv htrans hV hLV).comp
      ((measurable_const.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_fst))

include hP hηb hr har hcarrier hInv htrans in
/-- Joint image measurability for the frozen substitution (`bg-full-complex-amplitude`). -/
theorem frozenKernelImage_measurable (hV : IsOpen V) (hLV : L ⊆ V) (x y : Euclidean n) :
    MeasurableSet {p : Euclidean 2 × Euclidean n |
      p.2 ∈ frozenKernelForward T Q x y p.1 '' frozenKernelDomain T z₀ ηb r a x y p.1} := by
  simp_rw [frozenKernel_image_iff T Q hP hηb hr har hcarrier hInv htrans]
  exact ((frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV).preimage
    ((continuous_const.prodMk (continuous_const.prodMk continuous_snd)).prodMk
      continuous_fst)).measurableSet

include hP hr har hcarrier in
/-- On the frozen input domain, the actual phase difference is the physical
averaged-gradient phase, with no Fourier conversion inserted
(`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenKernel_input_phase_identity {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    inner ℝ (normalizedTransportPosition T Q 0 (p.1.1, p.2.1)) p.2.2 -
        inner ℝ (normalizedTransportPosition T Q 0 (p.1.2, p.2.1)) p.2.2 =
      inner ℝ (p.1.1 - p.1.2)
        (transportAveragedGradient (normalizedTransportPosition T Q 0) p) := by
  have hz := phaseBuffer_of_frozenInputDomain T hr hP har hcarrier hp
  rw [normalizedTransportPhase_zero T Q hz, normalizedTransportPhase_zero T Q hz,
    transportAveragedGradient_zero T Q p hz, inner_sub_left]

include hP hηb hr har hcarrier hf hInv htrans in
/-- The adapter determinant agrees with the literal Jacobian at every value
of the retained inverse, including its zero extension outside the image.
This supplies `SymbolInputs.jacobian_eq` without replacing the Jacobian
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenKernel_inverse_jacobian (hn : 0 < n) (p : Variables n × Euclidean 2) :
    transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
      (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p) =
    |(frozenKernelDifferential T Q z₀ ηb r a
      (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p)).det| := by
  by_cases hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a
  · exact (frozenKernelDifferential_det T Q hP hηb hr har hcarrier hf
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp)).symm
  · have hi := frozenSymbolInverse_zero_outside T Q hp
    have hη : (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p).2.2 = 0 := by
      simp only [inverseCoordinates, hi, Prod.snd_zero]
    have hnot : inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a) p ∉
        frozenInputDomain z₀ ηb r a := fun h ↦ h.2.2.1 hη
    rw [frozenKernelJacobian_zero_frequency T Q hn _ hη,
      frozenKernelDifferential, indicator_of_notMem hnot]
    change 0 = |LinearMap.det (0 : Euclidean n →ₗ[ℝ] Euclidean n)|
    simp [LinearMap.det_zero, ne_of_gt hn]

end JanetCartan.ContinuumNormal.FrozenModel
