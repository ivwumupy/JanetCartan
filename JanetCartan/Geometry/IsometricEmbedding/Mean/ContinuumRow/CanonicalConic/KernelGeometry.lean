module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.ConicInverse
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The actual slice geometry for the kernel substitution

The measurable differential is the restriction of the joint differential.
On the supported cone it equals the literal slice derivative, so its absolute
determinant is precisely the Jacobian in `app:ch_background:eq:bg-jacobian`.
This extension supplies the globally measurable fields of `ChartInputs`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Restrict the actual joint derivative to the original integration slice.
This measurable extension agrees with the slice derivative on its smooth
domain (`app:ch_background:eq:bg-jacobian`). -/
def symbolDifferential (p : InputVariables n) : Euclidean n →L[ℝ] Euclidean n :=
  transportDifferentialRestriction (adaptedSliceCoordinates T)
    (fderiv ℝ (transportAveragedGradient (transportPosition T Q)) p)

/-- The same absolute determinant for both the kernel and symbol adapters
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def symbolJacobian (p : InputVariables n) : ℝ := |(symbolDifferential T Q p).det|

/-- Global measurability does not require a global phase extension theorem
(`app:ch_background:eq:bg-jacobian`). -/
theorem symbolDifferential_measurable : Measurable (symbolDifferential T Q) :=
  (transportDifferentialRestriction (adaptedSliceCoordinates T)).continuous.measurable.comp
    (measurable_fderiv ℝ _)

/-- The actual determinant extension is globally measurable (`bg-jacobian`). -/
theorem symbolDeterminant_measurable :
    Measurable (fun p ↦ (symbolDifferential T Q p).det) :=
  NormalComparison.contDiff_normalJacobianDet.continuous.measurable.comp
    (symbolDifferential_measurable T Q)

/-- Original physical positions, spectator, and the volume-preserving slice
coordinates; no initial variable is discarded (`bg-full-complex-amplitude`). -/
def kernelInput (x y : Euclidean n) (v : Euclidean 2) (t : Euclidean n) :
    InputVariables n :=
  ((x, y), (((adaptedSliceCoordinates T).equiv t).1, v),
    ((adaptedSliceCoordinates T).equiv t).2)

/-- Joint smoothness of the fixed insertion (`app:ch_background:eq:bg-Psi`). -/
theorem kernelInput_smooth (x y : Euclidean n) :
    ContDiff ℝ ∞ (fun p : Euclidean 2 × Euclidean n ↦ kernelInput T x y p.1 p.2) :=
  contDiff_const.prodMk
    ((((adaptedSliceCoordinates T).equiv.contDiff.comp contDiff_snd).fst.prodMk
      contDiff_fst).prodMk ((adaptedSliceCoordinates T).equiv.contDiff.comp contDiff_snd).snd)

/-- The kernel domain is the actual supported input cone in Euclidean slice
coordinates (`app:ch_background:eq:bg-Psi`). -/
def kernelDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
    (x y : Euclidean n) (v : Euclidean 2) : Set (Euclidean n) :=
  kernelInput T x y v ⁻¹' symbolInputDomain z₀ ηb r a

/-- The kernel uses the literal physical averaged gradient (`bg-Psi`). -/
def kernelForward (x y : Euclidean n) (v : Euclidean 2) (t : Euclidean n) : Euclidean n :=
  transportAveragedGradient (transportPosition T Q) (kernelInput T x y v t)

/-- The SAME constructed inverse in Euclidean slice coordinates (`bg-Psi`). -/
def kernelInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
    (x y : Euclidean n) (v : Euclidean 2) (k : Euclidean n) : Euclidean n :=
  (adaptedSliceCoordinates T).equiv.symm (symbolInverse T Q z₀ ηb r a ((x, y, k), v))

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}

/-- Slice-domain measurability follows from the open supported cone
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem kernelDomain_open (x y : Euclidean n) (v : Euclidean 2) :
    IsOpen (kernelDomain T z₀ ηb r a x y v) :=
  (symbolInputDomain_open z₀ ηb r a).preimage
    ((kernelInput_smooth T x y).continuous.comp (continuous_const.prodMk continuous_id))

/-- The joint image of the actual slice maps is precisely the constructed
symbol domain, including spectators outside the carrier chart (`bg-Psi`). -/
theorem kernel_image_iff (x y : Euclidean n) (v : Euclidean 2) (k : Euclidean n) :
    k ∈ kernelForward T Q x y v '' kernelDomain T z₀ ηb r a x y v ↔
      ((x, y, k), v) ∈ symbolDomain T Q z₀ ηb r a := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht.1, (adaptedSliceCoordinates T).equiv t, ht.2, rfl⟩
  · rintro ⟨hp, u, hu, he⟩
    refine ⟨(adaptedSliceCoordinates T).equiv.symm u, ?_, ?_⟩
    · change ((x, y), (((adaptedSliceCoordinates T).equiv
          ((adaptedSliceCoordinates T).equiv.symm u)).1, v),
          ((adaptedSliceCoordinates T).equiv ((adaptedSliceCoordinates T).equiv.symm u)).2) ∈
          symbolInputDomain z₀ ηb r a
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨hp, hu⟩
    · apply (adaptedSliceCoordinates T).equiv.injective
      simp only [kernelForward, kernelInput, ContinuousLinearEquiv.apply_symm_apply]
      exact he

variable (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))

include hηb hr hf in
/-- On the actual cone, the measurable determinant is the literal physical
Jacobian required by the global carrier producer (`bg-jacobian`). -/
theorem symbolJacobian_eq_actual :
    EqOn (symbolJacobian T Q)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q))
      (symbolInputDomain z₀ ηb r a) := by
  intro p hp
  have hd := ((transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).contDiffAt
    ((symbolInputDomain_open z₀ ηb r a).mem_nhds hp)).differentiableAt (by simp)
  exact congrArg (fun D : Euclidean n →L[ℝ] Euclidean n ↦ |D.det|)
    (transportSliceDifferential_eq_restriction (adaptedSliceCoordinates T) _ hd).symm

include hηb hr hf in
/-- The original slice map has the claimed derivative on its actual domain
(`app:ch_background:eq:bg-Psi`). -/
theorem kernelForward_hasFDerivAt (x y : Euclidean n) (v : Euclidean 2)
    {t : Euclidean n} (ht : t ∈ kernelDomain T z₀ ηb r a x y v) :
    HasFDerivAt (kernelForward T Q x y v)
      (symbolDifferential T Q (kernelInput T x y v t)) t := by
  have hd := ((transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).contDiffAt
    ((symbolInputDomain_open z₀ ηb r a).mem_nhds ht)).differentiableAt (by simp)
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

include hηb hr hInv htrans in
/-- Left inversion is deduced from the actual augmented inverse identity
(`app:ch_background:eq:bg-Psi`). -/
theorem kernelInverse_forward (x y : Euclidean n) (v : Euclidean 2)
    {t : Euclidean n} (ht : t ∈ kernelDomain T z₀ ηb r a x y v) :
    kernelInverse T Q z₀ ηb r a x y v (kernelForward T Q x y v t) = t := by
  have he := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans ht
  have hs := congrArg (fun p : InputVariables n ↦ (p.2.1.1, p.2.2)) he
  apply (adaptedSliceCoordinates T).equiv.injective
  simpa only [kernelInverse, kernelForward, kernelInput, inverseCoordinates,
    augmentedTransportGradient, ContinuousLinearEquiv.apply_symm_apply] using hs

include hηb hr hInv htrans in
/-- Injectivity on the whole actual kernel cone (`app:ch_background:eq:bg-Psi`). -/
theorem kernelForward_injective (x y : Euclidean n) (v : Euclidean 2) :
    InjOn (kernelForward T Q x y v) (kernelDomain T z₀ ηb r a x y v) := by
  intro t ht u hu he
  rw [← kernelInverse_forward T Q hηb hr hInv htrans x y v ht,
    ← kernelInverse_forward T Q hηb hr hInv htrans x y v hu, he]

include hηb hr hInv htrans in
/-- Global measurability of the SAME kernel inverse (`bg-full-complex-amplitude`). -/
theorem kernelInverse_measurable (hV : IsOpen V) (hLV : L ⊆ V) (x y : Euclidean n) :
    Measurable (fun p : Euclidean 2 × Euclidean n ↦
      kernelInverse T Q z₀ ηb r a x y p.1 p.2) :=
  (adaptedSliceCoordinates T).equiv.symm.continuous.measurable.comp
    ((symbolInverse_measurable T Q hηb hr hInv htrans hV hLV).comp
      ((measurable_const.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_fst))

include hηb hr hInv htrans in
/-- Measurability of the actual spectator/frequency image (`bg-full-complex-amplitude`). -/
theorem kernelImage_measurable (hV : IsOpen V) (hLV : L ⊆ V) (x y : Euclidean n) :
    MeasurableSet {p : Euclidean 2 × Euclidean n |
      p.2 ∈ kernelForward T Q x y p.1 '' kernelDomain T z₀ ηb r a x y p.1} := by
  simp_rw [kernel_image_iff]
  exact ((symbolDomain_open T Q hηb hr hInv htrans hV hLV).preimage
    ((continuous_const.prodMk (continuous_const.prodMk continuous_snd)).prodMk
      continuous_fst)).measurableSet

end JanetCartan.ContinuumRow.CanonicalConic
