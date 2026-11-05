module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Realization
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives.Estimates

/-!
# Scalar Sobolev gain for the image-normal remainder

For `app:ch_background:prop:bg-frame`, Step 1, a smooth compact kernel maps
all of scalar L² to H¹. Its actual output derivative kernels give bounded
L² representatives of the weak derivatives. Swapping the spatial arguments
proves the same assertion for the Hilbert adjoint, without symmetry.
The consumer is the vector assembly of `localizedImageNormalRemainderOperator`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private def scalarKernelOutputDerivative (K : E × E → ℂ) (i : Fin d) : E × E → ℂ :=
  fun p ↦ fderiv ℝ K p (EuclideanSpace.basisFun (Fin d) ℝ i, 0)

private theorem continuous_scalarKernelOutputDerivative (K : E × E → ℂ)
    (hK : ContDiff ℝ ∞ K) (i : Fin d) : Continuous (scalarKernelOutputDerivative K i) :=
  (hK.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem compactSupport_scalarKernelOutputDerivative (K : E × E → ℂ)
    (hs : HasCompactSupport K) (i : Fin d) :
    HasCompactSupport (scalarKernelOutputDerivative K i) :=
  hs.fderiv_apply ℝ _

private theorem scalarKernelOutputDerivative_section (K : E × E → ℂ)
    (hK : ContDiff ℝ ∞ K) (i : Fin d) (x y : E) :
    fderiv ℝ (fun z ↦ K (z, y)) x (EuclideanSpace.basisFun (Fin d) ℝ i) =
      scalarKernelOutputDerivative K i (x, y) := by
  have h := ((hK.differentiable (by simp) (x, y)).hasFDerivAt.comp (f := fun z : E ↦ (z, y)) x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))).fderiv
  exact congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.basisFun (Fin d) ℝ i)) h

private theorem integrable_scalarKernel_schwartz_pairing (K : E × E → ℂ)
    (hc : Continuous K) (hs : HasCompactSupport K) (f : L²) (φ : 𝓢(E, ℂ)) :
    Integrable (fun p : E × E ↦ φ p.1 * K p * f p.2) (volume.prod volume) := by
  have hi := integrable_compactKernel_L2_pairing
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (t := fun x y ↦ star (K (x, y))) hc.star
    (hs.comp_left (star_zero ℂ)) (φ : L²) (star f)
  apply hi.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (φ.coeFn_toLp 2 volume),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_star f)] with p hp hq
  dsimp only [Function.comp_def] at hp hq
  simp only [hp, hq, Pi.star_apply, star_star]
  ring

private theorem scalarKernel_weak_outputDerivative (K : E × E → ℂ)
    (hK : ContDiff ℝ ∞ K) (hs : HasCompactSupport K)
    (f : L²) (φ : 𝓢(E, ℂ)) (i : Fin d) :
    (∫ x, fderiv ℝ φ x (EuclideanSpace.basisFun (Fin d) ℝ i) *
      (∫ y, K (x, y) * f y)) =
      -(∫ x, φ x * (∫ y, scalarKernelOutputDerivative K i (x, y) * f y)) := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ i
  have hi := integrable_scalarKernel_schwartz_pairing K hK.continuous hs f
    (LineDeriv.lineDerivOp v φ)
  have hid := integrable_scalarKernel_schwartz_pairing (scalarKernelOutputDerivative K i)
    (continuous_scalarKernelOutputDerivative K hK i)
    (compactSupport_scalarKernelOutputDerivative K hs i) f φ
  have hparts (y : E) :
      (∫ x, fderiv ℝ φ x v * K (x, y)) =
        -(∫ x, φ x * scalarKernelOutputDerivative K i (x, y)) := by
    have hsection : ContDiff ℝ ∞ (fun x ↦ K (x, y)) :=
      hK.comp (contDiff_id.prodMk contDiff_const)
    have hssection : HasCompactSupport (fun x ↦ K (x, y)) := by
      apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
      intro x hx
      exact ⟨(x, y), subset_tsupport K hx, rfl⟩
    let ψ : 𝓢(E, ℂ) := hssection.toSchwartzMap hsection
    have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) φ ψ v
    change (∫ x, φ x * fderiv ℝ (fun z ↦ K (z, y)) x v) =
      -(∫ x, fderiv ℝ φ x v * K (x, y)) at h
    simpa only [neg_neg, v, scalarKernelOutputDerivative_section K hK] using
      congrArg Neg.neg h.symm

  calc
    _ = ∫ x, ∫ y, (fderiv ℝ φ x v * K (x, y)) * f y := by
      simp only [← integral_const_mul, mul_assoc, v]
    _ = ∫ y, ∫ x, (fderiv ℝ φ x v * K (x, y)) * f y := by
      exact integral_integral_swap hi
    _ = -(∫ y, ∫ x, (φ x * scalarKernelOutputDerivative K i (x, y)) * f y) := by
      simp_rw [integral_mul_const, hparts, neg_mul, integral_neg]
    _ = -(∫ x, ∫ y, (φ x * scalarKernelOutputDerivative K i (x, y)) * f y) :=
      congrArg Neg.neg (integral_integral_swap hid).symm
    _ = _ := by simp only [← integral_const_mul, mul_assoc]

private theorem scalarKernel_hasCoordinateDerivative (K : E × E → ℂ)
    (hK : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) (f : L²) (i : Fin d) :
    HasEuclideanL2CoordinateDerivative i
      (compactKernelOperator (μ := volume) (ν := volume)
        (t := fun x y ↦ K (x, y)) hK.continuous hs f)
      (compactKernelOperator (μ := volume) (ν := volume)
        (t := fun x y ↦ scalarKernelOutputDerivative K i (x, y))
        (continuous_scalarKernelOutputDerivative K hK i)
        (compactSupport_scalarKernelOutputDerivative K hs i) f) := by
  have hu := compactKernelOperator_ae_integral (μ := volume) (ν := volume)
    (t := fun x y ↦ K (x, y)) hK.continuous hs f
  have hv := compactKernelOperator_ae_integral (μ := volume) (ν := volume)
    (t := fun x y ↦ scalarKernelOutputDerivative K i (x, y))
    (continuous_scalarKernelOutputDerivative K hK i)
    (compactSupport_scalarKernelOutputDerivative K hs i) f
  unfold HasEuclideanL2CoordinateDerivative euclideanCoordinateDerivative
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  rw [integral_congr_ae (show
    (fun x ↦ fderiv ℝ φ x (EuclideanSpace.basisFun (Fin d) ℝ i) *
      compactKernelOperator (μ := volume) (ν := volume)
        (t := fun x y ↦ K (x, y)) hK.continuous hs f x) =ᵐ[volume] _ from
      hu.mono (fun x hx ↦ congrArg
        (fun z ↦ fderiv ℝ φ x (EuclideanSpace.basisFun (Fin d) ℝ i) * z) hx))]
  rw [integral_congr_ae (show
    (fun x ↦ φ x * compactKernelOperator (μ := volume) (ν := volume)
      (t := fun x y ↦ scalarKernelOutputDerivative K i (x, y))
      (continuous_scalarKernelOutputDerivative K hK i)
      (compactSupport_scalarKernelOutputDerivative K hs i) f x) =ᵐ[volume] _ from
      hv.mono (fun x hx ↦ congrArg (fun z ↦ φ x * z) hx))]
  exact neg_eq_iff_eq_neg.mpr (scalarKernel_weak_outputDerivative K hK hs f φ i)

private theorem scalarCompactKernel_sobolev_bound (K : E × E → ℂ)
    (hK : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 (compactKernelOperator (μ := volume) (ν := volume)
        (t := fun x y ↦ K (x, y)) hK.continuous hs f) ∧
      fourierSobolevNorm 1 (compactKernelOperator (μ := volume) (ν := volume)
        (t := fun x y ↦ K (x, y)) hK.continuous hs f) ≤ C * ‖f‖ := by
  let T : L² →L[ℂ] L² := compactKernelOperator (t := fun x y ↦ K (x, y)) hK.continuous hs
  let D : Fin d → L² →L[ℂ] L² := fun i ↦
    compactKernelOperator (t := fun x y ↦ scalarKernelOutputDerivative K i (x, y))
      (continuous_scalarKernelOutputDerivative K hK i)
      (compactSupport_scalarKernelOutputDerivative K hs i)
  refine ⟨‖T‖ + ∑ i, ‖D i‖, by positivity, ?_⟩
  intro f
  have hd : ∀ i, HasEuclideanL2CoordinateDerivative i (T f) (D i f) :=
    scalarKernel_hasCoordinateDerivative K hK hs f
  have hm := (memFourierSobolev_zero (T f)).of_coordinateDerivatives (s := 0)
    le_rfl (fun i ↦ memFourierSobolev_zero (D i f)) hd
  have hn := fourierSobolevNorm_le_coordinateDerivatives (s := 0) le_rfl
    (memFourierSobolev_zero (T f)) (fun i ↦ memFourierSobolev_zero (D i f)) hd
  refine ⟨by simpa only [zero_add] using hm, ?_⟩
  change fourierSobolevNorm 1 (T f) ≤ _
  calc
    _ ≤ ‖T f‖ + ∑ i, ‖D i f‖ := by simpa only [zero_add, fourierSobolevNorm_zero] using hn
    _ ≤ ‖T‖ * ‖f‖ + ∑ i, ‖D i‖ * ‖f‖ :=
      add_le_add (T.le_opNorm f) (Finset.sum_le_sum (fun i _ ↦ (D i).le_opNorm f))
    _ = _ := by rw [add_mul, Finset.sum_mul]

private theorem realCompactKernel_sobolev_bound (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 (imageNormalRealKernelOperator K hK.continuous hs f) ∧
      fourierSobolevNorm 1 (imageNormalRealKernelOperator K hK.continuous hs f) ≤ C * ‖f‖ :=
  scalarCompactKernel_sobolev_bound (fun p ↦ (K p : ℂ))
    (Complex.ofRealCLM.contDiff.comp hK) (hs.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl)

/-- A fixed smooth compact real kernel and its actual Hilbert adjoint both
map every scalar L² input into H¹ with a common finite bound. This supplies
the scalar entries of the smoothing estimate in
`app:ch_background:prop:bg-frame`, Step 1. The first derivative operators are
constructed from the kernel itself; no symmetry or smoothing premise is used. -/
theorem imageNormalRealKernelOperator_sobolev_one_bounds (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (hs : HasCompactSupport K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L²,
      MemFourierSobolev 1 (imageNormalRealKernelOperator K hK.continuous hs f) ∧
      fourierSobolevNorm 1 (imageNormalRealKernelOperator K hK.continuous hs f) ≤ C * ‖f‖ ∧
      MemFourierSobolev 1 ((imageNormalRealKernelOperator K hK.continuous hs).adjoint f) ∧
      fourierSobolevNorm 1 ((imageNormalRealKernelOperator K hK.continuous hs).adjoint f) ≤
        C * ‖f‖ := by
  have hswap : ContDiff ℝ ∞ (fun p : E × E ↦ K (p.2, p.1)) :=
    hK.comp (contDiff_snd.prodMk contDiff_fst)
  have hswapSupport : HasCompactSupport (fun p : E × E ↦ K (p.2, p.1)) :=
    hs.comp_homeomorph (Homeomorph.prodComm E E)
  have hadj : (imageNormalRealKernelOperator K hK.continuous hs).adjoint =
      imageNormalRealKernelOperator (fun p ↦ K (p.2, p.1)) hswap.continuous hswapSupport := by
    ext f : 1
    apply Lp.ext
    have hl := compactKernelOperator_adjoint_ae_integral (μ := volume) (ν := volume)
      (t := fun x y ↦ (K (x, y) : ℂ)) (Complex.continuous_ofReal.comp hK.continuous)
      (hs.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) f
    have hr := compactKernelOperator_ae_integral (μ := volume) (ν := volume)
      (t := fun x y ↦ (K (y, x) : ℂ)) (Complex.continuous_ofReal.comp hswap.continuous)
      (hswapSupport.comp_left (g := fun z : ℝ ↦ (z : ℂ)) rfl) f
    have hl' : (imageNormalRealKernelOperator K hK.continuous hs).adjoint f =ᵐ[volume]
        fun y ↦ ∫ x, (K (x, y) : ℂ) * f x := by
      simpa only [imageNormalRealKernelOperator, Complex.star_def, Complex.conj_ofReal] using hl
    have hr' : imageNormalRealKernelOperator (fun p ↦ K (p.2, p.1))
        hswap.continuous hswapSupport f =ᵐ[volume] fun y ↦ ∫ x, (K (x, y) : ℂ) * f x := hr
    exact hl'.trans hr'.symm
  obtain ⟨C, hC, hforward⟩ := realCompactKernel_sobolev_bound K hK hs
  obtain ⟨D, _, hreverse⟩ :=
    realCompactKernel_sobolev_bound (fun p ↦ K (p.2, p.1)) hswap hswapSupport
  refine ⟨max C D, hC.trans (le_max_left _ _), fun f ↦ ?_⟩
  rw [hadj]
  exact ⟨(hforward f).1,
    (hforward f).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)),
    (hreverse f).1,
    (hreverse f).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f))⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal
