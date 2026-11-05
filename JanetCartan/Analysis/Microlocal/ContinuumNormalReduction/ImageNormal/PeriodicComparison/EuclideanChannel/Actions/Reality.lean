module
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Actions.Complex
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# Reality of the concrete Euclidean channel

The real Bessel projection identity and the real masked coefficients give
reality on Schwartz families, then on all L² inputs by density. Taking
adjoints of this projection identity proves reality of the literal adjoint.
The complex-inclusion identities are consumed by the Schwartz actions and
the transfer of the complex H¹ estimate in
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal JanetCartan.PeriodicLocalL2
namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 d E
local notation "p" => imageScalarRealProjection
local notation "P" => (SchwartzMap.postcompCLM p : S →L[ℝ] S)
local notation "Q" => (ContinuousLinearMap.comp (l2ComplexInclusion (ι := Fin d) (volume : Measure E))
  (l2RealPart (volume : Measure E)))

private theorem projection_toLp (u : S) :
    (p).compLpL 2 (volume : Measure E) (u.toLp 2) = (P u).toLp 2 := by
  apply Lp.ext
  filter_upwards [(p).coeFn_compLpL (u.toLp 2), u.coeFn_toLp 2,
    (P u).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz, SchwartzMap.postcompCLM_apply]

private theorem projection_bessel (u : S) :
    P (imageBesselSchwartzCLM u) = imageBesselSchwartzCLM (P u) := by
  apply SchwartzMap.injective_toLp 2 (volume : Measure E)
  have h := imageBesselL2Operator_realProjection (u.toLp 2)
  rw [imageBesselL2Operator_toLp, projection_toLp, projection_toLp,
    imageBesselL2Operator_toLp] at h
  exact h

private theorem projection_derivative (v : E) (u : S) :
    P (lineDerivOp v u) = lineDerivOp v (P u) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := (p).hasFDerivAt.comp x (u.differentiableAt (x := x)).hasFDerivAt
  exact (congrArg (fun L : E →L[ℝ] ℂ ↦ L v) h.fderiv).symm

private theorem projection_mask (c : E → ℝ) (hc : c.HasTemperateGrowth) (u : S) :
    P (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) u) =
      SchwartzMap.smulLeftCLM ℂ (fun x ↦ (c x : ℂ)) (P u) := by
  have ht : (fun x ↦ (c x : ℂ)).HasTemperateGrowth := by fun_prop
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply ht, imageScalarRealProjection, Complex.mul_re]

private theorem masked_real_temperate (μ c : E → ℝ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (hc : ContDiff ℝ ∞ c) :
    (fun x ↦ μ x * c x).HasTemperateGrowth :=
  hμc.mul_right.hasTemperateGrowth (hμ.mul hc)

variable (A : EuclideanSpace ℝ (Fin d) → Fin d → Matrix (Fin d) (Fin d) ℝ)
  (Z : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
  (χ μ : EuclideanSpace ℝ (Fin d) → ℝ)
  (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
  (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
  (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
  (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)

include hA hZ hχ hχc hμ hμc in
private theorem projection_channel (u : Fin d → S) :
    (fun i ↦ P (channelSchwartz A Z χ μ u i)) =
      channelSchwartz A Z χ μ (fun i ↦ P (u i)) := by
  funext i
  simp only [channelSchwartz, maskedCoefficientSchwartzCLM, ContinuousLinearMap.pi_apply,
    add_apply, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    map_add, map_sum, LineDeriv.lineDerivOpCLM_apply]
  simp only [projection_mask _ (masked_real_temperate μ _ hμ hμc (hA _ _ _)),
    projection_mask _ (masked_real_temperate μ _ hμ hμc (hZ _ _)), projection_derivative,
    projection_bessel, projection_mask χ (hχc.hasTemperateGrowth hχ)]

private theorem projection_family_toLp (v : Fin d → S) :
    Q (imageSchwartzFamilyToLp v) = imageSchwartzFamilyToLp (fun i ↦ P (v i)) := by
  apply Lp.ext
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL
      (l2RealPart volume (imageSchwartzFamilyToLp v)),
    euclideanRealPart.coeFn_compLpL (imageSchwartzFamilyToLp v),
    imageSchwartzFamilyToLp_ae v, imageSchwartzFamilyToLp_ae (fun i ↦ P (v i))]
    with x hx hy hv hp
  change Q (imageSchwartzFamilyToLp v) x = euclideanComplexInclusion _ at hx
  change l2RealPart volume (imageSchwartzFamilyToLp v) x = euclideanRealPart _ at hy
  rw [hx, hy, hv, hp]
  rfl

private theorem projection_channelL2 (f : C²) :
    Q (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f) =
      complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc (Q f) := by
  let T := complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc
  refine denseRange_imageSchwartzFamilyToLp.induction_on f ?_ ?_
  · exact isClosed_eq ((Q).continuous.comp T.continuous)
      (T.continuous.comp (Q).continuous)
  · intro v
    rw [complexEuclideanChannel_toLp, projection_family_toLp, projection_family_toLp,
      complexEuclideanChannel_toLp, projection_channel A Z χ μ hA hZ hχ hχc hμ hμc]

private theorem projection_adjoint (T : C² →L[ℂ] C²)
    (hT : ∀ f, Q (T f) = T (Q f)) (f : C²) :
    Q (T.adjoint f) = T.adjoint (Q f) := by
  have hi : (l2ComplexInclusion (ι := Fin d) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  have hQ : (Q).adjoint = Q := by
    rw [ContinuousLinearMap.adjoint_comp, l2RealPart_adjoint, hi]
  have he : (Q).comp (T.restrictScalars ℝ) = (T.restrictScalars ℝ).comp Q := by
    ext1 g
    exact hT g
  have ha := congrArg (fun L : C² →L[ℝ] C² ↦ L.adjoint) he
  simp only [ContinuousLinearMap.adjoint_comp, hQ, adjoint_restrictScalars_complex] at ha
  exact (DFunLike.congr_fun ha f).symm

private theorem inclusion_compression (T : C² →L[ℂ] C²)
    (hT : ∀ f, Q (T f) = T (Q f)) (f : R²) :
    l2ComplexInclusion volume (realOutputCompression T f) =
      T (l2ComplexInclusion volume f) := by
  change Q (T (l2ComplexInclusion volume f)) = _
  rw [hT]
  change T (l2ComplexInclusion volume (l2RealPart volume (l2ComplexInclusion volume f))) = _
  rw [JanetCartan.RegularSector.Realization.realPart_inclusion]

/-- Complex inclusion intertwines the actual real and complex channels on
every input, for transfer of the complex H¹ estimate
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_complexInclusion (f : R²) :
    l2ComplexInclusion volume (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f) =
      complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc
        (l2ComplexInclusion volume f) :=
  inclusion_compression _ (projection_channelL2 A Z χ μ hA hZ hχ hχc hμ hμc) f

/-- The literal real adjoint also intertwines complex inclusion, as needed
for its Schwartz action (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_adjoint_complexInclusion (f : R²) :
    l2ComplexInclusion volume ((euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint f) =
      (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint
        (l2ComplexInclusion volume f) := by
  rw [euclideanChannel_adjoint]
  exact inclusion_compression _
    (projection_adjoint _ (projection_channelL2 A Z χ μ hA hZ hχ hχc hμ hμc)) f
end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
