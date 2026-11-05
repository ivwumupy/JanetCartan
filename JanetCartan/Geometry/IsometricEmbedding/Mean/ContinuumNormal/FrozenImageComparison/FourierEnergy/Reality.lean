module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Model
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# Reality of the frozen uncut image channel

The concrete differentiated Bessel factors commute with real projection on
Schwartz inputs. Density gives the same identity for the actual bounded
channel, and taking adjoints proves it for the literal Hilbert adjoint.
Complex inclusion therefore intertwines both real operators with their
complex realizations and preserves the adjoint norm, including in dimension
zero.

These identities supply the reality input to
`norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy` in the frozen image
contribution and real Plancherel step of `paper-v2.tex`,
`app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.PeriodicLocalL2
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => 𝓢(E, ℂ)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 n E
local notation "p" => imageScalarRealProjection
local notation "P" => (SchwartzMap.postcompCLM p : S →L[ℝ] S)
local notation "Q" => (ContinuousLinearMap.comp
  (l2ComplexInclusion (ι := Fin n) (volume : Measure E))
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

private theorem projection_real_smul (c : ℝ) (u : S) :
    P ((c : ℂ) • u) = (c : ℂ) • P u := by
  ext x
  simp [SchwartzMap.postcompCLM_apply, imageScalarRealProjection]

private def uncutSchwartzChannel (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → S) (i : Fin n) : S :=
  ∑ j, ∑ a, (A a i j : ℂ) •
    lineDerivOp (EuclideanSpace.single a (1 : ℝ)) (imageBesselSchwartzCLM (v j))

private theorem uncutSchwartzChannel_toLp
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S) :
    uncutComplexChannel A (imageSchwartzFamilyToLp v) =
      imageSchwartzFamilyToLp (uncutSchwartzChannel A v) := by
  apply (finiteL2CoordinateIsometry volume).injective
  ext i : 1
  simp only [uncutComplexChannel, finiteL2CoordinateIsometry_vectorMatrixL2Operator,
    matrixOperator_apply, imageSchwartzFamilyToLp_coordinates,
    sum_apply, smul_apply, imageDerivativeBesselL2Operator_toLp,
    uncutSchwartzChannel]
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_sum, map_smul]

private theorem projection_uncutSchwartzChannel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → S) :
    (fun i ↦ P (uncutSchwartzChannel A v i)) =
      uncutSchwartzChannel A (fun i ↦ P (v i)) := by
  funext i
  simp only [uncutSchwartzChannel, map_sum, projection_real_smul,
    projection_derivative, projection_bessel]

private theorem projection_family_toLp (v : Fin n → S) :
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

private theorem projection_uncutComplexChannel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : C²) :
    Q (uncutComplexChannel A f) = uncutComplexChannel A (Q f) := by
  refine denseRange_imageSchwartzFamilyToLp.induction_on f ?_ ?_
  · exact isClosed_eq ((Q).continuous.comp (uncutComplexChannel A).continuous)
      ((uncutComplexChannel A).continuous.comp (Q).continuous)
  · intro v
    rw [uncutSchwartzChannel_toLp, projection_family_toLp, projection_family_toLp,
      uncutSchwartzChannel_toLp, projection_uncutSchwartzChannel]

private theorem projection_adjoint (T : C² →L[ℂ] C²)
    (hT : ∀ f, Q (T f) = T (Q f)) (f : C²) :
    Q (T.adjoint f) = T.adjoint (Q f) := by
  have hi : (l2ComplexInclusion (ι := Fin n) (volume : Measure E)).adjoint =
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

/-- The literal real frozen channel intertwines complex inclusion with its
complex realization (`app:ch_background:prop:bg-frame`, frozen image contribution).
This supplies the real-input compatibility for the frozen Fourier energy. -/
theorem uncutRealChannel_complexInclusion
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    l2ComplexInclusion volume (uncutRealChannel A u) =
      uncutComplexChannel A (l2ComplexInclusion volume u) :=
  inclusion_compression _ (projection_uncutComplexChannel A) u

/-- The real adjoint is the compression of the same complex channel's adjoint
(`app:ch_background:prop:bg-frame`, frozen image contribution). This identifies
the operator used by `uncutRealChannel_adjoint_complexInclusion`. -/
theorem uncutRealChannel_adjoint
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (uncutRealChannel A).adjoint = realOutputCompression (uncutComplexChannel A).adjoint := by
  have hi : (l2ComplexInclusion (ι := Fin n) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [uncutRealChannel, realOutputCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictScalars_complex, l2RealPart_adjoint, hi, ContinuousLinearMap.comp_assoc]

/-- Complex inclusion also intertwines the literal real and complex adjoints
(`app:ch_background:prop:bg-frame`, frozen image contribution). The real projection
identity is proved for the concrete channel and passed to its adjoint. -/
theorem uncutRealChannel_adjoint_complexInclusion
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    l2ComplexInclusion volume ((uncutRealChannel A).adjoint u) =
      (uncutComplexChannel A).adjoint (l2ComplexInclusion volume u) := by
  rw [uncutRealChannel_adjoint]
  exact inclusion_compression _
    (projection_adjoint _ (projection_uncutComplexChannel A)) u

/-- The complex and real adjoint norms agree on the actual included real input
(`app:ch_background:prop:bg-frame`, real Plancherel step). This is the reality
input to `norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy`. -/
theorem norm_uncutComplexChannel_adjoint_complexInclusion
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) :
    ‖(uncutComplexChannel A).adjoint (l2ComplexInclusion volume u)‖ =
      ‖(uncutRealChannel A).adjoint u‖ := by
  rw [← uncutRealChannel_adjoint_complexInclusion]
  apply le_antisymm
  · simpa using (l2ComplexInclusion volume).le_of_opNorm_le
      (l2ComplexInclusion_norm_le volume) ((uncutRealChannel A).adjoint u)
  · have h := (l2RealPart volume).le_of_opNorm_le (l2RealPart_norm_le volume)
      (l2ComplexInclusion volume ((uncutRealChannel A).adjoint u))
    simpa only [JanetCartan.RegularSector.Realization.realPart_inclusion, one_mul] using h

end JanetCartan.ContinuumNormal.FrozenImageComparison
