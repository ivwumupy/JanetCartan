module

public import JanetCartan.Iteration.PhysicalMean.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.SmoothRealization

/-!
# The literal fixed-source run on the original smooth auxiliary source space

For `new:eq:mean-operators`, the auxiliary normal is UNCUT.  Only the supplied
sampled wave components carry the one fixed input cutoff.  The original
`Q₀`, full coefficient array, image/source masks, exterior channel, continuum
carriers, sampled row and smooth corrected raw maps are kept literally.

The auxiliary torus is only the existing localized operator realization.  No
physical Schwartz increment is made periodic.  The original inverse producer
must supply `hreg` on these same objects; the corrected atom producer supplies
the literal measured raw action.  Neither is a successful mean-solver premise.
The new run itself and its smoothness are constructed, not assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily ContinuumRow CanonicalChange

variable {n : ℕ} {ι ν m : Type*} [Fintype ι] [Fintype ν] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The fixed sampled complete normal in v2 uses the UNCUT image and exterior
normal, with the same sampled raw row; no Picard-index-dependent cutoff occurs. -/
def uncutSampledNormal
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) (μ : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n) : OutputL2 n →L[ℝ] OutputL2 n :=
  preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ +
    (CanonicalRow.weightedRow μ A).comp (CanonicalRow.weightedRow μ A).adjoint

/-- The one actual canonical derivative map, restricted to smooth real source
representatives, with the same original adjoints and inverse. -/
def fixedSourceDerivative (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) :
    SmoothResidual n →ₗ[ℝ] SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ) :=
  (smoothCanonicalDerivative A G Q₀).comp (smoothResidualToL2 n)

/-- The complete measured Hermitian source polynomial on the actual smooth
source space.  Both quadratures and every lower-order derivative are retained. -/
def fixedSourceQuadratic (μ : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) :
    SmoothResidual n →ₗ[ℝ] SmoothResidual n →ₗ[ℝ] SmoothResidual n :=
  ((tensorBilinear μ).compl₁₂ (fixedSourceDerivative A G Q₀) (fixedSourceDerivative A G Q₀)).compr₂
    (measurementFamily C hC)

/-- The exact same bilinear source as an L²-class action. -/
def fixedSourceQuadraticL2 (μ : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) :
    OutputL2 n →ₗ[ℝ] OutputL2 n →ₗ[ℝ] OutputL2 n :=
  (measuredHermitianBilinear μ C hC).compl₁₂
    (smoothCanonicalDerivative A G Q₀) (smoothCanonicalDerivative A G Q₀)

/-- No norm or final polynomial estimate is needed to identify the two
realizations of the complete quadratic source. -/
theorem fixedSourceQuadratic_toL2 (μ : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u v : SmoothResidual n) :
    smoothResidualToL2 n (fixedSourceQuadratic μ C hC A G Q₀ u v) =
      fixedSourceQuadraticL2 μ C hC A G Q₀ (smoothResidualToL2 n u) (smoothResidualToL2 n v) := rfl

section OriginalInverse

variable (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ν s)
    (μ : ι → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))

/-- `new:eq:mean-operators`: the smooth action of the same uncut-auxiliary
plus fixed-sampled-wave normal, followed by the prescribed inverse. -/
def fixedSourceLinear : SmoothResidual n →ₗ[ℝ] SmoothResidual n :=
  preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg +
    (smoothCanonicalResponse μ A (smoothRawCrossResponse base C hC G) Q₀).comp
      (smoothResidualToL2 n)

/-- The smooth fixed linear source action is literally the original
`uncutSampledNormal ∘ Q₀`.  The only raw action premise belongs to the corrected
atom realization, and no normal comparison or successful source is assumed. -/
theorem fixedSourceLinear_toL2 (hμ : ∀ i, 0 ≤ μ i)
    (hraw : ∀ i v, smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) = A i v)
    (e : SmoothResidual n) :
    smoothResidualToL2 n (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G e) =
      uncutSampledNormal c χmeas χsrc ψ μ A (Q₀ (smoothResidualToL2 n e)) := by
  have haux : smoothResidualToL2 n
      (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) =
      preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ (Q₀ (smoothResidualToL2 n e)) :=
    preparationAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e
  simp only [fixedSourceLinear, LinearMap.add_apply, LinearMap.comp_apply, map_add,
    haux, smoothCanonicalResponse, LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, map_sum, map_smul, hraw,
    uncutSampledNormal, add_apply, ContinuousLinearMap.comp_apply,
    CanonicalRow.weightedRow_normal_apply μ hμ]

/-- `app:ch_mean_pairs:eq:single-iteration`: the actual finite source is a
smooth representative by construction.  Every underlying operator and the
input cutoff encoded in `A,G` is fixed BEFORE the step count. -/
def canonicalSourceIterate (g : SmoothResidual n) (J : ℕ) : SmoothResidual n :=
  sourceIterate (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G)
    (fixedSourceQuadratic μ C hC A G Q₀) g J

/-- The real smooth run and its L² recurrence are the SAME finite source,
including the exterior output.  This supports genuine L² precision estimates
without treating the exterior channel as a physical strain. -/
theorem canonicalSourceIterate_toL2 (hμ : ∀ i, 0 ≤ μ i)
    (hraw : ∀ i v, smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) = A i v)
    (g : SmoothResidual n) (J : ℕ) :
    smoothResidualToL2 n
      (canonicalSourceIterate c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G g J) =
      sourceIterate ((uncutSampledNormal c χmeas χsrc ψ μ A).comp Q₀).toLinearMap
        (fixedSourceQuadraticL2 μ C hC A G Q₀) (smoothResidualToL2 n g) J := by
  change smoothResidualToL2 n
    (sourceIterate (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G)
      (fixedSourceQuadratic μ C hC A G Q₀) g J) = _
  induction J with
  | zero => simp [sourceIterate]
  | succ J ih =>
    simp only [sourceIterate, map_sub, map_add,
      fixedSourceLinear_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G hμ hraw,
      fixedSourceQuadratic_toL2, ih, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]

/-- All source Sobolev levels are genuine memberships of the same constructed
run, not an assumed finite-iteration regularity field.  Their quantitative
profile still requires the original aggregate source estimates. -/
theorem canonicalSourceIterate_mem (g : SmoothResidual n) (J s : ℕ) :
    smoothResidualToL2 n
      (canonicalSourceIterate c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg μ base C hC A G g J) ∈
      (periodicSobolevScale n (Euclidean n)).level s :=
  smoothResidualToL2_mem _ _

end OriginalInverse

end JanetCartan.PhysicalMean
