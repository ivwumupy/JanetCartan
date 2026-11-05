module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.LocalComplex
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.FixedSolverReconstruction

/-!
# The reduced L² class belongs to the original smooth response solver

The normalized construction supplies a global almost-everywhere representative
for its smooth solver. Its two original stress admissions combine into exactly
the complex field used by ambient reconstruction. The following identification
does not select another smooth representative or change either source cutoff.
Source: `app:ch_response:eq:response-actual-solver-formula`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal JanetCartan.RegularSector.Realization
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport RegularSector RegularSector.Realization
open CompatibleResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "CF" => EuclideanSpace ℂ (Fin (d + 1))
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Use the normalized inverse's actual global smooth-solver representative
on both original tensor admissions. Their complex sum is the exact L²
observation used by the reduced-envelope proof, on the same domain and with
the same corrected sources. The a.e. input is the global representative
clause of `NormalizedBandInverse/Smooth`, retained by the common initializer
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fixedSmoothSolverComplexSolution_ae_complex_observation
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (η : E → ℝ)
    {sourceSupport U W : Set E} (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : sourceSupport ⊆ U)
    (solver : smoothSource W E →ₗ[ℝ] (E → E))
    (S : H →L[ℂ] H)
    (hS : conjugateOperator S.toLinearMap = S.toLinearMap)
    (Corr : LocalL2 W E →L[ℝ] LocalL2 W E)
    (hsolver : ∀ v : smoothSource W E,
      solver v =ᵐ[volume] realCompression S (zeroExtend hW (Corr v)))
    (tensor : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hre : tensorFieldRealPart tensor ∈ compactSmoothSources sourceSupport)
    (him : tensorFieldImagPart tensor ∈ compactSmoothSources sourceSupport) :
    fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver tensor hre him =ᵐ[volume]
      S (zeroExtend hW
        (l2ComplexInclusion (volume.restrict W)
            (Corr (cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre⟩)) +
          Complex.I • l2ComplexInclusion (volume.restrict W)
            (Corr (cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him⟩)))) := by
  let re := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre⟩
  let im := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him⟩
  rw [zeroExtend_complex_quadratures, realCompression_quadratures S hS]
  change (fun x ↦ euclideanComplexInclusion (solver re x) +
      Complex.I • euclideanComplexInclusion (solver im x)) =ᵐ[volume]
    (l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr re))) +
      Complex.I • l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr im))) : H)
  filter_upwards [hsolver re, hsolver im,
    euclideanComplexInclusion.coeFn_compLpL (realCompression S (zeroExtend hW (Corr re))),
    euclideanComplexInclusion.coeFn_compLpL (realCompression S (zeroExtend hW (Corr im))),
    Lp.coeFn_smul Complex.I
      (l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr im)))),
    Lp.coeFn_add
      (l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr re))))
      (Complex.I • l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr im))))]
    with x hxr hxi hir hii hs ha
  change (l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr re))) : E → CF) x = _ at hir
  change (l2ComplexInclusion volume (realCompression S (zeroExtend hW (Corr im))) : E → CF) x = _ at hii
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, hir, hii, hxr, hxi]

/-- The SAME initialized smooth solution is the literal complex inverse
observation used by `reduced_solution_envelope_of_normalized_real_remainders`.
The real correction identity is supplied by
`SignedProductEstimates.normalized_correctedSource_eq_measured_inverse`, and
the original initializer supplies its `χ₃` plateau. Thus `χ₂` stays inside
the inverse and `χ₃` stays immediately before zero extension, with no change
of the two stress admissions
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem fixedSmoothSolverComplexSolution_ae_complex_neumann_observation
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (η : E → ℝ)
    {sourceSupport U W : Set E} (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : sourceSupport ⊆ U)
    (solver : smoothSource W E →ₗ[ℝ] (E → E))
    (S : H →L[ℂ] H)
    (hS : conjugateOperator S.toLinearMap = S.toLinearMap)
    (R : LocalL2 W CF →L[ℂ] LocalL2 W CF)
    (hR : conjugateOperator R.toLinearMap = R.toLinearMap) (hsmall : ‖R‖ < 1)
    {center : E} (χ₂ χ₃ : ContDiffBump center)
    (Corr : LocalL2 W E →L[ℝ] LocalL2 W E)
    (hCorr : Corr = (neumannInverse (realOutputCompression R)).comp
      (bumpL2 (p := 2) le_rfl χ₂))
    (hfix : ∀ v : LocalL2 W E, bumpL2 (p := 2) le_rfl χ₃ (Corr v) = Corr v)
    (hsolver : ∀ v : smoothSource W E,
      solver v =ᵐ[volume] realCompression S (zeroExtend hW (Corr v)))
    (tensor : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hre : tensorFieldRealPart tensor ∈ compactSmoothSources sourceSupport)
    (him : tensorFieldImagPart tensor ∈ compactSmoothSources sourceSupport) :
    let re := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, hre⟩
    let im := cutoffStressSmoothSource Q η hU hQ hη hSU (W := W) ⟨_, him⟩
    let source : LocalL2 W CF :=
      l2ComplexInclusion (volume.restrict W) (bumpL2 (p := 2) le_rfl χ₂ (re : LocalL2 W E)) +
        Complex.I • l2ComplexInclusion (volume.restrict W)
          (bumpL2 (p := 2) le_rfl χ₂ (im : LocalL2 W E))
    fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver tensor hre him =ᵐ[volume]
      S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (complexNeumannInverse R hsmall source))) := by
  intro re im source
  have hsame : complexNeumannInverse R hsmall source =
      l2ComplexInclusion (volume.restrict W) (Corr re) +
        Complex.I • l2ComplexInclusion (volume.restrict W) (Corr im) := by
    dsimp only [source]
    rw [neumannInverse_quadratures R hR hsmall]
    rw [hCorr]
    rfl
  rw [hsame, bumpL2_complex_quadratures, hfix, hfix]
  exact fixedSmoothSolverComplexSolution_ae_complex_observation
    Q η hU hW hQ hη hSU solver S hS Corr hsolver tensor hre him

end JanetCartan.FixedDomainInverse
