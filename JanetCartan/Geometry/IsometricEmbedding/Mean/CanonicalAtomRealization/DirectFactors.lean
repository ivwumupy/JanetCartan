module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverJointRegularity
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.SolverRealization

/-!
# The direct solver as the original two physical factors

For `app:ch_response:eq:response-full-map`, `ambientExtension` takes the
source correction and physical solve separately, while `DirectSmooth` also
exports their composite on its all-order local Lebesgue source space. Use its
actual smooth corrected source `Z` and its global a.e. realization of the
same physical operator. The physical solve descends to the image of `Z`:
identical corrected fields give identical L² outputs and hence identical
smooth representatives. The two algebraic extensions are needed only to fill
the ambient API's domain of all coordinate fields. On the original admitted
sources their values are forced by the supplied operators.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open CorrectedAtoms FixedDomainInverse LocalSobolev PrimarySourceAdmission ResponseSourceExtension
open AmbientResponse ResponseSmoothParameters RetardedSobolev.Spaces

/-- Descend a physical factor to its actual source image; only the extension
off that image is algebraic (`app:ch_response:eq:response-full-map`). -/
private def extendSourceFactor {E H G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup H] [Module ℝ H] [AddCommGroup G] [Module ℝ G]
    (j : E →ₗ[ℝ] H) (L : E →ₗ[ℝ] G) (h : j.ker ≤ L.ker) : H →ₗ[ℝ] G :=
  (((j.ker.liftQ L h).comp j.quotKerEquivRange.symm.toLinearMap).exists_extend).choose

/-- The extension retains the literal values of the factor on all original
sources (`app:ch_response:eq:response-full-map`). -/
private theorem extendSourceFactor_apply {E H G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup H] [Module ℝ H] [AddCommGroup G] [Module ℝ G]
    (j : E →ₗ[ℝ] H) (L : E →ₗ[ℝ] G) (h : j.ker ≤ L.ker) (v : E) :
    extendSourceFactor j L h (j v) = L v := by
  let g := (j.ker.liftQ L h).comp j.quotKerEquivRange.symm.toLinearMap
  have he := DFunLike.congr_fun g.exists_extend.choose_spec (j.rangeRestrict v)
  change extendSourceFactor j L h (j v) = g (j.rangeRestrict v) at he
  rw [he]
  change (j.ker.liftQ L h) (j.quotKerEquivRange.symm ⟨j v, _⟩) = L v
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {n : ℕ}

/-- The physical coordinate fields of a Euclidean-valued source. This only
unbundles its components for `AmbientResponse.correctedStressSource`
(`app:ch_response:eq:response-full-map`). -/
private def sourceComponents : (Euclidean n → Euclidean n) →ₗ[ℝ] (Euclidean n → Fin n → ℝ) where
  toFun u x := (u x).ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Realize the original cutoff stress on the direct solver's local Lebesgue
source space, extending its existing admission map only off the image of
admitted stresses (`app:ch_regular:eq:exact-physical`). -/
private def stressAdmissionFactor
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ) {S U W : Set (Euclidean n)}
    (hU : IsOpen U) (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] smoothSource W (Euclidean n) := by
  let raw := ((cutoffSource η).comp (stressSource Q)).comp (compactSmoothSources S).subtype
  let admit := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU
  refine extendSourceFactor raw admit ?_
  intro h hh
  change cutoffSource η (stressSource Q h) = 0 at hh
  change admit h = 0
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q η hU hQ hη hSU h,
    (Lp.coeFn_zero (Euclidean n) 2 (volume.restrict W))] with y hy hz
  change _ = (0 : LocalL2 W (Euclidean n)) y
  rw [hy, hz]
  change WithLp.toLp 2 (cutoffSource η (stressSource Q h) y) = 0
  rw [hh]
  rfl

variable (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ) {S U W : Set (Euclidean n)}
    (hU : IsOpen U) (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (Z : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))

/-- The coordinate-valued source-correction factor of the direct solver.
On admitted tensor sources it is the supplied smooth realization of `Corr`,
with the original source cutoff (`app:ch_response:eq:response-full-map`). -/
def directStressCorrectionFactor : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ) :=
  (sourceComponents.comp Z).comp (stressAdmissionFactor Q η hU hQ hη hSU)

/-- Applying the correction factor after the original stress projection gives
exactly the supplied `Z` on the original local L² class
(`app:ch_response:eq:response-full-map`). -/
theorem correctedStressSource_directStressCorrectionFactor (h : compactSmoothSources S) :
    correctedStressSource Q η (directStressCorrectionFactor Q η hU hQ hη hSU Z) h =
      fun x ↦ (Z (cutoffStressSmoothSource Q η hU hQ hη hSU h) x).ofLp := by
  exact congrArg (fun u ↦ sourceComponents (Z u)) (extendSourceFactor_apply
    (((cutoffSource η).comp (stressSource Q)).comp (compactSmoothSources S).subtype)
    (cutoffStressSmoothSource Q η hU hQ hη hSU) _ h)

variable (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n)) (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hW : MeasurableSet W) (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (Pphys : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ] Lp (Euclidean n) 2 volume)
    (hZ : ∀ v : smoothSource W (Euclidean n), Z v =ᵐ[volume] SmallSupport.zeroExtend hW (Corr v))
    (hphysical : ∀ v : smoothSource W (Euclidean n), solver v =ᵐ[volume]
      Pphys (SmallSupport.zeroExtend hW (Corr v)))

include hsolver hZ hphysical in
/-- The physical solve descends to the corrected source itself. A vanishing
smooth corrected source has zero Lebesgue class, so the SAME physical operator
and its smooth representative vanish. These are the two realization identities
exported by `DirectSmooth` (`app:ch_regular:eq:exact-physical`). -/
private theorem correctedSourceComponents_ker_le_solver_ker :
    (sourceComponents.comp Z).ker ≤ solver.ker := by
  intro v hv
  change sourceComponents (Z v) = 0 at hv
  have hz : Z v = 0 := by
    funext y
    apply WithLp.ofLp_injective 2
    exact congrFun hv y
  have hclass : SmallSupport.zeroExtend hW (Corr v) = 0 := by
    apply Lp.ext
    filter_upwards [hZ v, Lp.coeFn_zero (Euclidean n) 2 (volume : Measure (Euclidean n))] with y hy h0
    rw [← hy, hz, h0]
  change solver v = 0
  have hh := hphysical v
  rw [hclass, map_zero] at hh
  exact Measure.eq_of_ae_eq (hh.trans (Lp.coeFn_zero _ _ _)) (hsolver v).continuous continuous_zero

/-- The physical solve factor for the actual corrected stress. It extends the
given direct solution from the image of `Z`; no new physical solver or inverse
is selected (`app:ch_response:eq:response-full-map`). -/
def directPhysicalSolveFactor : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n) :=
  extendSourceFactor (sourceComponents.comp Z) solver
    (correctedSourceComponents_ker_le_solver_ker Z solver hsolver hW Corr Pphys hZ hphysical)

/-- On every corrected source the physical factor is the direct solver's SAME
smooth output, not merely the same local L² class
(`app:ch_regular:eq:exact-physical`). -/
theorem directPhysicalSolveFactor_apply (v : smoothSource W (Euclidean n)) :
    directPhysicalSolveFactor Z solver hsolver hW Corr Pphys hZ hphysical
      (fun x ↦ (Z v x).ofLp) = solver v :=
  extendSourceFactor_apply _ _ _ v

/-- The two factors required by `WholeSource` produce precisely the supplied
direct solution on every original compact smooth tensor source. This also
provides their spatial regularity (`app:ch_response:eq:response-full-map`). -/
theorem directPhysicalSolveFactor_correctedStressSource (h : compactSmoothSources S) :
    directPhysicalSolveFactor Z solver hsolver hW Corr Pphys hZ hphysical
      (correctedStressSource Q η (directStressCorrectionFactor Q η hU hQ hη hSU Z) h) =
        solver (cutoffStressSmoothSource Q η hU hQ hη hSU h) := by
  rw [correctedStressSource_directStressCorrectionFactor, directPhysicalSolveFactor_apply]

end JanetCartan.CanonicalAtomRealization
