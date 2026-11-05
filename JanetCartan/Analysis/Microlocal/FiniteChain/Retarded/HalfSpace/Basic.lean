module

public import JanetCartan.Analysis.Microlocal.Localization.Vector
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Half-space integrals and their compact supports

Measure-theoretic prerequisites for the half-space argument in
`app:ch_regular:lem:finite-chain`, “A common kernel estimate” and “Retarded
and signed factors”. The normal variable is integrated over `d ≥ 0`;
no differentiation of this restriction occurs in these lemmas.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The half-space integral in `app:ch_regular:lem:finite-chain`, with
Lebesgue measure in the normal variable and the specified tangential measure. -/
def halfSpaceIntegral (μ : Measure E) (f : ℝ × E → ℂ) : ℂ :=
  ∫ x in Ici (0 : ℝ) ×ˢ (univ : Set E), f x ∂(volume.prod μ)

/-- The actual oscillatory integral of `app:ch_regular:lem:finite-chain`.
The unscaled phase is real, and `R` is the oscillation frequency. -/
def halfSpaceOscillatoryIntegral (μ : Measure E) (R : ℝ)
    (F : ℝ × E → ℝ) (a : ℝ × E → ℂ) : ℂ :=
  halfSpaceIntegral μ (fun x ↦ Localization.phaseOscillation (R • F) x * a x)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `app:ch_regular:lem:finite-chain`: a common joint compact support gives
the same compact tangential support for every normal slice. -/
theorem tsupport_slice_subset_projection {a : ℝ × E → ℂ} {K : Set (ℝ × E)}
    (hK : IsCompact K) (ha : tsupport a ⊆ K) (d : ℝ) :
    tsupport (fun z ↦ a (d, z)) ⊆ Prod.snd '' K := by
  apply closure_minimal ?_ (hK.image continuous_snd).isClosed
  intro z hz
  exact ⟨(d, z), ha (subset_tsupport a hz), rfl⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `app:ch_regular:lem:finite-chain`: every slice has compact support,
including slices at the boundary, rather than merely almost every slice. -/
theorem hasCompactSupport_slice {a : ℝ × E → ℂ} {K : Set (ℝ × E)}
    (hK : IsCompact K) (ha : tsupport a ⊆ K) (d : ℝ) :
    HasCompactSupport (fun z ↦ a (d, z)) :=
  (hK.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_slice_subset_projection hK ha d)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `app:ch_regular:lem:finite-chain`: slice integrability follows from
continuity and the explicit common compact support. -/
theorem integrable_slice {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {a : ℝ × E → ℂ} {K : Set (ℝ × E)} (hK : IsCompact K)
    (ha : tsupport a ⊆ K) (hac : Continuous a) (d : ℝ) :
    Integrable (fun z ↦ a (d, z)) μ :=
  (hac.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hK ha d)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `app:ch_regular:lem:finite-chain`: the inner integral is supported in
the normal projection of the same common compact set. -/
theorem tsupport_integral_slice_subset_projection (μ : Measure E)
    {a : ℝ × E → ℂ} {K : Set (ℝ × E)} (hK : IsCompact K)
    (ha : tsupport a ⊆ K) :
    tsupport (fun d ↦ ∫ z, a (d, z) ∂μ) ⊆ Prod.fst '' K := by
  apply closure_minimal ?_ (hK.image continuous_fst).isClosed
  intro d hd
  by_contra hdK
  apply hd
  have hz (z : E) : a (d, z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hdK ⟨(d, z), ha h, rfl⟩
  simp only [hz, integral_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `app:ch_regular:lem:finite-chain`: Fubini on the closed half-space.
The restriction is a measure restriction, not a differentiated function. -/
theorem halfSpaceIntegral_eq_integral_slice {μ : Measure E} [SFinite μ]
    {f : ℝ × E → ℂ} (hf : Integrable f (volume.prod μ)) :
    halfSpaceIntegral μ f = ∫ d in Ici (0 : ℝ), ∫ z, f (d, z) ∂μ := by
  unfold halfSpaceIntegral
  rw [← Measure.restrict_prod_eq_prod_univ]
  exact integral_prod f (by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hf.restrict)

/-- `app:ch_regular:lem:finite-chain`: smooth compactly supported amplitudes
make the joint oscillatory integrand integrable for every real frequency. -/
theorem integrable_oscillatoryIntegrand {μ : Measure E} [μ.IsAddHaarMeasure]
    {F : ℝ × E → ℝ} {a : ℝ × E → ℂ} (hF : ContDiff ℝ ∞ F)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (R : ℝ) :
    Integrable (fun x ↦ Localization.phaseOscillation (R • F) x * a x)
      (volume.prod μ) := by
  exact Localization.integrable_phaseOscillation_smul isOpen_univ (R • F) a
    (hF.const_smul R).contDiffOn ha.contDiffOn (subset_univ _) hc

/-- `app:ch_regular:lem:finite-chain`: the half-space oscillatory integral
equals the iterated integral, with all Fubini hypotheses discharged. -/
theorem halfSpaceOscillatoryIntegral_eq_integral_slice
    {μ : Measure E} [μ.IsAddHaarMeasure] {F : ℝ × E → ℝ} {a : ℝ × E → ℂ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (R : ℝ) :
    halfSpaceOscillatoryIntegral μ R F a =
      ∫ d in Ici (0 : ℝ), ∫ z,
        Localization.phaseOscillation (R • F) (d, z) * a (d, z) ∂μ :=
  halfSpaceIntegral_eq_integral_slice (integrable_oscillatoryIntegrand hF ha hc R)

/-- `app:ch_regular:lem:finite-chain`: splitting a smooth compact amplitude
is compatible with the half-space integral. -/
theorem halfSpaceOscillatoryIntegral_add {μ : Measure E} [μ.IsAddHaarMeasure]
    {F : ℝ × E → ℝ} {a c : ℝ × E → ℂ} (hF : ContDiff ℝ ∞ F)
    (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hca : HasCompactSupport a) (hcc : HasCompactSupport c) (R : ℝ) :
    halfSpaceOscillatoryIntegral μ R F (a + c) =
      halfSpaceOscillatoryIntegral μ R F a + halfSpaceOscillatoryIntegral μ R F c := by
  simp only [halfSpaceOscillatoryIntegral, halfSpaceIntegral, Pi.add_apply, mul_add]
  exact integral_add (integrable_oscillatoryIntegrand hF ha hca R).restrict
    (integrable_oscillatoryIntegrand hF hc hcc R).restrict

end JanetCartan.FiniteChain.Retarded.HalfSpace
