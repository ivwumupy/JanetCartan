module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier

/-!
# Physical and input Fourier multipliers on the graph Hilbert space

These are the actual multipliers in
`app:ch_regular_base:eq:fixed-source-multiplication`, on vector Euclidean
Lebesgue L². The input symbol is in cycle frequency; its Schwartz realization
explicitly uses the physical argument `2π ξ`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Filter
open scoped ENNReal
namespace JanetCartan.FourierIntegral.BoundedSourceMultiplier
open LowBounds LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "ℰ" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure ℰ)

/-- Scalar multiplication on the graph Hilbert space. Consumer: the bounded
source-symbol identity in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def physicalMultiplier (a : Lp ℂ ∞ (volume : Measure ℰ)) : H →L[ℂ] H :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := V)).holderL volume ∞ 2 2 a

/-- The multiplier is literal pointwise multiplication (same source formula). -/
theorem physicalMultiplier_coeFn (a : Lp ℂ ∞ (volume : Measure ℰ)) (f : H) :
    physicalMultiplier a f =ᵐ[volume] fun x ↦ a x • f x :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := V)).coeFn_holder a f

/-- The L∞ budget proves boundedness without a symbol-order assumption;
source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem norm_physicalMultiplier_le (a : Lp ℂ ∞ (volume : Measure ℰ)) :
    ‖physicalMultiplier (r := r) a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ (E := V)).holderL volume ∞ 2 2‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.opNorm_lsmul_le)
      (norm_nonneg a)
    _ = _ := one_mul _

/-- L²/Schwartz agreement for the physical multiplier, including a fixed
compact source mask in `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem physicalMultiplier_schwartzVectorToLp
    (a : Lp ℂ ∞ (volume : Measure ℰ)) (m : ℰ → ℂ) (hm : m.HasTemperateGrowth)
    (ha : a =ᵐ[volume] m) (u : SchwartzMap ℰ (Fin r → ℂ)) :
    physicalMultiplier a (schwartzVectorToLp u) =
      schwartzVectorToLp (SchwartzMap.smulLeftCLM (Fin r → ℂ) m u) := by
  apply Lp.ext
  filter_upwards [physicalMultiplier_coeFn a (schwartzVectorToLp u), ha,
    schwartzVectorToLp_ae u,
    schwartzVectorToLp_ae (SchwartzMap.smulLeftCLM (Fin r → ℂ) m u)] with x hx ha hu hv
  rw [hx, ha, hu, hv, SchwartzMap.smulLeftCLM_apply_apply hm]
  rfl

/-- The bounded fixed input cutoff. Its L∞ symbol is in cycles, as for
`CoordinateInverse.canonicalFrequencyCutoff`; the physical symbol is `q` in
`inputFrequencyCutoff_schwartzVectorToLp`. Source: the fixed-source formula. -/
def inputFrequencyCutoff (a : Lp ℂ ∞ (volume : Measure ℰ)) : H →L[ℂ] H :=
  (fourierInvCLM ℂ H).comp ((physicalMultiplier a).comp (fourierCLM ℂ H))

/-- Plancherel proves the input cutoff budget (same source formula). -/
theorem norm_inputFrequencyCutoff_le (a : Lp ℂ ∞ (volume : Measure ℰ)) :
    ‖inputFrequencyCutoff (r := r) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro f
  change ‖(Lp.fourierTransformₗᵢ ℰ V).symm (physicalMultiplier a (𝓕 f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, ← Lp.norm_fourier_eq f]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_physicalMultiplier_le a) (norm_nonneg _))

private theorem toEuclideanSchwartz_sourceInputFrequencyCutoff
    (q : ℰ → ℂ) (hq : q.HasTemperateGrowth) (u : SchwartzMap ℰ (Fin r → ℂ)) :
    toEuclideanSchwartz (sourceInputFrequencyCutoff q hq u) =
      𝓕⁻ (SchwartzMap.smulLeftCLM V (fun ξ ↦ q ((2 * Real.pi) • ξ))
        (𝓕 (toEuclideanSchwartz u))) := by
  apply (fourierEquiv ℂ (SchwartzMap ℰ V)).injective
  change 𝓕 (toEuclideanSchwartz (sourceInputFrequencyCutoff q hq u)) =
    𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM V (fun ξ ↦ q ((2 * Real.pi) • ξ))
      (𝓕 (toEuclideanSchwartz u))))
  rw [← toEuclideanSchwartz_fourier, fourier_fourierInv_eq]
  simp only [sourceInputFrequencyCutoff, fourier_fourierInv_eq]
  apply SchwartzMap.ext
  intro ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    ← toEuclideanSchwartz_fourier]
  rfl

/-- The bounded input cutoff acts by exactly the original physical-frequency
Schwartz cutoff, including its shoulders. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem inputFrequencyCutoff_schwartzVectorToLp
    (a : Lp ℂ ∞ (volume : Measure ℰ)) (q : ℰ → ℂ) (hq : q.HasTemperateGrowth)
    (ha : a =ᵐ[volume] fun ξ ↦ q ((2 * Real.pi) • ξ))
    (u : SchwartzMap ℰ (Fin r → ℂ)) :
    inputFrequencyCutoff a (schwartzVectorToLp u) =
      schwartzVectorToLp (sourceInputFrequencyCutoff q hq u) := by
  simp only [schwartzVectorToLp_eq_toEuclideanSchwartz_toLp]
  change 𝓕⁻ (physicalMultiplier a (𝓕 ((toEuclideanSchwartz u).toLp 2))) = _
  rw [SchwartzMap.toLp_fourier_eq]
  have hm : physicalMultiplier a ((𝓕 (toEuclideanSchwartz u)).toLp 2) =
      (SchwartzMap.smulLeftCLM V (fun ξ ↦ q ((2 * Real.pi) • ξ))
        (𝓕 (toEuclideanSchwartz u))).toLp 2 := by
    apply Lp.ext
    filter_upwards [physicalMultiplier_coeFn a ((𝓕 (toEuclideanSchwartz u)).toLp 2),
      ha, (𝓕 (toEuclideanSchwartz u)).coeFn_toLp 2,
      (SchwartzMap.smulLeftCLM V (fun ξ ↦ q ((2 * Real.pi) • ξ))
        (𝓕 (toEuclideanSchwartz u))).coeFn_toLp 2] with ξ hm ha hu hv
    rw [hm, ha, hu, hv, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rw [hm, SchwartzMap.toLp_fourierInv_eq, toEuclideanSchwartz_sourceInputFrequencyCutoff]

/-- Squaring the original real source cutoff is multiplication by its literal
square. This permits `1-χs²` to be formed by subtracting a compact multiplier
from the identity; no compact-support assertion about `1-χs²` is used.
Source: `app:ch_regular_base:eq:source-cut-normal`. -/
theorem sourceCutMultiplier_sq
    (χ : ℰ → ℝ) (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (m : SchwartzMap ℰ ℂ) (hm : ∀ x, m x = (χ x : ℂ) ^ 2) :
    sourceCutMultiplier (r := r) χ hχ hb ∘L sourceCutMultiplier χ hχ hb =
      physicalMultiplier (m.toLp ∞) := by
  ext f : 1
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hb (sourceCutMultiplier χ hχ hb f),
    sourceCutMultiplier_coeFn χ hχ hb f, physicalMultiplier_coeFn (m.toLp ∞) f,
    m.coeFn_toLp ∞] with x hx hy hz hm'
  simp only [ContinuousLinearMap.comp_apply]
  rw [hx, hy, hz, hm', hm, smul_smul, pow_two]

end JanetCartan.FourierIntegral.BoundedSourceMultiplier
