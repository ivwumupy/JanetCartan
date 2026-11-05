module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Auxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Carrier

/-!
# Squared raw-input cutoffs on the continuum row

The multiplier deduction in `main:eq:linear-two-errors`,
`app:ch_mean_pairs:eq:mean-input-raw-one-high`, and
`app:ch_background:eq:bg-Vaux-raw-band`. Both auxiliary inputs and every complex
carrier channel are retained in `ContinuumRow.AugmentedInput`.

These are conditional estimates for actual L² multipliers. Producers must
establish the mask identities on the support of the raw adjoint and its weighted
energy membership. The carrier weight must dominate `(1+|η|²)^(s/2)`. Identifying
this weighted energy with, or bounding it by, the full initial-variable `X^s`
norm is a producer obligation; no torus/Lebesgue identification is made here.
The physical source cutoff belongs after these raw operators.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.RawCutoffBounds
open ContinuumRow

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Diagonal raw square, retaining image, exterior and all carrier inputs
(`app:ch_background:defn:bg-mixed`). -/
def rawSquaredCutoff (K : ℝ) (m : ι → Lp ℝ ∞ (carrierMeasure n))
    (h : AugmentedInput n ι) : AugmentedInput n ι :=
  WithLp.toLp 2 (WithLp.toLp 2 (auxiliarySquaredCutoff K h.fst.fst,
    WithLp.toLp 2 (fun a ↦ carrierSquaredCutoff (m a) (h.fst.snd a))),
    auxiliarySquaredCutoff K h.snd)

/-- Explicit weighted-energy membership for every raw channel
(`app:ch_background:defn:bg-mixed`). Auxiliary membership includes summability;
carrier membership includes integrability on the literal initial measure. -/
structure RawWeightedMem (s : ℕ) (w : ι → CarrierVariable n → ℝ)
    (h : AugmentedInput n ι) : Prop where
  image : h.fst.fst ∈ (periodicSobolevScale n (Euclidean n)).level s
  exterior : h.snd ∈ (periodicSobolevScale n (Euclidean n)).level s
  carrier : ∀ a, CarrierWeightedMem (w a) (h.fst.snd a)

/-- The finite Hilbert sum of the explicitly convergent raw energies
(`app:ch_background:defn:bg-mixed`). -/
def rawWeightedNorm (s : ℕ) (w : ι → CarrierVariable n → ℝ)
    (h : AugmentedInput n ι) (hh : RawWeightedMem s w h) : ℝ :=
  Real.sqrt ((periodicSobolevScale n (Euclidean n)).gradeNorm s h.fst.fst ^ 2 +
    ∑ a, carrierWeightedNorm (w a) (h.fst.snd a) (hh.carrier a) ^ 2 +
    (periodicSobolevScale n (Euclidean n)).gradeNorm s h.snd ^ 2)

/-- `main:eq:linear-two-errors`: the full finite Hilbert-sum tail bound, with
both auxiliary channels and both quadratures in every carrier slot. The input
assumptions concern masks, weights and convergence, never the tail estimate. -/
theorem rawSquaredCutoff_tail {K : ℝ} (hK : 1 ≤ K) (s : ℕ)
    (m : ι → Lp ℝ ∞ (carrierMeasure n)) (h : AugmentedInput n ι)
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      h.fst.snd a x ≠ 0 → ‖x.2‖ ≤ K → m a x = 1)
    (w : ι → CarrierVariable n → ℝ) (hh : RawWeightedMem s w h)
    (hweight : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s ≤ w a x) :
    ‖h - rawSquaredCutoff K m h‖ ≤ K ^ (-(s : ℝ)) * rawWeightedNorm s w h hh := by
  have hi := auxiliarySquaredCutoff_tail hK s h.fst.fst hh.image
  have he := auxiliarySquaredCutoff_tail hK s h.snd hh.exterior
  have hc (a : ι) := carrierSquaredCutoff_tail hK s (m a) (h.fst.snd a)
    (hm a) (hone a) (w a) (hh.carrier a) (hweight a)
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
  have hc2 := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (hc a) 2)
  simp only [mul_pow, ← Finset.mul_sum] at hi2 he2 hc2
  have hn : ‖h - rawSquaredCutoff K m h‖ ^ 2 =
      ‖h.fst.fst - auxiliarySquaredCutoff K h.fst.fst‖ ^ 2 +
      ∑ a, ‖h.fst.snd a - carrierSquaredCutoff (m a) (h.fst.snd a)‖ ^ 2 +
      ‖h.snd - auxiliarySquaredCutoff K h.snd‖ ^ 2 := by
    simp [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, rawSquaredCutoff]
  have hw0 : 0 ≤ (periodicSobolevScale n (Euclidean n)).gradeNorm s h.fst.fst ^ 2 +
      ∑ a, carrierWeightedNorm (w a) (h.fst.snd a) (hh.carrier a) ^ 2 +
      (periodicSobolevScale n (Euclidean n)).gradeNorm s h.snd ^ 2 := by positivity
  rw [Real.rpow_neg (le_trans zero_le_one hK), Real.rpow_natCast]
  have hnonneg : 0 ≤ (K ^ s)⁻¹ * rawWeightedNorm s w h hh := by
    unfold rawWeightedNorm
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) hnonneg).mp
  unfold rawWeightedNorm
  rw [mul_pow, Real.sq_sqrt hw0, hn]
  nlinarith

/-- The diagonal raw square as a bounded real linear map, so the original row
and adjoint can be composed with it without inserting any output cutoff
(`app:ch_background:defn:bg-mixed`). -/
def rawSquaredCutoffCLM {K : ℝ} (hK : 1 ≤ K)
    (m : ι → Lp ℝ ∞ (carrierMeasure n)) : AugmentedInput n ι →L[ℝ] AugmentedInput n ι where
  toFun := rawSquaredCutoff K m
  map_add' u v := by
    simp only [rawSquaredCutoff, ← auxiliarySquaredCutoffCLM_apply hK]
    simp only [map_add, WithLp.add_fst, WithLp.add_snd, PiLp.add_apply,
      ← WithLp.toLp_add, Pi.add_def, Prod.mk_add_mk]
  map_smul' c u := by
    simp only [rawSquaredCutoff, ← auxiliarySquaredCutoffCLM_apply hK]
    simp only [map_smul, WithLp.smul_fst, WithLp.smul_snd, PiLp.smul_apply,
      ← WithLp.toLp_smul, Pi.smul_def, Prod.smul_mk, RingHom.id_apply]
  cont := by
    unfold rawSquaredCutoff
    simp only [← auxiliarySquaredCutoffCLM_apply hK]
    fun_prop

/-- Agreement of the bounded diagonal operator and the componentwise raw square
(`app:ch_background:defn:bg-mixed`). -/
@[simp] theorem rawSquaredCutoffCLM_apply {K : ℝ} (hK : 1 ≤ K)
    (m : ι → Lp ℝ ∞ (carrierMeasure n)) (h : AugmentedInput n ι) :
    rawSquaredCutoffCLM hK m h = rawSquaredCutoff K m h := rfl

end JanetCartan.RawCutoffBounds
