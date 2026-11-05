module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Radial
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Rounding
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Kernel

/-!
# The unchanged continuum carrier prefix and its raw tail

The masks are lifted to the literal `carrierMeasure`, including the continuous
carrier variable. The source predicate `κⱼ ≤ K` gives plateau constant `c = 1`
and support constant `C = 4`. Consequently the carrier tail and the auxiliary
tail use the same `K`; the auxiliary row is never changed to another cutoff.
The raw weighted membership and weight comparison remain explicit analytic
inputs of the current-mean/adjoint producer (`main:eq:linear-two-errors`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
namespace JanetCartan.RawInputPartition
open ContinuumRow RawCutoffBounds

/-- Lift of the literal finite square prefix to continuous carrier variables
(`app:ch_background:defn:bg-mixed`). -/
def carrierPrefix (n J : ℕ) (x : CarrierVariable n) : ℝ := radialPrefix n J x.2

/-- Lift of an original band, with no discretization of the carrier parameter
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def carrierBand (n j : ℕ) (x : CarrierVariable n) : ℝ := radialBand n j x.2

/-- Measurability on the actual product carrier measure
(`app:ch_background:defn:bg-mixed`). -/
theorem measurable_carrierPrefix (n J : ℕ) : Measurable (carrierPrefix n J) :=
  (measurable_radialPrefix n J).comp measurable_snd

/-- Boundedness on the actual carrier variables (`app:ch_background:defn:bg-mixed`). -/
theorem carrierPrefix_mem (n J : ℕ) (x : CarrierVariable n) :
    carrierPrefix n J x ∈ Set.Icc 0 1 := scalarPrefix_mem J ‖x.2‖

/-- Literal L∞ multiplier, packaged through the shared cutoff API
(`app:ch_background:defn:bg-mixed`). -/
def carrierPrefixMask (n J : ℕ) : Lp ℝ ∞ (carrierMeasure n) :=
  carrierMask (carrierPrefix n J) (measurable_carrierPrefix n J).aestronglyMeasurable
    (Filter.Eventually.of_forall (carrierPrefix_mem n J))

/-- Exact representative of the carrier prefix multiplier
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierPrefixMask_coeFn (n J : ℕ) :
    carrierPrefixMask n J =ᵐ[carrierMeasure n] carrierPrefix n J := carrierMask_coeFn _ _ _

/-- The literal rounded cutoff retains the original band labels
(`app:ch_background:defn:bg-mixed`). -/
def roundedCarrierMask (n : ℕ) (K : ℝ) : Lp ℝ ∞ (carrierMeasure n) :=
  carrierPrefixMask n (cutoffCount K)

/-- The continuous carrier mask square is the exact radial square sum on
all of the given floor-one high-pass (`app:ch_background:defn:bg-row`). -/
theorem sum_carrierBand_sq_eq_prefix_sq {n : ℕ} (J : ℕ)
    (χ : CarrierVariable n → ℝ) (hχ : ∀ x, ‖x.2‖ ≤ 1 → χ x = 0)
    {x : CarrierVariable n} (hx : χ x ≠ 0) :
    ∑ j ∈ Finset.range J, carrierBand n j x ^ 2 = carrierPrefix n J x ^ 2 :=
  sum_scalarBand_sq_eq_prefix_sq J (le_of_lt (lt_of_not_ge (fun h ↦ hx (hχ x h))))

/-- Multiplying by an arbitrary fixed detector preserves the exact identity;
no symmetry or smoothness of that detector is inferred
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_detector_carrierBand_sq {n : ℕ} (J : ℕ)
    (χ : CarrierVariable n → ℝ) (hχ : ∀ x, ‖x.2‖ ≤ 1 → χ x = 0)
    (a : CarrierVariable n → ℝ) (x : CarrierVariable n) :
    ∑ j ∈ Finset.range J, (a x * χ x * carrierBand n j x) ^ 2 =
      (a x * χ x * carrierPrefix n J x) ^ 2 := by
  simp only [mul_pow, ← Finset.mul_sum]
  by_cases hx : χ x = 0
  · simp [hx]
  · rw [sum_carrierBand_sq_eq_prefix_sq J χ hχ hx]

/-- The AE contraction bounds needed by the actual raw multiplier tail
(`main:eq:linear-two-errors`). -/
theorem roundedCarrierMask_mem (n : ℕ) (K : ℝ) :
    ∀ᵐ x ∂carrierMeasure n, roundedCarrierMask n K x ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [carrierPrefixMask_coeFn n (cutoffCount K)] with x hx
  change carrierPrefixMask n (cutoffCount K) x ∈ _
  rw [hx]
  exact carrierPrefix_mem _ _ _

/-- The exact low-frequency identity at the original auxiliary cutoff `K`
(`app:ch_background:defn:bg-mixed`). -/
theorem roundedCarrierMask_eq_one {n : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    ∀ᵐ x ∂carrierMeasure n, ‖x.2‖ ≤ K → roundedCarrierMask n K x = 1 := by
  filter_upwards [carrierPrefixMask_coeFn n (cutoffCount K)] with x hx hlow
  exact hx.trans (roundedPrefix_eq_one hK hlow)

/-- The original carrier square has support below `4K`
(`app:ch_background:defn:bg-mixed`). -/
theorem roundedCarrierMask_eq_zero {n : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    ∀ᵐ x ∂carrierMeasure n, 4 * K ≤ ‖x.2‖ → roundedCarrierMask n K x = 0 := by
  filter_upwards [carrierPrefixMask_coeFn n (cutoffCount K)] with x hx hhigh
  exact hx.trans (roundedPrefix_eq_zero hK hhigh)

/-- Tail of the literal raw square, retaining both auxiliary channels at `K`.
The constructed plateau constant is `c = 1`, so `max 1 (c^(-s)) = 1` and
its threshold is exactly `K ≥ 1`. Membership and weight domination are the
remaining current-mean/adjoint inputs (`main:eq:linear-two-errors`). -/
theorem rawSquaredCutoff_rounded_tail {n : ℕ} {ι : Type*} [Fintype ι]
    {K : ℝ} (hK : 1 ≤ K) (s : ℕ) (h : AugmentedInput n ι)
    (w : ι → CarrierVariable n → ℝ) (hh : RawWeightedMem s w h)
    (hweight : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s ≤ w a x) :
    ‖h - rawSquaredCutoff K (fun _ ↦ roundedCarrierMask n K) h‖ ≤
      K ^ (-(s : ℝ)) * rawWeightedNorm s w h hh := by
  apply rawSquaredCutoff_tail hK s _ h (fun _ ↦ roundedCarrierMask_mem n K) _ w hh hweight
  intro a
  filter_upwards [roundedCarrierMask_eq_one (n := n) hK] with x hx
  exact fun _ hlow ↦ hx hlow

/-- Exact normal-density identity with the given high-pass and detector
reassembled before any smooth symbol calculus
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_carrierBand_normalDensity {n N : ℕ} (J : ℕ) (d : CarrierData n N)
    (χ : CarrierVariable n → ℝ) (hχ : ∀ u, ‖u.2‖ ≤ 1 → χ u = 0)
    (a m : CarrierVariable n → ℝ) (x y : Torus n) (i j : Fin n)
    (u : CarrierVariable n) :
    (∑ k ∈ Finset.range J, ContinuumRow.carrierNormalDensity d
      (fun v ↦ m v * (a v * χ v * carrierBand n k v)) x y i j u) =
      ContinuumRow.carrierNormalDensity d
        (fun v ↦ m v * (a v * χ v * carrierPrefix n J v)) x y i j u :=
  ContinuumRow.sum_carrierNormalDensity_eq d (Finset.range J) m
    (fun v ↦ a v * χ v * carrierPrefix n J v)
    (fun k v ↦ a v * χ v * carrierBand n k v)
    (sum_detector_carrierBand_sq J χ hχ a) x y i j u

end JanetCartan.RawInputPartition
