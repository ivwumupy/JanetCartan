module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinedEstimates

/-!
# The constructed partition with the unchanged detector

For `app:ch_waves:thm:individual` and `app:ch_waves:eq:sampling-prefix-normal`,
`d` is the given detector times the given high-pass. Only its measurability,
bound and floor-one vanishing are inputs. All radial-mask hypotheses are
proved here. Sharp annular indicators disappear almost everywhere after the
two components of each original band are reassembled. No evenness of `d` is
required, and no smooth calculus is applied to a sharp indicator.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

variable {n J : ℕ}

/-- The given detector/high-pass product times the constructed radial band
(`app:ch_waves:thm:individual`). -/
def weightedRadialBand (d : Euclidean (n - 1) → ℂ) (j : ℕ)
    (η : Euclidean (n - 1)) : ℂ := d η * (radialBand n j η : ℂ)

/-- Measurability comes from the given detector, with the radial factor proved
smooth (`app:ch_waves:thm:individual`). -/
theorem measurable_weightedRadialBand {d : Euclidean (n - 1) → ℂ}
    (hd : Measurable d) (j : ℕ) : Measurable (weightedRadialBand d j) :=
  hd.mul (Complex.measurable_ofReal.comp (measurable_radialBand n j))

/-- The radial factor adds no loss to the given detector bound
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_weightedRadialBand_le {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : ∀ η, ‖d η‖ ≤ M) (j : ℕ) (η : Euclidean (n - 1)) :
    ‖weightedRadialBand d j η‖ ≤ M := by
  have hb : radialBand n j η ∈ Set.Icc 0 1 := bandProfile_mem (‖η‖ / dyadicScale j)
  calc
    _ = ‖d η‖ * radialBand n j η := by
      simp only [weightedRadialBand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hb.1]
    _ ≤ ‖d η‖ * 1 := mul_le_mul_of_nonneg_left hb.2 (norm_nonneg _)
    _ ≤ M := by simpa using hd η

/-- Exact wide support of the actual masked band (`app:ch_waves:thm:individual`). -/
theorem weightedRadialBand_eq_zero_off_wideBand (d : Euclidean (n - 1) → ℂ)
    {j : ℕ} {η : Euclidean (n - 1)} (hη : η ∉ wideBand n j) :
    weightedRadialBand d j η = 0 := by
  simp [weightedRadialBand, radialBand_eq_zero_off_wideBand hη]

/-- The original wide-band synthesis with the actual constructed masks
(`app:ch_waves:thm:individual`). -/
def weightedWideSynthesis {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M) : WideInput n J →L[ℂ] Output n :=
  wideSynthesis (fun j ↦ (measurable_weightedRadialBand hd j.val).aestronglyMeasurable)
    (fun j ↦ Filter.Eventually.of_forall (norm_weightedRadialBand_le hb j.val))

/-- The same masks on the literal two-shell refined input
(`app:ch_waves:thm:individual`). -/
def weightedRefinedSynthesis {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) :
    RefinedInput n J →L[ℂ] Output n :=
  synthesis (fun i ↦ (measurable_weightedRadialBand hd i.1.val).aestronglyMeasurable)
    (fun _ ↦ hM)
    (fun i ↦ Filter.Eventually.of_forall (norm_weightedRadialBand_le hb i.1.val))

/-- The actual masked synthesis commutes with the isometric refinement
(`app:ch_waves:thm:individual`). -/
theorem weightedWideSynthesis_eq_refined {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) :
    weightedWideSynthesis (J := J) hd hb =
      (weightedRefinedSynthesis hd hM hb).comp
        (wideRefinement n J).toContinuousLinearEquiv.toContinuousLinearMap :=
  wideSynthesis_eq_refined _ (fun _ ↦ hM) _

/-- Exact equality of the original and refined masked prefix normals
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weightedWideSynthesis_prefix_normal_eq_refined
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (L : ℕ) :
    (weightedWideSynthesis hd hb).comp
        ((widePrefix n J L).comp (weightedWideSynthesis hd hb).adjoint) =
      (weightedRefinedSynthesis hd hM hb).comp
        ((refinedPrefix n J L).comp (weightedRefinedSynthesis hd hM hb).adjoint) :=
  wideSynthesis_prefix_normal_eq_refined _ (fun _ ↦ hM) _ L

/-- The measurable split of one actual band reassembles to its smooth square
almost everywhere; the common boundary sphere is null
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_refined_band_indicators (d : Euclidean (n - 1) → ℂ) (j : ℕ) :
    ∀ᵐ η ∂(volume : Measure (Euclidean (n - 1))),
      (∑ b : Fin 2, (annulus n ((2 : ℝ) ^ (j + b.val))).indicator
        (fun η ↦ ‖weightedRadialBand d j η‖ ^ 2) η) = ‖weightedRadialBand d j η‖ ^ 2 := by
  filter_upwards [ae_not_mem_both_annuli n j] with η hdis
  rw [Fin.sum_univ_two]
  by_cases h₀ : η ∈ annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val))
  · simp only [Set.indicator_of_mem h₀, Set.indicator_of_notMem (show η ∉ annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val)) from
      fun h₁ ↦ hdis ⟨h₀, h₁⟩), add_zero]
  · by_cases h₁ : η ∈ annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val))
    · simp only [Set.indicator_of_notMem h₀, Set.indicator_of_mem h₁, zero_add]
    · have hw : η ∉ wideBand n j := by rw [wideBand_eq_union]; exact fun h ↦ h.elim h₀ h₁
      simp only [Set.indicator_of_notMem h₀, Set.indicator_of_notMem h₁,
        weightedRadialBand_eq_zero_off_wideBand d hw, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]

/-- The exact square sum with an unchanged detector/high-pass product. Floor
one is literal, including the entire transition between one and two
(`app:ch_background:defn:bg-row`, `app:ch_background:defn:bg-mixed`). -/
theorem sum_weightedRadialBand_sq (d : Euclidean (n - 1) → ℂ)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → d η = 0) (L : ℕ) (η : Euclidean (n - 1)) :
    ∑ j ∈ Finset.range L, ‖weightedRadialBand d j η‖ ^ 2 =
      ‖d η‖ ^ 2 * radialPrefix n L η ^ 2 := by
  simp only [weightedRadialBand, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, ← Finset.mul_sum]
  by_cases hη : ‖η‖ ≤ 1
  · simp [hfloor η hη]
  · rw [show (∑ j ∈ Finset.range L, radialBand n j η ^ 2) = radialPrefix n L η ^ 2 from
      sum_scalarBand_sq_eq_prefix_sq L (le_of_not_ge hη)]

/-- The selected sharp normal weight is exactly the original smooth square
prefix after reassembly, with no factor from the number of bands
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normalWeight_weightedRadial_prefix (d : Euclidean (n - 1) → ℂ)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → d η = 0) {L : ℕ} (hL : L ≤ J) :
    normalWeight (radius := refinedRadius (J := J))
      (fun i ↦ weightedRadialBand d i.1.val)
      (Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val + 1 ≤ L)) =ᵐ[volume]
      fun η ↦ ‖η‖ * (‖d η‖ ^ 2 * radialPrefix n L η ^ 2) := by
  have ha := Filter.eventually_all.mpr (fun j : Fin J ↦ sum_refined_band_indicators d j.val)
  filter_upwards [ha] with η hη
  unfold normalWeight
  congr 1
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have he : (∑ j : Fin J, ∑ b : Fin 2,
      if j.val + 1 ≤ L then (annulus n (refinedRadius (j, b))).indicator
        (fun η ↦ ‖weightedRadialBand d j.val η‖ ^ 2) η else 0) =
      ∑ j : Fin J, if j.val < L then ‖weightedRadialBand d j.val η‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < L
    · simp only [show j.val + 1 ≤ L by omega, hj, ite_true]
      exact hη j
    · simp [hj, show ¬j.val + 1 ≤ L by omega]
  rw [he, Fin.sum_univ_eq_sum_range
    (fun j ↦ if j < L then ‖weightedRadialBand d j η‖ ^ 2 else 0)]
  have hs : (∑ j ∈ Finset.range J, if j < L then ‖weightedRadialBand d j η‖ ^ 2 else 0) =
      ∑ j ∈ Finset.range L, ‖weightedRadialBand d j η‖ ^ 2 := by
    rw [← Finset.sum_subset (Finset.range_mono hL) (fun j _ hj ↦ by
      simp only [Finset.mem_range, not_lt] at hj
      simp [Nat.not_lt.mpr hj])]
    exact Finset.sum_congr rfl (fun j hj ↦ ite_eq_left (Finset.mem_range.mp hj))
  rw [hs, sum_weightedRadialBand_sq d hfloor]

/-- Literal output multiplier of every smaller prefix on the same full input.
This is the assembled masked normal used by sampling and canonical changes
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weightedRefinedSynthesis_prefix_normal_coeFn
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → d η = 0) {L : ℕ} (hL : L ≤ J) (f : Output n) :
    weightedRefinedSynthesis hd hM hb
      (refinedPrefix n J L ((weightedRefinedSynthesis hd hM hb).adjoint f)) =ᵐ[volume]
      fun η ↦ ((‖η‖ * (‖d η‖ ^ 2 * radialPrefix n L η ^ 2) : ℝ) : ℂ) * f η := by
  have he := synthesis_prefix_normal_coeFn (radius := refinedRadius (J := J))
    (fun i : RefinedIndex J ↦ (measurable_weightedRadialBand hd i.1.val).aestronglyMeasurable)
    (fun _ ↦ hM) (fun i ↦ Filter.Eventually.of_forall (norm_weightedRadialBand_le hb i.1.val))
    (Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val + 1 ≤ L)) f
  exact he.trans ((normalWeight_weightedRadial_prefix d hfloor hL).mono
    (fun η hη ↦ congrArg (fun t : ℝ ↦ (t : ℂ) * f η) hη))

end JanetCartan.RawInputPartition
