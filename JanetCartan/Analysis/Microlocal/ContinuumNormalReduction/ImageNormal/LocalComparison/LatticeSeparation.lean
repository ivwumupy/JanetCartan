module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Fourier.Descent

/-!
# Separation from the nonzero lattice translates

The geometric gap for the smooth remainder in
`app:ch_background:prop:bg-frame`, Step 1. Both cutoffs must lie in one cube
of radius strictly smaller than `1/2`. This is a gap for differences of two
points, not an assertion that the whole Euclidean kernel is periodic.
-/

@[expose] public noncomputable section

open scoped SchwartzMap

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A nonzero lattice vector separates differences of two points in the
support cube by `1 - 2r` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_sub_add_integerTranslation_ge {r : ℝ} {x y : E}
    (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r)
    {k : Fin d → ℤ} (hk : k ≠ 0) :
    1 - 2 * r ≤ ‖x - y + integerTranslation k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have hone : (1 : ℝ) ≤ |(k i : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hi)
  have hcoord := PiLp.norm_apply_le (x - y + integerTranslation k) i
  change |x i - y i + (k i : ℝ)| ≤ ‖x - y + integerTranslation k‖ at hcoord
  have htri := abs_add_le (x i - y i + (k i : ℝ)) (y i - x i)
  have hdiff : |y i - x i| ≤ 2 * r := by
    calc
      _ ≤ |y i| + |x i| := abs_sub _ _
      _ ≤ 2 * r := by linarith [hx i, hy i]
  have hid : x i - y i + (k i : ℝ) + (y i - x i) = (k i : ℝ) := by ring
  rw [hid] at htri
  linarith

/-- No singularity of a nonzero translate meets the two cutoff supports
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem sub_add_integerTranslation_ne_zero {r : ℝ} (hr : r < 1 / 2)
    {x y : E} (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r)
    {k : Fin d → ℤ} (hk : k ≠ 0) : x - y + integerTranslation k ≠ 0 := by
  intro h
  have hb := norm_sub_add_integerTranslation_ge hx hy hk
  rw [h, norm_zero] at hb
  linarith

/-- Compactly supported Schwartz data have only their zero translate on
the closed fundamental cell (`app:ch_background:defn:bg-row`). -/
theorem schwartzLatticePeriodization_eq_on_cell {r : ℝ} (hr : r < 1 / 2)
    (u : 𝓢(E, ℂ)) (hu : AmplitudeBound.SupportedInCenteredBox r u)
    {x : E} (hx : x ∈ fundamentalCell d) :
    schwartzLatticePeriodization u x = u x := by
  classical
  unfold schwartzLatticePeriodization
  rw [tsum_eq_single (0 : Fin d → ℤ)]
  · simp only [Pi.zero_apply, Int.cast_zero]
    rw [show (WithLp.toLp 2 (fun _ : Fin d ↦ (0 : ℝ)) : E) = 0 from rfl, add_zero]
  intro k hk
  by_contra h
  have hs := hu (x + integerTranslation k) h
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra hki
    push Not at hki
    exact hk (funext hki)
  have hone : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast (Int.one_le_abs hi)
  have hc : |x i| ≤ (1 / 2 : ℝ) := abs_le.mpr (hx i)
  have hb := abs_sub ((x + integerTranslation k) i) (x i)
  have hid : (x + integerTranslation k) i - x i = (k i : ℝ) := by
    change x i + (k i : ℝ) - x i = _
    ring
  rw [hid] at hb
  linarith [hs i]

/-- The Schwartz periodization agrees with the existing chart periodization
for supported tests (`app:ch_background:defn:bg-row`). Thus no lift or
restriction identification is assumed in the test-level comparison. -/
theorem schwartzTorusPeriodization_eq_amplitudePeriodization {r : ℝ} (hr : r < 1 / 2)
    (u : 𝓢(E, ℂ)) (hu : AmplitudeBound.SupportedInCenteredBox r u) :
    (schwartzTorusPeriodization u : Torus d → ℂ) =
      AmplitudeBound.amplitudePeriodization u := by
  funext z
  rw [← AmplitudeBound.torusQuotient_centeredTorusRepresentative z,
    schwartzTorusPeriodization_torusQuotient,
    schwartzLatticePeriodization_eq_on_cell hr u hu
      (AmplitudeBound.centeredTorusRepresentative_mem z)]
  simp only [AmplitudeBound.amplitudePeriodization, Function.comp_apply,
    AmplitudeBound.torusQuotient_centeredTorusRepresentative]

end JanetCartan.ContinuumNormalReduction.ImageNormal
