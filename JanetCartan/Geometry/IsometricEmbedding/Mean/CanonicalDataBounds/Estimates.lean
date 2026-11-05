module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalDataBounds.Basic

/-!
# Individual canonical estimates

`app:ch_mean_pairs:eq:mean-canonical-bounds`, with explicit constants independent
of band count and sample weights. The mask and ceiling inputs belong to the raw
primary construction, the individual operator bound to the corrected atoms,
and the inverse bound to the continuum L² inverse. The physical estimate is
the current wave estimate `app:ch_waves:eq:raw-physical-bound`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CanonicalDataBounds

open RawInputRealization

variable {n J : ℕ} {β : Fin J → Euclidean (n - 1) → ℂ}
  {Output : Type*} [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
  [CompleteSpace Output]
  (A : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val) →L[ℝ] Output)
  (Q0 : Output →L[ℝ] Output)

/-- Support below `C K` of the actual canonical input before cutoff
(`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem fourierDensity_eq_zero_of_dyadic_ceiling {C K : ℝ}
    (hceil : (2 : ℝ) ^ J ≤ C * K) (r : Output)
    {η : Euclidean (n - 1)} (hη : C * K < ‖η‖) :
    fourierDensity β A Q0 r η = 0 := by
  apply fourierDensity_eq_zero_above_ceiling β A Q0 r _ hη
  intro i
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) i.isLt.le).trans hceil

/-- Set-theoretic Fourier support of the uncut initial datum in
`app:ch_mean_pairs:eq:mean-canonical-bounds`. -/
theorem support_fourierDensity_subset_closedBall {C K : ℝ}
    (hceil : (2 : ℝ) ^ J ≤ C * K) (r : Output) :
    Function.support (fourierDensity β A Q0 r) ⊆ Metric.closedBall 0 (C * K) := by
  intro η hη
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hη (fourierDensity_eq_zero_of_dyadic_ceiling A Q0 hceil r (lt_of_not_ge h))

/-- Fourier `L¹ ≤ C K^p ‖r‖₂`, `p=(n+1)/2`, obtained from the raw exponent
`n/2` and the individual adjoint's additional `1/2`
(`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem integral_norm_fourierDensity_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M C CA CQ K : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M) (hC : 0 ≤ C)
    (hCA : 0 ≤ CA) (hK : 0 < K) (hceil : (2 : ℝ) ^ J ≤ C * K)
    (hA : ‖A‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ) (r : Output) :
    (∫ η, ‖fourierDensity β A Q0 r η‖) ≤
      (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ) *
        K ^ (((n : ℝ) + 1) / 2) * ‖r‖ := by
  have h := size_adjointInput_le A Q0 (fun v ↦ ∫ η, ‖density β v η‖)
    (by positivity : 0 ≤ M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2))
    hCA hK hA hQ
    (integral_norm_density_ceiling_le hn hβ hM0 hM hC hK.le hceil) r
  simpa only [fourierDensity,
    show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring] using h

/-- Initial `C^m ≤ C_m K^(m+p) ‖r‖₂`, on any initial observation set
(`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem cNorm_initialDatum_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M C CA CQ K : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M) (hC : 0 ≤ C)
    (hCA : 0 ≤ CA) (hK : 1 ≤ K) (hceil : (2 : ℝ) ^ J ≤ C * K)
    (hA : ‖A‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ)
    (r : Output) (m : ℕ) (s : Set (Euclidean (n - 1))) :
    cNorm s m (initialDatum β A Q0 r) ≤
      (((m + 1 : ℕ) : ℝ) * M * Real.sqrt (unitBallVolume n) *
        C ^ ((m : ℝ) + (n : ℝ) / 2) * CA * CQ) *
        K ^ ((m : ℝ) + ((n : ℝ) + 1) / 2) * ‖r‖ := by
  have h := size_adjointInput_le A Q0 (fun v ↦ cNorm s m (field β v))
    (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ) * M * Real.sqrt (unitBallVolume n) *
      C ^ ((m : ℝ) + (n : ℝ) / 2)) hCA (lt_of_lt_of_le zero_lt_one hK) hA hQ
    (fun v ↦ cNorm_field_ceiling_le hn hβ hM0 hM hC hK hceil v m s) r
  simpa only [initialDatum, show (m : ℝ) + (n : ℝ) / 2 + 1 / 2 =
    (m : ℝ) + ((n : ℝ) + 1) / 2 by ring] using h

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The physical current change uses the same datum and adjoint. For `K ≥ L`,
the supplied raw physical estimate gives the physical half of
`app:ch_mean_pairs:eq:mean-canonical-bounds`. No inverse sample weight occurs. -/
theorem cNorm_physicalChange_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M C CA CQ K L P : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M) (hC : 0 ≤ C)
    (hCA : 0 ≤ CA) (hK : 0 < K) (hL0 : 0 ≤ L) (hLK : L ≤ K)
    (hceil : (2 : ℝ) ^ J ≤ C * K)
    (hA : ‖A‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ)
    (G : (Euclidean (n - 1) → ℂ) → (X → V)) (m : ℕ) (s : Set X)
    (hP : 0 ≤ P)
    (hphysical : ∀ v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val),
      cNorm s m (G (field β v)) ≤ P * (K + L) ^ m * (∫ η, ‖density β v η‖))
    (r : Output) :
    cNorm s m (physicalChange G β A Q0 r) ≤
      (P * 2 ^ m * (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ)) *
        K ^ ((m : ℝ) + ((n : ℝ) + 1) / 2) * ‖r‖ := by
  have hQ0 : 0 ≤ CQ := (norm_nonneg _).trans hQ
  have hfourier := integral_norm_fourierDensity_le A Q0 hn hβ hM0 hM hC hCA hK
    hceil hA hQ r
  calc
    _ ≤ P * (K + L) ^ m * (∫ η, ‖fourierDensity β A Q0 r η‖) :=
      hphysical (adjointInput A Q0 r)
    _ ≤ P * (2 * K) ^ m *
        ((M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ) *
          K ^ (((n : ℝ) + 1) / 2) * ‖r‖) := by
      gcongr
      · linarith
    _ = _ := by rw [mul_pow, Real.rpow_add hK, Real.rpow_natCast]; ring

/-- The sum of the initial and physical norms, in exactly the form of
`app:ch_mean_pairs:eq:mean-canonical-bounds`. Actual producers must instantiate
the mask, individual operator, continuum inverse, and physical wave hypotheses. -/
theorem cNorm_initialDatum_add_physicalChange_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M C CA CQ K L P : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M) (hC : 0 ≤ C)
    (hCA : 0 ≤ CA) (hK : 1 ≤ K) (hL0 : 0 ≤ L) (hLK : L ≤ K)
    (hceil : (2 : ℝ) ^ J ≤ C * K)
    (hA : ‖A‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ)
    (G : (Euclidean (n - 1) → ℂ) → (X → V)) (m : ℕ)
    (s₀ : Set (Euclidean (n - 1))) (s : Set X) (hP : 0 ≤ P)
    (hphysical : ∀ v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val),
      cNorm s m (G (field β v)) ≤ P * (K + L) ^ m * (∫ η, ‖density β v η‖))
    (r : Output) :
    cNorm s₀ m (initialDatum β A Q0 r) + cNorm s m (physicalChange G β A Q0 r) ≤
      ((((m + 1 : ℕ) : ℝ) * M * Real.sqrt (unitBallVolume n) *
          C ^ ((m : ℝ) + (n : ℝ) / 2) * CA * CQ) +
        P * 2 ^ m * (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ)) *
        K ^ ((m : ℝ) + ((n : ℝ) + 1) / 2) * ‖r‖ := by
  have hi := cNorm_initialDatum_le A Q0 hn hβ hM0 hM hC hCA hK hceil hA hQ r m s₀
  have hp := cNorm_physicalChange_le A Q0 hn hβ hM0 hM hC hCA
    (lt_of_lt_of_le zero_lt_one hK) hL0 hLK hceil hA hQ G m s hP hphysical r
  convert add_le_add hi hp using 1; ring

end JanetCartan.CanonicalDataBounds
