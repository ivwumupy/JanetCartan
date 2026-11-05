module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds.Continuity

/-!
# Symbol jets on a finite buffered annular cover

For `app:ch_seed:prop:seed-actual-menu`, Step 1, local estimates assemble on
any fixed finite cover of the working compact annulus. The physical balls
lie in the construction set. The cover and the nonzero-covector buffers are
geometric inputs, independent of the current frame and the derivative order.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.NormalizedSymbolBounds

/-- A fixed finite buffered cover gives the annular one-high bound with
reserve zero, independent of `r` (`app:ch_seed:prop:seed-actual-menu`, Step 1).
The physical construction seminorm controls every chart, and the constant
is chosen before the frame. No symbol derivative bound is an input. -/
theorem exists_cNorm_symbol_le_frame_finiteCover {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n × Euclidean n) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hzero : ∀ i, ∀ ξ ∈ Metric.closedBall (a i).2 (ρ i), ξ ≠ 0)
    {K : Set (Euclidean n × Euclidean n)} {B : Set (Euclidean n)} (hB : IsCompact B)
    (hcover : ∀ z ∈ K, ∃ i, z ∈ Metric.closedBall (a i) (ρ i))
    (hphysical : ∀ i, Metric.closedBall (a i).1 (ρ i) ⊆ B) (M : ℝ) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U → B ⊆ U →
      ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiffOn ℝ ∞ Q U → (∀ x ∈ B, ‖Q x‖ ≤ M) →
      cNorm K r (normalizedSymbol Q) ≤
        C * (1 + cNorm B r Q) := by
  classical
  choose C hC hb using fun i ↦
    exists_cNorm_symbol_le_frame_contDiffOn (a i) (hρ i) (hzero i) M r
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨(r + 1 : ℝ) * (1 + ∑ i, C i), by positivity, ?_⟩
  intro U hU hBU Q hQ hM
  have hFat : ∀ x ∈ B, ContDiffAt ℝ ∞ Q x := fun x hx ↦
    (hQ x (hBU hx)).contDiffAt (hU.mem_nhds (hBU hx))
  have hlocal (i : ι) : cNorm (Metric.closedBall (a i) (ρ i)) r
      (normalizedSymbol Q) ≤
      (1 + ∑ j, C j) * (1 + cNorm B r Q) := by
    apply (hb i U hU ((hphysical i).trans hBU) Q hQ
      (fun x hx ↦ hM x (hphysical i hx))).trans
    have hm := cNorm_mono_set_of_contDiffAt (hphysical i) hB
      (fun x hx ↦ (hFat x hx).of_le (by simp : (r : ℕ∞ω) ≤ ∞))
    have hi : C i ≤ 1 + ∑ j, C j := by
      have := Finset.single_le_sum (s := Finset.univ) (f := C)
        (fun j _ ↦ (hC j).le) (Finset.mem_univ i)
      linarith
    exact mul_le_mul hi (by linarith) (by positivity [cNorm_nonneg (Metric.closedBall (a i).1 (ρ i)) r Q])
      (by positivity)
  have hjets : ∀ j ≤ r, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (normalizedSymbol Q) z‖ ≤
        (1 + ∑ i, C i) * (1 + cNorm B r Q) := by
    intro j hj z hz
    obtain ⟨i, hi⟩ := hcover z hz
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun w hw ↦ ?_) hi hj).trans (hlocal i)
    have hw' : max (dist w.1 (a i).1) (dist w.2 (a i).2) ≤ ρ i := hw
    exact (contDiffAt_normalizedSymbol (hFat w.1 (hphysical i ((le_max_left _ _).trans hw')))
      (hzero i w.2 ((le_max_right _ _).trans hw'))).of_le (by simp)
  have hh := cNorm_le_sum_of_bounds (fun j (_ : j ≤ r) ↦
    mul_nonneg (by positivity : 0 ≤ 1 + ∑ i, C i)
      (add_nonneg zero_le_one (cNorm_nonneg B r Q))) hjets
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, ← mul_assoc] using hh

/-- Finite-order continuity on a fixed annular cover follows from frame
closeness on the construction set, with no loss of derivatives
(`app:lem:common-hamilton-phase`). Constants depend on the cover, frozen frame,
order and tolerance, and are independent of the perturbed frame. -/
theorem exists_symbol_comparison_radius_finiteCover {n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (a : ι → Euclidean n × Euclidean n) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hzero : ∀ i, ∀ ξ ∈ Metric.closedBall (a i).2 (ρ i), ξ ≠ 0)
    {K : Set (Euclidean n × Euclidean n)} {B : Set (Euclidean n)} (hB : IsCompact B)
    (hcover : ∀ z ∈ K, ∃ i, z ∈ Metric.closedBall (a i) (ρ i))
    (hphysical : ∀ i, Metric.closedBall (a i).1 (ρ i) ⊆ B)
    (Q₀ : Fin n → MetricTensor n) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U → B ⊆ U →
      ∀ Q : Euclidean n → Fin n → MetricTensor n, ContDiffOn ℝ ∞ Q U →
      cNorm B m (Q - fun _ ↦ Q₀) < δ →
      cNorm K m (normalizedSymbol Q - normalizedSymbol (fun _ ↦ Q₀)) < ε := by
  classical
  let η := ε / (2 * (m + 1 : ℝ))
  have hη : 0 < η := div_pos hε (by positivity)
  choose d hd hb using fun i ↦ exists_symbol_comparison_radius_contDiffOn
    (a i) (hρ i) (hzero i) Q₀ m hη
  refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun i _ ↦ hd i)
  intro U hU hBU Q hQ hsmall
  have hFat : ∀ x ∈ B, ContDiffAt ℝ ∞ Q x := fun x hx ↦
    (hQ x (hBU hx)).contDiffAt (hU.mem_nhds (hBU hx))
  let e := normalizedSymbol Q - normalizedSymbol (fun _ ↦ Q₀)
  have he (i : ι) : ∀ z ∈ Metric.closedBall (a i) (ρ i), ContDiffAt ℝ m e z := by
    intro z hz
    have hz' : max (dist z.1 (a i).1) (dist z.2 (a i).2) ≤ ρ i := hz
    have hξ := hzero i z.2 ((le_max_right _ _).trans hz')
    exact ((contDiffAt_normalizedSymbol (hFat z.1 (hphysical i ((le_max_left _ _).trans hz'))) hξ).sub
      (contDiffAt_normalizedSymbol (Q := fun _ ↦ Q₀) contDiffAt_const hξ)).of_le (by simp)
  have hl (i : ι) : cNorm (Metric.closedBall (a i) (ρ i)) m e < η := by
    apply hb i U hU ((hphysical i).trans hBU) Q hQ
    apply (cNorm_mono_set_of_contDiffAt (hphysical i) hB
      (fun x hx ↦ ((hFat x hx).sub contDiffAt_const).of_le (by simp))).trans_lt
    exact hsmall.trans_le (Finset.inf'_le d (Finset.mem_univ i))
  have hjets : ∀ j ≤ m, ∀ z ∈ K, ‖iteratedFDeriv ℝ j e z‖ ≤ η := by
    intro j hj z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (he i) hi hj).trans (hl i).le
  have hh := cNorm_le_sum_of_bounds (fun _ (_ : _ ≤ m) ↦ hη.le) hjets
  have hsum : (∑ _j ∈ Finset.range (m + 1), η) = (m + 1 : ℝ) * η := by simp
  have hηeq : η * (2 * (m + 1 : ℝ)) = ε := div_mul_cancel₀ _ (by positivity)
  exact hh.trans_lt (by rw [hsum]; nlinarith)

/-- The annular symbol budget for order `r` phase construction has the fixed
immersion reserve three (`app:ch_seed:eq:seed-frame-tame`). The only quantitative
analytic input is the primitive frame estimate with reserve two. -/
theorem exists_symbol_phase_input_finiteCover {n N : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n × Euclidean n) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hzero : ∀ i, ∀ ξ ∈ Metric.closedBall (a i).2 (ρ i), ξ ≠ 0)
    {K : Set (Euclidean n × Euclidean n)} {B : Set (Euclidean n)} (hB : IsCompact B)
    (hcover : ∀ z ∈ K, ∃ i, z ∈ Metric.closedBall (a i) (ρ i))
    (hphysical : ∀ i, Metric.closedBall (a i).1 (ρ i) ⊆ B)
    (M : ℝ) (r : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C > (0 : ℝ), ∀ (U : Set (Euclidean n)), IsOpen U → B ⊆ U →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
      (F : Euclidean n → Euclidean N), ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ B, ‖Q x‖ ≤ M) →
      cNorm B (r + 1) Q ≤ D * (1 + cNorm B (r + 3) F) →
      cNorm K (r + 1) (normalizedSymbol Q) ≤
        C * (1 + cNorm B (r + 3) F) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_symbol_le_frame_finiteCover a ρ hρ hzero
    hB hcover hphysical M (r + 1)
  refine ⟨C * (1 + D), by positivity, ?_⟩
  intro U hU hBU Q F hQ hM hframe
  apply (hb U hU hBU Q hQ hM).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith [cNorm_nonneg B (r + 3) F]

end JanetCartan.ActualCarriers.NormalizedSymbolBounds
