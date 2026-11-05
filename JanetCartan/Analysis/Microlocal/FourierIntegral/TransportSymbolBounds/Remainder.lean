module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.JointDerivatives

/-!
# Joint derivatives of the complete transport remainder

The actual derivative of `b₋₁` is used in
`app:ch_regular_base:eq:direct-graph-identity`. The primitive budget is `n + 1`,
not one order-`n` budget for each factor. The term `B b₋₁` is retained.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff
namespace JanetCartan.FourierIntegral
variable {E ι R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [NormedRing R] [NormedAlgebra ℂ R]
local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- Joint Leibniz estimate for the full expression in
`app:ch_regular_base:eq:direct-graph-identity`, before substituting the actual
correction and its derivatives. -/
theorem norm_iteratedFDeriv_transportRemainder_le {N : ℕ∞ω}
    {A db : ι → E → R} {B b : E → R}
    (hA : ∀ j, ContDiff ℝ N (A j)) (hdb : ∀ j, ContDiff ℝ N (db j))
    (hB : ContDiff ℝ N B) (hb : ContDiff ℝ N b) (x : E) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
      (fun j ↦ db j y) (B y) (b y)) x‖ ≤
      (∑ j, transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k (A j) x‖)
        (fun k ↦ ‖iteratedFDeriv ℝ k (db j) x‖) n) +
      transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k B x‖)
        (fun k ↦ ‖iteratedFDeriv ℝ k b x‖) n := by
  have hp (j : ι) := ((hA j).mul (hdb j)).of_le hn
  have hsum := ContDiff.sum (fun j (_ : j ∈ Finset.univ) ↦ hp j)
  have hprod := (hB.mul hb).of_le hn
  simp only [transportRemainder,
    iteratedFDeriv_const_smul_apply' (hsum.add hprod).contDiffAt,
    fun_iteratedFDeriv_add_apply hsum.contDiffAt hprod.contDiffAt,
    norm_smul, norm_neg, Complex.norm_I, one_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hp j).contDiffAt)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
      norm_iteratedFDeriv_mul_le (hA j) (hdb j) x hn)
  · exact norm_iteratedFDeriv_mul_le hB hb x hn

/-- A physical directional derivative uses exactly one additional joint jet,
as needed for `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem norm_iteratedFDeriv_directional_le {N : ℕ∞ω} {f : E → R}
    (hf : ContDiff ℝ N f) (x v : E) (n : ℕ) (hn : (n : ℕ∞ω) + 1 ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hD := hf.fderiv_right (m := n) hn
  simpa only [norm_iteratedFDeriv_fderiv] using
    (norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) hD.contDiffAt le_rfl)

/-- The complete remainder is bounded by derivatives of the supplied
primitives only. In `app:ch_regular_base:eq:direct-graph-identity`, take `v j`
to be the physical coordinate directions in the joint chart. No bound on the
correction amplitude or its derivative is a hypothesis. -/
theorem norm_iteratedFDeriv_completeTransportRemainder_le
    (n : ℕ) {A : ι → E → R} {B : E → R}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hA : ∀ j, ContDiff ℝ n (A j)) (hB : ContDiff ℝ n B)
    (hc1 : ∀ j, ContDiff ℝ (n + 1) (c1 j))
    (hdU : ∀ j, ContDiff ℝ (n + 1) (dU j))
    (hc2 : ∀ j l, ContDiff ℝ (n + 1) (c2 j l))
    (hS : ∀ j l, ContDiff ℝ (n + 1) (S j l))
    (hU : ContDiff ℝ (n + 1) U) (x : E) (v : ι → E) :
    let b := fun y ↦ correctionAmplitude (fun j ↦ c1 j y) (fun j ↦ dU j y)
      (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)
    let Q := correctionDerivativeBound (fun j k ↦ ‖iteratedFDeriv ℝ k (c1 j) x‖)
      (fun j k ↦ ‖iteratedFDeriv ℝ k (dU j) x‖)
      (fun j l k ↦ ‖iteratedFDeriv ℝ k (c2 j l) x‖)
      (fun j l k ↦ ‖iteratedFDeriv ℝ k (S j l) x‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k U x‖)
    ‖iteratedFDeriv ℝ n (fun y ↦ transportRemainder (fun j ↦ A j y)
      (fun j ↦ fderiv ℝ b y (v j)) (B y) (b y)) x‖ ≤
      (∑ j, transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k (A j) x‖)
        (fun k ↦ ‖v j‖ * Q (k + 1)) n) +
        transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k B x‖) Q n := by
  intro b Q
  have hb : ContDiff ℝ (n + 1) b := contDiff_correctionAmplitude hc1 hdU hc2 hS hU
  have hb0 : ContDiff ℝ n b := hb.of_le (by exact_mod_cast Nat.le_succ n)
  have hdb (j : ι) : ContDiff ℝ n (fun y ↦ fderiv ℝ b y (v j)) :=
    (hb.fderiv_right (m := n) (by simp)).clm_apply contDiff_const
  have hQ (k : ℕ) (hk : k ≤ n + 1) : ‖iteratedFDeriv ℝ k b x‖ ≤ Q k :=
    norm_iteratedFDeriv_correctionAmplitude_le hc1 hdU hc2 hS hU x k
      (by exact_mod_cast hk)
  apply (norm_iteratedFDeriv_transportRemainder_le hA hdb hB hb0 x n le_rfl).trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    refine transportLeibnizBound_mono (fun _ _ ↦ norm_nonneg _) ?_ (fun _ _ ↦ le_rfl) ?_
    · intro k hk
      have hk' : k + 1 ≤ n + 1 := Nat.add_le_add_right hk 1
      exact mul_nonneg (norm_nonneg _) ((norm_nonneg (iteratedFDeriv ℝ (k + 1) b x)).trans (hQ _ hk'))
    · intro k hk
      apply (norm_iteratedFDeriv_directional_le hb x (v j) k
        (by exact_mod_cast Nat.add_le_add_right hk 1)).trans
      exact mul_le_mul_of_nonneg_left (hQ _ (Nat.add_le_add_right hk 1)) (norm_nonneg _)
  · exact transportLeibnizBound_mono (fun _ _ ↦ norm_nonneg _)
      (fun k hk ↦ (norm_nonneg (iteratedFDeriv ℝ k b x)).trans (hQ k (hk.trans (Nat.le_succ n))))
      (fun _ _ ↦ le_rfl) (fun k hk ↦ hQ k (hk.trans (Nat.le_succ n)))

end JanetCartan.FourierIntegral
