module
public import JanetCartan.Iteration.PhysicalMean.Profiles
import all JanetCartan.Iteration.PhysicalMean.Profiles
public import JanetCartan.Iteration.PhysicalPrimary.Norms

/-!
# Fixed-geometry physical profiles of one normal completion

The normal multiplier cost and its geometric threshold precede every Picard
count. The algebra here does not reselect a threshold after the W/target/full-H
budgets. Actual producers are original110 normal-buffer, original117 FULL W and
FULL strain, actual14 normalized tensor, and original116 FULL sampled self.
This intermediate deduction becomes the actual mean profile only when those
four producers are instantiated on the SAME selected fields
(`main:eq:mean-normal-field`, `main:eq:mean-size`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Metric Finset MeasureTheory FourierTransform
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean
open CurrentMean

/-- Explicit complementary-order convolution of the fixed normal multiplier
and the full initialized/target/self budgets. No threshold is selected here. -/
def completedMeanOrderConstant (Cn CW CT CH : ℕ → ℝ) (s : ℕ) : ℝ :=
  CW s + ∑ q ∈ range (s+1), ∑ i ∈ range (q+1),
    (q.choose i : ℝ) * Cn i * (CT (q-i) + CW (q-i) + CH (q-i))

theorem completedMeanOrderConstant_nonneg (Cn CW CT CH : ℕ → ℝ)
    (hn : ∀ s, 0 ≤ Cn s) (hw : ∀ s, 0 ≤ CW s)
    (ht : ∀ s, 0 ≤ CT s) (hh : ∀ s, 0 ≤ CH s) (s : ℕ) :
    0 ≤ completedMeanOrderConstant Cn CW CT CH s := by
  unfold completedMeanOrderConstant
  apply add_nonneg (hw s)
  exact sum_nonneg fun q _ ↦ sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hn i))
      (add_nonneg (add_nonneg (ht _) (hw _)) (hh _))

/-- The actual single completion has the true physical R profile from its
primitive bounds. Only the original fixed normal multiplier is used; no new
geometric threshold may depend on the variable primitive budgets. -/
theorem completedMean_profile_of_primitive_bounds {n N : ℕ}
    (F W : Euclidean n → Euclidean N) (target H : MetricField n)
    {r a : ℝ} (hra : r < a)
    (hF : ContDiffOn ℝ ∞ F (ball 0 a)) (hW : ContDiffOn ℝ ∞ W (ball 0 a))
    (ht : ContDiffOn ℝ ∞ target (ball 0 a)) (hH : ContDiffOn ℝ ∞ H (ball 0 a))
    (hi : IsImmersionOn F (ball 0 a)) (hrank : HasFullNormalRankOn F (ball 0 a))
    (T R : ℝ) (hT : 0 ≤ T) (hTR : T ≤ R) (hR : 1 ≤ R)
    (Cn CW CT CH : ℕ → ℝ) (hCn : ∀ s, 0 ≤ Cn s)
    (hCW : ∀ s, 0 ≤ CW s) (hCT : ∀ s, 0 ≤ CT s) (hCH : ∀ s, 0 ≤ CH s)
    (hnormal : ∀ s, cNorm (closedBall 0 r) s
        (meanNormalCorrection F (target - linearizedMetric F W - H)) ≤
      ∑ q ∈ range (s+1), ∑ i ∈ range (q+1),
        (q.choose i : ℝ) * Cn i * T^i *
          cNorm (closedBall 0 r) (q-i) (target - linearizedMetric F W - H))
    (hWb : ∀ s, cNorm (closedBall 0 r) s W +
        cNorm (closedBall 0 r) s (linearizedMetric F W) ≤ CW s * R^s)
    (htb : ∀ s, cNorm (closedBall 0 r) s target ≤ CT s * R^s)
    (hHb : ∀ s, cNorm (closedBall 0 r) s H ≤ CH s * R^s)
    (s : ℕ) :
    cNorm (closedBall 0 r) s (completedMeanField F W target H) ≤
      completedMeanOrderConstant Cn CW CT CH s * R^s := by
  let D := fun q ↦ CT q + CW q + CH q
  have hD (q : ℕ) : 0 ≤ D q := add_nonneg (add_nonneg (hCT q) (hCW q)) (hCH q)
  have hstrain : ContDiffOn ℝ ∞ (linearizedMetric F W) (ball 0 a) :=
    AmbientResponse.contDiffOn_linearizedMetric isOpen_ball hF hW
  have hdef : ContDiffOn ℝ ∞ (target - linearizedMetric F W - H) (ball 0 a) :=
    (ht.sub hstrain).sub hH
  have hdatum (q : ℕ) : cNorm (closedBall 0 r) q (target - linearizedMetric F W - H) ≤
      D q * R^q := by
    have hs := cNorm_sub_local hra (ht.sub hstrain) hH q
    have hs' := cNorm_sub_local hra ht hstrain q
    have hl : cNorm (closedBall 0 r) q (linearizedMetric F W) ≤ CW q * R^q :=
      (le_add_of_nonneg_left (cNorm_nonneg _ _ W)).trans (hWb q)
    exact (hs.trans (add_le_add (hs'.trans (add_le_add (htb q) hl)) (hHb q))).trans_eq
      (by dsimp only [D]; ring)
  have hn := (hnormal s).trans <| sum_le_sum fun q _ ↦ sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_left (hdatum (q-i))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCn i)) (pow_nonneg hT i))
  have hp : cNorm (closedBall 0 r) s (meanNormalCorrection F (target - linearizedMetric F W - H)) ≤
      (∑ q ∈ range (s+1), ∑ i ∈ range (q+1), (q.choose i : ℝ) * Cn i * D (q-i)) * R^s := by
    apply hn.trans
    rw [sum_mul]
    apply sum_le_sum
    intro q hq
    rw [sum_mul]
    apply sum_le_sum
    intro i hiq
    have hqs : q ≤ s := by have := mem_range.mp hq; omega
    have hiq' : i ≤ q := by have := mem_range.mp hiq; omega
    calc
      _ ≤ (q.choose i : ℝ) * Cn i * R^i * (D (q-i) * R^(q-i)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hD _) (pow_nonneg (zero_le_one.trans hR) _))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTR i)
          (mul_nonneg (Nat.cast_nonneg _) (hCn i))
      _ = ((q.choose i : ℝ) * Cn i * D (q-i)) * R^q := by
        rw [show (q.choose i : ℝ) * Cn i * R^i * (D (q-i) * R^(q-i)) =
          ((q.choose i : ℝ) * Cn i * D (q-i)) * (R^i * R^(q-i)) by ring,
          ← pow_add, Nat.add_sub_of_le hiq']
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hqs)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCn i)) (hD _))
  change cNorm (closedBall 0 r) s (W + meanNormalCorrection F _) ≤ _
  apply (cNorm_add_local hra hW (contDiffOn_meanNormalCorrection isOpen_ball hF hdef hi hrank) s).trans
  have hw := (le_add_of_nonneg_right (cNorm_nonneg _ _ (linearizedMetric F W))).trans (hWb s)
  exact (add_le_add hw hp).trans_eq (by dsimp only [completedMeanOrderConstant,D]; ring)

/-- The lossless-order physical cutoff/Sobolev cost, before all fields,
frequencies and Picard budgets. The physical frequency remains 2πξ. -/
def physicalMeanCutoffConstant (n N : ℕ) (D : LocalDomain) (s : ℕ) : ℝ :=
  (PhysicalPrimary.exists_cutSchwartzOfSupport_physicalWeightedNorm_bound (n := n) (N := N) D s).choose

theorem physicalMeanCutoffConstant_nonneg (n N : ℕ) (D : LocalDomain) (s : ℕ) :
    0 ≤ physicalMeanCutoffConstant n N D s :=
  (PhysicalPrimary.exists_cutSchwartzOfSupport_physicalWeightedNorm_bound (n := n) (N := N) D s).choose_spec.1

/-- Lossless true-R transfer for the literal cutSchwartzOfSupport field.
The actual original support radius and buffer are explicit, not shrunk to
repair residual cancellation. No new smooth or Schwartz field is chosen. -/
theorem physicalMean_cutoff_profile {n N : ℕ} (D : LocalDomain)
    (V : Euclidean n → Euclidean N) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U)
    (hcut : tsupport (UniformStep.physicalCutoff (n := n) D) ⊆ U)
    (r : ℝ) (hr : (UniformStep.physicalCutoff (n := n) D).rOut ≤ r)
    (hrU : closedBall (0 : Euclidean n) r ⊆ U)
    (C R : ℝ) (s : ℕ) (hprofile : cNorm (closedBall 0 r) s V ≤ C*R^s) :
    (eLpNorm (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight (s : ℝ)
      ((2*Real.pi) • ξ) • 𝓕 (PhysicalCutoff.complexify
        (PhysicalPrimary.cutSchwartzOfSupport D V hU hV hcut)) ξ) 2 volume).toReal ≤
      (physicalMeanCutoffConstant n N D s * C) * R^s := by
  have hlocal : cNorm (closedBall (0 : Euclidean n)
      (UniformStep.physicalCutoff (n := n) D).rOut) s V ≤ cNorm (closedBall 0 r) s V :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hr)
      (isCompact_closedBall (0 : Euclidean n) r)
      (fun x hx ↦ (hV.contDiffAt (hU.mem_nhds (hrU hx))).of_le (by simp))
  have hb := (PhysicalPrimary.exists_cutSchwartzOfSupport_physicalWeightedNorm_bound (n := n) (N := N) D s).choose_spec.2 V hU hV hcut
  exact hb.trans ((mul_le_mul_of_nonneg_left (hlocal.trans hprofile)
    (physicalMeanCutoffConstant_nonneg n N D s)).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.PhysicalMean
end
