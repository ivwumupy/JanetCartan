module
public import JanetCartan.Iteration.PhysicalMean.FullHermitianProfiles
import all JanetCartan.Iteration.PhysicalMean.PhysicalHermitianProfile
public import JanetCartan.Iteration.PhysicalMean.CanonicalPhysicalIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension
/-!
# Exact local joins for the original full sampled Hermitian tensor

Consumers: the original fullSampledSelf54 physical profile and
`main:eq:mean-normal-field`. These deductions preserve the single sample,
original weight once, unscaled baseline and complete native source. The local
baseline is used only through its germs on the unchanged positive-radius
physical buffer; the existing global full-self estimate is reused verbatim.
Actual baseline112, source15 and common Picard14 inputs remain explicit here
and are discharged in OriginalSelectedHermitianProfiles.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
open CurrentMean
/-- The full source tensor uses the original weight once. A zero outer weight
needs no baseline/source equality (main:eq:mean-normal-field). -/
theorem weighted_full_self_eq_on_active {n N : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (Z W : ι → Matrix (Fin N) (Fin n) ℂ)
    (h : ∀ i, μ i ≠ 0 → Z i = W i) :
    (∑ i, μ i • hermitianTensor (Z i)) = ∑ i, μ i • hermitianTensor (W i) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : μ i = 0
  · simp only [hi,zero_smul]
  · rw [h i hi]

/-- Combine the actual baseline and complete native-source profiles BEFORE the
full Hermitian square, with the released O(1) mass and complementary orders.
The source scale h is only bounded by one, never by an inverse sample count.
Inputs are supplied by actual baseline112/source15/Picard14 producers; this
lemma alone is not an actual original-data profile (main:prop:mean). -/
theorem weighted_full_base_change_profile {n N : ℕ} {ι : Type*} [Fintype ι]
    {K : Set (Euclidean n)} (hK : IsCompact K) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (B D : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hB : ∀ i, μ i ≠ 0 → ContDiff ℝ ∞ (B i))
    (hD : ∀ i, μ i ≠ 0 → ContDiff ℝ ∞ (D i))
    (CB CD : ℕ → ℝ) (hCB : ∀ q, 0 ≤ CB q) (hCD : ∀ q, 0 ≤ CD q)
    {R h Cweight : ℝ} (hR : 1 ≤ R) (hh : h ≤ 1)
    (hmass : ∑ i, μ i ≤ Cweight) (s : ℕ)
    (hBp : ∀ i, μ i ≠ 0 → ∀ q, q ≤ s → cNorm K q (B i) ≤ CB q*R^q)
    (hDp : ∀ i, μ i ≠ 0 → ∀ q, q ≤ s → cNorm K q (D i) ≤ CD q*h*R^q) :
    cNorm K s (fun x ↦ weightedHermitianTensor μ (fun y i ↦ B i y+D i y) x) ≤
      (Cweight*hermitianPhysicalOrderConstant (fun q ↦ CB q+CD q) s)*R^s := by
  apply FullHermitianProfiles.weighted_full_self_profile hK μ hμ (fun i x ↦ B i x+D i x)
    (fun i hi ↦ (hB i hi).add (hD i hi)) (fun q ↦ CB q+CD q)
    (fun q ↦ add_nonneg (hCB q) (hCD q)) hR hmass s
  intro i hi q hq
  have hd : CD q*h*R^q ≤ CD q*R^q :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hCD q) hh)
      (pow_nonneg (zero_le_one.trans hR) q)
  exact ((cNorm_add_le hK ((hB i hi).of_le (by simp)) ((hD i hi).of_le (by simp))).trans
    (add_le_add (hBp i hi q hq) ((hDp i hi q hq).trans hd))).trans_eq (by ring)
/-- The original baseline112 provides ambient jet bounds on its whole chart,
not an artificial global smoothness hypothesis. Existing germ-preserving smooth
extensions are used only inside this proof; the tensor on the left is unchanged.
The compact ball may be the full physical buffer11a/12, without shrinking it
(main:prop:mean; main:eq:mean-normal-field). -/
theorem weighted_full_base_change_profile_on_chart {n N : ℕ} {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hKU : closedBall 0 r ⊆ U) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (B D : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hB : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (B i) U)
    (hD : ∀ i, μ i ≠ 0 → ContDiff ℝ ∞ (D i))
    (CB CD : ℕ → ℝ) (hCB : ∀ q, 0 ≤ CB q) (hCD : ∀ q, 0 ≤ CD q)
    {R h Cweight : ℝ} (hR : 1 ≤ R) (hh : h ≤ 1)
    (hmass : ∑ i, μ i ≤ Cweight) (s : ℕ)
    (hBp : ∀ i, μ i ≠ 0 → ∀ q, q ≤ s → ∀ x ∈ closedBall 0 r,
      ‖iteratedFDeriv ℝ q (B i) x‖ ≤ CB q*R^q)
    (hDp : ∀ i, μ i ≠ 0 → ∀ q, q ≤ s → cNorm (closedBall 0 r) q (D i) ≤ CD q*h*R^q) :
    cNorm (closedBall 0 r) s
        (fun x ↦ weightedHermitianTensor μ (fun y i ↦ B i y+D i y) x) ≤
      (Cweight*hermitianPhysicalOrderConstant
        (fun q ↦ (∑ j ∈ Finset.range (q+1), CB j)+CD q) s)*R^s := by
  classical
  have hext : ∀ i, ∃ B' : Euclidean n → Matrix (Fin N) (Fin n) ℂ,
      ContDiff ℝ ∞ B' ∧ ∀ x ∈ closedBall 0 r, μ i ≠ 0 → B' =ᶠ[𝓝 x] B i := by
    intro i
    by_cases hi : μ i = 0
    · exact ⟨fun _ ↦ 0,contDiff_const,fun _ _ hne ↦ False.elim (hne hi)⟩
    · obtain ⟨B',hB',_,_,he⟩ := ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall
        (0 : Euclidean n) hr hU hKU (hB i hi)
      exact ⟨B',hB',fun x hx _ ↦ he x hx⟩
  choose B' hB' he using hext
  have hnorm (i : ι) (hi : μ i ≠ 0) (q : ℕ) :
      cNorm (closedBall 0 r) q (B' i) = cNorm (closedBall 0 r) q (B i) :=
    GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦ he i x hx hi) q
  have hfull : cNorm (closedBall 0 r) s
      (fun x ↦ weightedHermitianTensor μ (fun y i ↦ B' i y+D i y) x) =
      cNorm (closedBall 0 r) s
      (fun x ↦ weightedHermitianTensor μ (fun y i ↦ B i y+D i y) x) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    have hh : ∀ᶠ y in 𝓝 x, ∀ i, μ i ≠ 0 → B' i y = B i y := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hi : μ i = 0
      · exact Filter.Eventually.of_forall (fun _ hne ↦ False.elim (hne hi))
      · exact (he i x hx hi).mono (fun _ h _ ↦ h)
    filter_upwards [hh] with y hy
    apply weighted_full_self_eq_on_active
    intro i hi
    change B' i y+D i y = B i y+D i y
    rw [hy i hi]
  rw [← hfull]
  apply weighted_full_base_change_profile (isCompact_closedBall 0 r) μ hμ B' D
    (fun i _ ↦ hB' i) hD (fun q ↦ ∑ j ∈ Finset.range (q+1), CB j) CD
    (fun _ ↦ Finset.sum_nonneg (fun j _ ↦ hCB j)) hCD hR hh hmass s
  · intro i hi q hq
    rw [hnorm i hi q]
    apply (cNorm_le_sum_of_bounds (fun j _ ↦ mul_nonneg (hCB j)
      (pow_nonneg (zero_le_one.trans hR) j))
      (fun j hj x hx ↦ hBp i hi j (hj.trans hq) x hx)).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hR (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (hCB j)
  · exact hDp
/-- The original χ₂ support already lies in the full source chart. Any buffer
within its inner radius is therefore admissible for the baseline/source germs;
no comparison with the smaller background core occurs (main:prop:mean). -/
theorem original_buffer_subset_source_chart {n : ℕ}
    (χ : ContDiffBump (0 : Euclidean n)) {U : Set (Euclidean n)}
    (hχ : tsupport χ ⊆ U) {r : ℝ} (hr : r ≤ χ.rIn) : closedBall 0 r ⊆ U := by
  intro x hx
  have hone := χ.one_of_mem_closedBall (closedBall_subset_closedBall hr hx)
  exact hχ (subset_tsupport χ (hone.trans_ne one_ne_zero))
/-- Nonnegativity of the exact baseline-plus-complete-source budget used for
CH_N, before any physical history or target is supplied (main:prop:mean). -/
theorem full_hermitian_budget_nonneg (Cweight : ℝ) (CB CD : ℕ → ℝ)
    (hCweight : 0 ≤ Cweight) (hCB : ∀ q, 0 ≤ CB q) (hCD : ∀ q, 0 ≤ CD q) (s : ℕ) :
    0 ≤ Cweight*hermitianPhysicalOrderConstant
      (fun q ↦ (∑ j ∈ Finset.range (q+1), CB j)+CD q) s :=
  mul_nonneg hCweight (hermitianPhysicalOrderConstant_nonneg _
    (fun q ↦ add_nonneg (Finset.sum_nonneg (fun j _ ↦ hCB j)) (hCD q)) s)
/-- Transfer the SAME canonical periodic baseline from its full-parent slice
on the whole source chart, then use T≤R. No inner angular support or global
smoothness premise is introduced (main:eq:mean-normal-field; main:prop:mean). -/
theorem sampled_baseline_profile_of_parent {n N : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U) (B P : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (heq : ∀ x ∈ U, B x = P x) (hP : ContDiffOn ℝ ∞ P U)
    (CB : ℕ → ℝ) (hCB : ∀ q, 0 ≤ CB q) {T R : ℝ} (hT : 0 ≤ T) (hTR : T ≤ R)
    (hjets : ∀ q x, x ∈ U → ‖iteratedFDeriv ℝ q P x‖ ≤ CB q*T^q) :
    ContDiffOn ℝ ∞ B U ∧ ∀ q x, x ∈ U → ‖iteratedFDeriv ℝ q B x‖ ≤ CB q*R^q := by
  refine ⟨hP.congr heq, ?_⟩
  intro q x hx
  have he : B =ᶠ[𝓝 x] P := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  exact (hjets q x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTR q) (hCB q))

/-- The unchanged buffer has the same full-tensor seminorm as its exact native
B+D expression, using whole-chart germs rather than a smaller core
(main:eq:mean-normal-field). -/
theorem full_self_cNorm_eq_native_on_chart {n N : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (Euclidean n)} (hU : IsOpen U) {r : ℝ} (hKU : closedBall 0 r ⊆ U)
    (μ : ι → ℝ) (B D : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (heq : ∀ x ∈ U, H x = weightedHermitianTensor μ (fun y i ↦ B i y+D i y) x) (s : ℕ) :
    cNorm (closedBall 0 r) s H = cNorm (closedBall 0 r) s
      (fun x ↦ weightedHermitianTensor μ (fun y i ↦ B i y+D i y) x) := by
  apply GeometricProfile.cNorm_eq_of_eventuallyEq
  intro x hx
  filter_upwards [hU.mem_nhds (hKU hx)] with y hy
  exact heq y hy
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.weighted_full_self_eq_on_active
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.weighted_full_base_change_profile
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.weighted_full_base_change_profile_on_chart
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.original_buffer_subset_source_chart
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.full_hermitian_budget_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sampled_baseline_profile_of_parent
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.full_self_cNorm_eq_native_on_chart
