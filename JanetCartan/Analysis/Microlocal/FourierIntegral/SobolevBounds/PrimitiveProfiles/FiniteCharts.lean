module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.Assembly

/-!
# Primitive profiles on finitely many normalized charts

The fixed boxes in Step 3 of `app:ch_regular_base:thm:actual-calculus` need not
fit in one ball away from zero frequency. Sum the actual profiles over a fixed
finite cover. This preserves monotonicity and individual interpolation (with a
fixed larger constant), and bounds weighted jets on the entire covered carrier.
The amplitude and phase seminorm convention is the sum of their chart seminorms.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
variable {n r : ℕ} {ι : Type*} [Fintype ι]

/-- Sum of the actual primitive profiles on the fixed normalized boxes in
Step 3 of `app:ch_regular_base:thm:actual-calculus`. All positions and masks
remain inside each differentiated field. -/
def finitePrimitiveProfile (z : ι → Point n) (δ : ι → ℝ)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (a : Option (ScalarIndex n)) (j : ℕ) : ℝ :=
  ∑ i, primitiveProfile (Metric.closedBall (z i) (δ i)) S A a j

private theorem sum_profile_interpolation
    (q : ι → ℕ → ℝ) (hq : ∀ i j, 0 ≤ q i j)
    (I : ι → ℝ) (hI : ∀ i, 0 ≤ I i) {b j k : ℕ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hi : ∀ i, q i j ≤ I i * q i b ^ (1 - θ) * q i k ^ θ) :
    (∑ i, q i j) ≤ (1 + ∑ i, I i) * (∑ i, q i b) ^ (1 - θ) *
      (∑ i, q i k) ^ θ := by
  classical
  have hle (i : ι) (j : ℕ) : q i j ≤ ∑ i, q i j :=
    Finset.single_le_sum (fun i _ ↦ hq i j) (Finset.mem_univ i)
  calc
    (∑ i, q i j) ≤ ∑ i, I i * (∑ i, q i b) ^ (1 - θ) * (∑ i, q i k) ^ θ := by
      apply Finset.sum_le_sum
      intro i _
      apply (hi i).trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hq i b) (hle i b) (sub_nonneg.mpr hθ')) (hI i))
        (Real.rpow_le_rpow (hq i k) (hle i k) hθ)
        (Real.rpow_nonneg (hq i k) _)
        (mul_nonneg (hI i) (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ ↦ hq i b)) _))
    _ = (∑ i, I i) * (∑ i, q i b) ^ (1 - θ) * (∑ i, q i k) ^ θ := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ ↦ hq i k)) _)
      apply mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ ↦ hq i b)) _)

/-- Finite normalized boxes produce the complete primitive inputs for both
strong graph estimates in `StrongAssembly`. The constants are independent of
the high amplitude and phase seminorms, the low baseline precedes `s`, and the
shift is `μ₀ + 2` for every `s`. The high seminorm convention is the sum over
the fixed charts. The actual carrier cover is geometric; individual primitive
interpolation and inverse bounds are conclusions, not inputs.
Source: Step 3 and `app:ch_regular_base:eq:fio-input`. -/
theorem exists_finitePrimitiveProfile_inputs
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ s : ℕ, ∃ C I : ℝ, 1 ≤ C ∧ 1 ≤ I ∧
      ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r),
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (uncurry A)) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 2)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      (∀ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) μ₀ (uncurry A) ≤ M) →
      let q := finitePrimitiveProfile z δ S A
      let H := C * (1 + (∑ i, normalizedSeminorm (Metric.closedBall (z i) (δ i))
        (s + (μ₀ + 2)) (uncurry A)) + ∑ i, cNorm (Metric.closedBall (z i) (δ i))
          (s + (μ₀ + 2)) (fun p : Point n ↦ S p.1.1 p.2))
      (∀ a j, 0 ≤ q a j) ∧ (∀ a, Monotone (q a)) ∧ 1 ≤ H ∧
      (∀ a, q a μ₀ ≤ L) ∧ (∀ a, q a (μ₀ + s) ≤ H) ∧
      (∀ a j, μ₀ < j → j < μ₀ + s →
        q a j ≤ I * q a μ₀ ^ (1 - ((j - μ₀ : ℕ) : ℝ) / s) *
          q a (μ₀ + s) ^ (((j - μ₀ : ℕ) : ℝ) / s)) ∧
      ∀ (T : Set (Point n)) (weight : Euclidean n → ℝ), (∀ η, 0 ≤ weight η) →
        (∀ p ∈ T, ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
          p = (v.1, R • v.2) ∧ weight p.2 ≤ R) →
        (∀ p ∈ T, ∀ w, weight p.2 ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤
          q none w.length) ∧
        (∀ p ∈ T, ∀ a w,
          weight p.2 ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
            q (some a) w.length) := by
  classical
  choose L hL hs using fun i ↦ exists_primitiveProfile_inputs (r := r)
    (z i) (hδ i) (hU i) hV (hball i) (hrad i) hX hD hchart hcone μ₀ hM B
  have hLn (i) : 0 ≤ L i := zero_le_one.trans (hL i)
  refine ⟨1 + ∑ i, L i, by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hLn i)], ?_⟩
  intro s
  choose C I hC hI hb using fun i ↦ hs i s
  have hCn (i) : 0 ≤ C i := zero_le_one.trans (hC i)
  have hIn (i) : 0 ≤ I i := zero_le_one.trans (hI i)
  refine ⟨1 + ∑ i, C i, 1 + ∑ i, I i,
    by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hCn i)],
    by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hIn i)], ?_⟩
  intro S A hS hhom hinv hgap hA hbA hlowS hlowA
  dsimp only
  let q (i : ι) := primitiveProfile (Metric.closedBall (z i) (δ i)) S A
  let aH (i : ι) := normalizedSeminorm (Metric.closedBall (z i) (δ i))
    (s + (μ₀ + 2)) (uncurry A)
  let pH (i : ι) := cNorm (Metric.closedBall (z i) (δ i))
    (s + (μ₀ + 2)) (fun p : Point n ↦ S p.1.1 p.2)
  have haH (i) : 0 ≤ aH i := normalizedSeminorm_nonneg _ _ _
  have hpH (i) : 0 ≤ pH i := cNorm_nonneg _ _ _
  have hsa := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ haH i)
  have hsp := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hpH i)
  have hsc := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hCn i)
  have hi (i : ι) := hb i S A hS hhom hinv (hgap i) hA (hbA i) (hlowS i) (hlowA i)
  have hq (i a j) : 0 ≤ q i a j := (hi i).1 a j
  have hle (i a j) : q i a j ≤ finitePrimitiveProfile z δ S A a j :=
    Finset.single_le_sum (fun i _ ↦ hq i a j) (Finset.mem_univ i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a j
    exact Finset.sum_nonneg (fun i _ ↦ hq i a j)
  · intro a j k hjk
    exact Finset.sum_le_sum (fun i _ ↦ (hi i).2.1 a hjk)
  · change 1 ≤ (1 + ∑ i, C i) * (1 + (∑ i, aH i) + ∑ i, pH i)
    nlinarith
  · intro a
    exact (Finset.sum_le_sum (fun i _ ↦ (hi i).2.2.2.1 a)).trans (by linarith)
  · intro a
    change (∑ i, q i a (μ₀ + s)) ≤
      (1 + ∑ i, C i) * (1 + (∑ i, aH i) + ∑ i, pH i)
    calc
      _ ≤ ∑ i, C i * (1 + (∑ i, aH i) + ∑ i, pH i) := by
        apply Finset.sum_le_sum
        intro i _
        apply ((hi i).2.2.2.2.1 a).trans
        apply mul_le_mul_of_nonneg_left _ (hCn i)
        have h₁ := Finset.single_le_sum (fun i _ ↦ haH i) (Finset.mem_univ i)
        have h₂ := Finset.single_le_sum (fun i _ ↦ hpH i) (Finset.mem_univ i)
        dsimp only [aH, pH] at h₁ h₂ ⊢
        linarith
      _ = (∑ i, C i) * (1 + (∑ i, aH i) + ∑ i, pH i) := by rw [Finset.sum_mul]
      _ ≤ _ := by nlinarith
  · intro a j hj hj'
    apply sum_profile_interpolation (fun i j ↦ q i a j) (fun i j ↦ hq i a j) I hIn
    · positivity
    · apply (div_le_one (by exact_mod_cast (show 0 < s by omega))).mpr
      exact_mod_cast (show j - μ₀ ≤ s by omega)
    · intro i
      exact (hi i).2.2.2.2.2.1 a j hj hj'
  · intro T weight hw hcover
    have hlocal (p) (hp : p ∈ T) : ∃ i,
        (∀ w, weight p.2 ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤ q i none w.length) ∧
        (∀ a w, weight p.2 ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
          q i (some a) w.length) := by
      obtain ⟨i, R, hR, v, hv, he, hwR⟩ := hcover p hp
      have hs := (hi i).2.2.2.2.2.2 {p} weight hw
        (by intro p' hp'; rw [Set.mem_singleton_iff] at hp'; subst p'
            exact ⟨R, hR, v, hv, he, hwR⟩)
      exact ⟨i, hs.1 p (Set.mem_singleton p), hs.2 p (Set.mem_singleton p)⟩
    constructor
    · intro p hp w
      obtain ⟨i, hA, _⟩ := hlocal p hp
      exact (hA w).trans (hle i none w.length)
    · intro p hp a w
      obtain ⟨i, _, hS⟩ := hlocal p hp
      exact (hS a w).trans (hle i (some a) w.length)

end JanetCartan.FourierIntegral.PrimitiveProfiles
