module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Perturbation
public import JanetCartan.Iteration.PhysicalInverseContinuity.Reserve
public import JanetCartan.Iteration.PhysicalRawInterpolation

/-!
# Fixed-source raw inverse tolerances in the full original finite grade

The common high budget comes from the zero-density estimate at a reserved
high grade with **zero** scale exponent. Only after fixing it do we choose the
interpolation frequency, the required base-norm accuracy, and the normal,
residual and fixed-vector adjoint tolerances. All are independent of the
subsequent current row or history. This is the quantitative final transfer
used by `app:ch_background:prop:bg-normalized`; the actual sources of its
three errors are kept separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow CarrierSobolev CoerciveInverse PhysicalRawInterpolation

/-- Fixed-σ final full-grade transfer, with the exact half-tolerance needed
for admission. The high residual cap, reference datum and fixed original gap
are before the current history; the actual `m+1` estimate's history exponent
vanishes by the pre-accuracy reserve. The inner carrier quadratures, cutoff,
unitary weights and uncut exterior component are unchanged. -/
theorem exists_raw_grade_perturbation_tolerance
    {n : ℕ} {ι : Type*} [Fintype ι] (A₀ : AugmentedInput n ι →L[ℝ] OutputL2 n)
    (e₀ : OutputL2 n) {γ γ₀ : ℝ} (hγ : 0 < γ) (hγ₀ : 0 < γ₀)
    (hgap₀ : ∀ w, γ₀ * ‖w‖ ^ 2 ≤ ‖A₀.adjoint w‖ ^ 2)
    {m rStar Bcan : ℕ} (hreserve : m + 1 + Bcan ≤ rStar)
    {Czero Be : ℝ} (hCzero : 0 ≤ Czero) (hBe : 0 ≤ Be)
    (hseed : rightInverse A₀ e₀ ∈ (augmentedInputSobolevScale n ι).level (m + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ (A : AugmentedInput n ι →L[ℝ] OutputL2 n) (e : OutputL2 n) (T : ℝ),
      (∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2) →
      e ∈ (periodicSobolevScale n (Euclidean n)).level (m + 1) →
      (periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) e ≤ Be →
      rightInverse A e ∈ (augmentedInputSobolevScale n ι).level (m + 1) →
      (periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) ((normalOperator A).inverse e) +
        (augmentedInputSobolevScale n ι).gradeNorm (m + 1) (rightInverse A e) ≤
          Czero * ((periodicSobolevScale n (Euclidean n)).gradeNorm (m + 1) e +
            T ^ ((m + 1) - (rStar - Bcan)) * ‖e‖) →
      ‖e - e₀‖ ≤ η → ‖normalOperator A - normalOperator A₀‖ ≤ η →
      ‖(A.adjoint - A₀.adjoint) ((normalOperator A₀).inverse e₀)‖ ≤ η →
      (augmentedInputSobolevScale n ι).gradeNorm m (rightInverse A e - rightInverse A₀ e₀) ≤ δ / 2 := by
  let X := augmentedInputSobolevScale n ι
  let D := (Fintype.card ι : ℝ) + 2
  have hD : 0 < D := by dsimp [D]; positivity
  let B := Czero * (Be + Be) + X.gradeNorm (m + 1) (rightInverse A₀ e₀)
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hCzero (add_nonneg hBe hBe)) (X.gradeNorm_nonneg ..)
  let K := 1 + 4 * D * B / δ
  have hK : 1 ≤ K := le_add_of_nonneg_right (div_nonneg (by positivity) hδ.le)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have htop : D * (K⁻¹ * B) ≤ δ / 4 := by
    have he : K * δ = δ + 4 * D * B := by dsimp only [K]; field_simp
    calc
      _ = D * B / K := by ring
      _ ≤ δ / 4 := (div_le_iff₀ hKpos).mpr (by nlinarith only [he, hδ.le])
  let L := δ / (4 * D * K ^ m)
  have hL : 0 < L := div_pos hδ (by positivity)
  have hlow : D * (K ^ m * L) = δ / 4 := by
    dsimp only [L]
    field_simp [hD.ne', hKpos.ne']
  obtain ⟨η, hη, hbase⟩ := exists_raw_L2_perturbation_tolerance A₀ e₀ hγ hγ₀ hgap₀ hL
  refine ⟨η, hη, ?_⟩
  intro A e T hgap he hcap hraw hcurrent hdiff hnormal hadj
  obtain ⟨hu, hhigh⟩ := raw_sub_gradeNorm_le_of_fixed_reserve A A₀ e e₀ hreserve hCzero
    he hcap hraw hseed hcurrent
  let u := rightInverse A e - rightInverse A₀ e₀
  have hu₀ : ‖u‖ ≤ L := hbase A e hgap hdiff hnormal hadj
  have hu₁ : X.gradeNorm (m + 1) u ≤ B := hhigh
  calc
    X.gradeNorm m u ≤ D * (K ^ m * ‖u‖ + K⁻¹ * X.gradeNorm (m + 1) u) :=
      augmentedInput_gradeNorm_le_scaled_endpoints m hK u hu
    _ ≤ D * (K ^ m * L + K⁻¹ * B) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hu₀ (pow_nonneg hKpos.le m))
        (mul_le_mul_of_nonneg_left hu₁ (inv_nonneg.mpr hKpos.le))) hD.le
    _ = D * (K ^ m * L) + D * (K⁻¹ * B) := mul_add ..
    _ ≤ δ / 4 + δ / 4 := add_le_add hlow.le htop
    _ = δ / 2 := by ring

end JanetCartan.PhysicalInverseContinuity
