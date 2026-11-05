module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.FiniteSums

/-!
# Finite reconstruction multipliers on Euclidean Sobolev spaces

The finite coordinate sums used in `app:ch_response:eq:response-graded-strain`
and `app:ch_response:eq:response-reconstruction-grading`. The norm is the shared
Hilbert sum of scalar Fourier Sobolev norms, including both complex quadratures.
All L² classes use Euclidean Lebesgue measure.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ} {I J : Type*} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The literal finite coefficient product used in
`app:ch_response:eq:response-reconstruction-grading`. -/
def localizedMatrixProduct (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (u : PiLp 2 (fun _ : J ↦ L2)) : PiLp 2 (fun _ : I ↦ L2) :=
  WithLp.toLp 2 (fun i ↦ ∑ j, localizedScalarProduct (c i j) (hc i j) (hcs i j) (u j))

omit [Fintype I] in
/-- Identification of the actual L² representative in
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem localizedMatrixProduct_ae (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (u : PiLp 2 (fun _ : J ↦ L2)) (i : I) :
    localizedMatrixProduct c hc hcs u i =ᵐ[volume] fun x ↦ ∑ j, c i j x * u j x := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun j ↦ localizedScalarProduct (c i j) (hc i j) (hcs i j) (u j)),
    ae_all_iff.mpr (fun j ↦ localizedScalarProduct_ae (c i j) (hc i j) (hcs i j) (u j))]
      with x hx hxj
  exact hx.trans (Finset.sum_congr rfl fun j _ ↦ hxj j)

/-- The concrete finite matrix multiplier estimate for
`app:ch_response:eq:response-graded-strain`. Only coefficient derivatives through
`n` are consumed. The output includes actual membership, and `s` may be real. -/
theorem localizedMatrixProduct_bound (n : ℕ) {s : ℝ} (hs : s ≤ n)
    (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbudget : ∀ i j r, r ≤ n → ∀ x, ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C r)
    (u : PiLp 2 (fun _ : J ↦ L2)) (hu : MemMatrixFourierSobolev (n : ℝ) u) :
    MemMatrixFourierSobolev s (localizedMatrixProduct c hc hcs u) ∧
      matrixFourierSobolevNorm s (localizedMatrixProduct c hc hcs u) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k)) * matrixFourierSobolevNorm (n : ℝ) u := by
  classical
  let D := localizedMultiplierConstant d n * ∑ k ∈ Finset.range (n + 1), C (n - k)
  have hp (i : I) (j : J) := localizedScalarProduct_frechet_bound n (c i j)
    (hc i j) (hcs i j) C hC (hbudget i j) (u j) (hu j)
  have hb (i : I) (j : J) :
      fourierSobolevNorm s (localizedScalarProduct (c i j) (hc i j) (hcs i j) (u j)) ≤
        D * matrixFourierSobolevNorm (n : ℝ) u := by
    apply (fourierSobolevNorm_mono (hp i j).1 hs).trans
    apply (hp i j).2.trans
    calc
      _ ≤ localizedMultiplierConstant d n *
          (∑ k ∈ Finset.range (n + 1), C (n - k) * matrixFourierSobolevNorm (n : ℝ) u) := by
        apply mul_le_mul_of_nonneg_left _ (localizedMultiplierConstant_pos d n).le
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hC _)
        exact (fourierSobolevNorm_mono (hu j)
          (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans
          (fourierSobolevNorm_coordinate_le _ u j)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hr (i : I) := fourierSobolev_finsetSum Finset.univ
    (fun j ↦ localizedScalarProduct (c i j) (hc i j) (hcs i j) (u j))
    (fun j _ ↦ (hp i j).1.mono hs)
  refine ⟨fun i ↦ (hr i).1, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _i : I, ∑ _j : J, D * matrixFourierSobolevNorm (n : ℝ) u := by
      apply Finset.sum_le_sum
      intro i _
      exact (hr i).2.trans (Finset.sum_le_sum fun j _ ↦ hb i j)
    _ = _ := by simp [D]; ring

/-- The graded finite coefficient estimate consumed by the displacement and
physical derivative expansions in `app:ch_response:prop:response-graded`.
The Hilbert input bound controls each coordinate. The constant depends only on
dimension, the finite jet budgets and order, never on `A`, `L`, or `K`. -/
theorem localizedMatrixProduct_graded_bound (n : ℕ) (hn : 0 < n)
    {s : ℝ} (hs : 0 ≤ s) (hsn : s ≤ n)
    (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (C B : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hB : ∀ r, 0 ≤ B r)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (hbudget : ∀ i j r, r ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C r * L ^ r)
    (u : PiLp 2 (fun _ : J ↦ L2)) (hu : MemMatrixFourierSobolev (n : ℝ) u)
    (hub : ∀ p, p ≤ n → matrixFourierSobolevNorm (p : ℝ) u ≤ B p * A * K ^ p) :
    MemMatrixFourierSobolev s (localizedMatrixProduct c hc hcs u) ∧
      matrixFourierSobolevNorm s (localizedMatrixProduct c hc hcs u) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
          (C 0 * B 0 + localizedMultiplierConstant d n *
            ∑ k ∈ Finset.range (n + 1), C (n - k) * B k)) * A * K ^ s := by
  classical
  have hp (i : I) (j : J) := localizedScalarProduct_real_graded_bound n hn hs hsn
    (c i j) (hc i j) (hcs i j) C B hC hB hA hL hLK (hbudget i j) (u j) (hu j)
    (fun p hpn ↦ (fourierSobolevNorm_coordinate_le _ u j).trans (hub p hpn))
  have hr (i : I) := fourierSobolev_finsetSum Finset.univ
    (fun j ↦ localizedScalarProduct (c i j) (hc i j) (hcs i j) (u j))
    (fun j _ ↦ (hp i j).1)
  refine ⟨fun i ↦ (hr i).1, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _i : I, ∑ _j : J,
        (C 0 * B 0 + localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ s := by
      apply Finset.sum_le_sum
      intro i _
      exact (hr i).2.trans (Finset.sum_le_sum fun j _ ↦ (hp i j).2)
    _ = _ := by simp; ring

/-- Choosing internal accuracy `Q + b` pays the fixed polynomial coefficient
cost `ρ^b` in `app:ch_response:eq:response-graded-strain`. This is a deduction
from coefficient jets and a reduced residual bound, not an ambient bound premise. -/
theorem localizedMatrixProduct_precision_bound (n : ℕ) {s : ℝ} (hs : s ≤ n)
    (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ρ A B Q b : ℝ} (hρ : 0 < ρ)
    (hbudget : ∀ i j r, r ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C r * ρ ^ b)
    (u : PiLp 2 (fun _ : J ↦ L2)) (hu : MemMatrixFourierSobolev (n : ℝ) u)
    (hub : matrixFourierSobolevNorm (n : ℝ) u ≤ B * A * ρ ^ (-(Q + b))) :
    MemMatrixFourierSobolev s (localizedMatrixProduct c hc hcs u) ∧
      matrixFourierSobolevNorm s (localizedMatrixProduct c hc hcs u) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k)) * B * A * ρ ^ (-Q) := by
  obtain ⟨hm, hb⟩ := localizedMatrixProduct_bound n hs c hc hcs
    (fun r ↦ C r * ρ ^ b) (fun r ↦ mul_nonneg (hC r) (Real.rpow_nonneg hρ.le _))
    hbudget u hu
  refine ⟨hm, hb.trans ?_⟩
  have hpos : 0 ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
      localizedMultiplierConstant d n * ∑ k ∈ Finset.range (n + 1), C (n - k) * ρ ^ b := by
    apply mul_nonneg (mul_nonneg (by positivity) (localizedMultiplierConstant_pos d n).le)
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hC _) (Real.rpow_nonneg hρ.le _)
  apply (mul_le_mul_of_nonneg_left hub hpos).trans_eq
  rw [← Finset.sum_mul]
  have he : ρ ^ b * ρ ^ (-(Q + b)) = ρ ^ (-Q) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  calc
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * localizedMultiplierConstant d n *
        ∑ k ∈ Finset.range (n + 1), C (n - k)) * B * A *
        (ρ ^ b * ρ ^ (-(Q + b))) := by ring
    _ = _ := by rw [he]

/-- The slow coefficient grade itself supplies the polynomial cost used in
`app:ch_response:eq:response-graded-strain`: through order `n`, `L^r ≤ ρ^n`.
Thus precision `Q + n` suffices when `1 ≤ L ≤ ρ`. -/
theorem localizedMatrixProduct_graded_precision_bound (n : ℕ) {s : ℝ} (hs : s ≤ n)
    (c : I → J → E → ℂ)
    (hc : ∀ i j, ContDiff ℝ ∞ (c i j)) (hcs : ∀ i j, HasCompactSupport (c i j))
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ρ L A B Q : ℝ} (hL : 1 ≤ L) (hLρ : L ≤ ρ)
    (hbudget : ∀ i j r, r ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ r (c i j) x‖ ≤ C r * L ^ r)
    (u : PiLp 2 (fun _ : J ↦ L2)) (hu : MemMatrixFourierSobolev (n : ℝ) u)
    (hub : matrixFourierSobolevNorm (n : ℝ) u ≤ B * A * ρ ^ (-(Q + n))) :
    MemMatrixFourierSobolev s (localizedMatrixProduct c hc hcs u) ∧
      matrixFourierSobolevNorm s (localizedMatrixProduct c hc hcs u) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * localizedMultiplierConstant d n *
          ∑ k ∈ Finset.range (n + 1), C (n - k)) * B * A * ρ ^ (-Q) := by
  have hρ : 1 ≤ ρ := hL.trans hLρ
  apply localizedMatrixProduct_precision_bound n hs c hc hcs C hC (by linarith)
    (b := (n : ℝ)) _ u hu hub
  intro i j r hr x
  apply (hbudget i j r hr x).trans
  apply mul_le_mul_of_nonneg_left _ (hC r)
  rw [Real.rpow_natCast]
  exact (pow_le_pow_left₀ (by linarith) hLρ r).trans (pow_le_pow_right₀ hρ hr)

end JanetCartan.IsometricEmbedding.Reconstruction
