module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Polarization retains the current-transport gain

The algebraic estimate in `app:ch_mean_pairs:eq:mean-density-lipschitz`.
The inputs are linear amplitude estimates and a bilinear product estimate;
no estimate on the quadratic discrepancy is assumed.
-/

@[expose] public noncomputable section
namespace JanetCartan.DensityDiscrepancy

variable {A V Y : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: difference of the actual
current and transport squares for a given bilinear polarization. -/
def squareDiscrepancy (B : V →ₗ[ℝ] V →ₗ[ℝ] Y) (U T : A →ₗ[ℝ] V) (a : A) : Y :=
  B (U a) (U a) - B (T a) (T a)

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: every term contains one
current-transport difference; no symmetry of the polarization is required. -/
theorem squareDiscrepancy_eq (B : V →ₗ[ℝ] V →ₗ[ℝ] Y) (U T : A →ₗ[ℝ] V) (a : A) :
    squareDiscrepancy B U T a = B ((U - T) a) (U a) + B (T a) ((U - T) a) := by
  simp only [squareDiscrepancy, LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
  abel

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: four-term polarization
of two discrepancies. The small linear error is retained in every term. -/
theorem squareDiscrepancy_sub_eq (B : V →ₗ[ℝ] V →ₗ[ℝ] Y)
    (U T : A →ₗ[ℝ] V) (a b : A) :
    squareDiscrepancy B U T a - squareDiscrepancy B U T b =
      B ((U - T) (a - b)) (U a) + B ((U - T) b) (U (a - b)) +
      B (T (a - b)) ((U - T) a) + B (T b) ((U - T) (a - b)) := by
  simp only [squareDiscrepancy, LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
  abel

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: linear operator bounds
imply the quadratic Lipschitz bound. `p` and `N` can be finite-jet seminorms;
`q` is the desired output seminorm. `δ` will be `λ⁻¹`. -/
theorem squareDiscrepancy_sub_le
    (B : V →ₗ[ℝ] V →ₗ[ℝ] Y) (U T : A →ₗ[ℝ] V)
    (p : A → ℝ) (N : V → ℝ) (q : Seminorm ℝ Y)
    {K C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hp : ∀ a, 0 ≤ p a) (hN : ∀ v, 0 ≤ N v)
    (hB : ∀ u v, q (B u v) ≤ K * N u * N v)
    (hU : ∀ a, N (U a) ≤ C * p a) (hT : ∀ a, N (T a) ≤ C * p a)
    (hD : ∀ a, N ((U - T) a) ≤ δ * C * p a) (a b : A) :
    q (squareDiscrepancy B U T a - squareDiscrepancy B U T b) ≤
      2 * K * C ^ 2 * δ * (p a + p b) * p (a - b) := by
  have hpa := hp a
  have hpb := hp b
  have hpab := hp (a - b)
  rw [squareDiscrepancy_sub_eq]
  calc
    _ ≤ q (B ((U - T) (a - b)) (U a)) + q (B ((U - T) b) (U (a - b))) +
        q (B (T (a - b)) ((U - T) a)) + q (B (T b) ((U - T) (a - b))) := by
      exact (map_add_le_add q _ _).trans (add_le_add
        ((map_add_le_add q _ _).trans (add_le_add (map_add_le_add q _ _) le_rfl)) le_rfl)
    _ ≤ K * (δ * C * p (a - b)) * (C * p a) +
        K * (δ * C * p b) * (C * p (a - b)) +
        K * (C * p (a - b)) * (δ * C * p a) +
        K * (C * p b) * (δ * C * p (a - b)) := by
      gcongr
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hD _) hK) (hU _) (hN _) (by positivity))
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hD _) hK) (hU _) (hN _) (by positivity))
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hT _) hK) (hD _) (hN _) (by positivity))
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hT _) hK) (hD _) (hN _) (by positivity))
    _ = _ := by ring

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the absolute discrepancy
bound, in particular at the unperturbed initial amplitude. -/
theorem squareDiscrepancy_le
    (B : V →ₗ[ℝ] V →ₗ[ℝ] Y) (U T : A →ₗ[ℝ] V)
    (p : A → ℝ) (N : V → ℝ) (q : Seminorm ℝ Y)
    {K C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hp : ∀ a, 0 ≤ p a) (hN : ∀ v, 0 ≤ N v)
    (hB : ∀ u v, q (B u v) ≤ K * N u * N v)
    (hU : ∀ a, N (U a) ≤ C * p a) (hT : ∀ a, N (T a) ≤ C * p a)
    (hD : ∀ a, N ((U - T) a) ≤ δ * C * p a) (a : A) :
    q (squareDiscrepancy B U T a) ≤ 2 * K * C ^ 2 * δ * p a ^ 2 := by
  have hpa := hp a
  rw [squareDiscrepancy_eq]
  calc
    _ ≤ q (B ((U - T) a) (U a)) + q (B (T a) ((U - T) a)) := map_add_le_add q _ _
    _ ≤ K * (δ * C * p a) * (C * p a) + K * (C * p a) * (δ * C * p a) := by
      apply add_le_add
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hD _) hK) (hU _) (hN _) (by positivity))
      · exact (hB _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hT _) hK) (hD _) (hN _) (by positivity))
    _ = _ := by ring

end JanetCartan.DensityDiscrepancy
