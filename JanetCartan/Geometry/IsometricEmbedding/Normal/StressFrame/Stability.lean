module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Stability of finite frames

The uniform Gram-gap step in `app:ch_background:defn:bg-geometry`.
An independent finite reference family has a uniform lower synthesis bound
throughout a fixed neighborhood measured by the sum of the vector differences.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.StressFrame

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Synthesis from Euclidean coefficients, used for the Gram form in
`app:ch_background:defn:bg-geometry`. -/
def synthesis (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- A finite independent frame has a uniform positive lower bound on a
neighborhood (`app:ch_background:defn:bg-geometry`). -/
theorem exists_uniform_synthesis_lower_bound {v : ι → E} (hv : LinearIndependent ℝ v) :
    ∃ ε > 0, ∃ a > 0, ∀ w : ι → E, (∑ i, ‖w i - v i‖) < ε →
      ∀ c : EuclideanSpace ℝ ι, a * ‖c‖ ≤ ‖∑ i, c i • w i‖ := by
  have hinj : Function.Injective (synthesis v) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro c hc
    ext i
    exact (Fintype.linearIndependent_iff.mp hv) (fun i ↦ c i) hc i
  obtain ⟨K, hK, hanti⟩ := (synthesis v).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hinj)
  have hK' : 0 < (K : ℝ) := hK
  let a : ℝ := 1 / (2 * K)
  have ha : 0 < a := by dsimp [a]; positivity
  have hKa : (K : ℝ) * a = 1 / 2 := by dsimp [a]; field_simp
  refine ⟨a, ha, a, ha, ?_⟩
  intro w hw c
  have herr : ‖(∑ i, c i • w i) - ∑ i, c i • v i‖ ≤
      ‖c‖ * ∑ i, ‖w i - v i‖ := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply norm_sum_le_of_le
    intro i _
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le c i) (norm_nonneg _)
  have hlow := ZeroHomClass.bound_of_antilipschitz (synthesis v) hanti c
  change ‖c‖ ≤ (K : ℝ) * ‖∑ i, c i • v i‖ at hlow
  have htriangle := norm_sub_norm_le (∑ i, c i • v i) (∑ i, c i • w i)
  rw [norm_sub_rev] at htriangle
  have herr' : ‖(∑ i, c i • w i) - ∑ i, c i • v i‖ ≤ ‖c‖ * a :=
    herr.trans (mul_le_mul_of_nonneg_left hw.le (norm_nonneg c))
  have hfirst : ‖c‖ / 2 ≤ (K : ℝ) * ‖∑ i, c i • w i‖ := by
    nlinarith [mul_le_mul_of_nonneg_left (htriangle.trans herr') hK'.le]
  calc
    a * ‖c‖ = a * (2 * (‖c‖ / 2)) := by ring
    _ ≤ a * (2 * ((K : ℝ) * ‖∑ i, c i • w i‖)) := by gcongr
    _ = (2 * ((K : ℝ) * a)) * ‖∑ i, c i • w i‖ := by ring
    _ = ‖∑ i, c i • w i‖ := by rw [hKa]; ring

/-- A positive synthesis lower bound proves independence of the perturbed
frame (`app:ch_seed:setup:seed-current`). -/
theorem linearIndependent_of_synthesis_lower_bound {w : ι → E} {a : ℝ} (ha : 0 < a)
    (h : ∀ c : EuclideanSpace ℝ ι, a * ‖c‖ ≤ ‖∑ i, c i • w i‖) :
    LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hb := h (WithLp.toLp 2 c)
  simp only [hc, norm_zero] at hb
  have hz : ‖WithLp.toLp 2 c‖ = 0 := by nlinarith [norm_nonneg (WithLp.toLp 2 c)]
  have heq := norm_eq_zero.mp hz
  exact congrArg (fun x : EuclideanSpace ℝ ι ↦ x i) heq

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gram quadratic form is the squared synthesis norm
(`app:ch_background:defn:bg-geometry`). -/
theorem gramQuadratic_eq_norm_synthesis_sq (w : ι → H) (c : EuclideanSpace ℝ ι) :
    (∑ i, ∑ j, c i * c j * inner ℝ (w i) (w j)) = ‖∑ i, c i • w i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    Finset.mul_sum, mul_assoc]
  congr 1
  ext i
  congr 1
  ext j
  rw [real_inner_comm (w j) (w i)]

/-- Uniform lower synthesis bounds give uniform positive Gram gaps with
Euclidean coefficient norm (`app:ch_background:defn:bg-geometry`). -/
theorem gramGap_of_synthesis_lower_bound {w : ι → H} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ c : EuclideanSpace ℝ ι, a * ‖c‖ ≤ ‖∑ i, c i • w i‖)
    (c : EuclideanSpace ℝ ι) :
    a ^ 2 * (∑ i, (c i) ^ 2) ≤ ∑ i, ∑ j, c i * c j * inner ℝ (w i) (w j) := by
  rw [gramQuadratic_eq_norm_synthesis_sq, ← EuclideanSpace.real_norm_sq_eq, ← mul_pow]
  exact (sq_le_sq₀ (mul_nonneg ha (norm_nonneg c)) (norm_nonneg _)).mpr (h c)

end InnerProduct

end JanetCartan.StressFrame
