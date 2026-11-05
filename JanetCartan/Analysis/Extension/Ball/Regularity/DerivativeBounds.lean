module

public import JanetCartan.Analysis.Extension.Ball.Regularity.DerivativeBounds.Scaling

/-!
# Uniform derivative bounds for exterior summands

The fixed-profile representation of `app:ch_regular_base:eq:extension-radial-formula`
and the quantitative chain rule give the sup-norm estimate underlying
`app:ch_regular_base:eq:extension-collar-l2`. The exponent is exactly the derivative
order. No ambient extension of the input is used.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : JanetCartan.BallExtension.Parameters E)

omit [InnerProductSpace ℝ E] in
/-- Active scaled coordinates lie in one fixed compact parameter collar, as used
in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem scaledCollarCoordinates_mem_compactCollar (k : ℕ) {x : E}
    (hx : p.radius ≤ ‖x - p.center‖)
    (hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width) :
    p.scaledCollarCoordinates k x ∈ Icc 0 p.width ×ˢ p.compactExteriorCollar := by
  have ht : 0 ≤ ‖x - p.center‖ - p.radius := sub_nonneg.mpr hx
  have hscale : ‖x - p.center‖ - p.radius ≤
      (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) :=
    le_mul_of_one_le_left ht (one_le_pow₀ (by norm_num))
  exact ⟨⟨mul_nonneg (by positivity) ht, hk.le⟩,
    hx, mem_closedBall_iff_norm.mpr (by
      change ‖x - p.center‖ ≤ p.radius + p.width
      linarith)⟩

/-- Outside the active collar all jets of a term vanish, as required for the
uniform exterior estimate in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDerivWithin_summand_eq_zero_of_width_le (a : ℕ → ℝ) (f : E → ℝ)
    (k m : ℕ) {x : E}
    (hk : p.width ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) :
    iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
      {y | p.radius ≤ ‖y - p.center‖} x = 0 := by
  have hs : ContinuousAt (fun y : E ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x := by
    fun_prop
  have hk' : p.width / 2 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    linarith [p.width_pos]
  have hz : (fun y ↦ p.summand a f y k) =ᶠ[𝓝 x] (0 : E → ℝ) := by
    filter_upwards [hs.eventually (lt_mem_nhds hk')] with y hy
    exact p.summand_eq_zero a f y k hy.le
  rw [(hz.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hz.eq_of_nhds m]
  exact congrFun iteratedFDerivWithin_zero x

/-- The unit-coefficient terms obey the sharp-order bound from
`app:ch_regular_base:eq:extension-collar-l2`, including on the sphere. -/
theorem exists_unit_summand_derivative_bound [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ x : E, p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand (fun _ ↦ 1) f y k)
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ C * (2 : ℝ) ^ (k * m) := by
  obtain ⟨C, hC, hprofile⟩ := p.exists_collarProfile_derivative_bound hf m
  obtain ⟨B, hB, hcoords⟩ := p.exists_scaledCollarCoordinates_derivative_bound m
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, ?_⟩
  intro k x hx
  by_cases hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width
  · let U : Set E := {y | (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius) < p.width}
    let X : Set E := {y | p.radius ≤ ‖y - p.center‖}
    have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
    have hs : UniqueDiffOn ℝ (X ∩ U) := p.uniqueDiffOn_closedExterior.inter hU
    have hxU : x ∈ U := hk
    have hmap : MapsTo (p.scaledCollarCoordinates k) (X ∩ U) p.collarProfileDomain := by
      intro y hy
      exact p.compactCollar_subset_profileDomain
        (p.scaledCollarCoordinates_mem_compactCollar k hy.1 hy.2)
    have heq : (fun y ↦ p.summand (fun _ ↦ 1) f y k) =
        p.collarProfile f ∘ p.scaledCollarCoordinates k := by
      funext y
      simpa only [one_mul, scaledCollarCoordinates, Function.comp_apply] using
        p.summand_eq_collarProfile (fun _ ↦ 1) f k y
    have hcomp := norm_iteratedFDerivWithin_comp_le (p.contDiffOn_collarProfile hf)
      ((p.contDiffOn_scaledCollarCoordinates k).mono (show X ∩ U ⊆ X from inter_subset_left))
      (show (m : ℕ∞ω) ≤ ∞ by simp) p.uniqueDiffOn_collarProfileDomain hs hmap
      (show x ∈ X ∩ U from ⟨hx, hxU⟩)
      (fun i hi ↦ hprofile i hi _ (p.scaledCollarCoordinates_mem_compactCollar k hx hk))
      (D := (2 : ℝ) ^ k * B) (fun i hi him ↦ by
        rw [iteratedFDerivWithin_inter_open hU hxU]
        exact hcoords k i hi him x (p.scaledCollarCoordinates_mem_compactCollar k hx hk).2)
    rw [iteratedFDerivWithin_inter_open hU hxU] at hcomp
    rw [heq]
    calc
      _ ≤ (m.factorial : ℝ) * C * ((2 : ℝ) ^ k * B) ^ m := hcomp
      _ = (m.factorial : ℝ) * C * B ^ m * (2 : ℝ) ^ (k * m) := by
        rw [mul_pow, ← pow_mul]
        ring
  · rw [p.iteratedFDerivWithin_summand_eq_zero_of_width_le (fun _ ↦ 1) f k m (le_of_not_gt hk),
      norm_zero]
    positivity

/-- Every exterior summand has its order-`m` derivative bounded by
`C * |a k| * 2^(k*m)`, uniformly in the sequence, index, and exterior point.
This is the sup-norm summand estimate used after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem exists_summand_derivative_bound [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℝ) (k : ℕ) (x : E),
      p.radius ≤ ‖x - p.center‖ →
      ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ C * |a k| * (2 : ℝ) ^ (k * m) := by
  obtain ⟨C, hC, hb⟩ := p.exists_unit_summand_derivative_bound hf m
  refine ⟨C, hC, ?_⟩
  intro a k x hx
  have heq : (fun y ↦ p.summand a f y k) =
      a k • (fun y ↦ p.summand (fun _ ↦ 1) f y k) := by
    funext y
    simp only [Pi.smul_apply, summand, one_mul, smul_eq_mul]
    ring
  rw [heq, iteratedFDerivWithin_const_smul_apply
    (((p.contDiffOn_summand_closedExterior (fun _ ↦ 1) hf k) x hx).of_le (by simp))
    p.uniqueDiffOn_closedExterior hx, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |a k| * (C * (2 : ℝ) ^ (k * m)) :=
      mul_le_mul_of_nonneg_left (hb k x hx) (abs_nonneg _)
    _ = C * |a k| * (2 : ℝ) ^ (k * m) := by ring

/-- Existential-exponent form of the bound in
`app:ch_regular_base:eq:extension-collar-l2`; the exponent can be chosen as `m`. -/
theorem exists_summand_derivative_bound_exponent [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    ∃ ell : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℝ) (k : ℕ) (x : E),
      x ∈ {y | p.radius ≤ ‖y - p.center‖} →
      ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ C * |a k| * (2 : ℝ) ^ (k * ell) :=
  ⟨m, p.exists_summand_derivative_bound hf m⟩

end JanetCartan.BallExtension.Parameters
