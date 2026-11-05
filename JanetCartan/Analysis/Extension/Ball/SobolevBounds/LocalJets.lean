module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.LocalJets.Profile
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Local input-jet estimates for exterior summands

The pointwise estimates for `app:ch_regular_base:eq:extension-collar-l2` retain
all input jets at the radial sampling point. Their constants depend only on the
fixed collar geometry and derivative order. They apply in every finite dimension,
including dimension one, without an angular coordinate chart.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : JanetCartan.BallExtension.Parameters E)

/-- The fixed profile samples at the actual radial point of the summand in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem collarSample_scaledCollarCoordinates (k : ℕ) (x : E) :
    p.collarSample (p.scaledCollarCoordinates k x) = p.radialPoint k x := rfl

/-- The one-sided local jet estimate underlying
`app:ch_regular_base:eq:extension-collar-l2`, also valid on the boundary sphere.
The constant is independent of the input function, sequence, index, and point. -/
theorem exists_summand_local_jet_bound_within [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      ∀ (a : ℕ → ℝ) (k : ℕ) (x : E), p.radius ≤ ‖x - p.center‖ →
      (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width →
      ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
        {y | p.radius ≤ ‖y - p.center‖} x‖ ≤
        A * |a k| * (2 : ℝ) ^ (k * m) *
          ∑ j ∈ Finset.range (m + 1),
            ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.radialPoint k x)‖ := by
  obtain ⟨C, hC, hprofile⟩ := p.exists_collarProfile_local_jet_bound m
  obtain ⟨B, hB, hcoords⟩ := p.exists_scaledCollarCoordinates_derivative_bound m
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, ?_⟩
  intro f hf a k x hx hk
  let M : ℝ := ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.radialPoint k x)‖
  have hunit : ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand (fun _ ↦ 1) f y k)
      {y | p.radius ≤ ‖y - p.center‖} x‖ ≤
      (m.factorial : ℝ) * C * B ^ m * (2 : ℝ) ^ (k * m) * M := by
    let U : Set E := {y | (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius) < p.width}
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
      (C := C * M)
      (fun i hi ↦ by
        simpa only [M, p.collarSample_scaledCollarCoordinates] using
          hprofile f hf i hi _ (p.scaledCollarCoordinates_mem_compactCollar k hx hk))
      (D := (2 : ℝ) ^ k * B) (fun i hi him ↦ by
        rw [iteratedFDerivWithin_inter_open hU hxU]
        exact hcoords k i hi him x (p.scaledCollarCoordinates_mem_compactCollar k hx hk).2)
    rw [iteratedFDerivWithin_inter_open hU hxU] at hcomp
    rw [heq]
    calc
      _ ≤ (m.factorial : ℝ) * (C * M) * ((2 : ℝ) ^ k * B) ^ m := hcomp
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have heq : (fun y ↦ p.summand a f y k) =
      a k • (fun y ↦ p.summand (fun _ ↦ 1) f y k) := by
    funext y
    simp only [Pi.smul_apply, summand, one_mul, smul_eq_mul]
    ring
  rw [heq, iteratedFDerivWithin_const_smul_apply
    (((p.contDiffOn_summand_closedExterior (fun _ ↦ 1) hf k) x hx).of_le (by simp))
    p.uniqueDiffOn_closedExterior hx, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |a k| * ((m.factorial : ℝ) * C * B ^ m * (2 : ℝ) ^ (k * m) * M) :=
      mul_le_mul_of_nonneg_left hunit (abs_nonneg _)
    _ = _ := by ring

/-- The exterior derivative estimate in `app:ch_regular_base:eq:extension-collar-l2`
uses only the input jets at `radialPoint k x`, with no ambient smooth extension. -/
theorem exists_summand_local_jet_bound [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      ∀ (a : ℕ → ℝ) (k : ℕ) (x : E), p.radius < ‖x - p.center‖ →
      (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width →
      ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ≤
        A * |a k| * (2 : ℝ) ^ (k * m) *
          ∑ j ∈ Finset.range (m + 1),
            ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.radialPoint k x)‖ := by
  obtain ⟨A, hA, hb⟩ := p.exists_summand_local_jet_bound_within m
  refine ⟨A, hA, ?_⟩
  intro f hf a k x hx hk
  have hn : ContinuousAt (fun y : E ↦ ‖y - p.center‖) x := by fun_prop
  have hnhds : {y : E | p.radius ≤ ‖y - p.center‖} ∈ 𝓝 x :=
    Filter.mem_of_superset (hn.eventually (lt_mem_nhds hx)) (fun _ hy ↦ hy.le)
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedExterior
    (((p.contDiffOn_summand_closedExterior a hf k) x hx.le).contDiffAt hnhds |>.of_le
      (by simp)) hx.le]
  exact hb f hf a k x hx.le hk

/-- All exterior derivatives vanish beyond the active scaled collar in
`app:ch_regular_base:eq:extension-collar-l2`. No regularity of the input is needed. -/
theorem iteratedFDeriv_summand_eq_zero_of_width_le (a : ℕ → ℝ) (f : E → ℝ)
    (k m : ℕ) {x : E}
    (hk : p.width ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) :
    iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x = 0 := by
  have hs : ContinuousAt (fun y : E ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x := by
    fun_prop
  have hk' : p.width / 2 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    linarith [p.width_pos]
  have hz : (fun y ↦ p.summand a f y k) =ᶠ[𝓝 x] (0 : E → ℝ) := by
    filter_upwards [hs.eventually (lt_mem_nhds hk')] with y hy
    exact p.summand_eq_zero a f y k hy.le
  rw [(hz.iteratedFDeriv ℝ m).eq_of_nhds]
  rw [← iteratedFDerivWithin_univ]
  exact congrFun iteratedFDerivWithin_zero x

/-- Squaring the local jet bound and applying finite Cauchy–Schwarz gives the
sum of squared input jets needed for the `L²` estimate in
`app:ch_regular_base:eq:extension-collar-l2`. The constant absorbs `m + 1`. -/
theorem exists_summand_local_jet_sq_bound [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      ∀ (a : ℕ → ℝ) (k : ℕ) (x : E), p.radius < ‖x - p.center‖ →
      (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width →
      ‖iteratedFDeriv ℝ m (fun y ↦ p.summand a f y k) x‖ ^ 2 ≤
        A * |a k| ^ 2 * (2 : ℝ) ^ (2 * k * m) *
          ∑ j ∈ Finset.range (m + 1),
            ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.radialPoint k x)‖ ^ 2 := by
  obtain ⟨A, hA, hb⟩ := p.exists_summand_local_jet_bound m
  refine ⟨A ^ 2 * (m + 1), by positivity, ?_⟩
  intro f hf a k x hx hk
  let J : ℕ → ℝ := fun j ↦
    ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) (p.radialPoint k x)‖
  have hs : (∑ j ∈ Finset.range (m + 1), J j) ^ 2 ≤
      (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), J j ^ 2 := by
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := J))
  calc
    _ ≤ (A * |a k| * (2 : ℝ) ^ (k * m) * ∑ j ∈ Finset.range (m + 1), J j) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hb f hf a k x hx hk) 2
    _ = (A * |a k| * (2 : ℝ) ^ (k * m)) ^ 2 *
        (∑ j ∈ Finset.range (m + 1), J j) ^ 2 := mul_pow _ _ _
    _ ≤ (A * |a k| * (2 : ℝ) ^ (k * m)) ^ 2 *
        ((m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), J j ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by
      rw [mul_pow, mul_pow, ← pow_mul, show k * m * 2 = 2 * k * m by ring]
      ring

end JanetCartan.BallExtension.Parameters
