module

public import JanetCartan.Analysis.Extension.Ball.Regularity
public import JanetCartan.Analysis.Extension.SeeleyCoefficients
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Uniform continuous derivative bounds for the fixed ball extension

The constants in `app:ch_regular_base:eq:ball-extension-continuous` depend on the
fixed geometry and the order, but not on the input function. We first bound the
fixed collar profile linearly in the input jets, then sum the Seeley majorants.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.BallExtension.Parameters

private theorem exists_compact_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {s K : Set X} (hK : IsCompact K) (hKs : K ⊆ s) (hs : UniqueDiffOn ℝ s)
    {g : X → Y} (hg : ContDiffOn ℝ ∞ g s) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ m, ∀ z ∈ K,
      ‖iteratedFDerivWithin ℝ i g s z‖ ≤ B := by
  have hb (i : ℕ) : ∃ B : ℝ, ∀ z ∈ K, ‖iteratedFDerivWithin ℝ i g s z‖ ≤ B :=
    hK.exists_bound_of_continuousOn
      ((hg.continuousOn_iteratedFDerivWithin (by simp) hs).mono hKs)
  choose B hB using hb
  refine ⟨1 + ∑ i ∈ Finset.range (m + 1), max 0 (B i), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))
  · intro i hi z hz
    have hsum := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (m + 1)) ↦ le_max_left 0 (B j))
      (Finset.mem_range.mpr (show i < m + 1 by omega))
    linarith [hB i z hz, le_max_right 0 (B i)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (p : JanetCartan.BallExtension.Parameters E)

/-- The fixed profile in `app:ch_regular_base:eq:extension-collar-l2` is bounded
linearly in the input jets through order `m`, with a constant independent of `f`. -/
theorem exists_collarProfile_uniform_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) → ∀ M : ℝ, 0 ≤ M →
      (∀ i ≤ m, ∀ y ∈ closedBall p.center p.radius,
        ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) y‖ ≤ M) →
      ∀ i ≤ m, ∀ z ∈ Icc 0 p.width ×ˢ p.compactExteriorCollar,
        ‖iteratedFDerivWithin ℝ i (p.collarProfile f) p.collarProfileDomain z‖ ≤ C * M := by
  let K := Icc 0 p.width ×ˢ p.compactExteriorCollar
  have hK : IsCompact K := isCompact_Icc.prod p.isCompact_compactExteriorCollar
  have hcut : ContDiffOn ℝ ∞ (fun z : ℝ × E ↦ p.cutoff z.1) p.collarProfileDomain :=
    p.cutoff.contDiff.comp_contDiffOn contDiffOn_fst
  obtain ⟨A, hA, hcutB⟩ := exists_compact_jet_bound hK p.compactCollar_subset_profileDomain
    p.uniqueDiffOn_collarProfileDomain hcut m
  obtain ⟨B, hB, hsampleB⟩ := exists_compact_jet_bound hK p.compactCollar_subset_profileDomain
    p.uniqueDiffOn_collarProfileDomain p.contDiffOn_collarSample m
  let C : ℕ → ℝ := fun i ↦ ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℝ) * A * ((i - j).factorial : ℝ) * B ^ (i - j)
  have hC (i : ℕ) : 0 ≤ C i := by dsimp [C]; positivity
  refine ⟨∑ i ∈ Finset.range (m + 1), C i, Finset.sum_nonneg (fun i _ ↦ hC i), ?_⟩
  intro f hf M hM hjet i hi z hz
  have hzD := p.compactCollar_subset_profileDomain hz
  have hcomp (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j (f ∘ p.collarSample) p.collarProfileDomain z‖ ≤
        (j.factorial : ℝ) * M * B ^ j := by
    apply norm_iteratedFDerivWithin_comp_le hf p.contDiffOn_collarSample (by simp)
      p.uniqueDiffOn_closedBall p.uniqueDiffOn_collarProfileDomain
      (fun _ hy ↦ p.collarSample_mem_closedBall hy) hzD
    · intro l hl
      exact hjet l (hl.trans hj) _ (p.collarSample_mem_closedBall hzD)
    · intro l hl hlm
      exact (hsampleB l (hlm.trans hj) z hz).trans (le_self_pow₀ hB (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDerivWithin ℝ j (fun z : ℝ × E ↦ p.cutoff z.1) p.collarProfileDomain z‖ *
        ‖iteratedFDerivWithin ℝ (i - j) (f ∘ p.collarSample) p.collarProfileDomain z‖ :=
      norm_iteratedFDerivWithin_mul_le hcut
        (hf.comp p.contDiffOn_collarSample (fun _ hy ↦ p.collarSample_mem_closedBall hy))
        p.uniqueDiffOn_collarProfileDomain hzD (by simp)
    _ ≤ ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * A * (((i - j).factorial : ℝ) * M * B ^ (i - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hcutB j (by have := Finset.mem_range.mp hj; omega) z hz)
          (by positivity)) (hcomp (i - j) (by omega)) (norm_nonneg _)
          (mul_nonneg (by positivity) (by linarith))
    _ = C i * M := by dsimp [C]; rw [Finset.sum_mul]; congr 1; ext j; ring
    _ ≤ (∑ l ∈ Finset.range (m + 1), C l) * M :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ ↦ hC l) (Finset.mem_range.mpr (by omega))) hM

/-- The summand estimate for `p = ∞` in
`app:ch_regular_base:eq:extension-collar-l2`, with a constant uniform in the input. -/
theorem exists_summand_uniform_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) → ∀ M : ℝ, 0 ≤ M →
      (∀ i ≤ m, ∀ y ∈ closedBall p.center p.radius,
        ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) y‖ ≤ M) →
      ∀ (a : ℕ → ℝ) (k : ℕ) (x : E), p.radius ≤ ‖x - p.center‖ →
        ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand a f y k)
          {y | p.radius ≤ ‖y - p.center‖} x‖ ≤ C * M * |a k| * (2 : ℝ) ^ (k * m) := by
  obtain ⟨C, hC, hprofile⟩ := p.exists_collarProfile_uniform_derivative_bound m
  obtain ⟨B, hB, hcoords⟩ := p.exists_scaledCollarCoordinates_derivative_bound m
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, ?_⟩
  intro f hf M hM hjet a k x hx
  have hunit : ‖iteratedFDerivWithin ℝ m (fun y ↦ p.summand (fun _ ↦ 1) f y k)
      {y | p.radius ≤ ‖y - p.center‖} x‖ ≤
      (m.factorial : ℝ) * C * B ^ m * M * (2 : ℝ) ^ (k * m) := by
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
        (fun i hi ↦ hprofile f hf M hM hjet i hi _
          (p.scaledCollarCoordinates_mem_compactCollar k hx hk))
        (D := (2 : ℝ) ^ k * B) (fun i hi him ↦ by
          rw [iteratedFDerivWithin_inter_open hU hxU]
          exact hcoords k i hi him x (p.scaledCollarCoordinates_mem_compactCollar k hx hk).2)
      rw [iteratedFDerivWithin_inter_open hU hxU] at hcomp
      rw [heq]
      calc
        _ ≤ (m.factorial : ℝ) * (C * M) * ((2 : ℝ) ^ k * B) ^ m := hcomp
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    · rw [p.iteratedFDerivWithin_summand_eq_zero_of_width_le (fun _ ↦ 1) f k m
        (le_of_not_gt hk), norm_zero]
      positivity
  have heq : (fun y ↦ p.summand a f y k) =
      a k • (fun y ↦ p.summand (fun _ ↦ 1) f y k) := by
    funext y
    simp only [Pi.smul_apply, summand, one_mul, smul_eq_mul]
    ring
  rw [heq, iteratedFDerivWithin_const_smul_apply
    (((p.contDiffOn_summand_closedExterior (fun _ ↦ 1) hf k) x hx).of_le (by simp))
    p.uniqueDiffOn_closedExterior hx, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |a k| * ((m.factorial : ℝ) * C * B ^ m * M * (2 : ℝ) ^ (k * m)) :=
      mul_le_mul_of_nonneg_left hunit (abs_nonneg _)
    _ = _ := by ring

/-- All global derivatives of the one Seeley extension obey the uniform bound
in `app:ch_regular_base:eq:ball-extension-continuous`. The coefficient conditions
are discharged by the universal coefficients, at every order. -/
theorem exists_extend_uniform_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) → ∀ M : ℝ, 0 ≤ M →
      (∀ i ≤ m, ∀ y ∈ closedBall p.center p.radius,
        ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) y‖ ≤ M) →
      ∀ x : E, ‖iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x‖ ≤ C * M := by
  obtain ⟨C, hC, hb⟩ := p.exists_summand_uniform_derivative_bound m
  let S := ∑' k, |Seeley.coeff k| * (2 : ℝ) ^ (k * m)
  refine ⟨max 1 (C * S), le_max_left _ _, ?_⟩
  intro f hf M hM hjet x
  have he : ContDiff ℝ ∞ (p.extend Seeley.coeff f) :=
    p.contDiff_extend Seeley.coeff Seeley.summable_abs_coeff_moment Seeley.infinite_moment hf
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · have hxB := mem_closedBall_iff_norm.mpr hx
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedBall
      (he.contDiffAt.of_le (by simp)) hxB,
      iteratedFDerivWithin_congr (p.extend_eq_on_closedBall Seeley.coeff f) hxB m]
    exact (hjet m le_rfl x hxB).trans (le_mul_of_one_le_left hM (le_max_left _ _))
  · have hxX : p.radius ≤ ‖x - p.center‖ := (lt_of_not_ge hx).le
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedExterior
      (he.contDiffAt.of_le (by simp)) hxX,
      iteratedFDerivWithin_congr
        (p.extend_eq_tsum_on_closedExterior Seeley.coeff
          (by simpa using Seeley.infinite_moment 0) f) hxX m,
      p.iteratedFDerivWithin_tsum_summand_closedExterior Seeley.coeff
        Seeley.summable_abs_coeff_moment hf m hxX]
    calc
      _ ≤ C * M * S := tsum_of_norm_bounded
        ((Seeley.summable_abs_coeff_moment m).hasSum.mul_left (C * M))
        (fun k ↦ by simpa only [mul_assoc] using hb f hf M hM hjet Seeley.coeff k x hxX)
      _ ≤ max 1 (C * S) * M := by
        rw [mul_assoc, mul_comm M S, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hM

/-- The intrinsic closed-ball `C^m` norm in
`app:ch_regular_base:eq:ball-extension-continuous`, using the unique one-sided
Fréchet jets. This does not depend on values outside the ball. -/
def closedBallCNorm (m : ℕ) (f : E → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    sSup ((fun x ↦ ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) x‖) ''
      closedBall p.center p.radius)

omit [FiniteDimensional ℝ E] in
/-- Nonnegativity of the input norm in
`app:ch_regular_base:eq:ball-extension-continuous`. -/
theorem closedBallCNorm_nonneg (m : ℕ) (f : E → ℝ) : 0 ≤ p.closedBallCNorm m f := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _)

/-- Each input jet is controlled by the intrinsic norm in
`app:ch_regular_base:eq:ball-extension-continuous`. -/
theorem norm_iteratedFDerivWithin_le_closedBallCNorm {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {i m : ℕ} (hi : i ≤ m)
    {x : E} (hx : x ∈ closedBall p.center p.radius) :
    ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) x‖ ≤ p.closedBallCNorm m f := by
  have hbounded : BddAbove ((fun x ↦
      ‖iteratedFDerivWithin ℝ i f (closedBall p.center p.radius) x‖) ''
      closedBall p.center p.radius) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      (hf.continuousOn_iteratedFDerivWithin (by simp) p.uniqueDiffOn_closedBall).norm).bddAbove
  apply (le_csSup hbounded ⟨x, hx, rfl⟩).trans
  unfold closedBallCNorm
  exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := i)
    (f := fun j : ℕ ↦ sSup ((fun y ↦
      ‖iteratedFDerivWithin ℝ j f (closedBall p.center p.radius) y‖)
        '' closedBall p.center p.radius))
    (fun j _ ↦ Real.sSup_nonneg (by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg _))
    (Finset.mem_range.mpr (by omega))

omit [FiniteDimensional ℝ E] in
/-- For ambient smooth functions the intrinsic norm agrees with the project's
`cNorm`, as used in `app:ch_regular_base:eq:ball-extension-continuous`. -/
theorem closedBallCNorm_eq_cNorm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    p.closedBallCNorm m f = cNorm (closedBall p.center p.radius) m f := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Set.image_congr
  intro x hx
  rw [iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedBall
    (hf.contDiffAt.of_le (by simp)) hx]

/-- The all-order `C^m` bound in `app:ch_regular_base:eq:ball-extension-continuous`
for one fixed operator and functions smooth only on the closed ball. -/
theorem exists_cNorm_extend_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cNorm univ m (p.extend Seeley.coeff f) ≤ C * p.closedBallCNorm m f := by
  choose C hC hb using p.exists_extend_uniform_derivative_bound
  refine ⟨1 + ∑ i ∈ Finset.range (m + 1), C i, ?_, ?_⟩
  · have := Finset.sum_nonneg (s := Finset.range (m + 1))
      (fun i _ ↦ le_trans zero_le_one (hC i))
    linarith
  · intro f hf
    have hM := p.closedBallCNorm_nonneg m f
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), C i * p.closedBallCNorm m f := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.sSup_le _ (mul_nonneg (le_trans zero_le_one (hC i)) hM)
        rintro _ ⟨x, _, rfl⟩
        apply hb i f hf _ hM
        intro j hj y hy
        exact p.norm_iteratedFDerivWithin_le_closedBallCNorm hf
          (show j ≤ m by have := Finset.mem_range.mp hi; omega) hy
      _ = (∑ i ∈ Finset.range (m + 1), C i) * p.closedBallCNorm m f :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + ∑ i ∈ Finset.range (m + 1), C i) * p.closedBallCNorm m f := by
        gcongr
        linarith

end JanetCartan.BallExtension.Parameters
