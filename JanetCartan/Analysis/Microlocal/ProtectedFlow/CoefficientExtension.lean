module

public import JanetCartan.Analysis.Extension.Ball

/-!
# The fixed affine coefficient extension

The construction in `app:ch_regular:eq:coefficient-extension` is the same Seeley
operator at every order. These results apply to each real component of the
coefficient array. The compact collar is independent of the current coefficient
and derivative order; at each order the bound is uniform in the current
coefficient. The background may be any fixed smooth function; it need not have
compact support.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual affine extension in `app:ch_regular:eq:coefficient-extension`.
For a finite coefficient array this formula is applied componentwise with the
same `p`, hence with the same support and extension constants. -/
def affineCoefficientExtension (p : BallExtension.Parameters E) (a₀ a : E → ℝ) : E → ℝ :=
  a₀ + p.seeleyExtension (a - a₀)

/-- The coefficient perturbation is the single linear Seeley extension
(`app:ch_regular:eq:coefficient-extension`). -/
theorem affineCoefficientExtension_sub (p : BallExtension.Parameters E) (a₀ a : E → ℝ) :
    affineCoefficientExtension p a₀ a - a₀ = p.seeleyExtension (a - a₀) := by
  simp [affineCoefficientExtension]

/-- The extension agrees on the entire closed coefficient ball, including its
boundary (`app:ch_regular:thm:no-return`). -/
theorem affineCoefficientExtension_eqOn (p : BallExtension.Parameters E) (a₀ a : E → ℝ) :
    EqOn (affineCoefficientExtension p a₀ a) a (closedBall p.center p.radius) := by
  intro x hx
  have h := p.seeleyExtension_eq_on_closedBall (a - a₀) hx
  change a₀ x + p.seeleyExtension (a - a₀) x = a x
  rw [h]
  simp

/-- Smooth coefficients give a smooth real extension
(`app:ch_regular:eq:coefficient-extension`). Only one-sided smoothness of the
current coefficient is needed on the ball. -/
theorem contDiff_affineCoefficientExtension [FiniteDimensional ℝ E] (p : BallExtension.Parameters E)
    {a₀ a : E → ℝ} (h₀ : ContDiff ℝ ∞ a₀)
    (ha : ContDiffOn ℝ ∞ a (closedBall p.center p.radius)) :
    ContDiff ℝ ∞ (affineCoefficientExtension p a₀ a) :=
  h₀.add (p.contDiff_seeleyExtension (ha.sub h₀.contDiffOn))

/-- The actual perturbation has fixed compact support, independently of its
size and of every derivative order (`app:ch_regular:eq:coefficient-extension`). -/
theorem tsupport_affineCoefficientExtension_sub (p : BallExtension.Parameters E)
    (a₀ a : E → ℝ) :
    tsupport (affineCoefficientExtension p a₀ a - a₀) ⊆
      closedBall p.center (p.radius + p.width / 2) := by
  rw [affineCoefficientExtension_sub]
  exact p.tsupport_seeleyExtension_subset _

variable [FiniteDimensional ℝ E]

private theorem cNorm_seeleyExtension_restrict_le (p : BallExtension.Parameters E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (K : Set E) (m : ℕ) :
    cNorm K m (p.seeleyExtension f) ≤ cNorm univ m (p.seeleyExtension f) := by
  obtain ⟨B, _, hB⟩ := (p.hasCompactSupport_seeleyExtension f).exists_bound_iteratedFDeriv
    (p.contDiff_seeleyExtension hf.contDiffOn) m
  apply cNorm_mono_set_of_bddAbove (subset_univ K)
  intro j hj
  exact ⟨B, by rintro _ ⟨x, _, rfl⟩; exact hB j hj x⟩

/-- The same affine operator has both the perturbation bound and the tame
coefficient bound of `app:ch_regular:eq:coefficient-extension` at every order.
The constant is chosen before the current coefficient. In particular the
perturbation estimate has no additive background term. -/
theorem exists_affineCoefficientExtension_bounds (p : BallExtension.Parameters E)
    {a₀ : E → ℝ} (h₀ : ContDiff ℝ ∞ a₀) {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : E → ℝ, ContDiff ℝ ∞ a →
      cNorm univ m (affineCoefficientExtension p a₀ a - a₀) ≤
        C * cNorm (closedBall p.center p.radius) m (a - a₀) ∧
      cNorm K m (affineCoefficientExtension p a₀ a) ≤
        C * (1 + cNorm (closedBall p.center p.radius) m a) := by
  obtain ⟨A, hA, hb⟩ := p.exists_cNorm_seeleyExtension_le m
  let B := cNorm K m a₀ + A * cNorm (closedBall p.center p.radius) m a₀
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg _ _ _) (mul_nonneg hA.le (cNorm_nonneg _ _ _))
  refine ⟨A + B + 1, by positivity, ?_⟩
  intro a ha
  have he := hb (a - a₀) (ha.sub h₀).contDiffOn
  rw [p.closedBallCNorm_eq_cNorm (show ContDiff ℝ ∞ (a - a₀) from ha.sub h₀)] at he
  constructor
  · rw [affineCoefficientExtension_sub]
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _))
  · have hadd := cNorm_add_le hK (h₀.of_le (by simp) : ContDiff ℝ m a₀)
      ((p.contDiff_seeleyExtension (ha.sub h₀).contDiffOn).of_le (by simp))
    have hsub := cNorm_sub_le (isCompact_closedBall p.center p.radius)
      (ha.of_le (by simp) : ContDiff ℝ m a) (h₀.of_le (by simp))
    have hlocal := cNorm_seeleyExtension_restrict_le p (ha.sub h₀) K m
    have htotal : cNorm K m (affineCoefficientExtension p a₀ a) ≤
        B + A * cNorm (closedBall p.center p.radius) m a := by
      change cNorm K m (a₀ + p.seeleyExtension (a - a₀)) ≤ _
      calc
        _ ≤ cNorm K m a₀ + cNorm K m (p.seeleyExtension (a - a₀)) := hadd
        _ ≤ cNorm K m a₀ + A * cNorm (closedBall p.center p.radius) m (a - a₀) :=
          add_le_add le_rfl (hlocal.trans he)
        _ ≤ cNorm K m a₀ + A *
            (cNorm (closedBall p.center p.radius) m a +
              cNorm (closedBall p.center p.radius) m a₀) := by gcongr
        _ = _ := by dsimp [B]; ring
    exact htotal.trans (by nlinarith [cNorm_nonneg (closedBall p.center p.radius) m a])

/-- Shrinking the current low neighborhood by a fixed constant places the
actual extension in any prescribed low neighborhood of the background. This
discharges the low-class extension step in `app:ch_regular:thm:no-return`. -/
theorem exists_affineCoefficientExtension_low_radius (p : BallExtension.Parameters E)
    (a₀ : E → ℝ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a : E → ℝ, ContDiff ℝ ∞ (a - a₀) →
      cNorm (closedBall p.center p.radius) k (a - a₀) < δ →
      cNorm univ k (affineCoefficientExtension p a₀ a - a₀) < ε := by
  obtain ⟨C, hC, hb⟩ := p.exists_cNorm_seeleyExtension_le k
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro a ha hsmall
  rw [affineCoefficientExtension_sub]
  have h := hb (a - a₀) ha.contDiffOn
  rw [p.closedBallCNorm_eq_cNorm ha] at h
  exact h.trans_lt ((mul_lt_mul_of_pos_left hsmall hC).trans_eq (mul_div_cancel₀ ε hC.ne'))

/-- Every graded coefficient profile is preserved by the *same* extension;
constants precede the slow scale and the current coefficient
(`app:ch_regular:eq:coefficient-extension`). -/
theorem affineCoefficientExtension_preserves_profile (p : BallExtension.Parameters E)
    {a₀ : E → ℝ} (h₀ : ContDiff ℝ ∞ a₀) {K : Set E} (hK : IsCompact K)
    (D : ℕ → ℝ) (r₀ : ℕ) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (T : ℝ), 1 ≤ T → ∀ a : E → ℝ, ContDiff ℝ ∞ a →
        HasDerivativeProfile (closedBall p.center p.radius) a r₀ T D →
        HasDerivativeProfile K (affineCoefficientExtension p a₀ a) r₀ T C := by
  choose B hB hb using exists_affineCoefficientExtension_bounds p h₀ hK
  refine ⟨fun r ↦ B r * (1 + max 0 (D r)), fun r ↦ mul_pos (hB r) (by positivity), ?_⟩
  intro T hT a ha hprofile r
  have hp : 1 ≤ T ^ (r - r₀) := one_le_pow₀ hT
  have hd := (hprofile r).trans (mul_le_mul_of_nonneg_right (le_max_right 0 (D r))
    (zero_le_one.trans hp))
  calc
    _ ≤ B r * (1 + cNorm (closedBall p.center p.radius) r a) := (hb r a ha).2
    _ ≤ B r * ((1 + max 0 (D r)) * T ^ (r - r₀)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (hB r).le
    _ = _ := by ring

end JanetCartan.ProtectedFlow
