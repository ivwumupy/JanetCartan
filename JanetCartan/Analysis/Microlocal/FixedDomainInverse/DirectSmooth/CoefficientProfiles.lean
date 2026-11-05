module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms.Membership
public import JanetCartan.Analysis.ContDiff.NestedCutoffs
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# Classical profiles for the original coefficient restriction classes

For `app:ch_regular:thm:fixed-high` and `app:ch_regular:eq:inverse-remainder`,
construct an actual smooth compact weak extension of each coefficient by one
fixed buffered cutoff. This bounds the restriction norm of the SAME
`smoothCoefficientL2` class from above by the original classical seminorm on a
larger ball, at the same derivative order. Constants precede the coefficients.

The paired deduction supplies the exact coefficient-profile input of
`ArbitraryAccuracy.inverse_remainder_restrictionSobolev`. `HistoryProfiles`
instantiates it with `ResponseTransfer.RetainedFactors.exists_admissible_history_retained_coefficient_profiles`,
which extracts the actual affine array's principal and zeroth components with
their original norms. The resulting coefficient classes must be used in the
same inverse and finite-remainder application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse
open LocalSobolev RegularSector.FiniteAssembly.CoefficientNorms
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem derivative_eLpNorm_le_cNorm
    (x : Euclidean n) (R : ℝ) {g : Euclidean n → F}
    (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ closedBall x R)
    (s j : ℕ) (hj : j ≤ s) :
    (eLpNorm (iteratedFDeriv ℝ j g) 2 volume).toReal ≤
      ((volume (closedBall x R)) ^ (1 / (2 : ℝ))).toReal * cNorm (closedBall x R) s g := by
  have hm : AEStronglyMeasurable (iteratedFDeriv ℝ j g) volume :=
    (hg.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))).aestronglyMeasurable
  have hsupport : Function.support (iteratedFDeriv ℝ j g) ⊆ closedBall x R :=
    (support_iteratedFDeriv_subset j).trans hs
  have hb : ∀ᵐ y ∂volume.restrict (closedBall x R),
      ‖iteratedFDeriv ℝ j g y‖ ≤ cNorm (closedBall x R) s g := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
    exact norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x R)
      (hg.of_le (by simp)) hy hj
  have h := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hm.restrict hb
  rw [eLpNorm_restrict_eq_of_support_subset hm hsupport, Measure.restrict_apply_univ] at h
  have ht : (volume (closedBall x R)) ^ (2 : ℝ≥0∞).toReal⁻¹ *
      ENNReal.ofReal (cNorm (closedBall x R) s g) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (isCompact_closedBall x R).measure_lt_top.ne).ne
      ENNReal.ofReal_ne_top
  have htoreal := ENNReal.toReal_mono ht h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cNorm_nonneg _ _ _),
    ENNReal.toReal_ofNat, one_div] using htoreal

/-- A fixed interior coefficient ball has restriction norm bounded above by the
original classical seminorm on a larger ball, with no derivative loss. The
consumer is `inverse_remainder_restrictionSobolev.hprofile`; the same actual
coefficient classes from the finite inverse construction are retained. -/
theorem exists_smoothCoefficientL2_restriction_bound
    (x : Euclidean n) {R Rplus : ℝ} (hR : 0 < R) (hRR : R < Rplus) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (hball : closedBall x R ⊆ Ω)
        (f : Euclidean n → F) (hf : ContDiff ℝ ∞ f) (s : ℕ),
        restrictionSobolevNorm (ball x R) s
          (smoothCoefficientL2 hΩ hR hball f hf.contDiffOn) ≤
            C s * cNorm (closedBall x Rplus) s f := by
  let χ := bufferedBallBump x R Rplus hR hRR
  let vol := ((volume (closedBall x Rplus)) ^ (1 / (2 : ℝ))).toReal
  let C := fun s : ℕ ↦ (s + 1 : ℝ) * (vol + 1) * (2 : ℝ)^s *
    (cNorm (closedBall x Rplus) s (χ : Euclidean n → ℝ) + 1)
  have hC : ∀ s, 0 < C s := by
    intro s
    dsimp only [C, vol]
    have := cNorm_nonneg (closedBall x Rplus) s (χ : Euclidean n → ℝ)
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ hball f hf s
  let g : Euclidean n → F := fun y ↦ χ y • f y
  have hg : ContDiff ℝ ∞ g := χ.contDiff.smul hf
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have hgs : tsupport g ⊆ closedBall x Rplus :=
    (tsupport_smul_subset_left (f := (χ : Euclidean n → ℝ)) (g := f)).trans
      ((bufferedBallBump_tsupport_subset x R Rplus hR hRR).trans ball_subset_closedBall)
  have heq : g =ᵐ[volume.restrict (ball x R)]
      smoothCoefficientL2 hΩ hR hball f hf.contDiffOn := by
    apply EventuallyEq.trans _ (smoothCoefficientL2_coeFn hΩ hR hball f hf.contDiffOn).symm
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hχ : χ y = 1 := by
      exact show y ∈ {y | bufferedBallBump x R Rplus hR hRR y = 1} from interior_subset
        (bufferedBallBump_plateau x R Rplus hR hRR (ball_subset_closedBall hy))
    simp only [g, hχ, one_smul]
  let e : SobolevExtension (ball x R) s (smoothCoefficientL2 hΩ hR hball f hf.contDiffOn) :=
    { toFun := g
      jet := fun j ↦ iteratedFDeriv ℝ j g
      weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hg.of_le (by simp)) univ
      memLp_fun := hg.continuous.memLp_of_hasCompactSupport hgc
      memLp_jet := fun j _ ↦
        (hg.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
          (hgc.iteratedFDeriv j)
      restrict_eq := heq }
  have hjet : e.jetNorm ≤ (s + 1 : ℝ) * vol * cNorm (closedBall x Rplus) s g := by
    calc
      e.jetNorm ≤ ∑ _j ∈ Finset.range (s + 1), vol * cNorm (closedBall x Rplus) s g := by
        apply Finset.sum_le_sum
        intro j hj
        exact derivative_eLpNorm_le_cNorm x Rplus hg hgs s j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring
  have hprod := cNorm_smul_le (isCompact_closedBall x Rplus)
    (χ.contDiff.of_le (by simp : (s : ℕ∞ω) ≤ (∞ : ℕ∞ω))) (hf.of_le (by simp))
  apply (restrictionSobolevNorm_le e).trans
  apply hjet.trans
  have hvol : 0 ≤ vol := ENNReal.toReal_nonneg
  have hχnorm := cNorm_nonneg (closedBall x Rplus) s (χ : Euclidean n → ℝ)
  have hfnorm := cNorm_nonneg (closedBall x Rplus) s f
  calc
    _ ≤ (s + 1 : ℝ) * vol *
        ((2 : ℝ)^s * cNorm (closedBall x Rplus) s (χ : Euclidean n → ℝ) *
          cNorm (closedBall x Rplus) s f) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (by positivity) hvol)
    _ ≤ C s * cNorm (closedBall x Rplus) s f := by
      dsimp only [C]
      calc
        _ = ((s + 1 : ℝ) * (2 : ℝ)^s * cNorm (closedBall x Rplus) s f) *
            (vol * cNorm (closedBall x Rplus) s (χ : Euclidean n → ℝ)) := by ring
        _ ≤ ((s + 1 : ℝ) * (2 : ℝ)^s * cNorm (closedBall x Rplus) s f) *
            ((vol + 1) * (cNorm (closedBall x Rplus) s (χ : Euclidean n → ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        _ = _ := by ring


/-- The paired coefficient profile needed by
`ArbitraryAccuracy.inverse_remainder_restrictionSobolev`: constants are fixed
before both coefficients and the derivative scale, and the shift is paid by
an already supplied classical baseline. The actual history application is
`exists_admissible_history_inverse_coefficient_profile` in `HistoryProfiles`,
using the original principal and zeroth projections on this larger ball.
This deduction does not assume an inverse or a restriction-norm profile. -/
theorem exists_coefficient_pair_inverse_profile
    (x : Euclidean n) {R Rplus : ℝ} (hR : 0 < R) (hRR : R < Rplus)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) (hAB : ∀ m, 0 ≤ AB m)
    (b r₀ : ℕ) (hbr : b ≤ r₀) :
    ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      ∀ {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (hball : closedBall x R ⊆ Ω)
        (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
        (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B) (L : ℝ), 1 ≤ L →
        HasDerivativeProfile (closedBall x Rplus) Q r₀ L AQ →
        HasDerivativeProfile (closedBall x Rplus) B r₀ L AB →
        ∀ j : ℕ,
          1 + restrictionSobolevNorm (ball x R) (j+b)
              (smoothCoefficientL2 hΩ hR hball Q hQ.contDiffOn) +
            restrictionSobolevNorm (ball x R) (j+b)
              (smoothCoefficientL2 hΩ hR hball B hB.contDiffOn) ≤ D j * L ^ j := by
  obtain ⟨CQ, hCQ, hQbound⟩ := exists_smoothCoefficientL2_restriction_bound
    (F := Fin n → MetricTensor n) x hR hRR
  obtain ⟨CB, hCB, hBbound⟩ := exists_smoothCoefficientL2_restriction_bound
    (F := MetricTensor n) x hR hRR
  refine ⟨fun j ↦ 1+CQ (j+b)*AQ (j+b)+CB (j+b)*AB (j+b), ?_, ?_⟩
  · intro j
    have hq := mul_nonneg (hCQ (j+b)).le (hAQ (j+b))
    have hb := mul_nonneg (hCB (j+b)).le (hAB (j+b))
    linarith
  intro Ω hΩ hball Q B hQ hB L hL hpQ hpB j
  have hpow : L ^ (j+b-r₀) ≤ L ^ j := pow_le_pow_right₀ hL (by omega)
  have hq := (hQbound hΩ hball Q hQ (j+b)).trans
    (mul_le_mul_of_nonneg_left ((hpQ (j+b)).trans
      (mul_le_mul_of_nonneg_left hpow (hAQ (j+b)))) (hCQ (j+b)).le)
  have hb := (hBbound hΩ hball B hB (j+b)).trans
    (mul_le_mul_of_nonneg_left ((hpB (j+b)).trans
      (mul_le_mul_of_nonneg_left hpow (hAB (j+b)))) (hCB (j+b)).le)
  calc
    _ ≤ L^j + CQ (j+b)*(AQ (j+b)*L^j) + CB (j+b)*(AB (j+b)*L^j) :=
      add_le_add (add_le_add (one_le_pow₀ hL) hq) hb
    _ = _ := by ring

end JanetCartan.FixedDomainInverse
