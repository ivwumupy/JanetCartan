module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.LocalL2
public import JanetCartan.Analysis.Sobolev.Local.Cutoff

/-!
# Literal zero extension and support of the fixed L² correction

These consequences of the existing inverse and support lemmas are used by
`exists_finite_direct_fixed_inverse`. That concrete constructor supplies the
residual, its H¹ bound and the contraction; no analytic premise is added there.
Source: `app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal
namespace JanetCartan.FixedDomainInverse
open LocalSobolev SmallSupport

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {W : Set (EuclideanSpace ℝ (Fin n))}

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Literal zero extension, core equation, supported corrected source and its
L² bound, for the SAME Neumann inverse (`app:ch_regular:thm:exact-correction`).
The concrete finite constructor discharges the residual estimates and contraction.
This lemma only packages consequences of the existing inverse and support APIs. -/
theorem localSobolevInverse_zeroExtension_support
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hW : MeasurableSet W) (hUW : ball c r ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
    (hmem : ∀ u, MemRestrictionSobolev (ball c r) 1 (A u))
    {M θ : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, restrictionSobolevNorm (ball c r) 1 (A u) ≤ M*‖u‖)
    {x : EuclideanSpace ℝ (Fin n)} (χ₂ χ₃ : ContDiffBump x)
    (hθ : θ < 1)
    (hnest : ∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1)
    (hcore : ball x χ₂.rIn ⊆ ball c r)
    (hplateau : ∀ y ∈ ball x χ₂.rIn, χ₂ y = 1) :
    let Rp := residualToLpOnBall c hr hUW A hmem hM hbound
    let K := localizedResidual (two_lt_ballSobolevExponent c hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp
    let Corr := correctedSource (two_lt_ballSobolevExponent c hr).le
      χ₂ χ₃ isOpen_ball.measurableSet Rp
    ‖K‖ ≤ θ →
      (∀ u : LocalL2 W F, K u =ᵐ[volume.restrict W]
        zeroExtend isOpen_ball.measurableSet
          (bumpL2 (p := 2) le_rfl χ₂ (A (bumpL2 (p := 2) le_rfl χ₃ u)))) ∧
      ∀ h : LocalL2 W F,
        (∀ᵐ y ∂volume.restrict W,
          y ∉ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) → Corr h y = 0) ∧
        bumpL2 (p := 2) le_rfl χ₃ (Corr h) = Corr h ∧
        (∀ᵐ y ∂volume.restrict (ball x χ₂.rIn), Corr h y + A (Corr h) y = h y) ∧
        (∀ᵐ y ∂volume, y ∉ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) →
          zeroExtend hW (Corr h) y = 0) ∧
        ‖Corr h‖ ≤ (1-θ)⁻¹*‖h‖ := by
  dsimp only
  intro hK
  refine ⟨?_, ?_⟩
  · intro u
    exact (localizedResidual_residualToLpOnBall_coeFn c hr hUW A hmem hM hbound
      χ₂ χ₃ u).trans (Filter.EventuallyEq.symm (ae_restrict_of_ae
        (zeroExtend_bumpL2_coeFn isOpen_ball.measurableSet χ₂
          (A (bumpL2 (p := 2) le_rfl χ₃ u)))))
  intro h
  obtain ⟨hsupport, hfixed, heq⟩ := correctedSource_localSobolev_ae c hr hUW A hmem
    hM hbound χ₂ χ₃ (hK.trans_lt hθ) hnest h
  refine ⟨hsupport, hfixed, ?_, ?_, ?_⟩
  · have hrestricted : ∀ᵐ y ∂(volume.restrict W).restrict (ball x χ₂.rIn), _ :=
      (ae_restrict_iff' isOpen_ball.measurableSet).mpr
        (heq.mono fun y hy hycore ↦ hy (hcore hycore) (hplateau y hycore))
    simpa only [Measure.restrict_restrict_of_subset (hcore.trans hUW)] using hrestricted
  · have hs' := (ae_restrict_iff' hW).mp hsupport
    filter_upwards [zeroExtend_coeFn hW
      (correctedSource (two_lt_ballSobolevExponent c hr).le χ₂ χ₃
        isOpen_ball.measurableSet (residualToLpOnBall c hr hUW A hmem hM hbound) h),
      hs'] with y hy hz
    intro hout
    rw [hy]
    by_cases hyW : y ∈ W
    · rw [indicator_of_mem hyW, hz hyW hout]
    · rw [indicator_of_notMem hyW]
  · let cut := bumpL2 (F := F) (μ := volume.restrict W) (p := 2) le_rfl χ₂
    have hcut : ‖cut h‖ ≤ ‖h‖ := by
      simpa only [one_mul] using cut.le_of_opNorm_le
        (norm_bumpL2_two_le_one (F := F) (μ := volume.restrict W) χ₂) h
    let K := localizedResidual (two_lt_ballSobolevExponent c hr).le χ₂ χ₃
      isOpen_ball.measurableSet (residualToLpOnBall c hr hUW A hmem hM hbound)
    change ‖neumannInverse K (cut h)‖ ≤ _
    exact (norm_neumannInverse_apply_le K hK hθ (cut h)).trans
      (mul_le_mul_of_nonneg_left hcut (inv_nonneg.mpr (sub_nonneg.mpr hθ.le)))

end JanetCartan.FixedDomainInverse
