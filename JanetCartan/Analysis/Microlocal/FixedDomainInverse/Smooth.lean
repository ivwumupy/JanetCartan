module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Smooth.Correction

/-!
# Smooth supported realization of the fixed local inverse

The smooth-preservation, support and pointwise physical conclusions of
`app:ch_regular:thm:exact-correction` and `app:ch_regular:eq:exact-physical`.
The cutoffs are those of `exists_fixed_cutoffs_localSobolevInverse`; the smooth
function represents exactly `correctedSource` on the original Lebesgue L²(W).

The actual sector L²-to-H¹ bound, localized one-gain regularity and parametrix
identity remain producer inputs. Smoothness of the physical expressions is
also an explicit input when upgrading their a.e. identity to a pointwise one.
These conditional deductions do not assert the unconditional sector theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter
open scoped ContDiff Topology NNReal ENNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {W : Set (EuclideanSpace ℝ (Fin n))}

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The cutoffs chosen before the residual and all high orders admit one
linear smooth realization of their corrected-source operator. The L²-to-H¹
bound chooses the supports; one-gain regularity then proves smoothness
(`app:ch_regular:thm:exact-correction`). -/
theorem exists_fixed_cutoffs_smoothCorrection (hn : 0 < n)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hW : IsOpen W) (hUW : ball c r ⊆ W)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball c r)
    {M : ℝ} (hM : 0 ≤ M) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c r ∧
      tsupport (χ₃ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c r ∧
      (∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1) ∧
      (ball x χ₂.rIn).Nonempty ∧ IsOpen (ball x χ₂.rIn) ∧
      ball x χ₂.rIn ⊆ ball c r ∧ (∀ y ∈ ball x χ₂.rIn, χ₂ y = 1) ∧
      ∀ (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
        (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f))
        (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖),
        let R := residualToLpOnBall c hr hUW A hmem hM hbound
        let hp := (two_lt_ballSobolevExponent (F := F) c hr).le
        let K := localizedResidual hp χ₂ χ₃ isOpen_ball.measurableSet R
        ‖K‖ ≤ θ ∧
        ((∀ s f, MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f)) →
          ∃ L : smoothSource W F →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → F),
            ∀ h : smoothSource W F,
              ContDiff ℝ ∞ (L h) ∧
              L h =ᵐ[volume.restrict W] correctedSource hp χ₂ χ₃ isOpen_ball.measurableSet R h ∧
              tsupport (L h) ⊆ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ∧
              W.indicator (L h) = L h) := by
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, hinv⟩ :=
    exists_fixed_cutoffs_localSobolevInverse (F := F) hn c hr hW.measurableSet hUW hx hM hθ₀ hθ₁
  refine ⟨χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, ?_⟩
  intro A hmem hbound
  have hK := (hinv A hmem hbound).1
  refine ⟨hK, fun hgain ↦ ?_⟩
  exact ⟨smoothCorrectedSourceLinear hW _ χ₂ χ₃ isOpen_ball.measurableSet _
    (hK.trans_lt hθ₁) (h₂.trans hUW) hgain,
    smoothCorrectedSource_spec hW _ χ₂ χ₃ isOpen_ball.measurableSet _
      (hK.trans_lt hθ₁) (h₂.trans hUW) hgain⟩

section Physical

variable (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
  (hW : IsOpen W) (hUW : ball c r ⊆ W)
  (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
  (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
  (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖)
  {x : EuclideanSpace ℝ (Fin n)} (χ₂ χ₃ : ContDiffBump x)

local notation "R" => residualToLpOnBall c hr hUW A hmem hM hbound
local notation "hp" => le_of_lt (two_lt_ballSobolevExponent (F := F) c hr)
local notation "K" => localizedResidual hp χ₂ χ₃ isOpen_ball.measurableSet R
local notation "Z" => correctedSource hp χ₂ χ₃ isOpen_ball.measurableSet R

variable (hK : ‖localizedResidual (two_lt_ballSobolevExponent (F := F) c hr).le
    χ₂ χ₃ isOpen_ball.measurableSet (residualToLpOnBall c hr hUW A hmem hM hbound)‖ < 1)
  (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c r)
  (hnest : ∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1)
  (hgain : ∀ (s : ℕ) (f : LocalL2 W F), MemRestrictionSobolev W s f →
    MemRestrictionSobolev W (s + 1)
      (localizedResidual (two_lt_ballSobolevExponent (F := F) c hr).le
        χ₂ χ₃ isOpen_ball.measurableSet (residualToLpOnBall c hr hUW A hmem hM hbound) f))

local notation "z" => smoothCorrectedSource hW hp χ₂ χ₃ isOpen_ball.measurableSet R hK
  (hsupport.trans hUW) hgain

include hUW hsupport in
private theorem core_subset_domain : ball x χ₂.rIn ⊆ W := by
  intro y hy
  apply hUW (hsupport ?_)
  apply subset_tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
  show χ₂ y ≠ 0
  rw [χ₂.one_of_mem_closedBall (ball_subset_closedBall hy)]
  exact one_ne_zero

include hnest

/-- The same corrected source satisfies the pointwise residual equation on
the fixed core when the actual residual has a continuous representative
(`app:ch_regular:thm:exact-correction`). -/
theorem smoothCorrectedSource_add_residual_eqOn (h : smoothSource W F)
    {f a : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContinuousOn f W) (hfh : f =ᵐ[volume.restrict W] h)
    (ha : ContinuousOn a (ball x χ₂.rIn))
    (haA : a =ᵐ[volume.restrict (ball c r)] A (Z h)) :
    EqOn (fun y ↦ z h y + a y) f (ball x χ₂.rIn) := by
  have hcoreW := core_subset_domain c hUW χ₂ hsupport
  have hcoreU : ball x χ₂.rIn ⊆ ball c r := by
    intro y hy
    apply hsupport
    apply subset_tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    show χ₂ y ≠ 0
    rw [χ₂.one_of_mem_closedBall (ball_subset_closedBall hy)]
    exact one_ne_zero
  have hs := smoothCorrectedSource_spec hW hp χ₂ χ₃ isOpen_ball.measurableSet R
    hK (hsupport.trans hUW) hgain h
  have he := (correctedSource_localSobolev_ae c hr hUW A hmem hM hbound χ₂ χ₃ hK hnest h).2.2
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_ball
    (hs.1.continuous.continuousOn.add ha) (hf.mono hcoreW)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hcoreW he,
    ae_restrict_of_ae_restrict_of_subset hcoreW hs.2.1,
    ae_restrict_of_ae_restrict_of_subset hcoreW hfh,
    ae_restrict_of_ae_restrict_of_subset hcoreU haA,
    ae_restrict_mem isOpen_ball.measurableSet] with y he hz hf ha hy
  simp only [Pi.add_apply]
  rw [hz, ha, hf]
  exact he (hcoreU hy) (χ₂.one_of_mem_closedBall (ball_subset_closedBall hy))

/-- `app:ch_regular:eq:exact-physical` pointwise on the original core, for
smooth physical expressions of the actual solver. The hypothesis is the
producer's localized parametrix identity, not the final physical equation.
The angular discrepancy and the original corrected L² input to `S` are retained. -/
theorem exact_physical_smooth_eqOn
    {X : Type*} (S : LocalL2 W F → X) (P : X → EuclideanSpace ℝ (Fin n) → F)
    (B : LocalL2 W F → EuclideanSpace ℝ (Fin n) → F)
    (hparam : ∀ v : LocalL2 W F,
      (∀ᵐ y ∂volume.restrict W, y ∉ ball c r → v y = 0) →
      ∀ᵐ y ∂volume.restrict (ball c r), P (S v) y = B v y + A v y)
    (h : smoothSource W F) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ ∞ f W) (hfh : f =ᵐ[volume.restrict W] h)
    (hP : ContDiffOn ℝ ∞ (P (S (Z h))) (ball x χ₂.rIn))
    (hB : ContDiffOn ℝ ∞ (B (Z h)) (ball x χ₂.rIn)) :
    EqOn (P (S (Z h))) (fun y ↦ f y + (B (Z h) y - z h y)) (ball x χ₂.rIn) := by
  have hcoreW := core_subset_domain c hUW χ₂ hsupport
  have hs := smoothCorrectedSource_spec hW hp χ₂ χ₃ isOpen_ball.measurableSet R
    hK (hsupport.trans hUW) hgain h
  have he := exact_physical_localSobolev_ae c hr hUW A hmem hM hbound χ₂ χ₃ hK
    hsupport hnest S P B hparam h
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_ball hP.continuousOn
    ((hf.continuousOn.mono hcoreW).add (hB.continuousOn.sub hs.1.continuous.continuousOn))
  filter_upwards [he, ae_restrict_of_ae_restrict_of_subset hcoreW hfh,
    ae_restrict_of_ae_restrict_of_subset hcoreW hs.2.1] with y hy hf hz
  simpa only [Pi.add_apply, Pi.sub_apply, hf, hz] using hy

end Physical

end JanetCartan.FixedDomainInverse
