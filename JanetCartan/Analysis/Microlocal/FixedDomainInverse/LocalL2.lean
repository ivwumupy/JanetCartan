module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Cutoffs
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Correction
public import JanetCartan.Analysis.Sobolev.Local.Scale.Graded
public import JanetCartan.Analysis.Sobolev.Local.Embedding
public import JanetCartan.Analysis.Sobolev.Local.Residual

/-!
# The fixed inverse on actual local L² and restriction Sobolev spaces

The functional-analytic assembly of `app:ch_regular:thm:exact-correction`.
The bounded H¹-to-Lᵖ inclusion is `RestrictionSobolevSpace.toLpBall`, proved
from the weak restriction Sobolev embedding. We retain its a.e. agreement with
the complete residual, including when changing to the nested restricted measure.

One choice of cutoffs works for every residual with the supplied L²-to-H¹
bound. The inverse identities and the estimates on the actual restriction
Sobolev scale are conclusions. The complete residual's analytic estimates and
the parametrix identity remain inputs from the regular-sector construction.
No assertion about pointwise smooth representatives is made here.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {W : Set (EuclideanSpace ℝ (Fin n))}

/-- The complete L² residual realized in Lᵖ on the nested measure used by
the cutoff operator (`app:ch_regular:eq:residual-negative-positive`). This
uses the proved bounded inclusion on the actual H¹ outputs. -/
def residualToLpOnBall (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hUW : ball c r ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖) :
    LocalL2 W F →L[ℝ]
      Lp F (ballSobolevExponent F c hr) ((volume.restrict W).restrict (ball c r)) :=
  (exists_lp_residual_ball c hr hUW A hmem hM hbound).choose

/-- Changing the output exponent preserves the complete residual a.e.
(`app:ch_regular:thm:exact-correction`). -/
theorem residualToLpOnBall_coeFn (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hUW : ball c r ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖)
    (f : LocalL2 W F) :
    residualToLpOnBall c hr hUW A hmem hM hbound f =ᵐ[volume.restrict (ball c r)] A f :=
  (exists_lp_residual_ball c hr hUW A hmem hM hbound).choose_spec.1 f

/-- The L²-to-Lᵖ bound used to choose supports before the residual and all
high orders (`app:ch_regular:thm:exact-correction`). -/
theorem residualToLpOnBall_norm_le (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hUW : ball c r ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖) :
    ‖residualToLpOnBall c hr hUW A hmem hM hbound‖ ≤
      ballSobolevEmbeddingConstant F c hr * M :=
  (exists_lp_residual_ball c hr hUW A hmem hM hbound).choose_spec.2

omit [FiniteDimensional ℝ F] in
/-- The literal paper one-gain estimates imply `HasOneGain` for the actual
restriction scale (`app:ch_regular:eq:one-gain-tame`). This only bundles
properties of the localized residual, never properties of its inverse. -/
theorem restrictionSobolev_hasOneGain (hW : MeasurableSet W)
    (K : LocalL2 W F →L[ℝ] LocalL2 W F) (C a : ℕ → ℝ) (b : ℕ)
    (hreg : ∀ s f, MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f))
    (hbound : ∀ s f, MemRestrictionSobolev W s f →
      restrictionSobolevNorm W (s + 1) (K f) ≤
        C (s + 1) * (restrictionSobolevNorm W s f + (1 + a (s + 1 + b)) * ‖f‖)) :
    (restrictionSobolevScale W F hW).HasOneGain K C a b where
  regularity := hreg
  bound s f hf := by
    rw [restrictionSobolevScale_gradeNorm hW (hreg s f hf),
      restrictionSobolevScale_gradeNorm hW hf]
    exact hbound s f hf

/-- One support choice gives the Neumann series on real L²(W), both inverse
identities, and the genuine restriction-norm estimate with the same shift `b`
(`app:ch_regular:thm:exact-correction`, `app:ch_regular:eq:inverse-tame`).
Only the complete residual's L²-to-H¹ and localized one-gain bounds are inputs.
Positive dimension is required for arbitrarily small volume supports. -/
theorem exists_fixed_cutoffs_localSobolevInverse (hn : 0 < n)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hW : MeasurableSet W) (hUW : ball c r ⊆ W)
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
        let K := localizedResidual (two_lt_ballSobolevExponent c hr).le
          χ₂ χ₃ isOpen_ball.measurableSet R
        let T := neumannInverse K
        ‖K‖ ≤ θ ∧ HasSum (fun j : ℕ ↦ (-K) ^ j) T ∧
        (1 + K) * T = 1 ∧ T * (1 + K) = 1 ∧ ‖T‖ ≤ (1 - θ)⁻¹ ∧
        ∀ (C a : ℕ → ℝ) (b : ℕ),
          (∀ s, 0 ≤ C s) → (∀ s, 0 ≤ a s) → Monotone a →
          (∀ s f, MemRestrictionSobolev W s f → MemRestrictionSobolev W (s + 1) (K f)) →
          (∀ s f, MemRestrictionSobolev W s f →
            restrictionSobolevNorm W (s + 1) (K f) ≤
              C (s + 1) * (restrictionSobolevNorm W s f + (1 + a (s + 1 + b)) * ‖f‖)) →
          ∀ (s : ℕ) (f : LocalL2 W F), MemRestrictionSobolev W s f →
            MemRestrictionSobolev W s (T f) ∧
            restrictionSobolevNorm W s (T f) ≤ inverseTameConstant θ C s *
              (restrictionSobolevNorm W s f + (1 + a (s + b)) * ‖f‖) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, hinv⟩ :=
    exists_fixed_cutoffs_neumannInverse (F := F) (μ := volume.restrict W)
      (two_lt_ballSobolevExponent (F := F) c hr) isOpen_ball hx
      (ballSobolevEmbeddingConstant F c hr * M) hθ₀ hθ₁
  refine ⟨χ₂, χ₃, h₂, h₃, hnest, hne, hopen, hcore, hplateau, ?_⟩
  intro A hmem hbound
  obtain ⟨hK, hsum, hleft, hright, hnorm, hgraded⟩ :=
    hinv (residualToLpOnBall c hr hUW A hmem hM hbound)
      (residualToLpOnBall_norm_le c hr hUW A hmem hM hbound)
  refine ⟨hK, hsum, hleft, hright, hnorm, ?_⟩
  intro C a b hC ha hmono hreg hgain s f hf
  obtain ⟨hz, hest⟩ := hgraded (restrictionSobolevScale W F hW) C a b hC ha hmono
    (restrictionSobolev_hasOneGain hW _ C a b hreg hgain) s f hf
  refine ⟨hz, ?_⟩
  simpa only [restrictionSobolevScale_gradeNorm hW hz,
    restrictionSobolevScale_gradeNorm hW hf] using hest

/-- Agreement with the L² representative on the output ball, expressed in
ambient a.e. language (`app:ch_regular:thm:exact-correction`). -/
theorem residualToLpOnBall_ae_on (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hUW : ball c r ⊆ W)
    (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
    (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖)
    (f : LocalL2 W F) :
    ∀ᵐ y ∂volume.restrict W, y ∈ ball c r →
      residualToLpOnBall c hr hUW A hmem hM hbound f y = A f y := by
  apply (ae_restrict_iff' isOpen_ball.measurableSet).mp
  rw [show ae ((volume.restrict W).restrict (ball c r)) =
    ae (volume.restrict (ball c r)) from congrArg ae
      (Measure.restrict_restrict_of_subset hUW)]
  exact residualToLpOnBall_coeFn c hr hUW A hmem hM hbound f

section Correction

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
  (hUW : ball c r ⊆ W)
  (A : LocalL2 W F →L[ℝ] LocalL2 (ball c r) F)
  (hmem : ∀ f, MemRestrictionSobolev (ball c r) 1 (A f)) {M : ℝ} (hM : 0 ≤ M)
  (hbound : ∀ f, restrictionSobolevNorm (ball c r) 1 (A f) ≤ M * ‖f‖)
  {x : EuclideanSpace ℝ (Fin n)} (χ₂ χ₃ : ContDiffBump x)

local notation "R" => residualToLpOnBall c hr hUW A hmem hM hbound
local notation "hp" => le_of_lt (two_lt_ballSobolevExponent (F := F) c hr)
local notation "K" => localizedResidual hp χ₂ χ₃ isOpen_ball.measurableSet R
local notation "Z" => correctedSource hp χ₂ χ₃ isOpen_ball.measurableSet R

/-- The concrete localized operator is exactly the zero extension of
`χ₂ A χ₃` a.e., with the complete residual's original L² representative
(`app:ch_regular:thm:exact-correction`). -/
theorem localizedResidual_residualToLpOnBall_coeFn (f : LocalL2 W F) :
    K f =ᵐ[volume.restrict W] fun y ↦
      χ₂ y • (ball c r).indicator (A (bumpL2 (p := 2) le_rfl χ₃ f)) y := by
  filter_upwards [localizedResidual_coeFn hp χ₂ χ₃ isOpen_ball.measurableSet R f,
    residualToLpOnBall_ae_on c hr hUW A hmem hM hbound
      (bumpL2 (p := 2) le_rfl χ₃ f)] with y hy hR
  rw [hy]
  by_cases hyU : y ∈ ball c r
  · simp only [indicator_of_mem hyU, hR hyU]
  · simp only [indicator_of_notMem hyU]

/-- Support containment and the plateau equation for the original L² residual
(`app:ch_regular:thm:exact-correction`). Both function identities are a.e. -/
theorem correctedSource_localSobolev_ae (hK : ‖K‖ < 1)
    (hnest : ∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1)
    (h : LocalL2 W F) :
    (∀ᵐ y ∂volume.restrict W,
      y ∉ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) → Z h y = 0) ∧
    bumpL2 (p := 2) le_rfl χ₃ (Z h) = Z h ∧
    (∀ᵐ y ∂volume.restrict W, y ∈ ball c r → χ₂ y = 1 →
      Z h y + A (Z h) y = h y) := by
  refine ⟨correctedSource_ae_zero_off_support hp χ₂ χ₃ isOpen_ball.measurableSet R hK h,
    bumpL2_correctedSource hp χ₂ χ₃ isOpen_ball.measurableSet R hK hnest h, ?_⟩
  filter_upwards [correctedSource_add_residual hp χ₂ χ₃ isOpen_ball.measurableSet R
    hK hnest h, residualToLpOnBall_ae_on c hr hUW A hmem hM hbound (Z h)] with y hy heq
  intro hyU hχ
  rw [← heq hyU]
  exact hy hyU hχ

/-- The actual residual's parametrix identity gives the exact physical identity
on the fixed nonempty core, a.e. (`app:ch_regular:eq:exact-physical`). The
angular discrepancy is retained. No smooth representative is required. -/
theorem exact_physical_localSobolev_ae (hK : ‖K‖ < 1)
    (hsupport : tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ ball c r)
    (hnest : ∀ y ∈ tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ), χ₃ y = 1)
    {X : Type*} (S : LocalL2 W F → X) (P : X → EuclideanSpace ℝ (Fin n) → F)
    (B : LocalL2 W F → EuclideanSpace ℝ (Fin n) → F)
    (hparam : ∀ v : LocalL2 W F,
      (∀ᵐ y ∂volume.restrict W, y ∉ ball c r → v y = 0) →
      ∀ᵐ y ∂volume.restrict (ball c r), P (S v) y = B v y + A v y)
    (h : LocalL2 W F) :
    ∀ᵐ y ∂volume.restrict (ball x χ₂.rIn),
      P (S (Z h)) y = h y + (B (Z h) y - Z h y) := by
  have hparam' : ∀ v : LocalL2 W F,
      (∀ᵐ y ∂volume.restrict W, y ∉ ball c r → v y = 0) →
      ∀ᵐ y ∂volume.restrict W, y ∈ ball c r →
        P (S v) y = B v y + R v y := by
    intro v hv
    have hPv : ∀ᵐ y ∂volume.restrict W, y ∈ ball c r →
        P (S v) y = B v y + A v y := by
      apply (ae_restrict_iff' isOpen_ball.measurableSet).mp
      rw [Measure.restrict_restrict_of_subset hUW]
      exact hparam v hv
    filter_upwards [hPv, residualToLpOnBall_ae_on c hr hUW A hmem hM hbound v] with y hy heq
    intro hyU
    rw [heq hyU]
    exact hy hyU
  have heq := exact_physical_ae hp χ₂ χ₃ isOpen_ball.measurableSet R hK
    hsupport hnest S P B hparam' h
  have hplateau : ∀ y ∈ ball x χ₂.rIn, χ₂ y = 1 :=
    fun _ hy ↦ χ₂.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hcore : ball x χ₂.rIn ⊆ ball c r := by
    intro y hy
    apply hsupport
    apply subset_tsupport (χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    show χ₂ y ≠ 0
    rw [hplateau y hy]
    exact one_ne_zero
  have hout : ∀ᵐ y ∂(volume.restrict W).restrict (ball x χ₂.rIn),
      P (S (Z h)) y = h y + (B (Z h) y - Z h y) := by
    apply (ae_restrict_iff' isOpen_ball.measurableSet).mpr
    filter_upwards [heq] with y hy
    exact fun hycore ↦ hy (hcore hycore) (hplateau y hycore)
  simpa only [Measure.restrict_restrict_of_subset (hcore.trans hUW)] using hout

end Correction

end JanetCartan.FixedDomainInverse
