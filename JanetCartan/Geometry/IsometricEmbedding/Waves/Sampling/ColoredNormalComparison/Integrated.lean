module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Comparison

/-!
# Finite charts and the fixed spectator integral

The integral assembly of `app:ch_waves:eq:colored-normal-comparison`.
The same complete normal, color labels and smooth-band prefixes are integrated
on the original fixed spectator measure. Only its fixed mass enters the
constant; no sample-count, band-count or inverse-weight factor is introduced.

The explicit Bochner integrability inputs below are required: the difference
of two undefined integrals is not an acceptable realization of a normal.
Their producer is the common-kernel disintegration on the Euclidean output,
to be instantiated by `jc-simultaneous-sampling` on its actual `BandKernelData`.
The existing torus-valued `CarrierSlices` identity cannot replace that step.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison RawInputPartition SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {n : ℕ} {Chart V : Type*} [Fintype Chart] [MeasurableSpace V]

/-- Fixed spectator integration and finite chart summation preserve a uniform
normal comparison with only the original measure masses. This elementary
integration step consumes the per-chart bound proved in `Comparison`, and
Bochner integrability from the common-kernel realization
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_sum_integral_normal_sub_le
    (ν : Chart → Measure V) [∀ a, IsFiniteMeasure (ν a)]
    (E T : Chart → V → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n)
    (hE : ∀ a, Integrable (E a) (ν a)) (hT : ∀ a, Integrable (T a) (ν a))
    (b : Chart → ℝ) (hb : ∀ a, ∀ᵐ v ∂ν a, ‖E a v - T a v‖ ≤ b a) :
    ‖(∑ a, ∫ v, E a v ∂ν a) - (∑ a, ∫ v, T a v ∂ν a)‖ ≤
      ∑ a, b a * (ν a).real univ := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← integral_sub (hE a) (hT a)]
  exact norm_integral_le_of_norm_le_const (hb a)

/-- Finite-family endpoint for Sampling and CurrentNormalComparison, after
the original fixed spectator integral. Every per-band estimate and the
transport endpoint are proved from the displayed primitive data; only the
integrability of the two literal normal families is an additional input to
this integration step. The full kernel realization must supply it before
this can be applied to the actual sampling mean. Both quadratures and the
original Lebesgue output are retained
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_integrated_colored_prefix_transport_bound
    (G : Chart → UniformNormalGeometry n n) (C : Chart → ℕ → ℝ)
    (ν : Chart → Measure V) [∀ a, IsFiniteMeasure (ν a)]
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) (Z : Chart → Euclidean n →L[ℝ] Point)
    {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > 0,
      ∀ (F : ∀ a, V → (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData (G a) (C a))
      (F₀ : ∀ a, V → ℕ → UniformNormalData (G a) (C a))
      (R : Chart → (Fin 3 → Fin (p + 1)) → ℝ) (Rmax : ℝ),
      (∀ a c, R a c ∈ Icc Rmin Rmax) →
      ∀ (ψ : Chart → Point → ℝ) (B P : Chart → ℝ),
      (∀ a, PatchBounds (ψ a) (B a) (P a)) →
      ∀ (z₀ : Chart → V → Point) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ g : ∀ a, V → (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict (G a).D),
      (∀ a v c, g a v c =ᵐ[volume.restrict (G a).D] fun u ↦
        (coloredBlockMask p (integerCube (blockCutoff p (B a) h))
          (convolvedBoxWindow κ p) h c (z₀ a v + Z a u) : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ →
      (∀ a, Λ / (Rmin * lam) ≤ (G a).ε₀) →
      ∀ J ≤ cutoffCount Λ,
      (∀ a v c j, j ∈ Finset.range J → ∀ x ∈ (G a).X, ∀ u ∈ (G a).D,
        (F a v c j).phase 0 x u = (F₀ a v j).phase 0 x u) →
      (∀ a v c j, j ∈ Finset.range J → ∀ x ∈ (G a).X, ∀ u ∈ (G a).D,
        (F a v c j).amplitude 0 x u = (F₀ a v j).amplitude 0 x u) →
      (∀ a v j, j ∈ Finset.range J → ∀ x u, u ∈ (G a).D →
        (F₀ a v j).amplitude 0 x u ≠ 0 → z₀ a v + Z a u ∈ Function.support (ψ a)) →
      (∀ a, Integrable (fun v ↦ coloredPrefixNormal (F a v) (R a) (g a v) lam J) (ν a)) →
      (∀ a, Integrable (fun v ↦ transportPrefixNormal (F₀ a v) J) (ν a)) →
      let E := ∑ a, ∫ v, coloredPrefixNormal (F a v) (R a) (g a v) lam J ∂ν a
      let T := ∑ a, ∫ v, transportPrefixNormal (F₀ a v) J ∂ν a
      ‖E - T‖ ≤ A * lam⁻¹ * Λ / h ∧
        ‖samplingOutputConjugation n E - samplingOutputConjugation n T‖ ≤
          A * lam⁻¹ * Λ / h ∧
        ‖samplingRealNormal n E - samplingRealNormal n T‖ ≤ 4 * (A * lam⁻¹ * Λ / h) := by
  choose A hA hb using fun a ↦
    exists_colored_prefix_transport_bound (G a) (C a) hc hs hm hn hk hp (Z a) hRmin
  let D := ∑ a, A a * (ν a).real univ
  have hD : 0 ≤ D := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hA a).le (measureReal_nonneg)
  refine ⟨D + 1, by linarith, ?_⟩
  intro F F₀ R Rmax hR ψ B P hψ z₀ h hh hh₁ g hg lam Λ hlam hΛ hbuffer
    J hJ hphase hamp hsupport hi hi₀
  dsimp only
  have he : ‖(∑ a, ∫ v, coloredPrefixNormal (F a v) (R a) (g a v) lam J ∂ν a) -
      (∑ a, ∫ v, transportPrefixNormal (F₀ a v) J ∂ν a)‖ ≤
        (D + 1) * lam⁻¹ * Λ / h := by
    calc
      _ ≤ ∑ a, (A a * lam⁻¹ * Λ / h) * (ν a).real univ :=
        norm_sum_integral_normal_sub_le ν _ _ hi hi₀ _ (fun a ↦
          Filter.Eventually.of_forall fun v ↦
            hb a (F a v) (F₀ a v) (R a) Rmax (hR a) (ψ a) (B a) (P a) (hψ a)
              (z₀ a v) h hh hh₁ (g a v) (hg a v) lam Λ hlam hΛ (hbuffer a)
              J hJ (hphase a v) (hamp a v) (hsupport a v))
      _ = D * lam⁻¹ * Λ / h := by
        simp only [D, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ (D + 1) * lam⁻¹ * Λ / h := by
        have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
        gcongr
        linarith
  exact ⟨he, sampling_normal_comparison_of_coordinate_bound _ _ he⟩

end JanetCartan.Sampling.ColoredNormalComparison
