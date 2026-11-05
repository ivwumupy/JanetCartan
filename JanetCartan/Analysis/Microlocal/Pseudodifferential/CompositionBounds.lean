module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Composition

/-!
# Finite convergence budgets for composition

For `app:ch_regular_base:thm:actual-calculus`, integration in the intermediate
source gives decay in the outer frequency. Schwartz decay of the input handles
polynomial growth in the incoming frequency. The source derivative reserve is
`m + dim V + 1`, where `m` is the outer frequency growth order.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: The explicit source derivative budget bounds the
Fourier transform, including bounded frequencies. -/
theorem norm_fourier_le_of_sourceDerivativeMass (f : V → F) (m n : ℕ)
    (hf : ContDiff ℝ n f) (hi : ∀ j ≤ n, Integrable (iteratedFDeriv ℝ j f))
    (A : ℝ) (ξ : V) (hA : sourceDerivativeMass f n ≤ A * (1 + ‖ξ‖) ^ m) :
    ‖𝓕 f ξ‖ ≤ (2 ^ (n - 1) * (1 + 2 ^ n)) * A *
      (1 + ‖ξ‖) ^ (-((n : ℝ) - m)) := by
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  have hh := one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass f n hf hi ξ
  have hb := hh.trans (mul_le_mul_of_nonneg_left hA (by positivity))
  have heq : (1 + ‖ξ‖) ^ (-((n : ℝ) - m)) = (1 + ‖ξ‖) ^ m / (1 + ‖ξ‖) ^ n := by
    rw [neg_sub, Real.rpow_sub hp, Real.rpow_natCast, Real.rpow_natCast]
  rw [heq, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hp n)).mpr
  nlinarith [hb]

/-- `app:ch_regular_base:thm:actual-calculus`: A finite source derivative mass bound with
polynomial growth in both frequencies gives joint integrability after a Schwartz incoming
frequency test. -/
theorem integrable_schwartz_sourceFourier_of_derivativeMass
    (g : V → V → V → F)
    (hg : Continuous (fun p : (V × V) × V ↦ g p.1.1 p.1.2 p.2))
    (m n k : ℕ) (hn : m + Module.finrank ℝ V < n)
    (hs : ∀ ξ η, ContDiff ℝ n (g ξ η))
    (hi : ∀ ξ η j, j ≤ n → Integrable (iteratedFDeriv ℝ j (g ξ η)))
    (A : ℝ) (hA : ∀ ξ η, sourceDerivativeMass (g ξ η) n ≤
      A * (1 + ‖η‖ ^ k) * (1 + ‖ξ‖) ^ m) (ψ : 𝓢(V, ℂ)) :
    Integrable (fun p : V × V ↦ ψ p.2 • 𝓕 (g p.1 p.2) p.1) := by
  let C : ℝ := 2 ^ (n - 1) * (1 + 2 ^ n)
  have hdim : (Module.finrank ℝ V : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) + Module.finrank ℝ V < n := by exact_mod_cast hn
    linarith
  have hmeas : StronglyMeasurable (fun p : V × V ↦ 𝓕 (g p.1 p.2) p.1) := by
    simp only [Real.fourier_eq]
    apply StronglyMeasurable.integral_prod_right
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul hg).stronglyMeasurable
  have hmajor := (integrable_one_add_norm (μ := volume) hdim).mul_prod
    ((ψ.integrable.norm.add (ψ.integrable_pow_mul volume k)).const_mul (C * A))
  apply hmajor.mono' ((ψ.continuous.comp continuous_snd).aestronglyMeasurable.smul
    hmeas.aestronglyMeasurable)
  filter_upwards [] with p
  change ‖ψ p.2 • 𝓕 (g p.1 p.2) p.1‖ ≤ _
  rw [norm_smul]
  have hbound := norm_fourier_le_of_sourceDerivativeMass (g p.1 p.2) m n
    (hs p.1 p.2) (hi p.1 p.2) (A * (1 + ‖p.2‖ ^ k)) p.1 (hA p.1 p.2)
  calc
    _ ≤ ‖ψ p.2‖ * (C * (A * (1 + ‖p.2‖ ^ k)) *
        (1 + ‖p.1‖) ^ (-((n : ℝ) - m))) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by dsimp only [Pi.add_apply]; ring

/-- `app:ch_regular_base:thm:actual-calculus`: Compact support in the intermediate source
discharges derivative integrability. The fixed reserve beyond outer growth is `dim V + 1`. -/
theorem integrable_schwartz_sourceFourier_of_compact_derivativeMass
    (g : V → V → V → F)
    (hg : Continuous (fun p : (V × V) × V ↦ g p.1.1 p.1.2 p.2))
    (m k : ℕ)
    (hs : ∀ ξ η, ContDiff ℝ (m + Module.finrank ℝ V + 1) (g ξ η))
    (hc : ∀ ξ η, HasCompactSupport (g ξ η))
    (A : ℝ) (hA : ∀ ξ η, sourceDerivativeMass (g ξ η) (m + Module.finrank ℝ V + 1) ≤
      A * (1 + ‖η‖ ^ k) * (1 + ‖ξ‖) ^ m) (ψ : 𝓢(V, ℂ)) :
    Integrable (fun p : V × V ↦ ψ p.2 • 𝓕 (g p.1 p.2) p.1) := by
  apply integrable_schwartz_sourceFourier_of_derivativeMass g hg m _ k
    (Nat.lt_succ_self _) hs _ A hA ψ
  intro ξ η j hj
  exact ((hs ξ η).continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
    ((hc ξ η).iteratedFDeriv j)
end JanetCartan.Pseudodifferential
