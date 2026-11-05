module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ProducerCutoffs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fourier
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.OperatorLimit

/-!
# The independent output cutoff as a bounded Fourier multiplier

The literal symbol `χo (1-mo)` is `(1-Mo) P`, with the order unchanged.
The output partial sums include their zeroth ball and are a cofinal sequence
of the already constructed contractive physical Fourier multipliers.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells LowBounds.FrequencyCutoff
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false

/-- Fourier multiplication factors the literal complementary left symbol,
including the identity term (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem complementary_leftLocalizer_schwartzMultiplier
    {ρ : ℝ} (hρ : ρ ≠ 0) (mo : LocalizerSymbol n) (ho : Continuous mo)
    (B : ℝ) (hb : ∀ x ξ, |mo (x, ξ)| ≤ B)
    (j : ℕ) (g : SchwartzMap E (Fin q → ℂ)) (x : E) :
    (schwartzMultiplier (Fin q → ℂ) j g) x -
        leftLocalizer ρ mo (schwartzMultiplier (Fin q → ℂ) j g) x =
      leftLocalizer ρ (fun p ↦ physicalCutoff j (ρ • p.2) * (1 - mo p)) g x := by
  have he (ξ : E) :
      channelFourierTransform (schwartzMultiplier (Fin q → ℂ) j g) ξ =
        complexPhysicalCutoff j ξ • channelFourierTransform g ξ := by
    change ((2 * Real.pi) ^ n : ℝ)⁻¹ •
        sourceInputFourierTransform (schwartzMultiplier (Fin q → ℂ) j g) ξ = _
    rw [sourceInputFourierTransform_schwartzMultiplier]
    exact smul_comm _ _ _
  rw [← complementary_channelFourierIntegral ρ mo _ x
    (ho.comp (continuous_const.prodMk (continuous_id.const_smul ρ⁻¹))) B
    (fun ξ ↦ hb x (ρ⁻¹ • ξ)), leftLocalizer_eq_channelFourierIntegral]
  simp only [he, smul_smul, mul_inv_cancel₀ hρ, one_smul, complexPhysicalCutoff,
    Complex.ofReal_mul]
  congr 1
  funext ξ
  congr 1
  ring

/-- The actual bounded complementary output multiplier represents the
independently cut left symbol on Schwartz data. The localizer realization
is supplied by `exists_bounded_physicalLocalizers`, without any graph-tail
bound (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem bounded_outputMultiplier_schwartz_realization
    {ρ : ℝ} (hρ : ρ ≠ 0) (mo : LocalizerSymbol n) (ho : Continuous mo)
    (hos : HasCompactSupport mo) (Mo : H →L[ℂ] H)
    (hMo : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) →
      Mo u =ᵐ[volume] fun x ↦
        WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (j : ℕ) (g : SchwartzMap E (Fin q → ℂ)) :
    (1 - Mo) (multiplier j (schwartzVectorToLp g)) =ᵐ[volume] fun x ↦
      WithLp.toLp 2 (leftLocalizer ρ
        (fun p ↦ physicalCutoff j (ρ • p.2) * (1 - mo p)) g x) := by
  let w := schwartzMultiplier (Fin q → ℂ) j g
  have hi (i : Fin q) : Integrable (fun y ↦ (schwartzVectorToLp w) y i) := by
    apply (w.integrable.eval i).congr
    filter_upwards [schwartzVectorToLp_ae w] with y hy
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin q) ↦ v i) hy).symm
  have hleft : leftLocalizer ρ mo (fun y ↦ ((schwartzVectorToLp w) y).ofLp) =
      leftLocalizer ρ mo w := by
    funext x
    unfold leftLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [schwartzVectorToLp_ae w] with y hy
    rw [hy]
  obtain ⟨B, hB⟩ := hos.exists_bound_of_continuous ho
  have hb (x ξ : E) : |mo (x, ξ)| ≤ B := by simpa using hB (x, ξ)
  rw [multiplier_schwartzVectorToLp]
  filter_upwards [Lp.coeFn_sub (schwartzVectorToLp w) (Mo (schwartzVectorToLp w)),
    schwartzVectorToLp_ae w, hMo (schwartzVectorToLp w) hi] with x hx hw hm
  change (schwartzVectorToLp w - Mo (schwartzVectorToLp w)) x = _
  rw [hx, Pi.sub_apply, hw, hm, hleft]
  exact congrArg (WithLp.toLp 2)
    (complementary_leftLocalizer_schwartzMultiplier hρ mo ho B hb j g x)

/-- Both finite output-frequency prefixes and their zeroth piece are
retained in the bounded realization (`app:ch_regular:eq:chain-tail`). -/
theorem outputPrefix_eq_physicalCutoff (N : ℕ) (ξ : E) :
    (∑ k ∈ Finset.range (N + 1), outputCutoff k ξ) = physicalCutoff (2 ^ N - 1) ξ := by
  rw [sum_outputCutoff_succ, expandingCutoff_eq_producer_dyadic]

/-- Removing the output cutoff remains valid while the graph-regularized
datum varies strongly. Contractivity supplies the uniform control; no
operator-tail estimate is assumed (`app:ch_regular:eq:chain-tail`). -/
theorem tendsto_outputMultiplier_diagonal
    (Mo : H →L[ℂ] H) (v : ℕ → H) (w : H) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun N ↦ (1 - Mo) (multiplier (2 ^ N - 1) (v N))) atTop
      (𝓝 ((1 - Mo) w)) := by
  have hz : Tendsto (fun N ↦ multiplier (2 ^ N - 1) (v N - w)) atTop (𝓝 (0 : H)) :=
    squeeze_zero_norm (fun N ↦ multiplier_norm_le _ _)
      (by simpa only [sub_self, norm_zero] using (hv.sub_const w).norm)
  have hlim := hz.add ((multiplier_tendsto w).comp tendsto_graphShell_producer_indices)
  simp only [Function.comp_def, map_sub, sub_add_cancel, zero_add] at hlim
  exact (1 - Mo).continuous.continuousAt.tendsto.comp hlim

/-- Graph and output regularizations may tend to infinity independently.
The contraction estimate is uniform in the output index, so no relation
between the two cutoffs is introduced (`app:ch_regular:eq:chain-tail`). -/
theorem tendsto_outputMultiplier_independent
    (Mo : H →L[ℂ] H) (v : ℕ → H) (w : H) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun p : ℕ × ℕ ↦ (1 - Mo) (multiplier (2 ^ p.2 - 1) (v p.1))) atTop
      (𝓝 ((1 - Mo) w)) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hz : Tendsto (fun p : ℕ × ℕ ↦ multiplier (2 ^ p.2 - 1) (v p.1 - w)) atTop
      (𝓝 (0 : H)) :=
    squeeze_zero_norm (fun p ↦ multiplier_norm_le _ _)
      (by simpa only [Function.comp_def, sub_self, norm_zero] using
        ((hv.comp hfst).sub_const w).norm)
  have hlim := hz.add
    (((multiplier_tendsto w).comp tendsto_graphShell_producer_indices).comp hsnd)
  simp only [Function.comp_def, map_sub, sub_add_cancel, zero_add] at hlim
  exact (1 - Mo).continuous.continuousAt.tendsto.comp hlim

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
