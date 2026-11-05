module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.Uniform.Jets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerSobolev

/-!
# Uniform all-data identity leakage for the selected proof masks

The common joint profiles, frequency carrier and diagonal buffer determine
one Sobolev estimate before the mask witnesses vary. The same bounded
left/right realizations and the single identity complement are preserved.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The common mask profile and positive diagonal buffer imply rapid leakage
of the literal identity term on ALL L² inputs. The bound is proved by the
uniform kernel jets, Schur estimates and weak-derivative realization; it is
not an assumption on chart leakage. The geometric inputs are the support,
derivative and nesting clauses of `SelectedSectorEvenNestedMaskConclusion`.
Constants precede its varying masks and coefficient fields. Consumer: the
single identity subtraction in the uniform complete physical residual
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakage_fourierSobolev_bound_of_uniform_profiles
    (R : ℝ) (I O : ℕ → ℝ) (hI : ∀ k, 0 ≤ I k) (hO : ∀ k, 0 ≤ O k)
    {buffer : ℝ} (hbuffer : 0 < buffer) (m : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → (∀ p, mo p ∈ Icc (0 : ℝ) 1) →
      Prod.snd '' tsupport mi ⊆ Metric.closedBall (0 : E) R →
      (∀ k z, ‖iteratedFDeriv ℝ k mi z‖ ≤ I k) →
      (∀ k z, ‖iteratedFDeriv ℝ k mo z‖ ≤ O k) →
      (∀ p ∈ tsupport mi, Metric.closedBall p buffer ⊆ interior {p | mo p = 1}) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (Mi Mo : H →L[ℂ] H),
      (∀ u, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      ∀ N (u : H),
        MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (Mi u)) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (Mi u)) ≤
          C N * ρ ^ (n + m) * (L / ρ) ^ N * ‖u‖ := by
  choose B hB hb using exists_identityLeakageScalarKernel_buffered_jet_decay_of_uniform_profiles
    R I O hI hO hbuffer m (n + 1)
  obtain ⟨C, hC, hSobolev⟩ :=
    PhysicalTailSobolev.exists_physicalTail_vector_fourierSobolev_constant (n := n) (r := r) m
  refine ⟨fun N ↦ C * B N, fun N ↦ mul_nonneg hC (hB N), ?_⟩
  intro mi mo hi his ho horange hfreq hiBound hoBound hplateau ρ L hL hLρ Mi Mo hMi hMo N u
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have h := hSobolev (identityLeakageScalarKernel ρ mi mo)
    (contDiff_identityLeakageScalarKernel hρ mi mo hi his ho)
    (B N * ρ ^ (n + m) * (L / ρ) ^ N)
    (mul_nonneg (mul_nonneg (hB N) (pow_nonneg hρ.le _))
      (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ.le) _))
    (hb N mi mo hi his ho hfreq hiBound hoBound hplateau ρ L hL hLρ) ((1 - Mo).comp Mi)
    (bounded_identityLeakage_graphTest_action hρ.ne' mi mo hi his ho.continuous horange
      Mi Mo hMi hMo) u
  exact ⟨h.1, h.2.trans_eq (by ring)⟩


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
