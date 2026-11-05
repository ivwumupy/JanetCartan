module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Vector

/-!
# The actual identity leakage between the same bounded localizers

The original compact smooth masks and their strict diagonal plateau give
an L²-to-Fourier-Hᵐ estimate for `(1-Mo) Mi`, with no differentiated datum
and no assumed kernel or operator bound. This supplies the identity term
of the principal defect in `finiteChain_observation_rapidDecayAt.hleak`,
for both literal orientations (`app:ch_regular:eq:chain-tail`).
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
set_option maxHeartbeats 1000000

/-- The existing literal left/right bounded realizations have the same
identity-leakage kernel on the dense graph tests. The hypotheses are exactly
those produced by `exists_bounded_physicalLocalizers`
(`app:ch_regular:eq:chain-tail`). -/
theorem bounded_identityLeakage_graphTest_action {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : Continuous mo) (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (Mi Mo : H →L[ℂ] H)
    (hMi : ∀ u, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hMo : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (u : graphTestSpace n r) :
    ((1 - Mo).comp Mi) (graphTestToLp u) =ᵐ[volume]
      fun x ↦ ∫ y, identityLeakageScalarKernel ρ mi mo x y • u.val y := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  have huSmooth : ContDiff ℝ ∞ (fun y : E ↦ (u.val y).ofLp) :=
    (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp u.property.1
  have huSupport : HasCompactSupport (fun y : E ↦ (u.val y).ofLp) :=
    u.property.2.comp_left e.map_zero
  let f : SchwartzMap E (Fin r → ℂ) := huSupport.toSchwartzMap huSmooth
  have hinput : (FrequencyCutoff.toEuclideanSchwartz f).toLp 2 = graphTestToLp u := by
    apply Lp.ext
    filter_upwards [(FrequencyCutoff.toEuclideanSchwartz f).coeFn_toLp 2,
      (graphTest_memLp u).coeFn_toLp] with y hy hy'
    exact hy.trans hy'.symm
  have h := bounded_identityLeakage_schwartz_ae_scalarKernel hρ mi mo hi his ho horange
    Mi Mo hMi hMo f
  rw [hinput] at h
  refine h.trans (.of_forall fun x ↦ ?_)
  exact (e.symm.integral_comp_comm (μ := volume)
    (fun y ↦ identityLeakageScalarKernel ρ mi mo x y • (u.val y).ofLp)).symm

/-- All-data rapid identity leakage for the SAME fixed localizers. The strict
plateau actually produces all weighted jets, which are passed to the proved
Schur/weak-derivative/Fourier-Sobolev endpoint. The loss `ρ^(n+m)` is independent
of accuracy and there is no coefficient loss. The realization premises come
from `exists_bounded_physicalLocalizers`; the plateau is the output of
`exists_diagonal_bufferedLocalizers_joint_gap`. This is the missing identity
summand in the principal PDO defect, in either literal orientation
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakage_fourierSobolev_bound
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) (m : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
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
  choose B hB hb using exists_identityLeakageScalarKernel_buffered_jet_decay
    mi mo hi his ho hos hplateau m (n + 1)
  obtain ⟨C, hC, hSobolev⟩ :=
    PhysicalTailSobolev.exists_physicalTail_vector_fourierSobolev_constant (n := n) (r := r) m
  refine ⟨fun N ↦ C * B N, fun N ↦ mul_nonneg hC (hB N), ?_⟩
  intro ρ L hL hLρ Mi Mo hMi hMo N u
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have h := hSobolev (identityLeakageScalarKernel ρ mi mo)
    (contDiff_identityLeakageScalarKernel hρ mi mo hi his ho)
    (B N * ρ ^ (n + m) * (L / ρ) ^ N)
    (mul_nonneg (mul_nonneg (hB N) (pow_nonneg hρ.le _))
      (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ.le) _))
    (hb N ρ L hL hLρ) ((1 - Mo).comp Mi)
    (bounded_identityLeakage_graphTest_action hρ.ne' mi mo hi his ho.continuous horange
      Mi Mo hMi hMo) u
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
