module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerComposition
/-!
# Decay of the literal identity-leakage kernel

The fixed input/output masks supply frequency derivative constants. The
strict diagonal plateau cancels the kernel near the diagonal, and Fourier
integration by parts gives arbitrary weighted decay with an accuracy-independent
frequency loss. Consumer: the identity term in principal-defect leakage for
`finiteChain_observation_rapidDecayAt.hleak` (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
open FiniteChain.Retarded.KernelDecay
variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem exists_uniform_identityLeakage_frequency_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y θ : E,
      (1 + ‖θ‖) ^ N *
        ‖𝓕 (fun η ↦ (((1 - mo (x, η)) * mi (y, η) : ℝ) : ℂ)) θ‖ ≤ C := by
  let a : E × E → ℂ := fun p ↦ (mi p : ℂ)
  let b : (E × E) × E → ℂ := fun p ↦ (mo (p.1.1, p.2) : ℂ) * (mi (p.1.2, p.2) : ℂ)
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp hi
  have hb : ContDiff ℝ ∞ b :=
    (Complex.ofRealCLM.contDiff.comp (ho.comp (contDiff_fst.fst.prodMk contDiff_snd))).mul
      (Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_fst.snd.prodMk contDiff_snd)))
  have hca : HasCompactSupport a := his.comp_left (g := fun t : ℝ ↦ (t : ℂ)) rfl
  have hcb : HasCompactSupport b := by
    apply HasCompactSupport.intro
      (((hos.image continuous_fst).prod (his.image continuous_fst)).prod (his.image continuous_snd))
    intro p hp
    by_cases hi0 : mi (p.1.2, p.2) = 0
    · simp [b, hi0]
    by_cases ho0 : mo (p.1.1, p.2) = 0
    · simp [b, ho0]
    exact (hp ⟨⟨⟨_, subset_tsupport mo ho0, rfl⟩,
      ⟨_, subset_tsupport mi hi0, rfl⟩⟩, ⟨_, subset_tsupport mi hi0, rfl⟩⟩).elim
  obtain ⟨A, hA, hAb⟩ := hca.exists_bound_iteratedFDeriv ha N
  obtain ⟨B, hB, hBb⟩ := hcb.exists_bound_iteratedFDeriv hb N
  obtain ⟨R, _, hR⟩ := (his.image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : E)
  let v := volume.real (Metric.closedBall (0 : E) R)
  refine ⟨(2 ^ (N - 1) * (1 + 2 ^ N)) * ((N + 1 : ℕ) : ℝ) * v * (A + B),
    by dsimp [v]; positivity, ?_⟩
  intro x y θ
  let f : E → ℂ := fun η ↦ (((1 - mo (x, η)) * mi (y, η) : ℝ) : ℂ)
  have hsm : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.sub (ho.comp (contDiff_const.prodMk contDiff_id))).mul
      (hi.comp (contDiff_const.prodMk contDiff_id)))
  have hs : tsupport f ⊆ Metric.closedBall (0 : E) R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro η hη
    apply hR
    refine ⟨(y, η), subset_tsupport mi ?_, rfl⟩
    intro hh
    apply hη
    simp only [f, hh, mul_zero, Complex.ofReal_zero]
  have hc : HasCompactSupport f :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport _) hs
  have hj k (hk : k ≤ N) η : ‖iteratedFDeriv ℝ k f η‖ ≤ A + B := by
    have he : f = (fun η ↦ a (y, η)) - fun η ↦ b ((x, y), η) := by
      funext η
      simp only [f, a, b, Pi.sub_apply, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have ha' : ContDiff ℝ k (fun η ↦ a (y, η)) :=
      (ha.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have hb' : ContDiff ℝ k (fun η ↦ b ((x, y), η)) :=
      (hb.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    rw [he, iteratedFDeriv_sub ha' hb']
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_iteratedFDeriv_symbol_slice_le ha k y η).trans (hAb k hk (y, η)))
      ((norm_iteratedFDeriv_symbol_slice_le hb k (x, y) η).trans (hBb k hk ((x, y), η))))
  have hint k : Integrable (iteratedFDeriv ℝ k f) :=
    ((hsm.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).continuous).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv k)
  have hmass : Pseudodifferential.sourceDerivativeMass f N ≤
      ((N + 1 : ℕ) : ℝ) * v * (A + B) := by
    unfold Pseudodifferential.sourceDerivativeMass
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), v * (A + B) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Metric.closedBall (0 : E) R) (fun η hη ↦ by
            rw [image_eq_zero_of_notMem_tsupport
              (fun hh ↦ hη (hs (tsupport_iteratedFDeriv_subset k hh))), norm_zero])]
        calc
          _ ≤ ‖∫ η in Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ k f η‖‖ := le_abs_self _
          _ ≤ (A + B) * v := by
            apply norm_setIntegral_le_of_norm_le_const
              (isCompact_closedBall (0 : E) R).measure_lt_top
            intro η _
            simpa only [norm_norm] using hj k (by simpa using Finset.mem_range.mp hk) η
          _ = v * (A + B) := mul_comm _ _
      _ = _ := by simp [mul_assoc]
  exact (Pseudodifferential.one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    f N (hsm.of_le (by simp)) (fun k _ ↦ hint k) θ).trans
      ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring))

/-- Physical rescaling of the actual identity-leakage kernel. In contrast to
a separate low bound for the identity, the Fourier amplitude retains the
cancelling product of the SAME two masks (`app:ch_regular:eq:chain-tail`). -/
theorem identityLeakageScalarKernel_eq_fourier {ρ : ℝ} (hρ : 0 < ρ)
    (mi mo : LocalizerSymbol n) (x y : E) :
    identityLeakageScalarKernel ρ mi mo x y =
      ((ρ / (2 * Real.pi)) ^ n : ℝ) •
        𝓕 (fun η ↦ (((1 - mo (x, η)) * mi (y, η) : ℝ) : ℂ))
          (-(ρ / (2 * Real.pi)) • (x - y)) :=
  rightLocalizerScalarKernel_eq_fourier hρ (fun p ↦ (1 - mo (x, p.2)) * mi p) x y

/-- Uniform weighted kernel decay for the SAME identity leakage. The
frequency loss is `ρ^n`, independent of accuracy. All constants come from
fixed smooth compact input/output symbols (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 < ρ → ∀ x y : E,
      (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N * ‖identityLeakageScalarKernel ρ mi mo x y‖ ≤
        C * ρ ^ n := by
  intro N
  obtain ⟨B, hB, hb⟩ := exists_uniform_identityLeakage_frequency_decay mi mo hi his ho hos N
  refine ⟨B / (2 * Real.pi) ^ n, by positivity, ?_⟩
  intro ρ hρ x y
  rw [identityLeakageScalarKernel_eq_fourier hρ, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (ρ / (2 * Real.pi)) ^ n)]
  have h := hb x y (-(ρ / (2 * Real.pi)) • (x - y))
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / (2 * Real.pi))] at h
  calc
    _ = (ρ / (2 * Real.pi)) ^ n *
        ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          ‖𝓕 (fun η ↦ (((1 - mo (x, η)) * mi (y, η) : ℝ) : ℂ))
            (-(ρ / (2 * Real.pi)) • (x - y))‖) := by ring
    _ ≤ (ρ / (2 * Real.pi)) ^ n * B := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- Arbitrary weighted kernel decay for the actual `(1-Mo) Mi`, derived
from the SAME buffered localizers. The polynomial losses are fixed (`ρ^n`,
no coefficient loss); accuracy changes only the constant and `(L/ρ)^N`.
The positive separation is produced from the strict diagonal plateau, rather
than assumed as a decay estimate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_buffered_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) (M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ x y : E,
      (1 + ‖x - y‖) ^ M * ‖identityLeakageScalarKernel ρ mi mo x y‖ ≤
        C * ρ ^ n * (L / ρ) ^ N := by
  obtain ⟨δ, hδ, hzero⟩ := exists_identityLeakageScalarKernel_zero_near_diagonal
    mi mo his hplateau
  intro N
  obtain ⟨B, hB, hb⟩ := exists_identityLeakageScalarKernel_decay mi mo hi his ho hos (N + M)
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D := a ^ N * c ^ M
  have hD : 0 < D := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨B / D, div_nonneg hB hD.le, ?_⟩
  intro ρ L hL hLρ x y
  have hρnn : 0 ≤ ρ := (zero_lt_one.trans_le (hL.trans hLρ)).le
  have hLnn : 0 ≤ L := zero_le_one.trans hL
  by_cases hxy : ‖x - y‖ ≤ δ
  · rw [hzero ρ x y hxy, norm_zero, mul_zero]
    positivity
  have hgap : δ ≤ ‖x - y‖ := (lt_of_not_ge hxy).le
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hfreq : ρ * a ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      ρ * a = ρ / (2 * Real.pi) * δ := by dsimp [a]; ring
      _ ≤ ρ / (2 * Real.pi) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ ≤ _ := by linarith
  have hcρ : c ≤ ρ / (2 * Real.pi) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right hρ (by positivity))
  have hspace : c * (1 + ‖x - y‖) ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
    calc
      _ = c + c * ‖x - y‖ := by ring
      _ ≤ _ := add_le_add (min_le_left _ _)
        (mul_le_mul_of_nonneg_right hcρ (norm_nonneg _))
  have hcombined :
      (ρ ^ N * D) * ((1 + ‖x - y‖) ^ M * ‖identityLeakageScalarKernel ρ mi mo x y‖) ≤
        B * ρ ^ n := by
    calc
      _ = ((ρ * a) ^ N * (c * (1 + ‖x - y‖)) ^ M) *
          ‖identityLeakageScalarKernel ρ mi mo x y‖ := by
            dsimp [D]
            simp only [mul_pow]
            ring
      _ ≤ ((1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ N *
          (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ M) *
            ‖identityLeakageScalarKernel ρ mi mo x y‖ := by gcongr
      _ ≤ B * ρ ^ n := by rw [← pow_add]; exact hb ρ hρpos x y
  have hdiv := (le_div_iff₀ (mul_pos (pow_pos hρpos N) hD)).mpr
    (show ((1 + ‖x - y‖) ^ M * ‖identityLeakageScalarKernel ρ mi mo x y‖) *
      (ρ ^ N * D) ≤ B * ρ ^ n by simpa only [mul_comm] using hcombined)
  calc
    _ ≤ (B * ρ ^ n) / (ρ ^ N * D) := hdiv
    _ = (B / D) * ρ ^ n * (1 / ρ) ^ N := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by gcongr

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
