module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets.Decay

/-!
# Jets of the literal physical cutoff tails

For the two physical tails in
`actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`, the original
smooth compact masks and their open plateau give arbitrary weighted decay of
every output jet. The exponent `n + m` is fixed independently of accuracy.
The downstream `PhysicalTailSobolev` construction uses these kernel bounds for
`app:ch_regular:eq:resolved-angular-tail` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The literal physical tail is jointly smooth, as follows from the original
compact frequency integral. Consumed by its Sobolev kernel realization
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem contDiff_rightLocalizerScalarKernel_physicalTail {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : E × E ↦
      ((1 - χ p.1 : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi p.1 p.2) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (hχ.comp contDiff_fst))).mul
    (contDiff_rightLocalizerScalarKernel hρ mi hi his)

/-- Derivative refinement of the physical cutoff-tail estimate for the SAME
literal kernel. The fixed compact smooth input jets produce every constant;
the original open plateau supplies the separation gap. The full multilinear
derivative norm is used, the source carrier is unchanged, and the frequency
exponent `n + m` is independent of accuracy. This supplies the two physical
tails in `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`, before
their independent Sobolev realization (`app:ch_regular:eq:resolved-angular-tail`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizerScalarKernel_physicalTail_jet_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χ x = 1})
    (m M : ℕ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ j ≤ m, ∀ x y : E,
      (1 + ‖x - y‖) ^ M *
        ‖iteratedFDeriv ℝ j
          (fun x ↦ ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) x‖ ≤
            C * ρ ^ (n + m) * (L / ρ) ^ N := by
  have hdis : Disjoint (Prod.fst '' tsupport mi) (tsupport (fun x ↦ 1 - χ x)) := by
    apply disjoint_left.mpr
    intro y hy hys
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hys
    filter_upwards [isOpen_interior.mem_nhds (hplateau y hy)] with z hz
    exact sub_eq_zero.mpr (interior_subset hz).symm
  obtain ⟨δ, hδ, hgap⟩ := CompatibleResponse.exists_uniform_source_gap
    (his.image continuous_fst) (isClosed_tsupport _) hdis
  have hχc : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hχcs : HasCompactSupport (fun x ↦ (χ x : ℂ)) :=
    hχs.comp_left (g := fun t : ℝ ↦ (t : ℂ)) rfl
  obtain ⟨A, hA, ha⟩ := hχcs.exists_bound_iteratedFDeriv hχc m
  have hcut : ContDiff ℝ ∞ (fun x ↦ ((1 - χ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hχ)
  have hcut_bound : ∀ k ≤ m, ∀ x,
      ‖iteratedFDeriv ℝ k (fun x ↦ ((1 - χ x : ℝ) : ℂ)) x‖ ≤ 1 + A := by
    intro k hk x
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (hχrange x).2)]
      linarith [(hχrange x).1]
    | succ k =>
      have he : (fun x ↦ ((1 - χ x : ℝ) : ℂ)) =
          (fun _ ↦ (1 : ℂ)) - (fun x ↦ (χ x : ℂ)) := by
        funext x
        simp
      rw [he, iteratedFDeriv_sub_apply contDiffAt_const (hχc.contDiffAt.of_le (by simp)),
        iteratedFDeriv_succ_const, Pi.zero_apply, zero_sub, norm_neg]
      exact (ha (k + 1) hk x).trans (by linarith)
  intro N
  obtain ⟨B, hB, hb⟩ :=
    exists_rightLocalizerScalarKernel_separated_jet_decay mi hi his hδ m M N
  refine ⟨2 ^ m * (1 + A) * B, by positivity, ?_⟩
  intro ρ L hL hLρ j hj x y
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  by_cases hy : y ∈ Prod.fst '' tsupport mi
  · by_cases hx : x ∈ tsupport (fun x ↦ 1 - χ x)
    · have hd : δ ≤ ‖x - y‖ := by
        simpa only [dist_eq_norm, norm_sub_rev] using (hgap y hy x hx).le
      have hk : ContDiff ℝ ∞ (fun x ↦ rightLocalizerScalarKernel ρ mi x y) :=
        (contDiff_rightLocalizerScalarKernel hρ.ne' mi hi his).comp (f := fun x : E ↦ (x, y))
          (contDiff_id.prodMk contDiff_const)
      have hchoose : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      calc
        _ ≤ (1 + ‖x - y‖) ^ M * ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun x ↦ ((1 - χ x : ℝ) : ℂ)) x‖ *
              ‖iteratedFDeriv ℝ (j - k) (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hcut hk x (by simp))
            (by positivity)
        _ = ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun x ↦ ((1 - χ x : ℝ) : ℂ)) x‖ *
              ((1 + ‖x - y‖) ^ M *
                ‖iteratedFDeriv ℝ (j - k) (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * (1 + A) * (B * ρ ^ (n + m) * (L / ρ) ^ N) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hcut_bound k (by
              have := Finset.mem_range.mp hk
              omega) x) (Nat.cast_nonneg _))
            (hb ρ L hL hLρ (j - k) ((Nat.sub_le _ _).trans hj) x y hd)
            (by positivity) (by positivity)
        _ = 2 ^ j * (1 + A) * (B * ρ ^ (n + m) * (L / ρ) ^ N) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
        _ ≤ 2 ^ m * (1 + A) * (B * ρ ^ (n + m) * (L / ρ) ^ N) := by
          gcongr
          norm_num
        _ = _ := by ring
    · have hsupport : tsupport (fun x ↦
          ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) ⊆
            tsupport (fun x ↦ 1 - χ x) := by
        apply tsupport_mul_subset_left.trans
        apply closure_mono
        intro z hz
        simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hz
      rw [image_eq_zero_of_notMem_tsupport
        (fun hh ↦ hx (hsupport (tsupport_iteratedFDeriv_subset j hh))), norm_zero, mul_zero]
      positivity
  · rw [iteratedFDeriv_rightLocalizerScalarKernel_physicalTail_zero_off_input ρ mi χ j x y hy,
      norm_zero, mul_zero]
    positivity

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
