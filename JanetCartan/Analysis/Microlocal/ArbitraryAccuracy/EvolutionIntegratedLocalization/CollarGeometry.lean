module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.GradientGaps
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputJets

/-!
# A fixed collar and open integration domains from buffered separation

The two nonstationarity statements proved in `GradientGaps` produce the
entire geometric input to the half-space estimate for
`app:ch_regular:eq:chain-tail`: a smooth collar partition, its fixed derivative
profile, open domains, positive squared-gradient gaps and upper bounds.
All choices precede the requested integration accuracy. Only the positive
interior is used; no gap is imposed at arbitrary negative elapsed times.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FiniteChain.Graph JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}

/-- Construct the fixed smooth collar and both open integration domains from
the actual boundary and interior stationary-point exclusions. The exclusions
are produced by the diagonal and zero-energy buffer theorems in
`GradientGaps`; the parent supplies the compact joint carrier. This closes
the collar/domain hypotheses of the half-space estimate, without assuming
a successful kernel estimate (`app:ch_regular:lem:finite-chain`). -/
theorem exists_jointElapsedPhase_collar_data
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κ ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (backward : Bool) (Ψ : TwoTimePhase d) (x y : Euclidean (d + 1))
    {K : Set (ℝ × JointVariables (Euclidean (d + 1)))} (hK : IsCompact K)
    (hF : ContDiff ℝ ∞ (jointElapsedPhase backward Ψ x y))
    (hB : ∀ p ∈ K,
      fderiv ℝ (fun w ↦ jointElapsedPhase backward Ψ x y (0, w)) p.2 ≠ 0)
    (hI : ∀ p ∈ K, 0 < p.1 → fderiv ℝ (jointElapsedPhase backward Ψ x y) p ≠ 0) :
    ∃ (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ)
      (UT UI : Set (ℝ × JointVariables (Euclidean (d + 1))))
      (ε δT δI G : ℝ) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ IsOpen UT ∧ IsOpen UI ∧ 0 < ε ∧ 0 < δT ∧ 0 < δI ∧
      (∀ p, |p.1| < ε → χ p = 1) ∧
      K ∩ tsupport χ ⊆ UT ∧
      (K ∩ tsupport (1 - χ)) ∩ {p | 0 < p.1} ⊆ UI ∧
      (∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
        δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward Ψ x y (r, w)) p) ∧
      (∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT →
        ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) (r, p)‖ ≤ G) ∧
      (∀ p ∈ UI ∩ {p | 0 < p.1},
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward Ψ x y) p) ∧
      (∀ p ∈ UI ∩ {p | 0 < p.1}, ‖fderiv ℝ (jointElapsedPhase backward Ψ x y) p‖ ≤ G) ∧
      (∀ j, 0 ≤ H j) ∧ (∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j χ p‖ ≤ H j) := by
  let F := jointElapsedPhase backward Ψ x y
  have ht : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      fderiv ℝ (fun w ↦ F (p.1, w)) p.2) := by
    apply ContDiff.fderiv (m := ∞) (g := Prod.snd) _ contDiff_snd (by simp)
    exact hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hcont : ∀ p ∈ K, ContinuousAt
      (fun tr : (ℝ × JointVariables (Euclidean (d + 1))) × ℝ ↦
        fderiv ℝ (fun w ↦ F (tr.2, w)) tr.1.2) (p, 0) := by
    intro p _
    exact (ht.continuous.comp (continuous_snd.prodMk continuous_fst.snd)).continuousAt
  obtain ⟨ε, hε, δT, hδT, hgapT⟩ := exists_jointElapsedPhase_boundary_collar_gap hK eT
    backward (fun _ ↦ Ψ) (fun _ ↦ x) (fun _ ↦ y) Prod.snd hcont hB
  have hKI : IsCompact (K ∩ {p | ε / 4 ≤ p.1}) :=
    hK.inter_right (isClosed_le continuous_const continuous_fst)
  have hdf : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  obtain ⟨δI, hδI, hgapI⟩ := exists_jointElapsedPhase_interior_gap hKI eI backward
    (fun _ ↦ Ψ) (fun _ ↦ x) (fun _ ↦ y) id hdf.continuousOn
    (fun p hp ↦ hI p hp.1 (lt_of_lt_of_le (by positivity) hp.2))
  obtain ⟨G, hG⟩ := hK.exists_bound_of_continuousOn hdf.continuousOn
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ := fun p ↦ (f p.1 : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_fst)
  have hχone : ∀ p, |p.1| ≤ ε / 4 → χ p = 1 := by
    intro p hp
    have hf := f.one_of_mem_closedBall (x := p.1) (by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hp)
    simp only [χ, hf, Complex.ofReal_one]
  have hχsupp : tsupport χ ⊆ {p | |p.1| ≤ ε / 2} := by
    apply closure_minimal ?_ (isClosed_le continuous_fst.abs continuous_const)
    intro p hp
    by_contra hn
    have hz := f.zero_of_le_dist (x := p.1) (by
      simpa only [Real.dist_eq, sub_zero] using (le_of_not_ge hn))
    exact hp (by simp only [χ, hz, Complex.ofReal_zero])
  have hcompsupp : tsupport (1 - χ) ⊆ {p | ε / 4 ≤ |p.1|} := by
    apply closure_minimal ?_ (isClosed_le continuous_const continuous_fst.abs)
    intro p hp
    by_contra hn
    exact hp (by simp only [Pi.sub_apply, Pi.one_apply, hχone p (le_of_not_ge hn), sub_self])
  have hsqT : Continuous (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      phaseGradientSquare eT (fun w ↦ F (p.1, w)) p.2) := by
    unfold phaseGradientSquare
    exact continuous_finsetSum _ fun i _ ↦ (ht.continuous.clm_apply continuous_const).pow 2
  have hsqI : Continuous (phaseGradientSquare eI F) := by
    unfold phaseGradientSquare
    exact continuous_finsetSum _ fun i _ ↦ (hdf.clm_apply continuous_const).pow 2
  let UT := {p : ℝ × JointVariables (Euclidean (d + 1)) |
    δT / 2 < phaseGradientSquare eT (fun w ↦ F (p.1, w)) p.2} ∩
      {p | ‖fderiv ℝ F p‖ < G + 1}
  let UI := {p : ℝ × JointVariables (Euclidean (d + 1)) |
    δI / 2 < phaseGradientSquare eI F p} ∩ {p | ‖fderiv ℝ F p‖ < G + 1}
  have hUT : IsOpen UT := (isOpen_lt continuous_const hsqT).inter
    (isOpen_lt hdf.norm continuous_const)
  have hUI : IsOpen UI := (isOpen_lt continuous_const hsqI).inter
    (isOpen_lt hdf.norm continuous_const)
  refine ⟨χ, UT, UI, ε / 4, δT / 2, δI / 2, G + 1, fun j ↦ cNorm K j χ,
    hχ, hUT, hUI, by positivity, half_pos hδT, half_pos hδI,
    fun p hp ↦ hχone p hp.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hg := hgapT p hp.1 p.1 ((hχsupp hp.2).trans (by linarith))
    exact ⟨(half_lt_self hδT).trans_le hg, (hG p hp.1).trans_lt (lt_add_one G)⟩
  · intro p hp
    have hr : ε / 4 ≤ |p.1| := hcompsupp hp.1.2
    rw [abs_of_pos (show 0 < p.1 from hp.2)] at hr
    exact ⟨(half_lt_self hδI).trans_le (hgapI p ⟨hp.1.1, hr⟩),
      (hG p hp.1.1).trans_lt (lt_add_one G)⟩
  · exact fun _ _ _ hp ↦ hp.1.le
  · exact fun _ _ _ hp ↦ hp.2.le
  · exact fun _ hp ↦ hp.1.1.le
  · exact fun _ hp ↦ hp.1.2.le
  · exact fun j ↦ cNorm_nonneg K j χ
  · exact fun p hp j ↦ norm_iteratedFDeriv_le_cNorm hK (hχ.of_le (by simp)) hp le_rfl

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
