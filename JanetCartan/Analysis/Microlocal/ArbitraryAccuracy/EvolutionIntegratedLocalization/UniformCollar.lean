module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CollarGeometry

/-!
# One collar for a compact family of elapsed kernels

The comparable-frequency estimate in `app:ch_regular:eq:chain-tail` needs
constants uniform in the external bases and the finite chart index. Applying
the single-kernel collar theorem separately does not supply that uniformity.
Here compactness is used on the total buffered carrier, including the external
parameters. A single cutoff, both positive gaps, the first-derivative bound
and every cutoff derivative constant are chosen before the parameter and the
integration accuracy. The open domains may depend on the parameter.

The parent supplies the compact total carrier and the diagonal/interior
stationary exclusions proved in `GradientGaps`. It may use a finite discrete
chart index times compact physical base sets as the parameter space. No
arbitrary-energy fixed-elapsed graph exclusion is required.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FiniteChain.Graph JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}

/-- The finite-family carrier used to make the constants in
`app:ch_regular:eq:chain-tail` uniform in both external bases. The three
covectors, elapsed time, actual closed source shoulders and entire output
complement are all retained. -/
def elapsedFiniteFamilyCarrier {α : Type*} [TopologicalSpace α]
    (B : α → Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (K : α → Set (ℝ × JointVariables (Euclidean (d + 1))))
    (mi mo : α → LocalizerSymbol (d + 1)) :
    Set ((α × (Euclidean (d + 1) × Euclidean (d + 1))) ×
      (ℝ × JointVariables (Euclidean (d + 1)))) :=
  {t | t.1.2 ∈ B t.1.1 ∧
    t.2 ∈ elapsedOutputJetCarrier (K t.1.1) (mi t.1.1) (mo t.1.1) t.1.2.1 t.1.2.2}

/-- Compact base and integration carriers give a compact total buffered
carrier for any finite family of charts. In particular the identity term
in the output complement does not require compact symbol support. Consumer:
`exists_compactFamily_jointElapsedPhase_collar_data`
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_elapsedFiniteFamilyCarrier {α : Type*} [Finite α] [TopologicalSpace α]
    (B : α → Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (K : α → Set (ℝ × JointVariables (Euclidean (d + 1))))
    (mi mo : α → LocalizerSymbol (d + 1))
    (hB : ∀ j, IsCompact (B j)) (hK : ∀ j, IsCompact (K j)) :
    IsCompact (elapsedFiniteFamilyCarrier B K mi mo) := by
  let C j := (B j ×ˢ K j) ∩
    {p : (Euclidean (d + 1) × Euclidean (d + 1)) ×
        (ℝ × JointVariables (Euclidean (d + 1))) |
      (p.1.2, p.2.2.2.2.1) ∈ tsupport (mi j) ∧
      (p.1.1, p.2.2.2.2.2) ∈ tsupport (fun z ↦ 1 - mo j z)}
  have hC j : IsCompact (C j) := (hB j |>.prod (hK j)).inter_right
    (((isClosed_tsupport (mi j)).preimage (by fun_prop)).inter
      ((isClosed_tsupport (fun z ↦ 1 - mo j z)).preimage (by fun_prop)))
  have he : elapsedFiniteFamilyCarrier B K mi mo =
      ⋃ j, (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) ×
        (ℝ × JointVariables (Euclidean (d + 1))) ↦ ((j, p.1), p.2)) '' C j := by
    ext ⟨⟨j, x, y⟩, p⟩
    constructor
    · intro ht
      exact mem_iUnion.mpr ⟨j, ⟨((x, y), p), ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩, rfl⟩⟩
    · intro ht
      obtain ⟨j', ⟨⟨x', y'⟩, p'⟩, hz, hez⟩ := mem_iUnion.mp ht
      simp only [Prod.mk.injEq] at hez
      rcases hez with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
  rw [he]
  exact isCompact_iUnion (fun j ↦ (hC j).image (by fun_prop))

/-- Uniform geometric inputs to the differentiated half-space estimate on a
compact *total* buffered carrier. The fibers need not be a common rectangle:
closed source shoulders and the output complement may depend on the external
bases. All constants and the smooth collar are shared by every fiber, and
are independent of the requested accuracy (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_compactFamily_jointElapsedPhase_collar_data
    {X ι κ : Type*} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κ ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (backward : Bool) (Ψ : X → TwoTimePhase d) (x y : X → Euclidean (d + 1))
    {K : Set (X × (ℝ × JointVariables (Euclidean (d + 1))))} (hK : IsCompact K)
    (hF : ∀ t, ContDiff ℝ ∞ (jointElapsedPhase backward (Ψ t) (x t) (y t)))
    (hcontB : ∀ t ∈ K, ContinuousAt
      (fun tr : (X × (ℝ × JointVariables (Euclidean (d + 1)))) × ℝ ↦
        fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ tr.1.1) (x tr.1.1) (y tr.1.1)
          (tr.2, w)) tr.1.2.2) (t, 0))
    (hcontI : ContinuousOn (fun t : X × (ℝ × JointVariables (Euclidean (d + 1))) ↦
      fderiv ℝ (jointElapsedPhase backward (Ψ t.1) (x t.1) (y t.1)) t.2) K)
    (hB : ∀ t ∈ K,
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ t.1) (x t.1) (y t.1) (0, w))
        t.2.2 ≠ 0)
    (hI : ∀ t ∈ K, 0 < t.2.1 →
      fderiv ℝ (jointElapsedPhase backward (Ψ t.1) (x t.1) (y t.1)) t.2 ≠ 0) :
    ∃ (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ)
      (UT UI : X → Set (ℝ × JointVariables (Euclidean (d + 1))))
      (ε δT δI G : ℝ) (H : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ t, IsOpen (UT t)) ∧ (∀ t, IsOpen (UI t)) ∧
      0 < ε ∧ 0 < δT ∧ 0 < δI ∧
      (∀ p, |p.1| < ε → χ p = 1) ∧
      (∀ t, {p | (t, p) ∈ K} ∩ tsupport χ ⊆ UT t) ∧
      (∀ t, ({p | (t, p) ∈ K} ∩ tsupport (1 - χ)) ∩ {p | 0 < p.1} ⊆ UI t) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT t →
        δT ≤ phaseGradientSquare eT
          (fun w ↦ jointElapsedPhase backward (Ψ t) (x t) (y t) (r, w)) p) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT t →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) (r, p)‖ ≤ G) ∧
      (∀ t p, p ∈ UI t ∩ {p | 0 < p.1} →
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (Ψ t) (x t) (y t)) p) ∧
      (∀ t p, p ∈ UI t ∩ {p | 0 < p.1} →
        ‖fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) p‖ ≤ G) ∧
      (∀ j, 0 ≤ H j) ∧
      (∀ p ∈ Prod.snd '' K, ∀ j, ‖iteratedFDeriv ℝ j χ p‖ ≤ H j) := by
  let F t := jointElapsedPhase backward (Ψ t) (x t) (y t)
  obtain ⟨ε, hε, δT, hδT, hgapT⟩ := exists_jointElapsedPhase_boundary_collar_gap hK eT
    backward (fun t ↦ Ψ t.1) (fun t ↦ x t.1) (fun t ↦ y t.1)
    (fun t ↦ t.2.2) hcontB hB
  have hKI : IsCompact (K ∩ {t | ε / 4 ≤ t.2.1}) :=
    hK.inter_right (isClosed_le continuous_const continuous_snd.fst)
  obtain ⟨δI, hδI, hgapI⟩ := exists_jointElapsedPhase_interior_gap hKI eI backward
    (fun t ↦ Ψ t.1) (fun t ↦ x t.1) (fun t ↦ y t.1) Prod.snd
    (hcontI.mono inter_subset_left)
    (fun t ht ↦ hI t ht.1 (lt_of_lt_of_le (by positivity) ht.2))
  obtain ⟨G, hG⟩ := hK.exists_bound_of_continuousOn hcontI
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ := fun p ↦ (f p.1 : ℂ)
  have hχ : ContDiff ℝ ∞ χ :=
    Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_fst)
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
    exact hp (by simp only [Pi.sub_apply, Pi.one_apply,
      hχone p (le_of_not_ge hn), sub_self])
  have hdf t : Continuous (fderiv ℝ (F t)) := (hF t).continuous_fderiv (by simp)
  have hsqT t : Continuous (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      phaseGradientSquare eT (fun w ↦ F t (p.1, w)) p.2) := by
    have ht : ContDiff ℝ ∞ (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
        fderiv ℝ (fun w ↦ F t (p.1, w)) p.2) := by
      apply ContDiff.fderiv (m := ∞) (g := Prod.snd) _ contDiff_snd (by simp)
      exact (hF t).comp (contDiff_fst.fst.prodMk contDiff_snd)
    unfold phaseGradientSquare
    exact continuous_finsetSum _ fun i _ ↦ (ht.continuous.clm_apply continuous_const).pow 2
  have hsqI t : Continuous (phaseGradientSquare eI (F t)) := by
    unfold phaseGradientSquare
    exact continuous_finsetSum _ fun i _ ↦ ((hdf t).clm_apply continuous_const).pow 2
  let UT t := {p : ℝ × JointVariables (Euclidean (d + 1)) |
    δT / 2 < phaseGradientSquare eT (fun w ↦ F t (p.1, w)) p.2} ∩
      {p | ‖fderiv ℝ (F t) p‖ < G + 1}
  let UI t := {p : ℝ × JointVariables (Euclidean (d + 1)) |
    δI / 2 < phaseGradientSquare eI (F t) p} ∩ {p | ‖fderiv ℝ (F t) p‖ < G + 1}
  refine ⟨χ, UT, UI, ε / 4, δT / 2, δI / 2, G + 1,
    fun j ↦ cNorm (Prod.snd '' K) j χ, hχ, ?_, ?_, by positivity,
    half_pos hδT, half_pos hδI, fun p hp ↦ hχone p hp.le,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t ↦ (isOpen_lt continuous_const (hsqT t)).inter
      (isOpen_lt (hdf t).norm continuous_const)
  · exact fun t ↦ (isOpen_lt continuous_const (hsqI t)).inter
      (isOpen_lt (hdf t).norm continuous_const)
  · intro t p hp
    have hg := hgapT (t, p) hp.1 p.1 ((hχsupp hp.2).trans (by linarith))
    exact ⟨(half_lt_self hδT).trans_le hg, (hG (t, p) hp.1).trans_lt (lt_add_one G)⟩
  · intro t p hp
    have hr : ε / 4 ≤ |p.1| := hcompsupp hp.1.2
    rw [abs_of_pos (show 0 < p.1 from hp.2)] at hr
    exact ⟨(half_lt_self hδI).trans_le (hgapI (t, p) ⟨hp.1.1, hr⟩),
      (hG (t, p) hp.1.1).trans_lt (lt_add_one G)⟩
  · exact fun _ _ _ _ hp ↦ hp.1.le
  · exact fun _ _ _ _ hp ↦ hp.2.le
  · exact fun _ _ hp ↦ hp.1.1.le
  · exact fun _ _ hp ↦ hp.1.2.le
  · exact fun j ↦ cNorm_nonneg _ j χ
  · exact fun p hp j ↦ norm_iteratedFDeriv_le_cNorm (hK.image continuous_snd)
      (hχ.of_le (by simp)) hp le_rfl

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
