module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.Jets

/-!
# Support of the same active and inactive sources

Parameter multiplication preserves the source's spatial support. Its parameter
support is contained in the intersection of the original closed support and
the support of the chosen scalar branch. These are the literal source-support
conditions for the two branches of `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ParameterSourceCutoffs

variable {X P F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed parameter multiplier preserves the joint smooth source used in
`app:ch_response:cor:finite-jets`. -/
theorem contDiff_parameter_smul (χ : P → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (a : X × P → F) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun q : X × P ↦ χ q.2 • a q) :=
  (hχ.comp contDiff_snd).smul ha

omit [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The same spatial compact support is retained by either parameter branch
of `app:ch_response:eq:fixed-factor-transfer`. -/
theorem parameter_smul_eq_zero_off_spatial_support
    (χ : P → ℝ) (a : X × P → F) {S : Set X}
    (hs : ∀ q, q.1 ∉ S → a q = 0) :
    ∀ q, q.1 ∉ S → χ q.2 • a q = 0 := by
  intro q hq
  rw [hs q hq, smul_zero]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℝ P] in
/-- At each fixed spatial point, parameter multiplication confines the source
to the original closed parameter support and the scalar branch's support.
Use `χ` on the active branch and `1-χ` on the inactive branch in
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem tsupport_parameter_smul_subset
    (χ : P → ℝ) (a : X × P → F) {C : Set P} (hC : IsClosed C)
    (hs : ∀ q, q.2 ∉ C → a q = 0) (y : X) :
    tsupport (fun c ↦ χ c • a (y,c)) ⊆ C ∩ tsupport χ := by
  have ha : tsupport (fun c ↦ a (y,c)) ⊆ C := by
    apply closure_minimal _ hC
    intro c hc
    by_contra hn
    exact hc (hs (y,c) hn)
  exact subset_inter ((tsupport_smul_subset_right χ (fun c ↦ a (y,c))).trans ha)
    (tsupport_smul_subset_left χ (fun c ↦ a (y,c)))

omit [NormedSpace ℝ X] [NormedSpace ℝ P] in
/-- Joint topological support of the literal cutoff source. In the selected
inactive graph estimate the second factor is exactly
`C ∩ tsupport (1-χ)`; no noncompact complement is promoted to a compact set
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem tsupport_parameter_smul_subset_product
    (χ : P → ℝ) (a : X × P → F) {S : Set X} {C : Set P}
    (hS : IsClosed S) (hC : IsClosed C)
    (hspatial : ∀ q, q.1 ∉ S → a q = 0)
    (hparameter : ∀ q, q.2 ∉ C → a q = 0) :
    tsupport (fun q : X × P ↦ χ q.2 • a q) ⊆ S ×ˢ (C ∩ tsupport χ) := by
  apply closure_minimal _ (hS.prod (hC.inter (isClosed_tsupport χ)))
  intro q hq
  change χ q.2 • a q ≠ 0 at hq
  have ha : a q ≠ 0 := fun hz ↦ hq (by rw [hz, smul_zero])
  have hχ : χ q.2 ≠ 0 := fun hz ↦ hq (by rw [hz, zero_smul])
  refine ⟨?_, ?_, subset_closure hχ⟩
  · by_contra hn
    exact ha (hspatial q hn)
  · by_contra hn
    exact ha (hparameter q hn)

end JanetCartan.FixedDomainInverse.ParameterSourceCutoffs
