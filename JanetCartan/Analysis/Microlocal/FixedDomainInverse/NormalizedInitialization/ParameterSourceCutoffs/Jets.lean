module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.UniformJetLimit.BranchBounds

/-!
# Fixed parameter cutoff jets

The active/inactive split of `app:ch_response:eq:fixed-factor-transfer`
multiplies the original source by a fixed smooth scalar cutoff and its
complement. Compact support bounds the cutoff's derivatives uniformly. The
complement has the same positive-order derivatives up to sign; its zeroth
order also contains the constant one. No compactness of the complement is
asserted or used.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ParameterSourceCutoffs

open ResponseTransfer.Complement.ParameterDerivatives

variable {P H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- The real scalar Leibniz formula for the unchanged source and its ordered
parameter jets. The original splitting keeps every multiplicity
(`app:ch_response:cor:finite-jets`). -/
theorem parameterListJet_real_smul (χ : P → ℝ) (f : P → H) {V : Set P}
    (hV : IsOpen V) (hχ : ContDiffOn ℝ ∞ χ V) (hf : ContDiffOn ℝ ∞ f V)
    (ps : List P) {c : P} (hc : c ∈ V) :
    parameterListJet (fun b ↦ χ b • f b) ps c =
      ((parameterLeibnizSplittings ps).map (fun q ↦
        parameterListJet χ q.1 c • parameterListJet f q.2 c)).sum := by
  have hχc : ContDiffOn ℝ ∞ (fun b ↦ (χ b : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hχ
  have hj (vs : List P) : parameterListJet (fun b ↦ (χ b : ℂ)) vs c =
      ((parameterListJet χ vs c : ℝ) : ℂ) := by
    unfold parameterListJet
    change iteratedFDeriv ℝ vs.length (Complex.ofRealCLM ∘ χ) c vs.get = _
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left
      (hχ.contDiffAt (hV.mem_nhds hc)) (by simp)]
    rfl
  have hh := parameterListJet_smul (fun b ↦ (χ b : ℂ)) f hV hχc hf ps hc
  have hscalar (a : ℝ) (w : H) : (a : ℂ) • w = a • w := algebraMap_smul ℂ a w
  simpa only [hj,hscalar] using hh

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H] in
/-- One family of constants bounds both fixed cutoff branches, uniformly over
all parameter points and all unit direction lists of bounded length. This is
the only cutoff cost in the reserved source profiles of
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_cutoff_and_complement_list_jet_bounds
    (χ : P → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ B : ℕ → ℝ, (∀ l, 0 ≤ B l) ∧
      ∀ l (ps : List P), ps.length ≤ l → (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ c,
        ‖parameterListJet χ ps c‖ ≤ B l ∧
        ‖parameterListJet (fun b ↦ 1 - χ b) ps c‖ ≤ B l := by
  choose C hC hbound using fun l ↦ hcχ.exists_bound_iteratedFDeriv hχ l
  refine ⟨fun l ↦ 1 + C l, fun l ↦ add_nonneg zero_le_one (hC l), ?_⟩
  intro l ps hlen hps c
  have hb : ‖parameterListJet χ ps c‖ ≤ C l := by
    unfold parameterListJet
    have he := (iteratedFDeriv ℝ ps.length χ c).le_opNorm_mul_prod_of_le
      (fun j ↦ hps (ps.get j) (List.get_mem ps j))
    simpa only [Finset.prod_const_one, mul_one] using he.trans
      (by simpa only [Finset.prod_const_one, mul_one] using hbound l ps.length hlen c)
  have hconst : ‖parameterListJet (fun _ : P ↦ (1 : ℝ)) ps c‖ ≤ 1 := by
    by_cases hz : ps.length = 0
    · have hp : ps = [] := List.length_eq_zero_iff.mp hz
      subst ps
      simp [parameterListJet]
    · simp [parameterListJet, iteratedFDeriv_const_of_ne hz]
  have hsub : parameterListJet (fun b ↦ 1 - χ b) ps c =
      parameterListJet (fun _ : P ↦ (1 : ℝ)) ps c - parameterListJet χ ps c := by
    unfold parameterListJet
    change iteratedFDeriv ℝ ps.length ((fun _ : P ↦ (1 : ℝ)) - χ) c ps.get = _
    rw [iteratedFDeriv_sub_apply contDiffAt_const
      (hχ.of_le (by simp)).contDiffAt]
    rfl
  refine ⟨hb.trans (by linarith), ?_⟩
  rw [hsub]
  exact (norm_sub_le _ _).trans (add_le_add hconst hb)

end JanetCartan.FixedDomainInverse.ParameterSourceCutoffs
