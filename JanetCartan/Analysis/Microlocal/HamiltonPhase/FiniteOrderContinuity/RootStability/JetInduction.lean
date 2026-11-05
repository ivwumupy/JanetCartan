module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.JetBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.LowOrder

/-!
# Higher root-jet differences

Subtracting the differentiated implicit equations in
`app:lem:common-hamilton-phase` gives the induction step for the planned
`exists_finiteOrder_root_stability_on_closedBall`. The single-block identity is
`scalarDerivative_smul_iteratedFDeriv_root`; every other partition uses strictly
lower root jets. Equation-jet comparisons are supplied by
`rootGraph_jet_sub_le_cNorm`, and the parent construction supplies the lower-jet
induction hypotheses and the fixed reference bounds.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem norm_rootGraph_jet_le {j : ℕ} (hj : 1 ≤ j)
    {g : P → ℝ} {p : P} {M : ℝ} (hM : 1 ≤ M)
    (hg : ContDiffAt ℝ j g p) (hb : ‖iteratedFDeriv ℝ j g p‖ ≤ M) :
    ‖iteratedFDeriv ℝ j (fun q ↦ (q, g q)) p‖ ≤ M := by
  by_cases hj1 : j = 1
  · subst j
    have hprod := iteratedFDeriv_prodMk contDiffAt_id hg le_rfl
    simp only [id_eq] at hprod
    rw [hprod, ContinuousMultilinearMap.opNorm_prod]
    apply max_le _ hb
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le.trans hM
  · rw [iteratedFDeriv_rootGraph_high (by omega) hg,
      ContinuousMultilinearMap.opNorm_prod, norm_zero]
    exact max_le (by linarith) hb

private theorem norm_rootGraph_jet_sub {j : ℕ} {g g₀ : P → ℝ} {p : P}
    (hg : ContDiffAt ℝ j g p) (hg₀ : ContDiffAt ℝ j g₀ p) :
    ‖iteratedFDeriv ℝ j (fun q ↦ (q, g q)) p -
      iteratedFDeriv ℝ j (fun q ↦ (q, g₀ q)) p‖ =
      ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ := by
  have h := iteratedFDeriv_prodMk contDiffAt_id hg le_rfl
  have h₀ := iteratedFDeriv_prodMk contDiffAt_id hg₀ le_rfl
  simp only [id_eq] at h h₀
  rw [h, h₀]
  have hprod (A : P [×j]→L[ℝ] P) (B B₀ : P [×j]→L[ℝ] ℝ) :
      A.prod B - A.prod B₀ = (0 : P [×j]→L[ℝ] P).prod (B - B₀) := by
    ext v <;> simp
  rw [hprod, ContinuousMultilinearMap.opNorm_prod, norm_zero,
    max_eq_right (norm_nonneg _)]

/-- The finite polynomial controlling the lower-root-jet remainder difference
in `app:lem:common-hamilton-phase`. It depends only on the order and jet budget. -/
def rootJetDifferenceConstant (n : ℕ) (M : ℝ) : ℝ :=
  ∑ s : OrderedFinpartition n with 2 ≤ s.length,
    (M * s.length * M ^ (s.length - 1) + M ^ s.length)

/-- Nonnegativity of the remainder difference constant used by the root
induction step in `app:lem:common-hamilton-phase`. -/
theorem rootJetDifferenceConstant_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ rootJetDifferenceConstant n M := by
  unfold rootJetDifferenceConstant
  positivity

/-- `app:lem:common-hamilton-phase`: the Faà di Bruno remainder difference
uses equation jets through `n` and root jets strictly below `n`. Its consumer is
`exists_root_jet_difference_step`; no top perturbed root bound is needed. -/
theorem norm_rootJetPartitionRemainder_sub_le {n : ℕ} {M ε : ℝ}
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    {f f₀ : P × ℝ → ℝ} {g g₀ : P → ℝ} {p : P}
    (hg : ContDiffAt ℝ n g p) (hg₀ : ContDiffAt ℝ n g₀ p)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (p, g p)‖ ≤ M)
    (hfdiff : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j f (p, g p) - iteratedFDeriv ℝ j f₀ (p, g₀ p)‖ ≤ ε)
    (hgjet : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g p‖ ≤ M)
    (hg₀jet : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g₀ p‖ ≤ M)
    (hgdiff : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ ≤ ε) :
    ‖rootJetPartitionRemainder n f g p - rootJetPartitionRemainder n f₀ g₀ p‖ ≤
      rootJetDifferenceConstant n M * ε := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  simp only [rootJetPartitionRemainder, rootJetDifferenceConstant,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  have hs2 := (Finset.mem_filter.mp hs).2
  have hsize (i : Fin s.length) := ODE.partSize_lt_of_two_le_length s hs2 i
  have hreg (i : Fin s.length) : ContDiffAt ℝ (s.partSize i) g p :=
    hg.of_le (by exact_mod_cast (hsize i).le)
  have hreg₀ (i : Fin s.length) : ContDiffAt ℝ (s.partSize i) g₀ p :=
    hg₀.of_le (by exact_mod_cast (hsize i).le)
  have hb (i : Fin s.length) :
      ‖iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p‖ ≤ M :=
    norm_rootGraph_jet_le (s.partSize_pos i) hM (hreg i)
      (hgjet _ (s.partSize_pos i) (hsize i))
  have hb₀ (i : Fin s.length) :
      ‖iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g₀ q)) p‖ ≤ M :=
    norm_rootGraph_jet_le (s.partSize_pos i) hM (hreg₀ i)
      (hg₀jet _ (s.partSize_pos i) (hsize i))
  have h₁ : ‖fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM0).mpr hb
  have h₀ : ‖fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g₀ q)) p‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM0).mpr hb₀
  have hd : ‖(fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p) -
      (fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g₀ q)) p)‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    simpa only [Pi.sub_apply, norm_rootGraph_jet_sub (hreg i) (hreg₀ i)] using
      hgdiff _ (s.partSize_pos i) (hsize i)
  have hp : ∏ i, ‖iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g₀ q)) p‖ ≤
      M ^ s.length := by
    calc
      _ ≤ ∏ _i : Fin s.length, M :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hb₀ i)
      _ = _ := by simp
  apply (s.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ s.length f (p, g p))
    (iteratedFDeriv ℝ s.length f₀ (p, g₀ p))
    (fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p)
    (fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g₀ q)) p)).trans
  calc
    _ ≤ M * s.length * M ^ (s.length - 1) * ε + ε * M ^ s.length := by
      gcongr
      · exact hfjet _ (by omega) s.length_le
      · exact max_le h₁ h₀
      · exact hfdiff _ (by omega) s.length_le
    _ = _ := by ring

/-- `app:lem:common-hamilton-phase`: the pointwise higher root-jet difference
step for `exists_finiteOrder_root_stability_on_closedBall`. The constant precedes
both equations, roots, the point and error. Subtracting the actual differentiated
equations requires only the reference top root jet, lower perturbed root jets,
and equation derivatives through the stated order. The parent construction must
produce these quantitative inputs before assembling finite-order stability. -/
theorem exists_root_jet_difference_step (n : ℕ) (hn : 2 ≤ n)
    (M c : ℝ) (hM : 1 ≤ M) (hc : 0 < c) :
    ∃ C > 0, ∀ (f f₀ : P × ℝ → ℝ) (g g₀ : P → ℝ) (p : P) (ε : ℝ),
      0 ≤ ε → ContDiffAt ℝ n f (p, g p) → ContDiffAt ℝ n f₀ (p, g₀ p) →
      ContDiffAt ℝ n g p → ContDiffAt ℝ n g₀ p →
      (∀ᶠ q in 𝓝 p, f (q, g q) = 0) → (∀ᶠ q in 𝓝 p, f₀ (q, g₀ q) = 0) →
      c ≤ |scalarDerivative f (p, g p)| →
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (p, g p)‖ ≤ M) →
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f₀ (p, g₀ p)‖ ≤ M) →
      (∀ j, 1 ≤ j → j ≤ n →
        ‖iteratedFDeriv ℝ j f (p, g p) - iteratedFDeriv ℝ j f₀ (p, g₀ p)‖ ≤ ε) →
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g₀ p‖ ≤ M) →
      (∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g p‖ ≤ M) →
      (∀ j, 1 ≤ j → j < n →
        ‖iteratedFDeriv ℝ j g p - iteratedFDeriv ℝ j g₀ p‖ ≤ ε) →
      ‖iteratedFDeriv ℝ n g p - iteratedFDeriv ℝ n g₀ p‖ ≤ C * ε := by
  let S := rootJetDifferenceConstant n M
  have hS : 0 ≤ S := rootJetDifferenceConstant_nonneg n (zero_le_one.trans hM)
  refine ⟨(1 + S + M) / c, div_pos (by linarith) hc, ?_⟩
  intro f f₀ g g₀ p ε hε hf hf₀ hg hg₀ heq heq₀ hgap hfjet _hf₀jet hfdiff hg₀jet hgjet hgdiff
  let d := scalarDerivative f (p, g p)
  let d₀ := scalarDerivative f₀ (p, g₀ p)
  let G := iteratedFDeriv ℝ n g p
  let G₀ := iteratedFDeriv ℝ n g₀ p
  let R := rootJetPartitionRemainder n f g p
  let R₀ := rootJetPartitionRemainder n f₀ g₀ p
  have hR : ‖R - R₀‖ ≤ S * ε := norm_rootJetPartitionRemainder_sub_le hM hε hg hg₀
    hfjet hfdiff hgjet (fun j hj hjn ↦ hg₀jet j hj hjn.le) hgdiff
  have hd : |d - d₀| ≤ ε := by
    have hjet := hfdiff 1 le_rfl (by omega)
    have hnorm : ‖iteratedFDeriv ℝ 1 f (p, g p) -
        iteratedFDeriv ℝ 1 f₀ (p, g₀ p)‖ =
        ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ := by
      simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
        iteratedFDeriv_zero_eq_comp]
    rw [hnorm] at hjet
    have h := (fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g₀ p)).le_opNorm
      ((0, 1) : P × ℝ)
    have hd' : |d - d₀| ≤ ‖fderiv ℝ f (p, g p) - fderiv ℝ f₀ (p, g₀ p)‖ := by
      simpa [d, d₀, scalarDerivative] using h
    exact hd'.trans hjet
  have hG : d • G = -R := scalarDerivative_smul_iteratedFDeriv_root hn hf hg heq
  have hG₀ : d₀ • G₀ = -R₀ := scalarDerivative_smul_iteratedFDeriv_root hn hf₀ hg₀ heq₀
  have hid : d • (G - G₀) = -(R - R₀) - (d - d₀) • G₀ := by
    rw [smul_sub, sub_smul, hG, hG₀]
    abel
  have hnorm : |d| * ‖G - G₀‖ ≤ (S + M) * ε := by
    calc
      _ = ‖d • (G - G₀)‖ := (norm_smul _ _).symm
      _ = ‖-(R - R₀) - (d - d₀) • G₀‖ := congrArg norm hid
      _ ≤ ‖R - R₀‖ + |d - d₀| * ‖G₀‖ := by
        simpa only [norm_neg, norm_smul, Real.norm_eq_abs] using
          norm_sub_le (-(R - R₀)) ((d - d₀) • G₀)
      _ ≤ S * ε + ε * M := add_le_add hR
        (mul_le_mul hd (hg₀jet n (by omega) le_rfl) (norm_nonneg _) hε)
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  change ‖G - G₀‖ * c ≤ (1 + S + M) * ε
  change c ≤ |d| at hgap
  nlinarith [norm_nonneg (G - G₀)]

end JanetCartan.CharacteristicRoot
