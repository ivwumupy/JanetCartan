module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.LowOrder
public import JanetCartan.Analysis.ODE.HigherVariational

/-!
# Differences of higher variational equations

The induction step for finite-order flow continuity in
`app:lem:common-hamilton-phase`. The remainder comparison uses only strictly
lower spatial flow jets. The top jet satisfies a linear differential inequality,
obtained by subtracting the actual differentiated ODEs. Its consumer is the
finite-order spatial-flow induction; joint time derivatives are recovered by
autonomous time augmentation.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:common-hamilton-phase`: the polynomial coefficient in the lower
spatial-jet remainder comparison. It is consumed by the Grönwall induction step. -/
def flowJetDifferenceConstant (n : ℕ) (M : ℝ) : ℝ :=
  ∑ p : OrderedFinpartition n with 2 ≤ p.length,
    (M * p.length * M ^ (p.length - 1) + M ^ p.length)

/-- `app:lem:common-hamilton-phase`: nonnegativity of the remainder coefficient. -/
theorem flowJetDifferenceConstant_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ flowJetDifferenceConstant n M := by
  unfold flowJetDifferenceConstant
  positivity

/-- `app:lem:common-hamilton-phase`: subtracting the explicit partition sums
uses field jets through `n` and flow jets strictly below `n`. This is the forcing
estimate in `norm_spatial_jet_sub_le_gronwall`, not a flow-closeness assumption. -/
theorem norm_jetPartitionRemainder_sub_le {n : ℕ} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) {V V₀ : E → E} {f f₀ : P → E} {x : P}
    (houter : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j V (f x)‖ ≤ M)
    (houterDiff : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j V (f x) - iteratedFDeriv ℝ j V₀ (f₀ x)‖ ≤ ε)
    (hinner : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hinner₀ : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f₀ x‖ ≤ M)
    (hinnerDiff : ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f₀ x‖ ≤ ε) :
    ‖jetPartitionRemainder n V f x - jetPartitionRemainder n V₀ f₀ x‖ ≤
      flowJetDifferenceConstant n M * ε := by
  classical
  simp only [jetPartitionRemainder, flowJetDifferenceConstant,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hp2 := (Finset.mem_filter.mp hp).2
  have hsize (i : Fin p.length) := partSize_lt_of_two_le_length p hp2 i
  have h₁ : ‖fun i ↦ iteratedFDeriv ℝ (p.partSize i) f x‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM).mpr fun i ↦ hinner _ (p.partSize_pos i) (hsize i)
  have h₀ : ‖fun i ↦ iteratedFDeriv ℝ (p.partSize i) f₀ x‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM).mpr fun i ↦ hinner₀ _ (p.partSize_pos i) (hsize i)
  have hd : ‖(fun i ↦ iteratedFDeriv ℝ (p.partSize i) f x) -
      (fun i ↦ iteratedFDeriv ℝ (p.partSize i) f₀ x)‖ ≤ ε :=
    (pi_norm_le_iff_of_nonneg hε).mpr fun i ↦ hinnerDiff _ (p.partSize_pos i) (hsize i)
  have hb : ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f₀ x‖ ≤ M ^ p.length := by
    calc
      _ ≤ ∏ _i : Fin p.length, M := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun i _ ↦ hinner₀ _ (p.partSize_pos i) (hsize i))
      _ = _ := by simp
  apply (p.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (iteratedFDeriv ℝ p.length V (f x)) (iteratedFDeriv ℝ p.length V₀ (f₀ x))
    (fun i ↦ iteratedFDeriv ℝ (p.partSize i) f x)
    (fun i ↦ iteratedFDeriv ℝ (p.partSize i) f₀ x)).trans
  calc
    _ ≤ M * p.length * M ^ (p.length - 1) * ε + ε * M ^ p.length := by
      gcongr
      · exact houter _ (by omega) p.length_le
      · exact max_le h₁ h₀
      · exact houterDiff _ (by omega) p.length_le
    _ = _ := by ring

private theorem norm_fderiv_sub_eq_norm_jet_one
    (V V₀ : E → E) (y y₀ : E) :
    ‖fderiv ℝ V y - fderiv ℝ V₀ y₀‖ =
      ‖iteratedFDeriv ℝ 1 V y - iteratedFDeriv ℝ 1 V₀ y₀‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map,
    iteratedFDeriv_zero_eq_comp]

/-- `app:lem:common-hamilton-phase`: the higher spatial-jet difference satisfies
Grönwall on either time direction. All derivative equations are deduced from the
actual ODE. Quantitative inputs involve field derivatives through `n`, reference
flow derivatives through `n`, and perturbed flow derivatives strictly below `n`.
The spatial induction must supply these lower-order bounds; this conditional
step alone does not assert finite-order continuity. -/
theorem norm_spatial_jet_sub_le_gronwall
    {U : Set P} (hU : IsOpen U) {T M ε : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    {Φ Φ₀ : P × ℝ → E} {V V₀ : E → E} {n : ℕ} (hn : 0 < n)
    (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-T) T))
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (U ×ˢ Ioo (-T) T))
    (hode : ∀ y ∈ U, ∀ τ ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ (y, s)) (V (Φ (y, τ))) τ)
    (hode₀ : ∀ y ∈ U, ∀ τ ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ₀ (y, s)) (V₀ (Φ₀ (y, τ))) τ)
    (hinit : ∀ y ∈ U, Φ (y, 0) = Φ₀ (y, 0))
    {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-T) T)
    (hV : ∀ τ ∈ uIcc 0 t, ContDiffAt ℝ n V (Φ (x, τ)))
    (hV₀ : ∀ τ ∈ uIcc 0 t, ContDiffAt ℝ n V₀ (Φ₀ (x, τ)))
    (houter : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j V (Φ (x, τ))‖ ≤ M)
    (houterDiff : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j V (Φ (x, τ)) - iteratedFDeriv ℝ j V₀ (Φ₀ (x, τ))‖ ≤ ε)
    (hinner : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x‖ ≤ M)
    (hinner₀ : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, τ)) x‖ ≤ M)
    (hinnerDiff : ∀ τ ∈ uIcc 0 t, ∀ j, 1 ≤ j → j < n →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ (y, τ)) x -
        iteratedFDeriv ℝ j (fun y ↦ Φ₀ (y, τ)) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t)) x -
        iteratedFDeriv ℝ n (fun y ↦ Φ₀ (y, t)) x‖ ≤
      gronwallBound 0 M (M + flowJetDifferenceConstant n M) T * ε := by
  let J := fun τ ↦ iteratedFDeriv ℝ n (fun y ↦ Φ (y, τ)) x
  let J₀ := fun τ ↦ iteratedFDeriv ℝ n (fun y ↦ Φ₀ (y, τ)) x
  let A := fun τ ↦ fderiv ℝ V (Φ (x, τ))
  let A₀ := fun τ ↦ fderiv ℝ V₀ (Φ₀ (x, τ))
  let Q := fun τ ↦ jetPartitionRemainder n V (fun y ↦ Φ (y, τ)) x
  let Q₀ := fun τ ↦ jetPartitionRemainder n V₀ (fun y ↦ Φ₀ (y, τ)) x
  have hseg : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hJi : J 0 = J₀ 0 := by
    have heq : (fun y ↦ Φ (y, 0)) =ᶠ[𝓝 x] (fun y ↦ Φ₀ (y, 0)) :=
      eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hx, hinit⟩
    exact (heq.iteratedFDeriv ℝ n).eq_of_nhds
  have hdiff τ (hτ : τ ∈ uIcc 0 t) :
      HasDerivAt (fun s ↦ J s - J₀ s)
        ((A τ).compContinuousMultilinearMap (J τ - J₀ τ) +
          (A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ) + (Q τ - Q₀ τ)) τ := by
    convert (hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder hU hΦ hode hn hx
      (hseg hτ) (hV τ hτ)).sub
      (hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder hU hΦ₀ hode₀ hn hx
        (hseg hτ) (hV₀ τ hτ)) using 1
    ext v
    change A τ (J τ v - J₀ τ v) + (A τ (J₀ τ v) - A₀ τ (J₀ τ v)) +
      (Q τ v - Q₀ τ v) = (A τ (J τ v) + Q τ v) - (A₀ τ (J₀ τ v) + Q₀ τ v)
    rw [map_sub]
    abel
  have hb τ (hτ : τ ∈ uIcc 0 t) :
      ‖(A τ).compContinuousMultilinearMap (J τ - J₀ τ) +
          (A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ) + (Q τ - Q₀ τ)‖ ≤
        M * ‖J τ - J₀ τ‖ + (M + flowJetDifferenceConstant n M) * ε := by
    have hA : ‖A τ‖ ≤ M := by
      simpa only [A, norm_iteratedFDeriv_one] using houter τ hτ 1 le_rfl hn
    have hAd : ‖A τ - A₀ τ‖ ≤ ε := by
      dsimp only [A, A₀]
      rw [norm_fderiv_sub_eq_norm_jet_one]
      exact houterDiff τ hτ 1 le_rfl hn
    have hQ : ‖Q τ - Q₀ τ‖ ≤ flowJetDifferenceConstant n M * ε :=
      norm_jetPartitionRemainder_sub_le hM hε (houter τ hτ) (houterDiff τ hτ)
        (hinner τ hτ) (fun j hj hjn ↦ hinner₀ τ hτ j hj hjn.le) (hinnerDiff τ hτ)
    calc
      _ ≤ (‖(A τ).compContinuousMultilinearMap (J τ - J₀ τ)‖ +
          ‖(A τ - A₀ τ).compContinuousMultilinearMap (J₀ τ)‖) + ‖Q τ - Q₀ τ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (M * ‖J τ - J₀ τ‖ + ε * M) + flowJetDifferenceConstant n M * ε := by
        apply add_le_add (add_le_add ?_ ?_) hQ
        · exact ((A τ).norm_compContinuousMultilinearMap_le _).trans
            (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        · exact ((A τ - A₀ τ).norm_compContinuousMultilinearMap_le _).trans
            (mul_le_mul hAd (hinner₀ τ hτ n hn le_rfl) (norm_nonneg _) hε)
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_hasDerivAt_uIcc hdiff
    (δ := 0) (by simp [hJi]) hb
  have hS := flowJetDifferenceConstant_nonneg n hM
  have htime : |t - 0| ≤ T := by simpa using (abs_lt.mpr ht).le
  apply (hg.trans (gronwallBound_mono le_rfl (by positivity) hM htime)).trans_eq
  simpa using gronwallBound_mul 0 M (M + flowJetDifferenceConstant n M) ε T

end JanetCartan.ODE
