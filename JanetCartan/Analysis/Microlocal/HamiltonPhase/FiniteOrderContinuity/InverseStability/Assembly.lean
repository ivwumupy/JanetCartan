module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.InverseStability.JetInduction

/-!
# Finite-order continuity of normalized inverses

The induction for `app:lem:common-hamilton-phase` derives every perturbed
inverse jet bound. The geometric gap comes from
`app:lem:buffered-inverse-stability`, separately from the order-`m` tolerance.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.HamiltonPhase.InverseContinuity
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `app:lem:common-hamilton-phase`: on fixed compact sets actual normalized
inverses are locally Lipschitz in each finite-order seminorm. The inverse
identity and lower jet comparisons discharge all inverse-derivative inputs.
Only the reference map, fixed before the constant, uses order `m+1`. -/
theorem exists_normalized_inverse_stability
    {f₀ : X → X} {g₀ : Y → X} {K D : Set X} {S U : Set Y}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hS : IsCompact S)
    (hD : IsOpen D) (hKD : K ⊆ D) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf₀ : ContDiffOn ℝ ∞ f₀ D) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (L : Y →L[ℝ] X) (hrange₀ : MapsTo g₀ S K) (heq₀ : EqOn (f₀ ∘ g₀) L U)
    (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : X → X) (g : Y → X),
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ g U → MapsTo g S K →
      EqOn (f ∘ g) L U →
      (∀ x ∈ K, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) →
      cNorm K m (f - f₀) ≤ 1 → cNorm S m (g - g₀) ≤ C * cNorm K m (f - f₀) := by
  induction m with
  | zero =>
    refine ⟨2, by norm_num, ?_⟩
    intro f g hf _hg hrange heq hgap _hbound
    rw [cNorm_order_zero]
    apply Real.sSup_le _ (mul_nonneg (by norm_num) (cNorm_nonneg _ _ _))
    rintro _ ⟨y, hy, rfl⟩
    exact norm_inverse_sub_le hK hconv hD hKD hf hf₀ hgap (hrange hy) (hrange₀ hy)
      ((heq (hSU hy)).trans (heq₀ (hSU hy)).symm) 0
  | succ m ih =>
    obtain ⟨B, hB, hprev⟩ := ih
    let M := 1 + cNorm K (m + 1) f₀ + cNorm S (m + 1) g₀ + B
    have hM : 1 ≤ M := by
      dsimp [M]
      linarith [cNorm_nonneg K (m + 1) f₀, cNorm_nonneg S (m + 1) g₀]
    let A := 1 + 2 * cNorm K (m + 1 + 1) f₀
    have hA : 0 < A := by dsimp [A]; linarith [cNorm_nonneg K (m + 1 + 1) f₀]
    let T := 2 * (inverseJetDifferenceConstant (m + 1) M + M)
    have hT : 0 < T := by
      dsimp [T]
      have := inverseJetDifferenceConstant_nonneg (m + 1) (zero_le_one.trans hM)
      positivity
    refine ⟨B + T * (A + B), by positivity, ?_⟩
    intro f g hf hg hrange heq hgap hbound
    let ε := cNorm K (m + 1) (f - f₀)
    have hε : 0 ≤ ε := cNorm_nonneg _ _ _
    have hlower : cNorm S m (g - g₀) ≤ B * ε :=
      (hprev f g hf hg hrange heq hgap
        ((cNorm_mono_order (Nat.le_succ m)).trans hbound)).trans
        (mul_le_mul_of_nonneg_left (cNorm_mono_order (Nat.le_succ m)) hB.le)
    have htop : ∀ y ∈ S, ‖iteratedFDeriv ℝ (m + 1) (g - g₀) y‖ ≤
        T * (A + B) * ε := by
      intro y hy
      have hyU := hSU hy
      have hz := hrange hy
      have hz₀ := hrange₀ hy
      have hgy : ContDiffAt ℝ ∞ g y := hg.contDiffAt (hU.mem_nhds hyU)
      have hg₀y : ContDiffAt ℝ ∞ g₀ y := hg₀.contDiffAt (hU.mem_nhds hyU)
      have hgjet₀ (j : ℕ) (hj : j ≤ m + 1) :
          ‖iteratedFDeriv ℝ j g₀ y‖ ≤ cNorm S (m + 1) g₀ :=
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
          (fun q hq ↦ (hg₀.contDiffAt (hU.mem_nhds (hSU hq))).of_le (by simp)) hy hj
      have hdiff (j : ℕ) (hj : j < m + 1) :
          ‖iteratedFDeriv ℝ j g y - iteratedFDeriv ℝ j g₀ y‖ ≤ B * ε :=
        (CompositionContinuity.norm_iteratedFDeriv_sub_le_cNorm hS
          (fun q hq ↦ (hg.contDiffAt (hU.mem_nhds (hSU hq))).of_le (by simp))
          (fun q hq ↦ (hg₀.contDiffAt (hU.mem_nhds (hSU hq))).of_le (by simp))
          (by omega : j ≤ m) hy).trans hlower
      rw [iteratedFDeriv_sub_apply (hgy.of_le (by simp)) (hg₀y.of_le (by simp)), mul_assoc]
      apply norm_inverse_jet_sub_le (Nat.succ_pos m) hM (by positivity : 0 ≤ (A + B) * ε) L
        ((hf.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
        ((hf₀.contDiffAt (hD.mem_nhds (hKD hz₀))).of_le (by simp))
        (hgy.of_le (by simp)) (hg₀y.of_le (by simp))
        (Filter.eventuallyEq_of_mem (hU.mem_nhds hyU) (fun q hq ↦ heq hq))
        (Filter.eventuallyEq_of_mem (hU.mem_nhds hyU) (fun q hq ↦ heq₀ hq)) (hgap _ hz)
      · intro j _hj hjn
        have hsame := CompositionContinuity.norm_iteratedFDeriv_sub_le_cNorm hK
          (fun z hz ↦ (hf.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
          (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp)) hjn hz
        have href : ‖iteratedFDeriv ℝ j f₀ (g y)‖ ≤ cNorm K (m + 1) f₀ :=
          norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun z hz ↦ (hf₀.contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp)) hz hjn
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (iteratedFDeriv ℝ j f (g y)) (iteratedFDeriv ℝ j f₀ (g y)) 0
        simp only [sub_zero] at htri
        dsimp [M]
        linarith [cNorm_nonneg S (m + 1) g₀]
      · intro j _hj hjn
        exact (norm_forward_jet_at_inverse_sub_le hK hconv hD hKD hf hf₀ hgap hz hz₀
          ((heq hyU).trans (heq₀ hyU).symm) hjn).trans
          (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith : A ≤ A + B) hε)
      · intro j _hj hjn
        have hd := hdiff j hjn
        have hb := hgjet₀ j hjn.le
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (iteratedFDeriv ℝ j g y) (iteratedFDeriv ℝ j g₀ y) 0
        simp only [sub_zero] at htri
        have hBε : B * ε ≤ B := by simpa using mul_le_mul_of_nonneg_left hbound hB.le
        dsimp [M]
        linarith [cNorm_nonneg K (m + 1) f₀]
      · intro j _hj hjn
        exact (hgjet₀ j hjn).trans (by dsimp [M]; linarith [cNorm_nonneg K (m + 1) f₀])
      · intro j _hj hjn
        exact (hdiff j hjn).trans
          (mul_le_mul_of_nonneg_right (by linarith : B ≤ A + B) hε)
    rw [cNorm_succ]
    calc
      _ ≤ B * ε + T * (A + B) * ε := by
        apply add_le_add hlower
        apply Real.sSup_le _ (by positivity)
        rintro _ ⟨p, hp, rfl⟩
        exact htop p hp
      _ = _ := by ring

end JanetCartan.HamiltonPhase.InverseContinuity
