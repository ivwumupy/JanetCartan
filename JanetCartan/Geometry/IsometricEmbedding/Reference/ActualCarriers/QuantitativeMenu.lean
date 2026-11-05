module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootQuantitative.Family
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ZeroEnergyBounds

/-!
# The reserve-six maximum for the selected carrier menu

The full phases retain their sharp reserve three and the carrier gradients
retain reserve four. Together with the actual incidence-root bounds, one
finite maximum has reserve six (`app:ch_seed:eq:seed-phase-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu ProjectedStressFrame CurrentFullPhase

/-- The maximum over the same zero-energy phases, carrier gradients and full
incidence parameter roots, with zero adjoined to handle an empty finite menu
(`app:ch_seed:eq:seed-phase-tame`). -/
def constructedCarrierMenuNorm {n : ℕ} {D : CoverData n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (R : IncidenceRefinement D) (r : ℝ)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
    (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
      Euclidean n × Euclidean n → ℝ) (m : ℕ) : ℝ :=
  sSup (insert 0
    ((Set.range fun i ↦ cNorm (T i).zeroEnergyBuffer m
      ((T i).zeroEnergyPhase ⟨Q, hQ, hlow i⟩)) ∪
    (Set.range fun i ↦ cNorm
      (closedBall (0 : Euclidean n) (2 * r) ×ˢ parameterCube (D.patches i.1 i.2).radius) m
      (fun p ↦ (T i).carrierGradient ⟨Q, hQ, hlow i⟩ p.1 p.2)) ∪
    (Set.range fun i : (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j)) ↦
      cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center i.1) (R.radius i.1)) m
        (fun p ↦ incidenceParameter (D.roots (R.sourceChart i.1) i.2 (R.center i.1))
          (g i.1 i.2 p)))))

/-- Quantitative output for the chosen charts and roots, including the sharp
individual estimates and the finite reserve-six maximum. This is a conclusion
proved below, not an analytic assumption (`app:ch_seed:eq:seed-phase-tame`). -/
def HasConstructedCarrierTameBounds {n N : ℕ} {D : CoverData n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (R : IncidenceRefinement D) (r : ℝ) (K : Set (Euclidean n)) (A : ℕ → ℝ)
    (F : Euclidean n → Euclidean N) (hQ : ContDiffOn ℝ ∞ (projectedStress F) U)
    (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold)
    (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
      Euclidean n × Euclidean n → ℝ) : Prop :=
  ∀ m,
    (∀ i,
      cNorm (closedBall ((T i).data.adapted.embedding (T i).data.adapted.baseData.1,
        (T i).data.adapted.baseData.2) (T i).family.radius) m
        (phase ((T i).currentChart ⟨projectedStress F, hQ, hlow i⟩).coordinates) ≤
          A m * (1 + cNorm K (m + 3) F) ∧
      cNorm (T i).zeroEnergyBuffer m
        ((T i).zeroEnergyPhase ⟨projectedStress F, hQ, hlow i⟩) ≤
          A m * (1 + cNorm K (m + 3) F) ∧
      cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ parameterCube (D.patches i.1 i.2).radius) m
        (fun p ↦ (T i).carrierGradient ⟨projectedStress F, hQ, hlow i⟩ p.1 p.2) ≤
          A m * (1 + cNorm K (m + 4) F)) ∧
    (∀ j a,
      cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center j) (R.radius j))
        m (g j a) ≤ A m * (1 + cNorm K (m + 6) F) ∧
      cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center j) (R.radius j)) m
        (fun p ↦ incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a p)) ≤
          A m * (1 + cNorm K (m + 6) F)) ∧
    constructedCarrierMenuNorm T R r (projectedStress F) hQ hlow g m ≤
      A m * (1 + cNorm K (m + 6) F)

/-- All three sharp estimates and their common reserve-six maximum follow
from the original immersion data and the SAME proved low roots. Constants
and the positive componentwise frame threshold precede the immersion and all
orders. The parent applies this to its actual detector witnesses
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_constructed_carrier_tame_bounds {n N : ℕ} {D : CoverData n}
    {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {R : IncidenceRefinement D} (hR : R.IsValid)
    {r : ℝ} (hr : 0 < r) (hradius : ∀ i, 3 * r < (T i).physicalRadius)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ cr : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (hcr : 0 < cr) :
    ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        ∀ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∀ (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ) (B ε : ℝ),
        IsConstructedIncidenceRootFamily D R r cr B ε (projectedStress F)
          (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g →
        HasConstructedCarrierTameBounds T R r K A F hQ hlow g := by
  classical
  let I := (j : Fin D.chartCount) × Fin (D.patchCount j)
  choose A hA ha using fun i : I ↦ (T i).exists_projected_phase_sharp_bound
    (N := N) hK hKU (hball i) C₀ hκmet hκ
  choose Az hAz haz using fun i : I ↦ (T i).exists_projected_zeroEnergyPhase_sharp_bound
    (N := N) hK hKU (hball i) C₀ hκmet hκ
  choose B hB hb using fun i : I ↦ (T i).exists_projected_carrierGradient_sharp_bound
    (N := N) (hD.2.2.2.2.1 i.1 i.2).1
    (Kc := closedBall (0 : Euclidean n) (2 * r) ×ˢ parameterCube (D.patches i.1 i.2).radius)
    ((isCompact_closedBall _ _).prod (isCompact_parameterCube _))
    (Set.prod_mono (closedBall_subset_ball (by linarith [hradius i]))
      (parameterCube_subset_doubledInterior (hD.2.2.2.2.1 i.1 i.2).1.1))
    hK hKU (hball i) C₀ hκmet hκ
  obtain ⟨δ, hδ, E, hE, he⟩ := exists_projected_rootFamily_bound (N := N)
    hD T hR hr hradius hK hKU hball C₀ hκmet hκ hcr
  let H (m : ℕ) := 1 + E m + ∑ i : I, (A i m + B i m + Az i m)
  have hH (m : ℕ) : 0 < H m := by
    have hh := Finset.sum_nonneg (s := (Finset.univ : Finset I))
      (fun i _ ↦ add_nonneg (add_nonneg (hA i m).le (hB i m).le) (hAz i m).le)
    change 0 < 1 + E m + ∑ i : I, (A i m + B i m + Az i m)
    linarith [hE m]
  have hEH (m : ℕ) : E m ≤ H m := by
    have hh := Finset.sum_nonneg (s := (Finset.univ : Finset I))
      (fun i _ ↦ add_nonneg (add_nonneg (hA i m).le (hB i m).le) (hAz i m).le)
    change E m ≤ 1 + E m + ∑ i : I, (A i m + B i m + Az i m)
    linarith
  have hABH (i : I) (m : ℕ) : A i m ≤ H m ∧ B i m ≤ H m ∧ Az i m ≤ H m := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset I))
      (fun i _ ↦ add_nonneg (add_nonneg (hA i m).le (hB i m).le) (hAz i m).le) (Finset.mem_univ i)
    change A i m ≤ 1 + E m + ∑ i : I, (A i m + B i m + Az i m) ∧
      B i m ≤ 1 + E m + ∑ i : I, (A i m + B i m + Az i m) ∧
      Az i m ≤ 1 + E m + ∑ i : I, (A i m + B i m + Az i m)
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hA i m, hB i m, hAz i m, hE m]
  refine ⟨δ, hδ, H, hH, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose hlow
  dsimp only
  intro g Broot ε hg m
  have hphase (i) := (ha i F hF hi hrank hlowF hmet hnormal (hlow i) m).trans
    (mul_le_mul_of_nonneg_right (hABH i m).1 (by linarith [cNorm_nonneg K (m + 3) F]))
  have hgrad (i) := (hb i F hF hi hrank hlowF hmet hnormal (hlow i) m).trans
    (mul_le_mul_of_nonneg_right (hABH i m).2.1 (by linarith [cNorm_nonneg K (m + 4) F]))
  have hzero (i) := (haz i F hF hi hrank hlowF hmet hnormal (hlow i) m).trans
    (mul_le_mul_of_nonneg_right (hABH i m).2.2 (by linarith [cNorm_nonneg K (m + 3) F]))
  have hroot (j a) := he F hF hi hrank hlowF hmet hnormal hclose hlow g Broot ε hg m j a
  have hrootH (j a) := And.intro
    ((hroot j a).1.trans (mul_le_mul_of_nonneg_right (hEH m) (by linarith [cNorm_nonneg K (m + 6) F])))
    ((hroot j a).2.trans (mul_le_mul_of_nonneg_right (hEH m) (by linarith [cNorm_nonneg K (m + 6) F])))
  refine ⟨fun i ↦ ⟨hphase i, hzero i, hgrad i⟩, hrootH, ?_⟩
  apply Real.sSup_le _ (mul_nonneg (hH m).le (by linarith [cNorm_nonneg K (m + 6) F]))
  rintro v (rfl | ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩))
  · exact mul_nonneg (hH m).le (by linarith [cNorm_nonneg K (m + 6) F])
  · exact (hzero i).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (cNorm_mono_order (by omega : m + 3 ≤ m + 6))) (hH m).le)
  · exact (hgrad i).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (cNorm_mono_order (by omega : m + 4 ≤ m + 6))) (hH m).le)
  · exact (hrootH i.1 i.2).2

end JanetCartan.ActualCarriers
