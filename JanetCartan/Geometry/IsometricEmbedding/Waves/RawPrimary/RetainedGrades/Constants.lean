module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Assembly

/-!
# Grade constants before the retained geometric conclusions

The retained leading producer exports the fixed working-ball containments after
its immersion argument. These containments do not depend on the immersion. A
case split lets the existing amplitude construction choose its constants before
that argument, without selecting any new cell or flow. The finite retained raw
family below supplies the geometric facts and every coefficient budget.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open ProjectedStressFrame AmplitudeGrades AmbientResponse ResponseTransfer

/-- Choose grade constants before the geometric facts exported by the retained
leading constructor. This only rearranges fixed geometry; the original ambient
amplitude reconstruction proves the estimates. Consumer:
`exists_finite_retained_graded_raw_family`, `app:ch_waves:eq:individual-grading`. -/
theorem exists_fullAmplitude_grades_on_retained_workingBall
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (I : Set (Euclidean (n - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ C Pξ Pζ : ℕ → ℝ, (∀ j, 0 < C j) ∧ (∀ j, 0 < Pξ j) ∧ (∀ j, 0 < Pζ j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      closedBall a.1 (2 * ρ) ⊆ K → closedBall a (2 * ρ) ⊆ domain T →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      let J := closedBall a ρ
      let D := fullDisplacementAmplitude T Q F row col Φ Y r τ
      let A := fullDerivativeAmplitude T Q F row col Φ Y r τ
      let R := fun w ↦ A w - fullLeadingPrincipalMatrix T Q F row col Φ Y r w
      let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        phaseGradient T Q w.1 w.2.2
      let ζ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        fderiv ℝ (phase T Q w.1) w.2.2
      ContDiffOn ℝ ∞ D (ball a (2 * ρ)) ∧ ContDiffOn ℝ ∞ A (ball a (2 * ρ)) ∧
      (∀ j, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j D w‖ ≤ τ * C j * L ^ (j - (rpar + 1)) ∧
        ‖iteratedFDeriv ℝ j A w‖ ≤ C j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j R w‖ ≤ τ * C j * L ^ (j - rpar)) ∧
      (∀ s k : ℕ, k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (s + k) D w‖ ≤ τ * C (s + k) * L ^ s ∧
        ‖iteratedFDeriv ℝ (s + k) A w‖ ≤ C (s + k) * L ^ s ∧
        ‖iteratedFDeriv ℝ (s + k) R w‖ ≤ τ * C (s + k) * L ^ s) ∧
      (∀ s : ℕ, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ s (fun x ↦ D (x, w.2)) w.1‖ ≤ τ * C s * L ^ s ∧
        ‖iteratedFDeriv ℝ s (fun x ↦ A (x, w.2)) w.1‖ ≤ C s * L ^ s ∧
        ‖iteratedFDeriv ℝ s (fun x ↦ R (x, w.2)) w.1‖ ≤ τ * C s * L ^ s) ∧
      HasDerivativeProfile J D (rpar + 1) L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J A rpar L (fun j ↦ ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J R rpar L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J ξ (rpar + 3) L Pξ ∧
      (∀ j, ∀ w ∈ J, ‖iteratedFDeriv ℝ j ζ w‖ ≤ Pζ j * L ^ (j - 1 - (rpar + 2))) ∧
      (∀ s k : ℕ, 1 ≤ s → k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (s + k) ξ w‖ ≤ Pξ (s + k) * L ^ (s - 1) ∧
        ‖iteratedFDeriv ℝ (s + k) ζ w‖ ≤ Pζ (s + k) * L ^ (s - 1)) ∧
      (∀ s : ℕ, 1 ≤ s → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ s (fun x ↦ fderiv ℝ (phase T Q x) w.2.2) w.1‖ ≤
          Pζ s * L ^ (s - 1)) := by
  classical
  by_cases hgeometry : closedBall a.1 (2 * ρ) ⊆ K ∧
      closedBall a (2 * ρ) ⊆ domain T
  · obtain ⟨C, Pξ, Pζ, hC, hPξ, hPζ, hgrades⟩ :=
      exists_fullAmplitude_grades_of_corrected_family_outputs T a hρ hK hKU hball
        hgeometry.1 hgeometry.2 I hγ hκ AF Ar E Γ hAF hAr hE hΓ
    refine ⟨C, Pξ, Pζ, hC, hPξ, hPζ, ?_⟩
    intro F hF hi hrank _hspace _hphase
    exact hgrades F hF hi hrank
  · refine ⟨fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ zero_lt_one, fun _ ↦ zero_lt_one, fun _ ↦ zero_lt_one, ?_⟩
    intro F hF hi hrank hspace hphase
    exact (hgeometry ⟨hspace, hphase⟩).elim

end JanetCartan.RawPrimary
