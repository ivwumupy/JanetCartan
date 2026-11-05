module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.Construction

/-!
# Common two-time Hamilton flows and phases from primitive root bounds

The common flow, inverse-projection and phase construction for `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. One fixed scalar `C³` bound determines
the initial, elapsed-time and joint source buffers before the root is chosen.
The same actual flow, inverse chart and phase have all single-high joint bounds,
with reserve one, and the physical clock and full segment containment in either
time orientation. `exists_common_twoTimeHamiltonPhase` also supplies a common
closed target buffer, the full phase differential and the spatial mixed half-gap.

The concrete reduced-pencil root producer is `Characteristic/RootFamily`.
The downstream consumers are `Characteristic/AmplitudeBounds` and
`EvolutionIntegral.SymbolBudgets`. Root-family instantiation, conic extension,
signed amplitudes, and the finite-sector operator assembly remain with their
respective producers; these geometric results do not assert the sector theorem.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance commonTwoTimeFlowNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Choose the common time interval, joint source ball and the complete
sequence of constants before the scalar root. Picard–Lindelöf constructs one
flow; all autonomous, two-time and projection budgets concern that same flow
at every order. The exact diagonal and full physical-time segment stay in the
prescribed root-state ball. Only smoothness and the fixed primitive `C³` budget
are assumed (`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_common_twoTimeHamiltonFlow
    (z : RootState E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ T > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ C : ℕ → ℝ,
      (∀ n, 0 < C n) ∧ 2 * ρ ≤ R / 4 ∧ 2 * ρ ≤ T / 4 ∧
      closedBall (z.1, z) ρ ⊆ twoTimeDomain z (R / 2) T ∧
      ∀ h : RootState E → ℝ, ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ∃ Φ : RootState E × ℝ → RootState E,
          ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ ∧
          ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z (R / 2) T) ∧
          ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z (R / 2) T) ∧
          (∀ q ∈ twoTimeDomain z (R / 2) T, ∀ v ∈ uIcc q.2.1 q.1,
            (v, q.2) ∈ twoTimeDomain z (R / 2) T ∧
            twoTimeState Φ (v, q.2) ∈ closedBall z R ∧ (twoTimeState Φ (v, q.2)).1 = v) ∧
          (∀ w ∈ closedBall z (R / 2),
            twoTimeState Φ (w.1, w) = w ∧ twoTimeProjection Φ (w.1, w) = (w.1, w)) ∧
          ∀ n, cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ +
            (cNorm (closedBall (z.1, z) ρ) n (twoTimeState Φ) +
              cNorm (closedBall (z.1, z) ρ) n (twoTimeProjection Φ)) ≤
                C n * (1 + cNorm (closedBall z R) (n + 1) h) := by
  obtain ⟨T, hT, A, hA, hflow⟩ := exists_common_rootHamiltonFlow z hR hM hD hRD
  let ρ := min R T / 16
  have hρ : 0 < ρ := div_pos (lt_min hR hT) (by norm_num)
  have hρR : 2 * ρ ≤ R / 4 := by dsimp [ρ]; linarith [min_le_left R T]
  have hρT : 2 * ρ ≤ T / 4 := by dsimp [ρ]; linarith [min_le_right R T]
  choose B hB hbound using fun n ↦
    exists_rootFlow_twoTime_cNorm_bound z hR hT hM hρR hρT hD hRD n
  refine ⟨T, hT, ρ, hρ, (fun n ↦ A n + B n), (fun n ↦ add_pos (hA n) (hB n)),
    hρR, hρT, closedBall_subset_twoTimeDomain z hR hT hρR hρT, ?_⟩
  intro h hh hlow
  obtain ⟨Φ, hΦ, hΦbound⟩ := hflow h hh hlow
  refine ⟨Φ, hΦ, rootFlow_twoTimeState_smooth hΦ, rootFlow_twoTimeProjection_smooth hΦ,
    (fun _ hq _ hv ↦ rootFlow_twoTimeState_segment hΦ hT hq hv),
    (fun _ hw ↦ rootFlow_twoTime_diagonal hΦ hw), ?_⟩
  intro n
  exact (add_le_add (hΦbound n) (hbound n h Φ hh hlow hΦ)).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic
