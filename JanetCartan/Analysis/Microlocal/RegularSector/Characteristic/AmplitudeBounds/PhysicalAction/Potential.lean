module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Differential

/-!
# The actual physical transport potential

This is the input needed by the signed row producer before the amplitude
products are formed. It uses only `Q,B,k,l`, with `k,l` the actual transported
nullvectors, and therefore has no dependence on a bound for the signed row.
The producers of those nullvector bounds are `AmplitudeBounds.RootData`
and the transported-primitive estimates. The parent must instantiate them.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

variable {n d : ℕ}

/-- A one-high bound with reserve one for the literal `pencilTransportPotential`.
Constants are chosen from fixed first-order bounds before the coefficients,
root, flow or inverse chart. The derivative acts on the substituted right
nullvector and retains the full `B` term. The signed-row producer consumes
this estimate (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_pencilTransportPotential_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M : ℝ)
    (himage : MapsTo (physicalPosition e) (closedBall z ρ) (closedBall x R)) :
    ∃ Cₚ : ℕ → ℝ, (∀ m, 0 < Cₚ m) ∧
      ∀ (Ω : Set (Euclidean n)) (V : Set (TwoTimePoint (Euclidean d))),
        IsOpen Ω → IsOpen V → closedBall x R ⊆ Ω → closedBall z ρ ⊆ V →
        MapsTo (physicalPosition e) V Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
          (h : RootState (Euclidean d) → ℝ)
          (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
          (r c : Fin n),
          let k := pencilChartRight e Q h Φ C r c
          let l := pencilChartLeft e Q h Φ C r c
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiffOn ℝ ∞ k V → ContDiffOn ℝ ∞ l V →
          cNorm (closedBall x R) 1 Q ≤ M → cNorm (closedBall x R) 1 B ≤ M →
          cNorm (closedBall z ρ) 1 k ≤ M → cNorm (closedBall z ρ) 1 l ≤ M →
          ∀ m, cNorm (closedBall z ρ) m (pencilTransportPotential e Q B h Φ C r c) ≤
            Cₚ m * (1 + cNorm (closedBall x R) (m + 1) Q +
              cNorm (closedBall x R) (m + 1) B + cNorm (closedBall z ρ) (m + 1) k +
              cNorm (closedBall z ρ) (m + 1) l) := by
  obtain ⟨A, hA, haction⟩ := exists_adaptedPencilApply_cNorm_bounds e z hρ x R M himage
  obtain ⟨D, hD, hdot⟩ := exists_smoothPair_cNorm_bounds z hρ M (A 0 * (1 + M + M + M))
    _ (contDiff_vectorPairing (n := n))
  refine ⟨fun m ↦ D m * (1 + A m),
    fun m ↦ mul_pos (hD m) (by linarith [hA m]), ?_⟩
  intro Ω V hΩ hV hKQ hK hmap Q B h Φ C r c k l hQ hB hk hl hQM hBM hkM hlM m
  let K := closedBall z ρ
  let KQ := closedBall x R
  have hq₀ : cNorm KQ 0 Q ≤ M := (cNorm_mono_order (by omega : 0 ≤ 1)).trans hQM
  have hb₀ : cNorm KQ 0 B ≤ M := (cNorm_mono_order (by omega : 0 ≤ 1)).trans hBM
  have hl₀ : cNorm K 0 l ≤ M := (cNorm_mono_order (by omega : 0 ≤ 1)).trans hlM
  have hpk := contDiffOn_adaptedPencilApply e hQ hB hV hmap hk
  have hpkBound j := haction Ω V hΩ hV hKQ hK hmap Q B k hQ hB hk hq₀ hb₀ hkM j
  have hpk₀ : cNorm K 0 (adaptedPencilApply e Q B k) ≤ A 0 * (1 + M + M + M) :=
    (hpkBound 0).trans (mul_le_mul_of_nonneg_left (by linarith) (hA 0).le)
  have hout := hdot V hV hK l (adaptedPencilApply e Q B k) hl hpk hl₀ hpk₀ m
  change cNorm K m (pencilTransportPotential e Q B h Φ C r c) ≤
    D m * (1 + cNorm K m l + cNorm K m (adaptedPencilApply e Q B k)) at hout
  apply hout.trans
  have hlmono := cNorm_mono_order (f := l) (s := K) (Nat.le_succ m)
  have hn : 1 + cNorm K m l + cNorm K m (adaptedPencilApply e Q B k) ≤
      (1 + A m) * (1 + cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B +
        cNorm K (m + 1) k + cNorm K (m + 1) l) := by
    nlinarith [hpkBound m, cNorm_nonneg KQ (m + 1) Q, cNorm_nonneg KQ (m + 1) B,
      cNorm_nonneg K (m + 1) k,
      mul_nonneg (hA m).le (cNorm_nonneg K (m + 1) l)]
  exact (mul_le_mul_of_nonneg_left hn (hD m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
