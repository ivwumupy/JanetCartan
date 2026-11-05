module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Potential
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Columns

/-!
# Quantitative physical calculus for the characteristic amplitudes

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the
existing physical action and potential have reserve one. The existing leading
and real correction columns, and the full physical action on the correction,
have reserve two. Their bounds contain one additive high quantity, with
constants fixed before the varying fields and uniform over the finite columns.
The exact physical directions hold source time and initial covector fixed;
the zeroth-order `B` term is retained throughout.

These are downstream deductions from explicit low/high norms of the actual
intermediate fields `k,l,a,b`. `AmplitudeBounds.RootData` and the transported
primitive construction produce `k,l,b`; the signed-row pullback produces `a`.
The parent primitive amplitude assembly must instantiate these inputs from
its same `Q,B,h,Φ,C.symm,σ`. This module does not assert that unconditional
primitive construction or the full regular-sector theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

variable {n d : ℕ}

/-- One common, column-uniform high bound for the literal potential, leading
amplitude, real correction, and physical correction residual. All constants
precede the input fields and depend only on fixed balls, the coordinate map,
and fixed second-order low bounds. Every displayed output is a conclusion,
including smoothness of the full physical action. This is the physical product
step for `app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:eq:two-term-null-identity`, and
`app:ch_regular_base:eq:energy-complete-residual`; primitive production of the
intermediate input norms remains the parent's obligation. -/
theorem exists_pencilPhysicalAmplitudes_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M : ℝ)
    (himage : MapsTo (physicalPosition e) (closedBall z ρ) (closedBall x R)) :
    ∃ Cₐ : ℕ → ℝ, (∀ m, 0 < Cₐ m) ∧
      ∀ (Ω : Set (Euclidean n)) (V : Set (TwoTimePoint (Euclidean d))),
        IsOpen Ω → IsOpen V → closedBall x R ⊆ Ω → closedBall z ρ ⊆ V →
        MapsTo (physicalPosition e) V Ω →
        ∀ (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
          (h : RootState (Euclidean d) → ℝ)
          (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
          (r c : Fin n) (σ : RootState (Euclidean d) → ℝ),
          let k := pencilChartRight e Q h Φ C r c
          let l := pencilChartLeft e Q h Φ C r c
          let a := pencilSignedRow e Q B h Φ C r c σ
          let b := pencilChartComplement e Q h Φ C r c
          let w₀ := pencilLeadingColumn e Q B h Φ C r c σ
          let w₁ := pencilCorrectionColumn e Q B h Φ C r c σ
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiffOn ℝ ∞ k V → ContDiffOn ℝ ∞ l V →
          ContDiffOn ℝ ∞ a V → ContDiffOn ℝ ∞ b V →
          cNorm (closedBall x R) 2 Q ≤ M → cNorm (closedBall x R) 2 B ≤ M →
          cNorm (closedBall z ρ) 2 k ≤ M → cNorm (closedBall z ρ) 2 l ≤ M →
          cNorm (closedBall z ρ) 2 a ≤ M → cNorm (closedBall z ρ) 2 b ≤ M →
          ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) V ∧
          (∀ j, ContDiffOn ℝ ∞ (w₀ j) V ∧ ContDiffOn ℝ ∞ (w₁ j) V ∧
            ContDiffOn ℝ ∞ (adaptedPencilApply e Q B (w₁ j)) V) ∧
          ∀ m,
            let H := 1 + cNorm (closedBall x R) (m + 2) Q +
              cNorm (closedBall x R) (m + 2) B + cNorm (closedBall z ρ) (m + 2) k +
              cNorm (closedBall z ρ) (m + 2) l + cNorm (closedBall z ρ) (m + 2) a +
              cNorm (closedBall z ρ) (m + 2) b
            cNorm (closedBall z ρ) m (pencilTransportPotential e Q B h Φ C r c) ≤ Cₐ m * H ∧
            ∀ j, cNorm (closedBall z ρ) m (w₀ j) ≤ Cₐ m * H ∧
              cNorm (closedBall z ρ) m (w₁ j) ≤ Cₐ m * H ∧
              cNorm (closedBall z ρ) m (adaptedPencilApply e Q B (w₁ j)) ≤ Cₐ m * H := by
  obtain ⟨A, hA, hpotential⟩ := exists_pencilTransportPotential_cNorm_bounds e z hρ x R M himage
  choose D hD hcolumns using fun j : Fin n ↦
    exists_pencilColumns_cNorm_bounds e z hρ x R M j himage
  let S := fun m ↦ ∑ j, D j m
  have hS m : 0 ≤ S m := Finset.sum_nonneg fun j _ ↦ (hD j m).le
  have hDS (j : Fin n) (m : ℕ) : D j m ≤ S m :=
    Finset.single_le_sum (fun i _ ↦ (hD i m).le) (Finset.mem_univ j)
  refine ⟨fun m ↦ A m + S m, fun m ↦ add_pos_of_pos_of_nonneg (hA m) (hS m), ?_⟩
  intro Ω V hΩ hV hKQ hK hmap Q B h Φ C r c σ k l a b w₀ w₁
    hQ hB hk hl ha hb hQM hBM hkM hlM haM hbM
  have hp j := hcolumns j Ω V hΩ hV hKQ hK hmap Q B h Φ C r c σ
    hQ hB hk ha hb hQM hBM hkM haM hbM
  have hpot := hpotential Ω V hΩ hV hKQ hK hmap Q B h Φ C r c hQ hB hk hl
    ((cNorm_mono_order (by omega : 1 ≤ 2)).trans hQM)
    ((cNorm_mono_order (by omega : 1 ≤ 2)).trans hBM)
    ((cNorm_mono_order (by omega : 1 ≤ 2)).trans hkM)
    ((cNorm_mono_order (by omega : 1 ≤ 2)).trans hlM)
  have hpotSmooth : ContDiffOn ℝ ∞ (pencilTransportPotential e Q B h Φ C r c) V :=
    contDiff_vectorPairing.comp_contDiffOn
      (hl.prodMk (contDiffOn_adaptedPencilApply e hQ hB hV hmap hk))
  refine ⟨hpotSmooth, fun j ↦ ⟨(hp j).1, (hp j).2.1, (hp j).2.2.1⟩, ?_⟩
  intro m H
  let K := closedBall z ρ
  let KQ := closedBall x R
  have hq0 := cNorm_nonneg KQ (m + 2) Q
  have hb0 := cNorm_nonneg KQ (m + 2) B
  have hk0 := cNorm_nonneg K (m + 2) k
  have hl0 := cNorm_nonneg K (m + 2) l
  have ha0 := cNorm_nonneg K (m + 2) a
  have hbb0 := cNorm_nonneg K (m + 2) b
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hpotH : 1 + cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B +
      cNorm K (m + 1) k + cNorm K (m + 1) l ≤ H := by
    have hq := cNorm_mono_order (f := Q) (s := KQ) (by omega : m + 1 ≤ m + 2)
    have hb := cNorm_mono_order (f := B) (s := KQ) (by omega : m + 1 ≤ m + 2)
    have hk := cNorm_mono_order (f := k) (s := K) (by omega : m + 1 ≤ m + 2)
    have hl := cNorm_mono_order (f := l) (s := K) (by omega : m + 1 ≤ m + 2)
    dsimp [H]; linarith
  refine ⟨(hpot m).trans ((mul_le_mul_of_nonneg_left hpotH (hA m).le).trans
    (mul_le_mul_of_nonneg_right (by linarith [hS m]) hH)), ?_⟩
  intro j
  have hcolH : 1 + cNorm KQ (m + 2) Q + cNorm KQ (m + 2) B +
      cNorm K (m + 2) k + cNorm K (m + 2) a + cNorm K (m + 2) b ≤ H := by
    dsimp [H]; linarith
  have hmajor : D j m * (1 + cNorm KQ (m + 2) Q + cNorm KQ (m + 2) B +
      cNorm K (m + 2) k + cNorm K (m + 2) a + cNorm K (m + 2) b) ≤
        (A m + S m) * H :=
    (mul_le_mul_of_nonneg_left hcolH (hD j m).le).trans
      (mul_le_mul_of_nonneg_right (by linarith [hDS j m, hA m]) hH)
  exact ⟨((hp j).2.2.2 m).1.trans hmajor,
    ((hp j).2.2.2 m).2.1.trans hmajor, ((hp j).2.2.2 m).2.2.trans hmajor⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
