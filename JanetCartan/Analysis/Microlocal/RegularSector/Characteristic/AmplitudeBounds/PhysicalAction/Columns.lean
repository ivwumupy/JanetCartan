module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Differential

/-!
# The leading, correction and physical residual columns

For `paper-v2.tex`, `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual`, the actual real columns
`W₀`, `b₋₁PW₀`, and `P(b₋₁PW₀)` have one additive high bound with reserve two.
All intermediate low bounds are deduced from the specified second-order
input bounds. No estimate for a product or physical action is an input.

The nullvector and complement inputs are produced by `AmplitudeBounds.RootData`
and the transported-primitive construction; the signed-row pullback produces
the row input. The parent amplitude assembly must supply those bounds for
its same primitive coefficients, flow and chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

variable {n d : ℕ}

/-- The literal leading and correction columns and their full physical
residual are smooth and have one additive high norm with fixed reserve two.
Constants depend on fixed balls, the fixed physical projection, a common
second-order low bound and the column index, and precede every varying field.
The actual `k,a,b` smoothness and low bounds are explicit intermediate inputs;
they are not a primitive amplitude theorem. This closes the physical product
deduction for `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_pencilColumns_cNorm_bounds
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : TwoTimePoint (Euclidean d)) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Euclidean n) (R M : ℝ) (j : Fin n)
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
          let a := pencilSignedRow e Q B h Φ C r c σ
          let b := pencilChartComplement e Q h Φ C r c
          let w₀ := pencilLeadingColumn e Q B h Φ C r c σ j
          let w₁ := pencilCorrectionColumn e Q B h Φ C r c σ j
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiffOn ℝ ∞ k V → ContDiffOn ℝ ∞ a V → ContDiffOn ℝ ∞ b V →
          cNorm (closedBall x R) 2 Q ≤ M → cNorm (closedBall x R) 2 B ≤ M →
          cNorm (closedBall z ρ) 2 k ≤ M → cNorm (closedBall z ρ) 2 a ≤ M →
          cNorm (closedBall z ρ) 2 b ≤ M →
          ContDiffOn ℝ ∞ w₀ V ∧ ContDiffOn ℝ ∞ w₁ V ∧
          ContDiffOn ℝ ∞ (adaptedPencilApply e Q B w₁) V ∧
          ∀ m,
            let H := 1 + cNorm (closedBall x R) (m + 2) Q +
              cNorm (closedBall x R) (m + 2) B + cNorm (closedBall z ρ) (m + 2) k +
              cNorm (closedBall z ρ) (m + 2) a + cNorm (closedBall z ρ) (m + 2) b
            cNorm (closedBall z ρ) m w₀ ≤ Cₐ m * H ∧
            cNorm (closedBall z ρ) m w₁ ≤ Cₐ m * H ∧
            cNorm (closedBall z ρ) m (adaptedPencilApply e Q B w₁) ≤ Cₐ m * H := by
  obtain ⟨D, hD, hleading⟩ := exists_smoothPair_cNorm_bounds z hρ M M _ (contDiff_leadingProduct j)
  let N₀ := D 2 * (1 + M + M)
  obtain ⟨A, hA, haction₀⟩ :=
    exists_adaptedPencilApply_cNorm_bounds e z hρ x R (max M N₀) himage
  let N₁ := A 1 * (1 + M + M + N₀)
  obtain ⟨E, hE, hcorrection⟩ := exists_smoothPair_cNorm_bounds z hρ M N₁ _
    (contDiff_matrixVectorProduct (n := n))
  let N₂ := E 1 * (1 + M + N₁)
  obtain ⟨F, hF, haction₁⟩ :=
    exists_adaptedPencilApply_cNorm_bounds e z hρ x R (max M N₂) himage
  let L := fun m ↦ A m * (1 + D (m + 1))
  let J := fun m ↦ E m * (1 + L m)
  let Z := fun m ↦ F m * (1 + J (m + 1))
  have hL m : 0 < L m := mul_pos (hA m) (by linarith [hD (m + 1)])
  have hJ m : 0 < J m := mul_pos (hE m) (by linarith [hL m])
  have hZ m : 0 < Z m := mul_pos (hF m) (by linarith [hJ (m + 1)])
  refine ⟨fun m ↦ D m + J m + Z m, fun m ↦ add_pos (add_pos (hD m) (hJ m)) (hZ m), ?_⟩
  intro Ω V hΩ hV hKQ hK hmap Q B h Φ C r c σ k a b w₀ w₁
    hQ hB hk ha hb hQM hBM hkM haM hbM
  let K := closedBall z ρ
  let KQ := closedBall x R
  have hq₀ : cNorm KQ 0 Q ≤ M := (cNorm_mono_order (by omega : 0 ≤ 2)).trans hQM
  have hb₀ : cNorm KQ 0 B ≤ M := (cNorm_mono_order (by omega : 0 ≤ 2)).trans hBM
  have hk₀ : cNorm K 0 k ≤ M := (cNorm_mono_order (by omega : 0 ≤ 2)).trans hkM
  have ha₀ : cNorm K 0 a ≤ M := (cNorm_mono_order (by omega : 0 ≤ 2)).trans haM
  have hb'₀ : cNorm K 0 b ≤ M := (cNorm_mono_order (by omega : 0 ≤ 2)).trans hbM
  have hw₀ : ContDiffOn ℝ ∞ w₀ V :=
    (contDiff_leadingProduct j).comp_contDiffOn (hk.prodMk ha)
  have hp₀ : ContDiffOn ℝ ∞ (adaptedPencilApply e Q B w₀) V :=
    contDiffOn_adaptedPencilApply e hQ hB hV hmap hw₀
  have hw₁ : ContDiffOn ℝ ∞ w₁ V :=
    contDiff_matrixVectorProduct.comp_contDiffOn (hb.prodMk hp₀)
  have hp₁ : ContDiffOn ℝ ∞ (adaptedPencilApply e Q B w₁) V :=
    contDiffOn_adaptedPencilApply e hQ hB hV hmap hw₁
  have hw₀Bound (i : ℕ) : cNorm K i w₀ ≤ D i * (1 + cNorm K i k + cNorm K i a) :=
    hleading V hV hK k a hk ha hk₀ ha₀ i
  have hw₀Low : cNorm K 2 w₀ ≤ N₀ :=
    (hw₀Bound 2).trans (mul_le_mul_of_nonneg_left (by linarith) (hD 2).le)
  have hw₀Low' : cNorm K 1 w₀ ≤ max M N₀ :=
    ((cNorm_mono_order (by omega : 1 ≤ 2)).trans hw₀Low).trans (le_max_right _ _)
  have hp₀Bound i := haction₀ Ω V hΩ hV hKQ hK hmap Q B w₀ hQ hB hw₀
    (hq₀.trans (le_max_left _ _)) (hb₀.trans (le_max_left _ _)) hw₀Low' i
  have hp₀Low : cNorm K 1 (adaptedPencilApply e Q B w₀) ≤ N₁ :=
    (hp₀Bound 1).trans (mul_le_mul_of_nonneg_left (by linarith) (hA 1).le)
  have hp₀Low' : cNorm K 0 (adaptedPencilApply e Q B w₀) ≤ N₁ :=
    (cNorm_mono_order (by omega : 0 ≤ 1)).trans hp₀Low
  have hw₁Bound (i : ℕ) : cNorm K i w₁ ≤
      E i * (1 + cNorm K i b + cNorm K i (adaptedPencilApply e Q B w₀)) :=
    hcorrection V hV hK b (adaptedPencilApply e Q B w₀) hb hp₀ hb'₀ hp₀Low' i
  have hbLow : cNorm K 1 b ≤ M := (cNorm_mono_order (by omega : 1 ≤ 2)).trans hbM
  have hw₁Low : cNorm K 1 w₁ ≤ N₂ :=
    (hw₁Bound 1).trans (mul_le_mul_of_nonneg_left (by linarith) (hE 1).le)
  have hp₁Bound i := haction₁ Ω V hΩ hV hKQ hK hmap Q B w₁ hQ hB hw₁
    (hq₀.trans (le_max_left _ _)) (hb₀.trans (le_max_left _ _))
    (hw₁Low.trans (le_max_right _ _)) i
  refine ⟨hw₀, hw₁, hp₁, ?_⟩
  intro m H
  have hq0 := cNorm_nonneg KQ (m + 2) Q
  have hb0 := cNorm_nonneg KQ (m + 2) B
  have hk0 := cNorm_nonneg K (m + 2) k
  have ha0 := cNorm_nonneg K (m + 2) a
  have hbb0 := cNorm_nonneg K (m + 2) b
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hqH (i : ℕ) (hi : i ≤ m + 2) :
      1 + cNorm KQ i Q + cNorm KQ i B ≤ H := by
    have hq := cNorm_mono_order (f := Q) (s := KQ) hi
    have hb := cNorm_mono_order (f := B) (s := KQ) hi
    dsimp [H]; linarith
  have hbH (i : ℕ) (hi : i ≤ m + 2) : 1 + cNorm K i b ≤ H := by
    have hb := cNorm_mono_order (f := b) (s := K) hi
    dsimp [H]; linarith
  have hleadingH (i : ℕ) (hi : i ≤ m + 2) : cNorm K i w₀ ≤ D i * H := by
    apply (hw₀Bound i).trans
    apply mul_le_mul_of_nonneg_left _ (hD i).le
    have hk := cNorm_mono_order (f := k) (s := K) hi
    have ha := cNorm_mono_order (f := a) (s := K) hi
    dsimp [H]; linarith
  have hactionH (i : ℕ) (hi : i + 1 ≤ m + 2) :
      cNorm K i (adaptedPencilApply e Q B w₀) ≤ L i * H := by
    apply (hp₀Bound i).trans
    have hn : 1 + cNorm KQ (i + 1) Q + cNorm KQ (i + 1) B +
        cNorm K (i + 1) w₀ ≤ (1 + D (i + 1)) * H := by
      nlinarith only [hqH (i + 1) hi, hleadingH (i + 1) hi]
    exact (mul_le_mul_of_nonneg_left hn (hA i).le).trans_eq (by dsimp [L]; ring)
  have hcorrectionH (i : ℕ) (hi : i + 1 ≤ m + 2) : cNorm K i w₁ ≤ J i * H := by
    apply (hw₁Bound i).trans
    have hn : 1 + cNorm K i b + cNorm K i (adaptedPencilApply e Q B w₀) ≤
        (1 + L i) * H := by
      nlinarith only [hbH i (by omega), hactionH i hi]
    exact (mul_le_mul_of_nonneg_left hn (hE i).le).trans_eq (by dsimp [J]; ring)
  have hresidual : cNorm K m (adaptedPencilApply e Q B w₁) ≤ Z m * H := by
    apply (hp₁Bound m).trans
    have hn : 1 + cNorm KQ (m + 1) Q + cNorm KQ (m + 1) B +
        cNorm K (m + 1) w₁ ≤ (1 + J (m + 1)) * H := by
      nlinarith only [hqH (m + 1) (by omega), hcorrectionH (m + 1) (by omega)]
    exact (mul_le_mul_of_nonneg_left hn (hF m).le).trans_eq (by dsimp [Z]; ring)
  exact ⟨(hleadingH m (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hJ m, hZ m]) hH),
    (hcorrectionH m (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hD m, hZ m]) hH),
    hresidual.trans (mul_le_mul_of_nonneg_right (by linarith [hD m, hJ m]) hH)⟩

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
