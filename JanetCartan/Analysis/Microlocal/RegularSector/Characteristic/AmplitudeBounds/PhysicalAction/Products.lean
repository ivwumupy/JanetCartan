module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilLeading
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RootData

/-!
# Local product bounds for the physical characteristic amplitudes

The consumers are the literal potential, leading column and correction column
in `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:two-term-null-identity`. Compact-range composition
keeps the two high norms additive. The constants precede the varying fields
and their open smoothness neighborhoods.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction

open FullPhaseCharts.InverseEstimates

variable {E F G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- On the fixed compact ball, an input value is bounded by any of its
`cNorm`s. This supplies the compact ranges for the products in
`app:ch_regular_base:lem:characteristic-kernel`. -/
theorem norm_le_cNorm_on {K V : Set E} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) {f : E → F} (hf : ContDiffOn ℝ ∞ f V)
    (m : ℕ) {x : E} (hx : x ∈ K) : ‖f x‖ ≤ cNorm K m f := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf.contDiffAt (hV.mem_nhds (hKV hy))).of_le
        (show (m : ℕ∞ω) ≤ ∞ by simp)) hx (Nat.zero_le m)

/-- Bundling the input fields for `app:ch_regular_base:lem:characteristic-kernel`
preserves the sum of their high norms on an open neighborhood. -/
theorem cNorm_pair_le_on_open {K V : Set E} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) {f : E → F} {g : E → G}
    (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    cNorm K m (fun q ↦ (f q, g q)) ≤ cNorm K m f + cNorm K m g :=
  cNorm_prodMk_le_on K hK m
    (fun q hq ↦ (hf.contDiffAt (hV.mem_nhds (hKV hq))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp))
    (fun q hq ↦ (hg.contDiffAt (hV.mem_nhds (hKV hq))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp))

/-- A fixed smooth product has one additive high norm on a compact ball.
The actual consumers are `lᵀPk`, `aⱼk`, and `b₋₁PW₀` in
`app:ch_regular_base:lem:characteristic-kernel`. Only the two input value
bounds are prescribed; no product bound is assumed. -/
theorem exists_smoothPair_cNorm_bounds
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (z : E) {ρ : ℝ} (hρ : 0 < ρ) (M N : ℝ)
    (g : F × G → H) (hg : ContDiff ℝ ∞ g) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (V : Set E), IsOpen V → closedBall z ρ ⊆ V →
        ∀ (u : E → F) (v : E → G),
          ContDiffOn ℝ ∞ u V → ContDiffOn ℝ ∞ v V →
          cNorm (closedBall z ρ) 0 u ≤ M → cNorm (closedBall z ρ) 0 v ≤ N →
          ∀ m, cNorm (closedBall z ρ) m (fun q ↦ g (u q, v q)) ≤
            C m * (1 + cNorm (closedBall z ρ) m u + cNorm (closedBall z ρ) m v) := by
  let T := closedBall (0 : F) M ×ˢ closedBall (0 : G) N
  have hT : IsCompact T := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  choose C hC hb using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn z hρ hT
      (le_refl m) (fun y _ ↦ hg.contDiffAt.of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  refine ⟨C, hC, ?_⟩
  intro V hV hKV u v hu hv hM hN m
  have hm : MapsTo (fun q ↦ (u q, v q)) (closedBall z ρ) T := by
    intro q hq
    constructor
    · simpa only [mem_closedBall, dist_zero_right] using
        (norm_le_cNorm_on (isCompact_closedBall _ _) hV hKV hu 0 hq).trans hM
    · simpa only [mem_closedBall, dist_zero_right] using
        (norm_le_cNorm_on (isCompact_closedBall _ _) hV hKV hv 0 hq).trans hN
  have hp := cNorm_prodMk_le_on (closedBall z ρ) (isCompact_closedBall _ _) m
    (fun q hq ↦ (hu.contDiffAt (hV.mem_nhds (hKV hq))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp))
    (fun q hq ↦ (hv.contDiffAt (hV.mem_nhds (hKV hq))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp))
  exact (hb m V hV hKV _ (hu.prodMk hv) hm).trans
    (mul_le_mul_of_nonneg_left (by linarith) (hC m).le)

variable {n : ℕ}

/-- Smoothness of the matrix-vector product used for the correction in
`app:ch_regular_base:eq:two-term-null-identity`, with Frobenius matrix norms. -/
theorem contDiff_matrixVectorProduct : ContDiff ℝ ∞
    (fun p : MetricTensor n × (Fin n → ℝ) ↦ p.1 *ᵥ p.2) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ ∞ (fun p : MetricTensor n × (Fin n → ℝ) ↦ ∑ j, p.1 i j * p.2 j)
  exact ContDiff.sum fun j _ ↦
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp contDiff_fst).mul
      (contDiff_pi.mp contDiff_snd j)

/-- Smoothness of the pairing in the actual potential `lᵀPk`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiff_vectorPairing : ContDiff ℝ ∞
    (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 ⬝ᵥ p.2) :=
  ContDiff.sum fun j _ ↦ (contDiff_pi.mp contDiff_fst j).mul
    (contDiff_pi.mp contDiff_snd j)

/-- Smoothness of the literal leading-column product `aⱼk`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiff_leadingProduct (j : Fin n) : ContDiff ℝ ∞
    (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 j • p.1) := by
  have ha : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 j) :=
    contDiff_pi.mp contDiff_snd j
  exact ha.smul contDiff_fst

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction
