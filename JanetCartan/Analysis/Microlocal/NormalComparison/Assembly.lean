module

public import JanetCartan.Analysis.Microlocal.NormalComparison.ScalarChannel
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators

/-!
# Exact masked normal comparison from the original uniform data

Assembles both steps of `app:ch_osc:prop:osc-normal`. The constants precede the
phase family, frequency, mask and parameter. The inverse-amplitude bounds,
scalar cutoff channel, literal transport coefficients and actual derivative
are all constructed from the original buffered input hypotheses.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ}

/-- The complete masked normal estimate `app:ch_osc:eq:osc-normal-mask`.
Only the mask's range and first derivative bound enter the constant. The
comparison concerns the actual Hilbert-adjoint composition on all of L². -/
theorem UniformNormalGeometry.exists_uniformOscillatoryNormalOperator_comparison
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ B > 0, ∀ F : UniformNormalData G C, ∀ K > 0,
      ∀ (m : Euclidean n → ℝ), ContDiffOn ℝ ∞ m G.D →
      ∀ h L : ℝ, 0 < h → h ≤ 1 → 0 ≤ L →
      (∀ u ∈ G.D, 0 ≤ m u ∧ m u ≤ 1) →
      (∀ u ∈ G.D, ‖fderiv ℝ m u‖ ≤ L / h) →
      ∀ g : Lp ℂ ∞ (volume.restrict G.D),
        g =ᵐ[volume.restrict G.D] (fun u ↦ (m u : ℂ)) →
      ∀ ε ∈ Icc 0 G.ε₀,
        ‖F.uniformOscillatoryNormalOperator K g ε -
          F.uniformOscillatoryNormalOperator K g 0‖ ≤
            B * (1 + (n : ℝ) * L) * ε / h := by
  let χ := fixedScalarNormalCutoffs G C
  obtain ⟨S, hS, hSb⟩ := χ.exists_scalarChannel_bound
  obtain ⟨R, _, A, hA, hc⟩ := G.exists_pairedTransportCoefficient_bounds C
  let B₀ := (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A * S ^ 2)
  have hB₀ : 0 ≤ B₀ := by
    have := fixedBoxAmplitudeConstant_nonneg n R
    dsimp [B₀]
    positivity
  let B := B₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro F K hK m hm h L hh hh₁ hL hmask hderiv g hg ε hε
  have hχone : ∀ z ∈ G.X₀ ×ˢ G.D₀, χ.amplitude z 0 = 1 := by
    intro z hz
    exact χ.amplitude_eq_one_on_plateau (χ.plateau_x hz.1) (χ.plateau_u hz.2) 0
  obtain ⟨g', hg', hg₀, hg₁, hchannels⟩ := F.exists_uniformTransportDerivative K hm
    hh hL hmask hderiv (fun x u ↦ χ.amplitude (x, u) 0) hχone
  have heqg : g' none = g := by
    apply Lp.ext
    exact (hg' none).trans hg.symm
  have hNall : ∀ s : ℝ,
      ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
        s ∈ Icc 0 G.ε₀ →
          (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
            fullNormalAmplitudeKernel (μ := volume.restrict G.D)
              (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase s)
                (fun x u ↦ χ.amplitude (x, u) 0))
              (fun u z ↦ F.pairedTransportCoefficient s k u z i j) (g' k) (f j) x) ∧
          HasDerivWithinAt (F.uniformOscillatoryNormalOperator K (g' none))
            (N none + ∑ k, N (some k)) (Icc 0 G.ε₀) s := by
    intro s
    by_cases hs : s ∈ Icc 0 G.ε₀
    · obtain ⟨N, hn, hd⟩ := hchannels s hs
      exact ⟨N, fun _ ↦ ⟨hn, hd⟩⟩
    · exact ⟨0, fun h ↦ (hs h).elim⟩
  choose N hN using hNall
  have hsub : Icc 0 ε ⊆ Icc 0 G.ε₀ := Icc_subset_Icc le_rfl hε.2
  have hbound : ∀ s ∈ Icc 0 ε, ∀ k, ‖N s k‖ ≤ B * ‖g' k‖ := by
    intro s hs k
    have hs' := hsub hs
    have hsq : ‖χ.scalarChannel F K s‖ ^ 2 ≤ S ^ 2 := by
      nlinarith [hSb F s hs' K hK, norm_nonneg (χ.scalarChannel F K s)]
    have hn := norm_matrixNormalChannel_le G.dimension_pos R
      G.isOpen_D.measurableSet
      (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase s)
        (fun x u ↦ χ.amplitude (x, u) 0))
      ((χ.toUniformNormalData F).normalizedKernel_contDiff hs' (normalOperatorScale n K) K 0)
      ((χ.toUniformNormalData F).normalizedKernel_hasCompactSupport hs'
        (normalOperatorScale n K) K 0)
      (χ.scalarChannel F K s) (χ.scalarChannel_ae_integral F K hs')
      (F.pairedTransportCoefficient s k) A (hc F s hs' k) (g' k) (N s k)
      ((hN s hs').1 k)
    calc
      ‖N s k‖ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A *
          ‖χ.scalarChannel F K s‖ ^ 2 * ‖g' k‖) := hn
      _ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A * S ^ 2 * ‖g' k‖) := by
        gcongr
        exact mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hA.le
      _ = B₀ * ‖g' k‖ := by dsimp [B₀]; ring
      _ ≤ B * ‖g' k‖ := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
  rw [← heqg]
  apply norm_sub_le_of_transport_channels_within
    (F.uniformOscillatoryNormalOperator K (g' none)) (fun s ↦ N s none)
    (fun s j ↦ N s (some j)) hε.1 hh hh₁ hB.le
  · intro s hs
    exact ((hN s (hsub hs)).2).mono hsub
  · intro s hs
    exact (hbound s hs none).trans (by simpa using mul_le_mul_of_nonneg_left hg₀ hB.le)
  · intro s hs j
    exact (hbound s hs (some j)).trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hg₁ j) hB.le)

/-- Both conclusions of `app:ch_osc:prop:osc-normal`, with one positive
constant chosen solely from the fixed geometry, input jets and first-mask-jet
budget. No operator, inverse or transport estimate is an extra hypothesis. -/
theorem UniformNormalGeometry.exists_uniformNormalComparison
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ B > 0, ∀ F : UniformNormalData G C, ∀ K ≥ 1,
      (∀ ε ∈ Icc 0 G.ε₀, ‖F.uniformOscillatoryOperator K ε‖ ≤ B) ∧
      ∀ (m : Euclidean n → ℝ), ContDiffOn ℝ ∞ m G.D →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ u ∈ G.D, 0 ≤ m u ∧ m u ≤ 1) →
      (∀ u ∈ G.D, ‖fderiv ℝ m u‖ ≤ L / h) →
      ∃ g : Lp ℂ ∞ (volume.restrict G.D),
        (g =ᵐ[volume.restrict G.D] (fun u ↦ (m u : ℂ))) ∧
        ∀ ε ∈ Icc 0 G.ε₀,
          ‖F.uniformOscillatoryNormalOperator K g ε -
            F.uniformOscillatoryNormalOperator K g 0‖ ≤ B * ε / h := by
  obtain ⟨S, hS, hSb⟩ := G.exists_uniformOscillatoryOperator_bound C
  obtain ⟨B, _, hBb⟩ := G.exists_uniformOscillatoryNormalOperator_comparison C
  refine ⟨max S (B * (1 + (n : ℝ) * L)), hS.trans_le (le_max_left _ _), ?_⟩
  intro F K hK
  have hK' : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨fun ε hε ↦ (hSb F ε hε K hK').trans (le_max_left _ _), ?_⟩
  intro m hm h hh hh₁ hmask hderiv
  obtain ⟨g, _, hg, _, _, _⟩ := exists_mask_derivative_symbols G.isOpen_D m
    (hm.of_le (by simp)) hh hL hmask hderiv
  refine ⟨g, hg, ?_⟩
  intro ε hε
  apply (hBb F K hK' m hm h L hh hh₁ hL hmask hderiv g hg ε hε).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hε.1) hh.le

end JanetCartan.NormalComparison
