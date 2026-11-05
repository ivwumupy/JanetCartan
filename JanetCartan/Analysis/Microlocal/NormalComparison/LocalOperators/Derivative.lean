module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.CoefficientTransfer

/-!
# Exact derivative of the original local normal family

The derivative in `app:ch_osc:prop:osc-normal`, Step 2, is the sum of full
normal channels with the original coefficients and fixed mask representatives.
The parameter derivative is taken within the closed interval, so the same
statement includes both endpoints.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
local notation "E" => Euclidean n

/-- The exact full transport channels give the actual operator-norm derivative
on the closed interval, with the original averaged-gradient velocity and the
literal `pairedTransportCoefficient` (`app:ch_osc:prop:osc-normal`, Step 2).
The fixed mask symbols can be constructed by `exists_mask_derivative_symbols`.
Only equality of the cutoff on the original carrier is needed for this identity. -/
theorem UniformNormalData.exists_uniformTransportDerivative_at
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m G.D)
    (g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ k, g k =ᵐ[volume.restrict G.D] compactTransportMask m k)
    (χ : E → E → ℂ) (hχone : ∀ z ∈ G.X₀ ×ˢ G.D₀, χ z.1 z.2 = 1) :
    ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
        fullNormalAmplitudeKernel (μ := volume.restrict G.D)
          (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε) χ)
          (fun u z ↦ F.pairedTransportCoefficient ε k u z i j) (g k) (f j) x) ∧
      HasDerivWithinAt (F.uniformOscillatoryNormalOperator K (g none))
        (N none + ∑ k, N (some k)) (Icc 0 G.ε₀) ε := by
  obtain ⟨a, S, hS, hSU, hS₀, ha, hs, hea⟩ := F.exists_localizedAmplitude
  obtain ⟨φ, hφ, heφ⟩ := F.exists_localizedPhase hS hSU
  obtain ⟨w, hw, hew⟩ := F.exists_localizedVelocity hε hS hSU
  have hSD : Prod.snd '' S ⊆ G.D := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hSU hz).2
  have hv x y u (hu : u ∈ G.D) (hx : (x, u) ∈ S) (hy : (y, u) ∈ S) :
      deriv (fun s ↦ φ s x u - φ s y u) ε =
        fderiv ℝ (fun v ↦ φ ε x v - φ ε y v) u (w (x, y) u) :=
    F.localized_phase_transport_identity hε (hSU hx).1 (hSU hy).1 hu
      (heφ ε hε _ hx) (heφ ε hε _ hy) (hew x y u hx hy).eq_of_nhds
  obtain ⟨N, hN, hd⟩ := exists_compactOscillatoryNormal_transportChannels
    G.isOpen_D (normalOperatorScale n K) K hφ ha hS hSD hs hm g hg
      (fun _ _ ↦ 1) (fun _ _ ↦ rfl) ε w hw hv
  have hc k x y u i j := F.localizedTransportEntry_eq hε ha hea
    (fun x y u hx hy hu ↦ (hew x y u (hS₀ ⟨hx, hu⟩) (hS₀ ⟨hy, hu⟩)).eq_of_nhds)
      k x y u i j
  refine ⟨N, ?_, ?_⟩
  · intro k f i
    refine (hN k f i).trans (Eventually.of_forall fun x ↦ ?_)
    apply Finset.sum_congr rfl
    intro j _
    unfold fullNormalAmplitudeKernel
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    simp only [splitPhysicalPositions_pairedPosition, hc,
      pairedTransportCoefficient, pairedNormalAmplitude_pairedPosition]
    by_cases hz : (x, (y, u)) ∈ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)
    · have hx := (heφ ε hε (x, u) (hS₀ ⟨hz.1, hz.2.2⟩)).eq_of_nhds
      have hy := (heφ ε hε (y, u) (hS₀ hz.2)).eq_of_nhds
      simp only [normalizedOscillatoryKernel, hx, hy,
        hχone (x, u) ⟨hz.1, hz.2.2⟩, hχone (y, u) hz.2]
    · have hz' : F.extendedTransportCoefficient ε k (x, (y, u)) = 0 := by
        by_contra hn
        exact hz (F.extendedTransportCoefficient_support hε k hn)
      simp [hz']
  · have heq s (hsI : s ∈ Icc 0 G.ε₀) :
        F.uniformOscillatoryOperator K s = compactOscillatoryOperator G.D
          (normalOperatorScale n K) K (φ := φ s) (a := a s)
          (hφ.continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) := by
      ext f i
      have hlocal := compactOscillatoryOperator_ae_integral G.D (normalOperatorScale n K) K
        (φ := φ s) (a := a s)
        (hφ.continuous.comp (continuous_const.prodMk continuous_id))
        (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
        (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) f i
      filter_upwards [F.uniformOscillatoryOperator_ae_integral K hsI f i, hlocal]
        with x hx hl
      rw [hx, hl]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro u
      dsimp only
      rw [hea s hsI x u]
      by_cases hz : (x, u) ∈ G.X₀ ×ˢ G.D₀
      · rw [(heφ s hsI (x, u) (hS₀ hz)).eq_of_nhds]
      · simp [F.amplitude_eq_zero_off_carrier hsI hz]
    have heqN : EqOn (F.uniformOscillatoryNormalOperator K (g none))
        (fun s ↦ compactOscillatoryNormalOperator G.D (normalOperatorScale n K) K
          (φ := φ s) (a := a s)
          (hφ.continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ (ha i).continuous.comp (continuous_const.prodMk continuous_id))
          (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s) (g none)) (Icc 0 G.ε₀) := by
      intro s hsI
      simp only [uniformOscillatoryNormalOperator, compactOscillatoryNormalOperator, heq s hsI]
    exact hd.hasDerivWithinAt.congr heqN (heqN hε)

/-- Fixed representatives of the mask and its first derivatives realize the
exact derivative channels for every admissible parameter, including endpoints.
This is the local-data form of Step 2 of `app:ch_osc:prop:osc-normal`; no higher
mask derivative bound or frequency-uniform norm estimate is assumed. -/
theorem UniformNormalData.exists_uniformTransportDerivative
    (F : UniformNormalData G C) (K : ℝ)
    {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m G.D)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hmask : ∀ u ∈ G.D, 0 ≤ m u ∧ m u ≤ 1)
    (hderiv : ∀ u ∈ G.D, ‖fderiv ℝ m u‖ ≤ L / h)
    (χ : E → E → ℂ) (hχone : ∀ z ∈ G.X₀ ×ˢ G.D₀, χ z.1 z.2 = 1) :
    ∃ g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D),
      (∀ k, g k =ᵐ[volume.restrict G.D] compactTransportMask m k) ∧
      ‖g none‖ ≤ 1 ∧ (∀ j, ‖g (some j)‖ ≤ L / h) ∧
      ∀ ε ∈ Icc 0 G.ε₀,
        ∃ N : Option (Fin n) → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
          (∀ k f i, (N k f) i =ᵐ[volume] fun x ↦ ∑ j,
            fullNormalAmplitudeKernel (μ := volume.restrict G.D)
              (normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε) χ)
              (fun u z ↦ F.pairedTransportCoefficient ε k u z i j) (g k) (f j) x) ∧
          HasDerivWithinAt (F.uniformOscillatoryNormalOperator K (g none))
            (N none + ∑ k, N (some k)) (Icc 0 G.ε₀) ε := by
  obtain ⟨g₀, g₁, hg₀, hb₀, hg₁, hb₁⟩ := exists_mask_derivative_symbols G.isOpen_D m
    (hm.of_le (by simp)) hh hL hmask hderiv
  let g : Option (Fin n) → Lp ℂ ∞ (volume.restrict G.D) := fun k ↦
    match k with
    | none => g₀
    | some j => g₁ j
  have hg (k) : g k =ᵐ[volume.restrict G.D] compactTransportMask m k := by
    cases k with
    | none => exact hg₀
    | some j => exact hg₁ j
  exact ⟨g, hg, hb₀, hb₁, fun ε hε ↦
    F.exists_uniformTransportDerivative_at K hε hm g hg χ hχone⟩

end JanetCartan.NormalComparison
