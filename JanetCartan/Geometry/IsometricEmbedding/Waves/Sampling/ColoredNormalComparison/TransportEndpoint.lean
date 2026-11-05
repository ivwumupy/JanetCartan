module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks
public import JanetCartan.Analysis.Microlocal.NormalComparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition

/-!
# The common transport endpoint of the colored normal homotopy

The endpoint in `app:ch_waves:eq:colored-normal-comparison` is derived from
primitive phase and amplitude agreement at zero on the original boxes. The
literal convolved-box masks are pulled back through the carrier map `z`.
Their sum is needed only where the reference amplitude is nonzero, and follows
from `sum_coloredBlockMask_eq_one` on the unchanged patch support.

Both physical positions are retained in the matrix kernel identity. Its
integrability comes from `UniformNormalData.maskedNormalIntegrand_integrable`.
The operator identity holds for every exact L∞ realization of these masks.
Finite prefixes keep the original `dyadicScale` labels, starting at one half;
the reference amplitudes retain the same smooth bands and high-pass cutoffs.

The consumer is `jc-sampling-colored-normal-comparison`. Its concrete phase
producer is `FullPhaseCharts.ActualPhase.modulation_zero` in `ActualQuotient`.
For the amplitude, `LeadingWave.FullModulation.CarrierCompatibility.amplitudes_eq_on_carrier`
identifies the full and carrier transport fields. The raw-primary formulas in
`RawPrimary.CanonicalAtom` apply at nonzero inverse frequency, and
`WKB.derivative_expansion` supplies the polynomial with its transport leading
term. The parent must instantiate the smooth zero extension, original cutoffs
and carrier pullback in the primitive equalities and support below. No equality
of normals or successful normal-comparison record is assumed here.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.ColoredNormalComparison
open NormalComparison AmplitudeBound SeparatedSampling LatticeQuadrature BackgroundQuadrature
  RawInputPartition
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

private theorem oscillatoryOperator_zero_eq_of_primitive
    (F F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ x ∈ G.X, ∀ u ∈ G.D, F.phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ x ∈ G.X, ∀ u ∈ G.D, F.amplitude 0 x u = F₀.amplitude 0 x u) :
    F.uniformOscillatoryOperator K 0 = F₀.uniformOscillatoryOperator K 0 := by
  have hzero : (0 : ℝ) ∈ Icc 0 G.ε₀ := ⟨le_rfl, G.ε₀_pos.le⟩
  ext f i
  filter_upwards [F.uniformOscillatoryOperator_ae_integral K hzero f i,
    F₀.uniformOscillatoryOperator_ae_integral K hzero f i] with x hx hx₀
  rw [hx, hx₀]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem G.isOpen_D.measurableSet] with u hu
  by_cases hxX : x ∈ G.X
  · rw [hphase x hxX u hu, hamp x hxX u hu]
  · have hz : (x, u) ∉ G.X₀ ×ˢ G.D₀ := fun h ↦ hxX (G.X₀_subset h.1)
    simp [F.amplitude_eq_zero_off_carrier hzero hz,
      F₀.amplitude_eq_zero_off_carrier hzero hz]

private theorem sum_normalOperator_zero_eq_of_partition
    {Color : Type*} [Fintype Color]
    (F : Color → UniformNormalData G C) (F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).amplitude 0 x u = F₀.amplitude 0 x u)
    (m : Color → Euclidean n → ℝ)
    (hpart : ∀ x u, u ∈ G.D → F₀.amplitude 0 x u ≠ 0 → ∑ c, m c u = 1)
    (g : Color → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ)) :
    ∑ c, (F c).uniformOscillatoryNormalOperator K (g c) 0 =
      (F₀.uniformOscillatoryOperator K 0).comp
        (F₀.uniformOscillatoryOperator K 0).adjoint := by
  have hzero : (0 : ℝ) ∈ Icc 0 G.ε₀ := ⟨le_rfl, G.ε₀_pos.le⟩
  have hT c := oscillatoryOperator_zero_eq_of_primitive (F c) F₀ K (hphase c) (hamp c)
  have hm : (∑ c, multiplicationOperator (g c)) = multiplicationOperator (∑ c, g c) := by
    simp only [multiplicationOperator, map_sum]
  have hleft : (F₀.uniformOscillatoryOperator K 0).comp
      (multiplicationOperator (∑ c, g c)) = F₀.uniformOscillatoryOperator K 0 := by
    ext f i
    filter_upwards [F₀.uniformOscillatoryOperator_ae_integral K hzero
      (multiplicationOperator (∑ c, g c) f) i,
      F₀.uniformOscillatoryOperator_ae_integral K hzero f i] with x hx hx₀
    change (F₀.uniformOscillatoryOperator K 0 (multiplicationOperator (∑ c, g c) f)) i x = _ at hx
    rw [ContinuousLinearMap.comp_apply, hx, hx₀]
    apply integral_congr_ae
    filter_upwards [multiplicationOperator_coeFn (∑ c, g c) f,
      Lp.coeFn_finsetSum Finset.univ g, eventually_all.mpr hg,
      ae_restrict_mem G.isOpen_D.measurableSet] with u hu hs hg' huD
    by_cases ha : F₀.amplitude 0 x u = 0
    · simp [ha]
    · have hsum : (∑ c, g c u) = 1 := by
        simp_rw [hg']
        rw [← Complex.ofReal_sum, hpart x u huD ha, Complex.ofReal_one]
      simp only [hu, hs, Finset.sum_apply, hsum, one_mul]
  simp_rw [UniformNormalData.uniformOscillatoryNormalOperator, hT]
  rw [← ContinuousLinearMap.comp_finsetSum, ← ContinuousLinearMap.finsetSum_comp,
    hm, ← ContinuousLinearMap.comp_assoc, hleft]

private theorem maskedNormalKernel_zero_eq_of_primitive
    (F F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ x ∈ G.X, ∀ u ∈ G.D, F.phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ x ∈ G.X, ∀ u ∈ G.D, F.amplitude 0 x u = F₀.amplitude 0 x u)
    (m : Euclidean n → ℝ) (x y : Euclidean n) :
    maskedNormalKernel G.D K (F.phase 0) (F.amplitude 0) m x y =
      maskedNormalKernel G.D K (F₀.phase 0) (F₀.amplitude 0) m x y := by
  have hzero : (0 : ℝ) ∈ Icc 0 G.ε₀ := ⟨le_rfl, G.ε₀_pos.le⟩
  unfold maskedNormalKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem G.isOpen_D.measurableSet] with u hu
  by_cases hxy : x ∈ G.X ∧ y ∈ G.X
  · have hA : NormalComparison.normalAmplitude (F.amplitude 0) x y u =
        NormalComparison.normalAmplitude (F₀.amplitude 0) x y u := by
      ext i j
      change F.amplitude 0 x u i * star (F.amplitude 0 y u j) =
        F₀.amplitude 0 x u i * star (F₀.amplitude 0 y u j)
      rw [hamp x hxy.1 u hu, hamp y hxy.2 u hu]
    rw [hphase x hxy.1 u hu, hphase y hxy.2 u hu, hA]
  · have hout : x ∉ G.X₀ ∨ y ∉ G.X₀ := by
      by_contra h
      push Not at h
      exact hxy ⟨G.X₀_subset h.1, G.X₀_subset h.2⟩
    simp only [F.normalAmplitude_eq_zero_of_not_mem_physical hzero hout,
      F₀.normalAmplitude_eq_zero_of_not_mem_physical hzero hout, smul_zero]

private theorem sum_maskedNormalKernel_zero_eq_of_partition
    {Color : Type*} [Fintype Color]
    (F : Color → UniformNormalData G C) (F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).amplitude 0 x u = F₀.amplitude 0 x u)
    (m : Color → Euclidean n → ℝ) (hm : ∀ c, ContinuousOn (m c) G.D)
    (hpart : ∀ x u, u ∈ G.D → F₀.amplitude 0 x u ≠ 0 → ∑ c, m c u = 1)
    (x y : Euclidean n) :
    ∑ c, maskedNormalKernel G.D K ((F c).phase 0) ((F c).amplitude 0) (m c) x y =
      maskedNormalKernel G.D K (F₀.phase 0) (F₀.amplitude 0) (fun _ ↦ 1) x y := by
  have hzero : (0 : ℝ) ∈ Icc 0 G.ε₀ := ⟨le_rfl, G.ε₀_pos.le⟩
  simp_rw [maskedNormalKernel_zero_eq_of_primitive _ F₀ K (hphase _) (hamp _)]
  unfold maskedNormalKernel
  rw [← Finset.smul_sum, ← integral_finsetSum Finset.univ
    (fun c _ ↦ F₀.maskedNormalIntegrand_integrable hzero K (hm c) x y)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem G.isOpen_D.measurableSet] with u hu
  rw [← Finset.smul_sum, ← Finset.sum_smul]
  by_cases ha : F₀.amplitude 0 x u = 0
  · have hz : NormalComparison.normalAmplitude (F₀.amplitude 0) x y u = 0 := by
      ext i j
      simp [NormalComparison.normalAmplitude, ha]
    simp [hz]
  · rw [hpart x u hu ha]

/-- The colored zero-parameter normals sum to the common transport normal,
from primitive phase/amplitude agreement on the original boxes and reference
amplitude support over the unchanged patch. The literal mask partition is
proved only where that amplitude is nonzero; every exact L∞ realization is
allowed (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_colored_normal_zero_eq_transport
    {κ : ℝ → ℝ} (hi : Integrable κ) (hm : ∫ t, κ t = 1)
    (hn : ∀ t, 0 ≤ κ t) (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : Euclidean n → Point)
    (F : (Fin 3 → Fin (p + 1)) → UniformNormalData G C)
    (F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ c x, x ∈ G.X → ∀ u ∈ G.D,
      (F c).amplitude 0 x u = F₀.amplitude 0 x u)
    (hsupport : ∀ x u, u ∈ G.D → F₀.amplitude 0 x u ≠ 0 → z u ∈ Function.support ψ)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c (z u) : ℂ)) :
    ∑ c, (F c).uniformOscillatoryNormalOperator K (g c) 0 =
      (F₀.uniformOscillatoryOperator K 0).comp
        (F₀.uniformOscillatoryOperator K 0).adjoint := by
  apply sum_normalOperator_zero_eq_of_partition F F₀ K hphase hamp
    (fun c u ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z u)) _ g hg
  intro x u hu ha
  exact sum_coloredBlockMask_eq_one hi hm hn hk hp hψ hh hh₁ (hsupport x u hu ha)

/-- The complete two-position matrix kernel at the colored zero endpoint is
exactly the uncolored transport kernel, with all original phase, amplitude,
normalization and cutoffs retained. Integrability of each summand is derived
from `UniformNormalData`, not assumed
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem sum_colored_maskedNormalKernel_zero_eq_transport
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : Euclidean n → Point) (hz : Continuous z)
    (F : (Fin 3 → Fin (p + 1)) → UniformNormalData G C)
    (F₀ : UniformNormalData G C) (K : ℝ)
    (hphase : ∀ c x, x ∈ G.X → ∀ u ∈ G.D, (F c).phase 0 x u = F₀.phase 0 x u)
    (hamp : ∀ c x, x ∈ G.X → ∀ u ∈ G.D,
      (F c).amplitude 0 x u = F₀.amplitude 0 x u)
    (hsupport : ∀ x u, u ∈ G.D → F₀.amplitude 0 x u ≠ 0 → z u ∈ Function.support ψ)
    (x y : Euclidean n) :
    ∑ c, maskedNormalKernel G.D K ((F c).phase 0) ((F c).amplitude 0)
      (fun u ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c (z u)) x y =
      maskedNormalKernel G.D K (F₀.phase 0) (F₀.amplitude 0) (fun _ ↦ 1) x y := by
  apply sum_maskedNormalKernel_zero_eq_of_partition F F₀ K hphase hamp _ _ _ x y
  · intro c
    exact ((contDiff_coloredBlockMask hc hs p (integerCube (blockCutoff p B h)) h c).continuous.comp
      hz).continuousOn
  · intro x u hu ha
    exact sum_coloredBlockMask_eq_one (hs.continuous.integrable_of_hasCompactSupport hc)
      hm hn hk hp hψ hh hh₁ (hsupport x u hu ha)

/-- Summing the endpoint over the identical original smooth band labels
preserves the common transport normal on every finite prefix. In particular
`j = 0` has scale one half; neither this band nor the high-pass transition
between one and two is removed (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_colored_prefix_normal_zero_eq_transport
    {κ : ℝ → ℝ} (hi : Integrable κ) (hm : ∫ t, κ t = 1)
    (hn : ∀ t, 0 ≤ κ t) (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : Euclidean n → Point)
    (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
    (F₀ : ℕ → UniformNormalData G C) (J : ℕ)
    (hphase : ∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
      (F c j).phase 0 x u = (F₀ j).phase 0 x u)
    (hamp : ∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
      (F c j).amplitude 0 x u = (F₀ j).amplitude 0 x u)
    (hsupport : ∀ j ∈ Finset.range J, ∀ x u, u ∈ G.D →
      (F₀ j).amplitude 0 x u ≠ 0 → z u ∈ Function.support ψ)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c (z u) : ℂ)) :
    ∑ c, ∑ j ∈ Finset.range J,
      (F c j).uniformOscillatoryNormalOperator (dyadicScale j) (g c) 0 =
      ∑ j ∈ Finset.range J, ((F₀ j).uniformOscillatoryOperator (dyadicScale j) 0).comp
        ((F₀ j).uniformOscillatoryOperator (dyadicScale j) 0).adjoint := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact sum_colored_normal_zero_eq_transport hi hm hn hk hp hψ hh hh₁ z
    (fun c ↦ F c j) (F₀ j) (dyadicScale j) (fun c ↦ hphase c j hj)
    (fun c ↦ hamp c j hj) (hsupport j hj) g hg

/-- The same finite-prefix identity at the full two-position matrix kernel
level, with the exact same amplitudes, masks and half-scale dyadic labels as
`sum_colored_prefix_normal_zero_eq_transport`
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_colored_prefix_maskedNormalKernel_zero_eq_transport
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : Euclidean n → Point) (hz : Continuous z)
    (F : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
    (F₀ : ℕ → UniformNormalData G C) (J : ℕ)
    (hphase : ∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
      (F c j).phase 0 x u = (F₀ j).phase 0 x u)
    (hamp : ∀ c j, j ∈ Finset.range J → ∀ x ∈ G.X, ∀ u ∈ G.D,
      (F c j).amplitude 0 x u = (F₀ j).amplitude 0 x u)
    (hsupport : ∀ j ∈ Finset.range J, ∀ x u, u ∈ G.D →
      (F₀ j).amplitude 0 x u ≠ 0 → z u ∈ Function.support ψ)
    (x y : Euclidean n) :
    ∑ c, ∑ j ∈ Finset.range J,
      maskedNormalKernel G.D (dyadicScale j) ((F c j).phase 0) ((F c j).amplitude 0)
        (fun u ↦ coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c (z u)) x y =
      ∑ j ∈ Finset.range J, maskedNormalKernel G.D (dyadicScale j)
        ((F₀ j).phase 0) ((F₀ j).amplitude 0) (fun _ ↦ 1) x y := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact sum_colored_maskedNormalKernel_zero_eq_transport hc hs hm hn hk hp hψ hh hh₁ z hz
    (fun c ↦ F c j) (F₀ j) (dyadicScale j) (fun c ↦ hphase c j hj)
    (fun c ↦ hamp c j hj) (hsupport j hj) x y

end JanetCartan.Sampling.ColoredNormalComparison
