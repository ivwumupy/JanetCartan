module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Construction

/-!
# The literal full matrix kernel of the actual normal operator

Identifies the Hilbert-adjoint composition with `maskedNormalKernel` in
`app:ch_osc:eq:osc-exact-normal-kernel`, enabling its exact change of variables.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance localOperatorsMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The complete matrix integrand is integrable from the local mask regularity
and the original compact carrier, for identification of the actual masked
normal operator (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.maskedNormalIntegrand_integrable
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (K : ℝ) {m : Euclidean n → ℝ} (hm : ContinuousOn m G.D)
    (x y : Euclidean n) :
    Integrable (fun u ↦ oscillatoryFactor K (F.phase ε x u - F.phase ε y u) •
      (m u • normalAmplitude (F.amplitude ε) x y u)) (volume.restrict G.D) := by
  let H := fun u ↦ oscillatoryFactor K (F.phase ε x u - F.phase ε y u) •
    (m u • normalAmplitude (F.amplitude ε) x y u)
  have hz (u : Euclidean n) (hu : u ∉ G.D₀) : H u = 0 := by
    have hq : (x, (y, u)) ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀) := fun h ↦ hu h.2.2
    simp [H, F.normalAmplitude_eq_zero_off_support hε hq]
  have hs : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact G.compact_D₀ (by
      intro u hu
      by_contra hout
      exact hu (hz u hout))
  have hc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro u
    by_cases hxy : x ∈ G.X₀ ∧ y ∈ G.X₀
    · by_cases hu : u ∈ G.D₀
      · have hx := G.X₀_subset hxy.1
        have hy := G.X₀_subset hxy.2
        have huD := G.D₀_subset hu
        have hp := ((F.phase_contDiffAt (F.parameter_subset hε) hx huD).comp u
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
        have hq := ((F.phase_contDiffAt (F.parameter_subset hε) hy huD).comp u
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
        have ha := (F.normalAmplitude_contDiffOn_spatial (F.parameter_subset hε)).contDiffAt (x := (x, (y, u)))
          ((G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds ⟨hx, hy, huD⟩)
        have ha' := (ha.comp u (contDiffAt_const.prodMk
          (contDiffAt_const.prodMk contDiffAt_id))).continuousAt
        exact ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_const.mul (hp.sub hq)))).cexp).smul
          ((hm.continuousAt (G.isOpen_D.mem_nhds huD)).smul ha')
      · apply (continuousAt_const (y := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
        filter_upwards [G.compact_D₀.isClosed.isOpen_compl.mem_nhds hu] with v hv
        exact hz v hv
    · have ho : x ∉ G.X₀ ∨ y ∉ G.X₀ := not_and_or.mp hxy
      apply (continuousAt_const (y := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
      exact Eventually.of_forall fun v ↦ by
        simp [H, F.normalAmplitude_eq_zero_of_not_mem_physical hε ho]
  exact hc.integrable_of_hasCompactSupport hs

/-- Entrywise formula for the complete matrix Bochner integral, without
interchanging evaluation and a potentially nonintegrable expression
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.maskedNormalKernel_apply
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (K : ℝ) {m : Euclidean n → ℝ} (hm : ContinuousOn m G.D)
    (x y : Euclidean n) (i j : Fin r) :
    maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) m x y i j =
      (((K / (2 * Real.pi)) ^ n : ℝ) : ℂ) *
        ∫ u in G.D, oscillatoryFactor K (F.phase ε x u - F.phase ε y u) *
          (F.amplitude ε x u i * star (F.amplitude ε y u j)) * (m u : ℂ) := by
  have hi := F.maskedNormalIntegrand_integrable hε K hm x y
  have he := (matrixEntryEvaluation i j).integral_comp_comm hi
  change _ = (∫ u in G.D, oscillatoryFactor K (F.phase ε x u - F.phase ε y u) •
    (m u • normalAmplitude (F.amplitude ε) x y u)) i j at he
  unfold maskedNormalKernel
  simp only [Matrix.smul_apply, Complex.real_smul]
  rw [← he]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  change oscillatoryFactor K (F.phase ε x u - F.phase ε y u) *
      ((m u : ℂ) * (F.amplitude ε x u i * star (F.amplitude ε y u j))) = _
  ring

/-- The actual Hilbert-adjoint composition acts by the literal full matrix
kernel used in the exact change of variables
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.uniformOscillatoryNormalOperator_ae_maskedNormalKernel
    (F : UniformNormalData G C) {K : ℝ} (hK : 0 ≤ K)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {m : Euclidean n → ℝ} (hm : ContinuousOn m G.D)
    (g : Lp ℂ ∞ (volume.restrict G.D))
    (hg : g =ᵐ[volume.restrict G.D] fun u ↦ (m u : ℂ))
    (f : NormalOutputL2 n r) (i : Fin r) :
    (F.uniformOscillatoryNormalOperator K g ε f) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, maskedNormalKernel G.D K (F.phase ε)
        (F.amplitude ε) m x y i j * f j y := by
  refine (F.uniformOscillatoryNormalOperator_ae_integral hK hε g f i).trans
    (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [F.maskedNormalKernel_apply hε K hm x y i j]
  congr 2
  apply integral_congr_ae
  filter_upwards [hg] with u hu
  rw [hu]

end JanetCartan.NormalComparison
