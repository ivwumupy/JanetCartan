module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels

/-!
# Compact elapsed carriers from the original masks

The compact-support premise of the elapsed half-space kernel identity is
constructed from the actual physical masks, input symbol and frequency
regularizers (`app:ch_regular:eq:chain-tail`). The complementary output
symbol is unrestricted. A fixed smooth elapsed cutoff is constructed on the
bounded slab; it does not depend on frequency or requested accuracy.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- A fixed compact smooth extension cutoff equals one on the entire closed
elapsed interval, including both endpoints. This supplies the time cutoff
in `integral_regularizedElapsedKernel_eq_halfSpace`
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem exists_elapsed_extension_cutoff (Δ : ℝ) :
    ∃ θ : ℝ → ℂ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      ∀ r ∈ Icc 0 Δ, θ r = 1 := by
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := |Δ| + 1
      rOut := |Δ| + 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨fun r ↦ (f r : ℂ), Complex.ofRealCLM.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  intro r hr
  have hrb : r ∈ Metric.closedBall (0 : ℝ) f.rIn := by
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
    dsimp only [f]
    linarith [le_abs_self Δ, hr.2]
  simp only [f.one_of_mem_closedBall hrb, Complex.ofReal_one]

/-- The compact extended amplitude carrier uses only the original physical
masks, source shoulders, the three covectors and the time cutoff. It makes
no compact-support assumption on `1-mo` and does not suppress low frequencies
(`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_cut_jointElapsedAmplitude
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (θ : ℝ → ℂ) (hθ : HasCompactSupport θ)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (hi : HasCompactSupport mi) (hg : HasCompactSupport χA) (ho : HasCompactSupport χo) :
    HasCompactSupport (fun p : ℝ × JointVariables (Euclidean (d + 1)) ↦
      θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p) := by
  let Kb := tsupport χout ×ˢ tsupport χsource
  let Kg := tsupport (fun ξ ↦ χA (ρ • ξ))
  let Ki := Prod.snd '' tsupport mi
  let Ko := tsupport (fun ζ ↦ χo (ρ • ζ))
  have hKb : IsCompact Kb := hout.prod hsource
  have hKg : IsCompact Kg := hg.comp_smul hρ
  have hKi : IsCompact Ki := hi.image continuous_snd
  have hKo : IsCompact Ko := ho.comp_smul hρ
  have hinput : tsupport (fun η ↦ mi (y, η)) ⊆ Ki := by
    apply closure_minimal ?_ hKi.isClosed
    intro η hη
    exact ⟨(y, η), subset_tsupport mi hη, rfl⟩
  have hbase (r : ℝ) (u z ξ : Euclidean (d + 1)) (huz : (u, z) ∉ Kb) :
      orientedElapsedAmplitude backward b χout χsource β r u z ξ = 0 := by
    have hzero : elapsedAmplitude b χout χsource β r u z ξ = 0 := by
      by_cases hu : u ∈ tsupport χout
      · have hz : z ∉ tsupport χsource := fun hz ↦ huz ⟨hu, hz⟩
        exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
          (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hz)))
      · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
          (Or.inl (image_eq_zero_of_notMem_tsupport hu))
    cases backward <;> simp [orientedElapsedAmplitude, hzero]
  have hs (r : ℝ) : tsupport (jointAmplitude ρ
      (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo x y) ⊆
      KernelEstimates.jointCarrier Kb Kg Ki Ko :=
    KernelEstimates.tsupport_jointAmplitude_subset ρ _ mi mo χA χo x y
      hKb hKg hKi hKo (hbase r) Subset.rfl hinput Subset.rfl
  apply HasCompactSupport.intro
    (hθ.prod (KernelEstimates.isCompact_jointCarrier hKb hKg hKi hKo))
  intro p hp
  by_cases hr : p.1 ∈ tsupport θ
  · have hother : p.2 ∉ KernelEstimates.jointCarrier Kb Kg Ki Ko := fun hh ↦ hp ⟨hr, hh⟩
    have hz := image_eq_zero_of_notMem_tsupport (fun hh ↦ hother (hs p.1 hh))
    simp only [jointElapsedAmplitude, hz, smul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport hr, zero_smul]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
