module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Channels
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth localized parameter families

Localization of the original data in `app:ch_osc:setup:osc-normal` gives a
smooth compact kernel family agreeing on the entire closed parameter interval.
This establishes operator-norm differentiability within the interval, including
both endpoints, without imposing support conditions on the given extensions.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}
local notation "E" => Euclidean n

/-- A smooth kernel family agreeing with the literal kernel on the closed
parameter interval. The cutoff is used to construct the differentiable
operator family in `app:ch_osc:prop:osc-normal`; no assumptions are made on
amplitude support outside that interval. -/
theorem UniformNormalData.exists_localizedKernelFamily
    (F : UniformNormalData G C) (K : ℝ)
    (χ : E → E → ℂ) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hsχ : tsupport (Function.uncurry χ) ⊆ G.X ×ˢ G.D)
    (hχone : ∀ z ∈ G.X₀ ×ˢ G.D₀, χ z.1 z.2 = 1) :
    ∃ t : Fin r → ℝ → E × E → ℂ,
      (∀ i, ContDiff ℝ ∞ (Function.uncurry (t i))) ∧
      (∀ i s z, z ∉ tsupport (Function.uncurry χ) → t i s z = 0) ∧
      ∀ s ∈ Icc 0 G.ε₀, ∀ i z,
        t i s z = normalizedOscillatoryKernel (normalOperatorScale n K) K
          (F.phase s) (fun x u ↦ F.amplitude s x u i) z.1 z.2 := by
  obtain ⟨W, hW, hIW, hWP, _⟩ := exists_open_between_and_isCompact_closure
    isCompact_Icc F.isOpen_parameterDomain F.parameter_subset
  obtain ⟨θ, hθ, _, hsθ, hθone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_Icc hIW
  have hθs : tsupport θ ⊆ F.parameterDomain := by
    simpa only [tsupport, hsθ] using hWP
  let t := fun i s (z : E × E) ↦ (θ s : ℂ) * χ z.1 z.2 *
    normalizedOscillatoryKernel (normalOperatorScale n K) K
      (F.phase s) (fun x u ↦ F.amplitude s x u i) z.1 z.2
  refine ⟨t, ?_, ?_, ?_⟩
  · intro i
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hpθ : p.1 ∈ tsupport θ
    · by_cases hpχ : p.2 ∈ tsupport (Function.uncurry χ)
      · have hp := F.phase_contDiffAt (hθs hpθ) (hsχ hpχ).1 (hsχ hpχ).2
        have ha := (contDiffAt_pi.mp
          (F.amplitude_contDiffAt (hθs hpθ) (hsχ hpχ).1 (hsχ hpχ).2)) i
        have ht : ContDiffAt ℝ ∞ (fun q : ℝ × (E × E) ↦
            normalizedOscillatoryKernel (normalOperatorScale n K) K
              (F.phase q.1) (fun x u ↦ F.amplitude q.1 x u i) q.2.1 q.2.2) p :=
          (contDiffAt_const.mul ((contDiffAt_const.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_const.mul hp))).cexp)).mul ha
        exact ((Complex.ofRealCLM.contDiff.comp (hθ.comp contDiff_fst)).contDiffAt.mul
          (hχ.comp contDiff_snd).contDiffAt).mul ht
      · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        have hev := (notMem_tsupport_iff_eventuallyEq.mp hpχ).comp_tendsto continuousAt_snd
        filter_upwards [hev] with q hq
        simp [t, Function.uncurry] at hq ⊢
        rw [hq]
        simp
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have hev := (notMem_tsupport_iff_eventuallyEq.mp hpθ).comp_tendsto continuousAt_fst
      filter_upwards [hev] with q hq
      change θ q.1 = 0 at hq
      simp [t, Function.uncurry, hq]
  · intro i s z hz
    have hzχ : χ z.1 z.2 = 0 := by
      by_contra hn
      exact hz (subset_tsupport (Function.uncurry χ) hn)
    simp [t, hzχ]
  · intro s hs i z
    by_cases hz : z ∈ G.X₀ ×ˢ G.D₀
    · simp [t, (hθone s).mp hs, hχone z hz]
    · simp [t, normalizedOscillatoryKernel, F.amplitude_eq_zero_off_carrier hs hz]

/-- Operator-norm differentiability of the actual masked normal family within
the closed manuscript interval, including both endpoints
(`app:ch_osc:prop:osc-normal`). The derivative exists without global smoothness
of the original family; its transport-channel formula is a separate result. -/
theorem UniformNormalData.uniformOscillatoryNormalOperator_differentiableWithinAt
    (F : UniformNormalData G C) (K : ℝ)
    (χ : E → E → ℂ) (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hcχ : HasCompactSupport (Function.uncurry χ))
    (hsχ : tsupport (Function.uncurry χ) ⊆ G.X ×ˢ G.D)
    (hχone : ∀ z ∈ G.X₀ ×ˢ G.D₀, χ z.1 z.2 = 1)
    (g : Lp ℂ ∞ (volume.restrict G.D)) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    DifferentiableWithinAt ℝ (F.uniformOscillatoryNormalOperator K g) (Icc 0 G.ε₀) ε := by
  obtain ⟨t, ht, hs, he⟩ := F.exists_localizedKernelFamily K χ hχ hsχ hχone
  have ht₁ i : ContDiff ℝ 1 (Function.uncurry (t i)) := (ht i).of_le (by simp)
  let T := fun s ↦ compactVectorKernelOperator G.D (t := fun i x u ↦ t i s (x, u))
    (fun i ↦ continuous_kernelSlice (ht₁ i) s)
    (fun i ↦ hasCompactSupport_kernelSlice hcχ (hs i) s)
  have hT s (hsI : s ∈ Icc 0 G.ε₀) : F.uniformOscillatoryOperator K s = T s := by
    ext f i
    have hlocal := compactVectorKernelOperator_ae_integral G.D
      (t := fun i x u ↦ t i s (x, u))
      (fun i ↦ continuous_kernelSlice (ht₁ i) s)
      (fun i ↦ hasCompactSupport_kernelSlice hcχ (hs i) s) f i
    filter_upwards [F.uniformOscillatoryOperator_ae_integral K hsI f i, hlocal]
      with x hx hl
    change (F.uniformOscillatoryOperator K s f) i x = _ at hx
    change (T s f) i x = _ at hl
    rw [hx, hl]
    apply integral_congr_ae
    exact Eventually.of_forall fun u ↦ by
      dsimp only
      rw [he s hsI i (x, u)]
      rfl
  have hd := hasDerivAt_compactVectorKernel_maskedNormal G.D ht₁ hcχ hs g ε
  have heq : EqOn (F.uniformOscillatoryNormalOperator K g)
      (fun s ↦ (T s).comp ((multiplicationOperator g).comp (T s).adjoint)) (Icc 0 G.ε₀) := by
    intro s hsI
    simp only [uniformOscillatoryNormalOperator, hT s hsI]
  exact hd.differentiableAt.differentiableWithinAt.congr heq (heq hε)

end JanetCartan.NormalComparison
