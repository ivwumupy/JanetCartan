module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.Approximation
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.UniformLimit

/-!
# Finite-order weak Sobolev regularity

For `app:not:fourier` and `app:ch_regular:thm:exact-correction`, mollification
and the limit argument combine with the smooth jet estimate to give a `Cᵏ`
representative of any function with weak L² derivatives through order `k + n + 1`
on Euclidean space. The representative theorem assumes only the weak jet and
its L² integrability.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The approximation and limit steps for finite-order regularity in
`app:not:fourier`, used in `app:ch_regular:thm:exact-correction`. The input
jet is genuinely weak. The smooth Sobolev estimate is a separate premise;
it must be discharged to obtain the unconditional representative theorem. -/
theorem exists_contDiff_ae_eq_of_smooth_estimate {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {k m : ℕ}
    (hw : Mollification.HasWeakJetOn μ f J univ m) (hf : MemLp f 2 μ)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 μ)
    (C : ℝ)
    (hest : ∀ v : E → F, ContDiff ℝ ∞ v →
      (∀ l ≤ m, MemLp (iteratedFDeriv ℝ l v) 2 μ) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j v x‖ ≤
        C * ∑ l ∈ Finset.range (m + 1), (eLpNorm (iteratedFDeriv ℝ l v) 2 μ).toReal) :
    ∃ g : E → F, ContDiff ℝ k g ∧ g =ᵐ[μ] f := by
  obtain ⟨v, hv, _, hvJ, hvf, hvconv⟩ := exists_smooth_approximation_weakJet μ hw hf hJ
  have hC := uniformCauchySeqOn_iteratedFDeriv_of_smooth_estimate hv hvJ hvconv C hest
  obtain ⟨g, hg, hvg⟩ := exists_contDiff_of_uniformCauchySeqOn_iteratedFDeriv hv hC
  exact ⟨g, hg, ae_eq_of_tendsto_eLpNorm_of_tendsto hvf hvg.tendsto_at⟩

end General

/-- Finite-order Sobolev regularity for `app:not:fourier`, used in the smoothness
argument of `app:ch_regular:thm:exact-correction`: a function with weak L² jets
through order `k + n + 1` has a `Cᵏ` representative. The smooth jet estimate is
discharged internally; no classical regularity of the given function is assumed. -/
theorem exists_contDiff_ae_eq_of_weakJet {n k : ℕ} (_hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [×j]→L[ℝ] F}
    (hw : Mollification.HasWeakJetOn volume f J univ (k + n + 1))
    (hf : MemLp f 2 volume) (hJ : ∀ j ≤ k + n + 1, MemLp (J j) 2 volume) :
    ∃ g : EuclideanSpace ℝ (Fin n) → F, ContDiff ℝ k g ∧ g =ᵐ[volume] f := by
  obtain ⟨C, _, hest⟩ := exists_smooth_jet_estimate (F := F) n k
  exact exists_contDiff_ae_eq_of_smooth_estimate volume hw hf hJ C hest

end JanetCartan.LocalSobolev.FiniteOrder
