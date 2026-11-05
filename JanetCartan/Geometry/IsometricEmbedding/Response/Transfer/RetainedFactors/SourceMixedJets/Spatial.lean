module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness

/-!
# Spatial derivatives of the original source without loss of order

For `app:ch_response:eq:direct-envelope-profile`, identify the Fourier-constructed
weak jet with the classical jet of the exact smooth representative. This is the
spatial input to the mixed source bound consumed by both integrated envelopes.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
open Pseudodifferential LocalSobolev

variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The actual spatial jet is L² with precisely its own Fourier order. The
constant retains the physical `2 * π` convention of `app:not:fourier` and
supplies the mixed datum estimate in `app:ch_response:eq:direct-envelope-profile`.
-/
theorem spatialJet_memLp_norm_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hm : MemLp f 2 volume) (s : ℕ)
    (hs : MemVectorFourierSobolev (s : ℝ) (hm.toLp f)) :
    ∃ hj : MemLp (iteratedFDeriv ℝ s f) 2 volume,
      ‖hj.toLp (iteratedFDeriv ℝ s f)‖ ≤
        (((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) ^ s *
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) := by
  obtain ⟨J, hw, hJ, hb⟩ := exists_vector_weakJet_nat_explicit n r s (hm.toLp f) hs
  have he : J s =ᵐ[volume] iteratedFDeriv ℝ s f := by
    simpa only [Measure.restrict_univ] using hw.ae_eq
      (Mollification.hasWeakJetOn_of_contDiff volume (hf.of_le (by simp)) univ)
      isOpen_univ (by simpa using hm.coeFn_toLp) s le_rfl
  have hj := (hJ s le_rfl).ae_eq he
  refine ⟨hj, ?_⟩
  rw [Lp.norm_toLp, ← eLpNorm_congr_ae he]
  exact (Finset.single_le_sum (f := fun j ↦ (eLpNorm (J j) 2 volume).toReal)
    (fun j _ ↦ ENNReal.toReal_nonneg)
    (Finset.mem_range.mpr (Nat.lt_succ_self s))).trans hb

end JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
