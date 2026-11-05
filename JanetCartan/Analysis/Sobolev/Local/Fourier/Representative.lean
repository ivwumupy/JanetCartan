module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakLimits

/-!
# Normalizing the representative of a whole-space weak extension

The real/complex restriction comparison in `app:not:fourier` projects a complex
extension to real values. This leaf restores the specified representative while
preserving every L² jet class and its norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function

namespace JanetCartan.LocalSobolev.SobolevExtension

variable {n s : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))} {v : LocalL2 U F}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Change to an a.e. equal whole-space representative, normalizing exactly
the order-zero jet and retaining the positive-order fields (`app:not:fourier`). -/
def withRepresentative (e : SobolevExtension U s v) (f : E → F)
    (hf : e.toFun =ᵐ[volume] f) : SobolevExtension U s v := by
  have hz : e.jet 0 =ᵐ[volume] iteratedFDeriv ℝ 0 f := by
    filter_upwards [hf] with x hx
    rw [e.weakJet.1]
    ext w
    simp only [iteratedFDeriv_zero_apply, hx]
  have hJ := fun j ↦ Mollification.normalizeWeakJet_ae (U := univ) (f := f) (J := e.jet)
    (by simpa only [Measure.restrict_univ] using hz) j
  refine ⟨f, Mollification.normalizeWeakJet f e.jet,
    e.weakJet.congr_ae rfl (fun j _ ↦ hJ j), e.memLp_fun.ae_eq hf, ?_, ?_⟩
  · intro j hj
    exact (e.memLp_jet j hj).ae_eq (by
      simpa only [Measure.restrict_univ] using hJ j)
  · have hfU : e.toFun =ᵐ[volume.restrict U] f := ae_restrict_of_ae hf
    exact hfU.symm.trans e.restrict_eq

/-- Restoring the specified representative leaves the auxiliary whole-space
Sobolev norm unchanged (`app:not:fourier`). -/
theorem jetNorm_withRepresentative (e : SobolevExtension U s v) (f : E → F)
    (hf : e.toFun =ᵐ[volume] f) : (e.withRepresentative f hf).jetNorm = e.jetNorm := by
  unfold jetNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply eLpNorm_congr_ae
  cases j with
  | zero =>
    filter_upwards [hf] with x hx
    change iteratedFDeriv ℝ 0 f x = e.jet 0 x
    rw [e.weakJet.1]
    ext w
    simp only [iteratedFDeriv_zero_apply, hx]
  | succ j => rfl

end JanetCartan.LocalSobolev.SobolevExtension
