module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer

/-!
# Sobolev algebra for the actual scalar operator estimates

The addition and compact-test derivative facts used to assemble
`app:ch_regular_base:eq:fio-input` from the actual derivative-transfer identity.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ContDiff ENNReal
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Addition of weighted Fourier representatives, used in
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem weightedL2Fourier_add_ae (s : ℝ) (u v : Lp ℂ 2 (volume : Measure E)) :
    weightedL2Fourier s (u + v) =ᵐ[volume]
      fun ξ ↦ weightedL2Fourier s u ξ + weightedL2Fourier s v ξ := by
  have h : 𝓕 (u + v) = 𝓕 u + 𝓕 v := fourier_add u v
  filter_upwards [Lp.coeFn_add (𝓕 u) (𝓕 v)] with ξ hξ
  simp only [weightedL2Fourier, h, hξ, Pi.add_apply, smul_add]

/-- Sobolev membership of the sum in
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.add {s : ℝ} {u v : Lp ℂ 2 (volume : Measure E)}
    (hu : MemFourierSobolev s u) (hv : MemFourierSobolev s v) :
    MemFourierSobolev s (u + v) :=
  (MemLp.add hu hv).ae_eq (weightedL2Fourier_add_ae s u v).symm

/-- Triangle inequality with finite weighted norms, used in the assembly of
`app:ch_regular_base:eq:fio-input`. -/
theorem fourierSobolevNorm_add_le {s : ℝ} {u v : Lp ℂ 2 (volume : Measure E)}
    (hu : MemFourierSobolev s u) (hv : MemFourierSobolev s v) :
    fourierSobolevNorm s (u + v) ≤ fourierSobolevNorm s u + fourierSobolevNorm s v := by
  have h := eLpNorm_add_le (μ := volume) (f := weightedL2Fourier s u) (g := weightedL2Fourier s v) (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  have he := eLpNorm_congr_ae (p := 2) (weightedL2Fourier_add_ae s u v)
  have h := he.trans_le h
  have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩) h
  simpa only [ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top,
    fourierSobolevNorm] using h'

/-- Compact smooth tests have their usual coordinate derivatives as actual L²
distributional derivatives, for `app:ch_regular_base:eq:fio-input`. -/
theorem hasEuclideanL2CoordinateDerivative_toLp
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (i : Fin d) :
    HasEuclideanL2CoordinateDerivative i
      ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u)
      (((contDiff_euclideanCoordinateDerivList hu [i]).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hus [i])).toLp
          (euclideanCoordinateDerivList [i] u)) := by
  let f : 𝓢(E, ℂ) := hus.toSchwartzMap hu
  have hf : (hu.continuous.memLp_of_hasCompactSupport hus).toLp u =
      (f : Lp ℂ 2 (volume : Measure E)) := rfl
  have hdf : (((contDiff_euclideanCoordinateDerivList hu [i]).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordinateDerivList hus [i])).toLp
        (euclideanCoordinateDerivList [i] u)) =
      ((lineDerivOp (EuclideanSpace.single i 1 : E) f) : Lp ℂ 2 (volume : Measure E)) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
      ((contDiff_euclideanCoordinateDerivList hu [i]).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hus [i])),
      (lineDerivOp (EuclideanSpace.single i 1 : E) f).coeFn_toLp 2 volume] with x hx hy
    rw [hx, hy, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  simp only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative, hf, hdf,
    Lp.toTemperedDistribution_toLp_eq]
  simpa only [EuclideanSpace.basisFun_apply] using
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq (μ := volume) f
      (EuclideanSpace.single i 1)

/-- All integer Sobolev memberships of the compact smooth data used in
`app:ch_regular_base:eq:fio-input`, with no extra membership premise. -/
theorem memFourierSobolev_nat_toLp (n : ℕ)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    MemFourierSobolev (n : ℝ) ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    exact (ih u hu hus).of_coordinateDerivatives (by positivity)
      (fun i ↦ ih _ (contDiff_euclideanCoordinateDerivList hu [i])
        (hasCompactSupport_euclideanCoordinateDerivList hus [i]))
      (hasEuclideanL2CoordinateDerivative_toLp u hu hus)

end JanetCartan.Pseudodifferential
