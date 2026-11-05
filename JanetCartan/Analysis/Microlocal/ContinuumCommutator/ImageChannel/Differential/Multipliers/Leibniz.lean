module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.Extension
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.CoefficientJets

/-!
# Full Sobolev Leibniz identities for image coefficients

For `app:ch_background:eq:bg-commutator`, differentiation hits the actual
coefficient or the datum, with the original coefficient in the latter branch.
Density proves the identity on all `H^(s+1)` data at every level.
-/

public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace ContinuumRow

variable {n : ℕ}

private theorem ofSmooth_add (s : ℕ) (f g : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    ofSmooth s (f + g) ⟨hf.1.add hg.1, hf.2.add hg.2⟩ =
      ofSmooth s f hf + ofSmooth s g hg := by
  apply toL2_injective s
  rw [map_add]
  apply Lp.ext
  exact (toL2_ofSmooth_ae s _ _).trans
    (((toL2_ofSmooth_ae s f hf).add (toL2_ofSmooth_ae s g hg)).symm.trans
      (Lp.coeFn_add _ _).symm)

/-- The complete coordinate Leibniz identity for the actual scalar multiplier
at every Sobolev level and on every datum (`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_cutoffSobolev (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (s : ℕ) (a : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s a (cutoffSobolev q hq (s + 1) u) =
      cutoffSobolev (coordinateCoefficient q hq a) (hq.coordinateDeriv a) s
        (inclusion (Nat.le_succ s) u) +
      cutoffSobolev q hq s (coordinateDerivative s a u) := by
  refine (denseRange_ofSmooth (n := n) (F := Euclidean n) (s + 1)).induction_on u
    (isClosed_eq ((coordinateDerivative s a).continuous.comp (cutoffSobolev q hq (s+1)).continuous)
      (((cutoffSobolev (coordinateCoefficient q hq a) (hq.coordinateDeriv a) s).continuous.comp
        (inclusion (Nat.le_succ s)).continuous).add
        ((cutoffSobolev q hq s).continuous.comp (coordinateDerivative s a).continuous))) ?_
  rintro ⟨f, hf⟩
  simp only [cutoffSobolev_ofSmooth, coordinateDerivative_ofSmooth, multiplier_inclusion_ofSmooth]
  rw [cutoffSobolev_ofSmooth (coordinateCoefficient q hq a) (hq.coordinateDeriv a) s f hf]
  simpa only [Exterior.coordinateDeriv_smul hq hf, Pi.add_def,
    coordinateCoefficient, ContinuousMap.coe_mk] using
    ofSmooth_add s _ _ (Exterior.smooth_smul (hq.coordinateDeriv a) hf)
      (Exterior.smooth_smul hq (hf.coordinateDeriv a))

/-- The constant matrix unit acts on the existing Sobolev space through the
shared, proved value-map construction (`app:ch_background:eq:bg-commutator`). -/
@[expose] def matrixUnitSobolev (s : ℕ) (i k : Fin n) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  HigherRegularity.RealCommutator.sobolevMap (reducedMatrixUnit i k) s

/-- The constant matrix unit has its original pointwise L² action
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_matrixUnitSobolev (s : ℕ) (i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (matrixUnitSobolev s i k u) =
      (reducedMatrixUnit i k).compLpL 2 volume (toL2 s u) := rfl

/-- Matrix-unit actions agree with their literal smooth representatives
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem matrixUnitSobolev_ofSmooth (s : ℕ) (i k : Fin n)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    matrixUnitSobolev s i k (ofSmooth s f hf) =
      ofSmooth s (fun x ↦ reducedMatrixUnit i k (f x)) (hf.comp_clm (reducedMatrixUnit i k)) :=
  HigherRegularity.RealCommutator.sobolevMap_ofSmooth _ _ _ _

/-- Matrix units are contractions at every Sobolev order, with no coefficient
cost (`app:ch_background:eq:bg-commutator`). -/
theorem norm_matrixUnitSobolev_le (s : ℕ) (i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) : ‖matrixUnitSobolev s i k u‖ ≤ ‖u‖ := by
  exact (HigherRegularity.RealCommutator.norm_sobolevMap_le _ s u).trans
    (mul_le_of_le_one_left (norm_nonneg _) (reducedMatrixUnit_norm_le i k))

/-- Differentiation commutes with a constant matrix unit on all Sobolev data
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_matrixUnitSobolev (s : ℕ) (a i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s a (matrixUnitSobolev (s + 1) i k u) =
      matrixUnitSobolev s i k (coordinateDerivative s a u) := by
  refine (denseRange_ofSmooth (n := n) (F := Euclidean n) (s + 1)).induction_on u
    (isClosed_eq ((coordinateDerivative s a).continuous.comp (matrixUnitSobolev (s+1) i k).continuous)
      ((matrixUnitSobolev s i k).continuous.comp (coordinateDerivative s a).continuous)) ?_
  rintro ⟨f, hf⟩
  simp only [matrixUnitSobolev_ofSmooth, coordinateDerivative_ofSmooth]
  simp only [periodicCoordinateDeriv_comp_clm hf (reducedMatrixUnit i k) a]

/-- The Sobolev realization of the existing reduced matrix-coefficient
multiplier (`app:ch_background:eq:bg-commutator`). -/
@[expose] def reducedCoefficientSobolev (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (i k : Fin n) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  matrixUnitSobolev s i k ∘L cutoffSobolev q hq s

/-- The constructed matrix action restricts the exact existing L² operator
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_reducedCoefficientSobolev (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (s : ℕ) (i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (reducedCoefficientSobolev q hq s i k u) =
      reducedCoefficientMultiplier q i k (toL2 s u) := by
  simp only [reducedCoefficientSobolev, ContinuousLinearMap.comp_apply,
    toL2_matrixUnitSobolev, toL2_cutoffSobolev, reducedCoefficientMultiplier]

/-- Literal smooth matrix-coefficient action, including the selected coordinate
and row of the matrix unit (`app:ch_background:eq:bg-commutator`). -/
theorem reducedCoefficientSobolev_ofSmooth (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (s : ℕ) (i k : Fin n)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    reducedCoefficientSobolev q hq s i k (ofSmooth s f hf) =
      ofSmooth s (fun x ↦ reducedMatrixUnit i k (q x • f x))
        ((Exterior.smooth_smul hq hf).comp_clm (reducedMatrixUnit i k)) := by
  simp only [reducedCoefficientSobolev, ContinuousLinearMap.comp_apply,
    cutoffSobolev_ofSmooth, matrixUnitSobolev_ofSmooth]

/-- Full coordinate Leibniz identity for the actual matrix coefficient; the
datum-derivative term uses the unchanged coefficient
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivative_reducedCoefficientSobolev (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (s : ℕ) (a i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) (s + 1)) :
    coordinateDerivative s a (reducedCoefficientSobolev q hq (s + 1) i k u) =
      reducedCoefficientSobolev (coordinateCoefficient q hq a) (hq.coordinateDeriv a) s i k
        (inclusion (Nat.le_succ s) u) +
      reducedCoefficientSobolev q hq s i k (coordinateDerivative s a u) := by
  simp only [reducedCoefficientSobolev, ContinuousLinearMap.comp_apply,
    coordinateDerivative_matrixUnitSobolev, coordinateDerivative_cutoffSobolev, map_add]

/-- Matrix coefficients obey the same finite jet/lower-Sobolev bound with no
additional matrix-unit constant (`app:ch_background:eq:bg-commutator`). -/
theorem norm_reducedCoefficientSobolev_le (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (i k : Fin n) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖reducedCoefficientSobolev q hq s i k u‖ ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift q) *
          (periodicSobolevScale n (Euclidean n)).gradeNorm (s-j) (toL2 s u) :=
  (norm_matrixUnitSobolev_le s i k _).trans (norm_cutoffSobolev_le_gradeNorm q hq s u)

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
