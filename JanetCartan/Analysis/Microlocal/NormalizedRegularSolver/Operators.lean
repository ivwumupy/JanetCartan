module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.AngularMask
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectedConstruction.SourceEquation
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RealPairing

/-!
# The normalized complete physical operators

Add the complementary elliptic operator to the original characteristic
operator, divide by two, and pair with the literal conjugate. The same common
output multiplier is applied to the elliptic branch before addition.
Consumers: the complete fixed inverse and its original angular discrepancy.
Sources: `energy-complete-residual`, `sector-theorem-identity`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks.ActualFamily EllipticComplement FiniteAssembly Realization
open Characteristic.EvolutionIntegral FourierIntegral.LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)

/-- External half-normalization followed by literal physical conjugation.
All original factors remain inside `T` (`real-sector-normalization`). -/
def normalizedPair (T : H →L[ℂ] H) : H →L[ℂ] H :=
  physicalPairedSectorSum {()} (fun _ : Unit ↦ (1/2 : ℂ) • T)

/-- The normalization halves both the original and the whole conjugate
operator (`energy-complete-residual`). -/
theorem normalizedPair_eq (T : H →L[ℂ] H) :
    normalizedPair T = (1/2 : ℂ) • (T + boundedConjugate T) := by
  simp only [normalizedPair, physicalPairedSectorSum, Finset.sum_singleton]
  ext1 u
  change (1/2 : ℂ) • T u + star ((1/2 : ℂ) • T (star u)) =
    (1/2 : ℂ) • (T u + star (T (star u)))
  simp only [star_smul, star_div₀, star_one, star_ofNat, smul_add]

/-- Normalization is additive on entire operators, separating the actual
source from the gain-one residual (`energy-complete-residual`). -/
theorem normalizedPair_add (S T : H →L[ℂ] H) :
    normalizedPair (S+T) = normalizedPair S + normalizedPair T := by
  simp only [normalizedPair, smul_add, physicalPairedSectorSum_add]

/-- The normalized pairing is fixed by physical conjugation
(`real-sector-normalization`). -/
theorem normalizedPair_conjugation (T : H →L[ℂ] H) :
    conjugateOperator (normalizedPair T).toLinearMap = (normalizedPair T).toLinearMap :=
  physicalPairedSectorSum_conjugation _ _

/-- The normalized adjoint retains the literal adjoint of every factor
(`measured-adjoint`). -/
theorem normalizedPair_adjoint (T : H →L[ℂ] H) :
    (normalizedPair T).adjoint = normalizedPair T.adjoint := by
  change (physicalPairedSectorSum {()} (fun _ : Unit ↦ (1/2 : ℂ) • T)).adjoint = _
  rw [ArbitraryAccuracy.ResidualLocalization.physicalPairedSectorSum_adjoint_eq]
  simp only [map_smulₛₗ, map_div₀, map_one, map_ofNat, normalizedPair]

/-- Real compression of the half-pair includes into exactly the same
normalized physical operator (`real-sector-normalization`). -/
theorem inclusion_realCompression_normalizedPair (T : H →L[ℂ] H) (u : RH) :
    l2ComplexInclusion volume (realCompression (normalizedPair T) u) =
      normalizedPair T (l2ComplexInclusion volume u) :=
  inclusion_realCompression_physicalPairedSectorSum _ _ _

variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
variable (Q : E → Fin (d+1) → Mat) (B : E → Mat)
variable (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)

/-- The corrected solver pairs the actual characteristic and elliptic sum
with one external half on each branch (`sector-theorem-solution`). -/
def pairedSolver (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) : H →L[ℂ] H :=
  normalizedPair (selectedFiniteDirectSolver f L Q B output ho hob retarded +
    (sourceCutMultiplier output ho hob).comp (ellipticSolver f hK L Q))

/-- The corrected source retains the original input and both output masks,
and the SAME final `2*L` collar (`sector-theorem-identity`). -/
def pairedSource (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) : H →L[ℂ] H :=
  normalizedPair ((sourceCutMultiplier output ho hob).comp
    (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L))

/-- The complete analytic residual adds the actual global elliptic residual
to all three original characteristic terms before normalization. Its full
zeroth-order coefficient is `B` (`energy-complete-residual`). -/
def pairedResidual (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (retardedPW₁ : H →L[ℂ] H) : H →L[ℂ] H :=
  normalizedPair (selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁ +
    (sourceCutMultiplier output ho hob).comp (ellipticResidual f hK L Q B))

/-- The actual real normalized solver (`sector-theorem-solution`). -/
def realSolver (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : H →L[ℂ] H) : RH →L[ℝ] RH :=
  realCompression (pairedSolver f hK L Q B output ho hob retarded)

/-- The actual normalized real source, for `Bobs = Anew-I`
(`sector-theorem-identity`, `resolved-angular-tail`). -/
def realSource (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) : RH →L[ℝ] RH :=
  realCompression (pairedSource f hK L output ho hob)

/-- The real gain-one residual, with the angular defect excluded
(`sector-theorem-residual`). -/
def realResidual (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (retardedPW₁ : H →L[ℂ] H) : RH →L[ℝ] RH :=
  realCompression (pairedResidual f hK L Q B output ho hob W₁ retardedPW₁)

/-- The complete real error subtracts one identity after normalization
(`prop:complete-residual`). -/
def realCompleteError (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (retardedPW₁ : H →L[ℂ] H) : RH →L[ℝ] RH :=
  (realSource f hK L output ho hob - 1) +
    realResidual f hK L Q B output ho hob W₁ retardedPW₁

/-- The normalized complete error keeps the angular defect and analytic
residual distinct and subtracts the identity exactly once (`prop:complete-residual`). -/
theorem realCompleteError_identity (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (retardedPW₁ : H →L[ℂ] H) :
    realSource f hK L output ho hob + realResidual f hK L Q B output ho hob W₁ retardedPW₁ =
      1 + realCompleteError f hK L Q B output ho hob W₁ retardedPW₁ := by
  unfold realCompleteError
  abel

end JanetCartan.RegularSector.NormalizedSolver
