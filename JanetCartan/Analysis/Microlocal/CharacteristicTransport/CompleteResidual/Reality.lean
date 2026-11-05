module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.WeakEquation
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Sector

/-!
# Physical reality pairing for the direct solver

The solver of `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`,
solves an equation for the real physical operator P. Its reality pairing is
S + cSc. This module constructs that pairing of a finite family of bounded
sectors and applies the existing real compression, retaining Euclidean
Lebesgue measure and the operators' original masks. The sectors still have
to be constructed by the complete-residual assembly.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped JanetCartan.RegularSector.Realization

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open RegularSector RegularSector.Realization

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "C2" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
local notation "R2" => Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E)

/-- The physical test action commutes with conjugation because every
coefficient is real, including the zeroth-order coefficient
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalTestAction_conj
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ) (u : E → Fin q → ℂ)
    (φ : E → ℝ) (i : Fin q) :
    physicalTestAction A B (fun x j ↦ star (u x j)) φ i =
      star (physicalTestAction A B u φ i) := by
  simp [physicalTestAction, ← integral_conj]

/-- The direct physical finite sum, paired with the conjugate of the whole
sum. Each supplied sector already contains both original physical masks
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalPairedSectorSum {ι : Type*} (s : Finset ι) (S : ι → C2 →L[ℂ] C2) : C2 →L[ℂ] C2 :=
  (∑ j ∈ s, S j) + boundedConjugate (∑ j ∈ s, S j)

/-- The plus pairing is conjugation fixed, with no additional scalar
normalization (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalPairedSectorSum_conjugation {ι : Type*}
    (s : Finset ι) (S : ι → C2 →L[ℂ] C2) :
    conjugateOperator (physicalPairedSectorSum s S).toLinearMap =
      (physicalPairedSectorSum s S).toLinearMap := by
  change conjugateOperator ((∑ j ∈ s, S j).toLinearMap +
      conjugateOperator (∑ j ∈ s, S j).toLinearMap) =
    (∑ j ∈ s, S j).toLinearMap + conjugateOperator (∑ j ∈ s, S j).toLinearMap
  rw [conjugateOperator_add, conjugateOperator_conjugateOperator, add_comm]

/-- Real compression realizes the same physical plus-paired solver on real
inputs. No anti-real sector solver is inserted
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem inclusion_realCompression_physicalPairedSectorSum {ι : Type*}
    (s : Finset ι) (S : ι → C2 →L[ℂ] C2) (f : R2) :
    l2ComplexInclusion volume (realCompression (physicalPairedSectorSum s S) f) =
      physicalPairedSectorSum s S (l2ComplexInclusion volume f) :=
  inclusion_realCompression _ (physicalPairedSectorSum_conjugation s S) f

/-- The real solver has exactly the original paired complex extension on
both quadratures (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalPairedSectorSum_complex_extension {ι : Type*}
    (s : Finset ι) (S : ι → C2 →L[ℂ] C2) (z : C2) :
    physicalPairedSectorSum s S z =
      l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s S) (l2RealPart volume z)) +
      Complex.I • l2ComplexInclusion volume
        (realCompression (physicalPairedSectorSum s S) (l2RealPart volume (-Complex.I • z))) :=
  realCompression_complex_extension _ (physicalPairedSectorSum_conjugation s S) z

/-- The adjoint is the literal adjoint of the plus pairing. The entire
conjugate factor remains intact, so adjunction cannot silently discard or
reorder either physical mask
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem physicalPairedSectorSum_adjoint {ι : Type*}
    (s : Finset ι) (S : ι → C2 →L[ℂ] C2) :
    (physicalPairedSectorSum s S).adjoint =
      (∑ j ∈ s, (S j).adjoint) + (boundedConjugate (∑ j ∈ s, S j)).adjoint := by
  simp [physicalPairedSectorSum]

end JanetCartan.CharacteristicTransport.CompleteResidual
