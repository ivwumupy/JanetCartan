module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.RetardedRealization.Sobolev.Coordinates

/-!
# One coordinate tuple for the actual observed core

These standard finite bases and the Cartesian split at index zero instantiate
only the universally quantified coordinate inputs of the retained core. No
source, reference, inverse or history is selected
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
open MeasureTheory FiniteChain.Graph FiniteChain.Graph.KernelLimits
open FourierIntegral.RetardedRealization

/-- The fixed joint-variable basis in the observed-core application. -/
def eT (d : ℕ) : Module.Basis
    (Fin (Module.finrank ℝ (JointVariables (Euclidean (d+1))))) ℝ
    (JointVariables (Euclidean (d+1))) :=
  Module.finBasis ℝ (JointVariables (Euclidean (d+1)))

/-- The fixed time/joint-variable basis in the observed-core application. -/
def eI (d : ℕ) : Module.Basis
    (Fin (Module.finrank ℝ (ℝ × JointVariables (Euclidean (d+1))))) ℝ
    (ℝ × JointVariables (Euclidean (d+1))) :=
  Module.finBasis ℝ (ℝ × JointVariables (Euclidean (d+1)))

/-- The standard physical input orthonormal basis. -/
def eu (d : ℕ) : OrthonormalBasis (Fin (d+1)) ℝ (Euclidean (d+1)) :=
  EuclideanSpace.basisFun (Fin (d+1)) ℝ

/-- Reuse exactly the same standard basis for the physical output. -/
def ez (d : ℕ) : OrthonormalBasis (Fin (d+1)) ℝ (Euclidean (d+1)) := eu d

/-- The fixed Cartesian graph coordinate split, with no additional choice. -/
def Jcoord (d : ℕ) : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d+1) :=
  retardedCartesianCoordinates (0 : Fin (d+1))

/-- The needed measure identity includes the graph's input swap. -/
theorem measurePreserving_Jcoord (d : ℕ) :
    MeasurePreserving (graphInputCoordinates (Jcoord d)) volume volume :=
  measurePreserving_retardedCartesianCoordinates (0 : Fin (d+1))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
