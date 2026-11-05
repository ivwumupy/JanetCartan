module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CutoffSums

/-!
# Exact splitting of the physical graph kernel

The high/low splitting in `app:ch_regular:eq:joint-kernel-phase` follows
from integrability and cutoff linearity. Its inputs are primitive continuity
and compact carriers, with no assumed kernel decomposition identity.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open FourierIntegral
variable {n r : ℕ}
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

/-- The actual physical kernel splits into its high and low graph annuli.
The carriers for the two pieces are constructed from the original primitive
carriers. Consumer: addition of the physical pair estimates in
`app:ch_regular:eq:chain-tail`. -/
theorem regularizedJointKernel_graphCutoff_split (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (j k : ℕ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (c : KernelLimits.RegularizedCarriers A mi (graphCutoff j) (outputCutoff k))
    (x y : Euclidean n) :
    KernelLimits.regularizedJointKernel backward S A mi mo (graphCutoff j) (outputCutoff k) x y =
      KernelLimits.regularizedJointKernel backward S A mi mo
        (highGraphCutoff j) (outputCutoff k) x y +
      KernelLimits.regularizedJointKernel backward S A mi mo
        (lowGraphCutoff j) (outputCutoff k) x y := by
  let χ : Fin 2 → Euclidean n → ℝ := ![highGraphCutoff j, lowGraphCutoff j]
  have hg (i : Fin 2) : Continuous (χ i) := by
    fin_cases i
    · exact (contDiff_highGraphCutoff j).continuous
    · exact (contDiff_lowGraphCutoff j).continuous
  have hcompact (i : Fin 2) : HasCompactSupport (χ i) := by
    fin_cases i
    · exact hasCompactSupport_highGraphCutoff j
    · exact hasCompactSupport_lowGraphCutoff j
  let c' (i : Fin 2) (_ : Unit) :
      KernelLimits.RegularizedCarriers A mi (χ i) (outputCutoff k) :=
    { c with compact_graphCutoff := hcompact i }
  have h := KernelLimits.regularizedJointKernel_finset_cutoffs
    Finset.univ (Finset.univ : Finset Unit) backward S A mi mo χ (fun _ => outputCutoff k)
    hS hA hi ho hg (fun _ => (contDiff_outputCutoff k).continuous) c' x y
  change KernelLimits.regularizedJointKernel backward S A mi mo
    (fun ξ => highGraphCutoff j ξ + lowGraphCutoff j ξ) (outputCutoff k) x y = _
  simpa [χ, Fin.sum_univ_two] using h

end JanetCartan.FiniteChain.Graph.PhysicalShells
