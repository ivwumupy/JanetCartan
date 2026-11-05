module

public import JanetCartan.Iteration.PhysicalPrimary.SolverStepTemplate
public import JanetCartan.Iteration.PhysicalEllipticWords.PairedCharts
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicPaired
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.Operators
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.ActualOperators
public meta import Lean

/-!
# The same normalized solver in the finite-word step

Keep the literal original common-chart retarded operators, the full algebraic
symbol at order zero with its `1/i` INSIDE the normalized pair, and the original
output-cut elliptic solver. The only finite sum is over the original fixed
mask-family centers, not the sampling family.

The structural assembly is for the `hsolverStep` input of
`actual_finite_residual_word_reserved_bounds_of_one_step`
(`app:ch_response:eq:response-graded-reduced`, `energy-complete-residual`).
The complete producer below DIRECTLY applies all three analytic constructors;
no solver-response bound is assumed. Its fixed primitive certificate prefix
still requires the original native-data realization in the physical-primary
parent; this module does not claim that parent or Main from a conditional sum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalPrimary
open PhysicalEllipticWords Pseudodifferential FourierIntegral FourierIntegral.LowBounds
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open FixedDomainInverse.FiniteResidualEnvelopes FixedDomainInverse.FiniteResidualWordProfiles
open RegularSector RegularSector.Realization RegularSector.NormalizedSolver
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteEvolution
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.Characteristic.PdoRealization RegularSector.FiniteResidual.FiniteIdentity
open RegularSector.EllipticComplement RegularSector.Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual

variable {d : ℕ} {I J : Type}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Fibre" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp Fibre 2 (volume : Measure E)

private theorem solver_reserved_bounds_finite_sum [Fintype J]
    {V : Set Par} (hV : IsOpen V) (g : J → I → Par → H)
    (A K : I → ℝ) (reserve : ℕ)
    (hg : ∀ j, ReservedLetterBounds V (g j) A K reserve) :
    ReservedLetterBounds V (fun i c ↦ ∑ j, g j i c) A K reserve := by
  classical
  refine ⟨fun i ↦ ContDiffOn.sum (fun j _ ↦ (hg j).1 i), ?_⟩
  have hb := ordered_reserved_bounds_finite_sum hV g (fun j i ↦ (hg j).1 i)
    A K reserve (by
      intro j ps hps s
      obtain ⟨C,hC,hb⟩ := (hg j).2 ps hps s
      exact ⟨C,hC,fun q ↦ hb q.1 q.2 q.2.property⟩)
  intro ps hps s
  obtain ⟨C,hC,hb⟩ := hb ps hps s
  exact ⟨C,hC,fun i c hc ↦ hb (i,⟨c,hc⟩)⟩

private theorem solver_normalizedPair_sum [Fintype J] (T : J → H →L[ℂ] H) :
    normalizedPair (∑ j, T j) = ∑ j, normalizedPair (T j) := by
  classical
  ext1 u
  simp only [normalizedPair_eq, smul_apply,
    add_apply, _root_.sum_apply]
  change (1/2 : ℂ) • ((∑ j, T j u) + star ((∑ j, T j) (star u))) =
    ∑ j, (1/2 : ℂ) • (T j u + star (T j (star u)))
  simp only [_root_.sum_apply, star_sum, Finset.smul_sum, smul_add, Finset.sum_add_distrib]

private theorem solver_normalizedPair_finitePhysicalOperator [Fintype J]
    (index : J → Fin (d+1)) (T : J → H →L[ℂ] H) :
    normalizedPair (finitePhysicalOperator index T) =
      ∑ j, FiniteEvolution.physicalOperator (index j) (normalizedPair (T j)) := by
  classical
  rw [finitePhysicalOperator, solver_normalizedPair_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [one_smul] using
    (physicalOperator_normalized_scalar_pair (index j) (T j) (1 : ℂ)).symm

private theorem solver_physicalOperator_add (index : Fin (d+1))
    (U V : H →L[ℂ] H) :
    FiniteEvolution.physicalOperator index (U+V) =
      FiniteEvolution.physicalOperator index U + FiniteEvolution.physicalOperator index V := by
  ext1 u
  simp only [FiniteEvolution.physicalOperator_apply, add_apply, map_add]

/-- Decompose the SAME original normalized solver into its full physical
retarded and algebraic chart pairs and its original output-cut elliptic pair.
The native graph-normal certificates prove the operator identity; no replacement
operator or identity hypothesis is introduced. The complex `1/i` stays inside
the whole conjugate pair (`energy-complete-residual`). -/
theorem pairedSolver_eq_normalized_physical_sum
    {Ω : Set E} {x : E} {RQ Mcap : ℝ} {K₀ : Set E}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (hK₀ : IsCompact K₀)
    (L : ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (Rnormal Cnormal : f.centers → ℝ)
    (hcertificate : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 0)) (Rnormal p) (Cnormal p))
    (T : f.centers → H →L[ℂ] H) :
    pairedSolver f hK₀ L Q B output ho hob
      ((sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))) =
      (∑ p, (FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair (selectedCommonChartRetarded f p output ho hob hib (T p))) +
        FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair ((1/Complex.I) • maskedPhysicalPDO
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*L) Q B 0))))) +
      normalizedPair ((sourceCutMultiplier output ho hob).comp (ellipticSolver f hK₀ L Q)) := by
  let ell : H →L[ℂ] H :=
    (sourceCutMultiplier output ho hob).comp (ellipticSolver f hK₀ L Q)
  let ret : H →L[ℂ] H := (sourceCutMultiplier output ho hob).comp
    ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
      (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
  let U : f.centers → H →L[ℂ] H :=
    fun p ↦ selectedCommonChartSolver f p L Q B output ho hob hib (T p)
  have hd : selectedFiniteDirectSolver f L Q B output ho hob ret =
      finitePhysicalOperator (fun p ↦ (f.chart p).index) U :=
    selectedFiniteDirectSolver_eq_commonChartSum f L Q B output ho hob hib hsupp
      Rnormal Cnormal hcertificate T
  have hs : normalizedPair (finitePhysicalOperator (fun p ↦ (f.chart p).index) U) =
      ∑ p, (FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair (selectedCommonChartRetarded f p output ho hob hib (T p))) +
        FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair ((1/Complex.I) • maskedPhysicalPDO
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*L) Q B 0)))) := by
    refine (solver_normalizedPair_finitePhysicalOperator
      (fun p : f.centers ↦ (f.chart p).index) U).trans ?_
    apply Finset.sum_congr rfl
    intro p _
    let Tr := selectedCommonChartRetarded f p output ho hob hib (T p)
    let Ta := (1/Complex.I) • maskedPhysicalPDO
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedAlgebraicSymbol f p (2*L) Q B 0)
    exact (congrArg (FiniteEvolution.physicalOperator (f.chart p).index)
      (normalizedPair_add Tr Ta)).trans
        (solver_physicalOperator_add (f.chart p).index (normalizedPair Tr) (normalizedPair Ta))
  exact (normalizedPair_add (selectedFiniteDirectSolver f L Q B output ho hob ret) ell).trans
    ((congrArg (fun U ↦ normalizedPair U + normalizedPair ell) hd).trans
      (congrArg (fun U ↦ U + normalizedPair ell) hs))

private theorem solver_demodulated_sum_apply [Fintype J]
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (U W : J → H →L[ℂ] H) (T : H →L[ℂ] H) (u : H) :
    demodulatedL2Operator lam φ hφ ((∑ j, (U j+W j))+T) u =
      (∑ j, (demodulatedL2Operator lam φ hφ (U j) u +
        demodulatedL2Operator lam φ hφ (W j) u)) +
      demodulatedL2Operator lam φ hφ T u := by
  simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply, add_apply,
    _root_.sum_apply, map_add, map_sum]

/-- Conditional assembly ONLY: the three response premises must be supplied
by the actual native retarded constructor at order zero, the actual paired
algebraic constructor at order zero, and the actual elliptic constructor with
`residual=false`. This concludes the SAME unmeasured normalized solver, not a
recut substitute. Its later right input cut is handled by the proved original
source plateau. Only constants over the original finite centers are summed
(`app:ch_response:eq:response-graded-reduced`, `energy-complete-residual`). -/
theorem pairedSolver_reserved_bounds_of_actual_letters
    {Ω : Set E} {x : E} {RQ Mcap : ℝ} {K₀ : Set E}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (hK₀ : IsCompact K₀)
    (threshold : ℝ)
    (Q : I → E → Fin (d+1) → MetricTensor (d+1)) (B : I → E → MetricTensor (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (Rnormal Cnormal : I → f.centers → ℝ)
    (hcertificate : ∀ i p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 0)) (Rnormal i p) (Cnormal i p))
    (T : I → f.centers → H →L[ℂ] H)
    {V : Set Par} (hV : IsOpen V) (lam A K : I → ℝ) (reserve : ℕ)
    (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i)
    (φ : I → E → Par → ℝ) (hφ : ∀ i c, Continuous (fun y ↦ φ i y c))
    (u : I → Par → H)
    (hret : ∀ p, ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair (selectedCommonChartRetarded f p output ho hob hib (T i p))))
        (u i c)) A K reserve)
    (halg : ∀ p, ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair ((1/Complex.I) • maskedPhysicalPDO
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 0)))) (u i c))
      (fun i ↦ lam i ^ (-1 : ℤ) * A i) K reserve)
    (hell : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (normalizedPair ((sourceCutMultiplier output ho hob).comp
          (ellipticSolver f hK₀ threshold (Q i)))) (u i c))
      (fun i ↦ lam i ^ (-1 : ℤ) * A i) K reserve) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (pairedSolver f hK₀ threshold (Q i) (B i) output ho hob
          ((sourceCutMultiplier output ho hob).comp
            ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
              (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))))
        (u i c)) A K reserve := by
  let Tr : f.centers → I → H →L[ℂ] H := fun p i ↦
    FiniteEvolution.physicalOperator (f.chart p).index
      (normalizedPair (selectedCommonChartRetarded f p output ho hob hib (T i p)))
  let Ta : f.centers → I → H →L[ℂ] H := fun p i ↦
    FiniteEvolution.physicalOperator (f.chart p).index
      (normalizedPair ((1/Complex.I) • maskedPhysicalPDO
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 0)))
  let Te : I → H →L[ℂ] H := fun i ↦ normalizedPair
    ((sourceCutMultiplier output ho hob).comp (ellipticSolver f hK₀ threshold (Q i)))
  let gr : f.centers → I → Par → H := fun p i c ↦
    demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (Tr p i) (u i c)
  let ga : f.centers → I → Par → H := fun p i c ↦
    demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (Ta p i) (u i c)
  let ge : I → Par → H := fun i c ↦
    demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (Te i) (u i c)
  have hsum : ReservedLetterBounds V
      (fun i c ↦ ∑ p, (gr p i c + ga p i c)) A K reserve :=
    solver_reserved_bounds_finite_sum hV (fun p i c ↦ gr p i c + ga p i c) A K reserve
      (fun p ↦ (hret p).add hV ((halg p).discard_inverse_frequency hlam hA hK))
  have he : ReservedLetterBounds V ge A K reserve := hell.discard_inverse_frequency hlam hA hK
  have hall := hsum.add hV he
  have hsame : (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
      (pairedSolver f hK₀ threshold (Q i) (B i) output ho hob
        ((sourceCutMultiplier output ho hob).comp
          ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (T i)).comp
            (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib)))) (u i c)) =
    (fun i c ↦ (∑ p, (gr p i c + ga p i c)) + ge i c) := by
    funext i c
    have hid := pairedSolver_eq_normalized_physical_sum f hK₀ threshold (Q i) (B i)
      output ho hob hib hsupp (Rnormal i) (Cnormal i) (hcertificate i) (T i)
    exact (congrArg (fun W ↦ demodulatedL2Operator (lam i)
      (fun y ↦ φ i y c) (hφ i c) W (u i c)) hid).trans
        (solver_demodulated_sum_apply (lam i) (fun y ↦ φ i y c) (hφ i c)
          (fun p ↦ Tr p i) (fun p ↦ Ta p i) (Te i) (u i c))
  exact Eq.mpr (congrArg (fun g ↦ ReservedLetterBounds V g A K reserve) hsame) hall

open FourierIntegral.FullLowBounds ResponseTransfer.FullEllipticApplication
open ResponseTransfer.DirectEvolution ResponseTransfer.DirectEvolution.AnnularComplement
open RegularSector.Characteristic AmplitudeBound

variable {ι : Type} [Fintype ι]
local notation "CW" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

/-- The elliptic field of `pairedSolver_reserved_bounds_of_actual_letters`
is PRODUCED from the original coefficient, phase and source profiles. This is
the actual inverse (`false,false`), with its original common output and both
normalized halves; there is no response-bound premise
(`app:ch_response:eq:response-graded-reduced`). -/
theorem elliptic_paired_solver_reserved_bounds
    {Ω : Set E} {x : E} {RQ Mcap : ℝ} {K₀ : Set E}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (hK₀ : IsCompact K₀)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ CW)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall (cubeStress (d+1)) f.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ Mcap)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ Mcap)
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*f.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hband : ∀ i c, c ∈ V → ∀ y ∈ ball x (3*f.physicalRadius),
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*f.physicalRadius))
    (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (normalizedPair ((sourceCutMultiplier output ho.continuous hob).comp
          (ellipticSolver f hK₀ threshold (Q i))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
  simpa only [ReservedLetterBounds, annularGraphOrientation, Bool.false_eq_true,
    ↓reduceIte, mul_assoc] using
    (actual_elliptic_normalized_reserved_ordered_bounds f hK₀ hΩ hball output ho hoc hos hob
      threshold ht basis hV hKpar hVK Rsource Rstar hRstar AQ AB Aphase hAQ hAB hAphase
      hν hν1 ha₀ hB₀ lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQl hBl hQp hBp
      φ hφ hcap hφjets hband S hS hSU a ha has Csource hfourier false false).2

open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.AlgebraicChart

/-- Produce the algebraic field of `pairedSolver_reserved_bounds_of_actual_letters`
from the original primitive symbol/phase/source profiles. The SAME physical datum
is pulled back and pushed forward by the original chart isometry. The full order
zero symbol and its complex `1/i` remain inside the normalized whole pair. No
measured response or response estimate is assumed
(`app:ch_response:eq:response-graded-reduced`, `energy-complete-residual`). -/
theorem algebraic_paired_solver_reserved_bounds
    {Ω : Set E} {x : E} {RQ Mcap : ℝ} {K₀ : Set E}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (p : f.centers)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col (cubeStress (d+1)) p.val.val c.root
        c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall (cubeStress (d+1)) f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    {ν alo ahi : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (halo : 0 < alo) (hahi : 0 < ahi)
    (basis : OrthonormalBasis ι ℝ CW)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rorig Rcoef : ℕ) (hRorig : Rsource+fullLowReserve (d+1)+3 ≤ Rorig)
    (hRcoef : Rorig+10 ≤ Rcoef)
    (AQ AB Aphase Dsymbol : ℕ → ℝ)
    (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) (hAphase : ∀ k, 0 ≤ Aphase k)
    (hDsymbol : ∀ k, 0 ≤ Dsymbol k)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall (cubeStress (d+1)) f.coefficientRadius))
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i ^ (k-Rcoef))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i ^ (k-Rcoef))
    (hcertificate : ∀ i (o : Fin 2), ∃ R N,
      GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) o)) R N ∧
      ∀ k ξ is, is.length ≤ k → ∀ z,
        (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) o) ξ) z‖ ≤
          Dsymbol k * (1+cNorm (closedBall x RQ) (k+1) (Q i)+cNorm (closedBall x RQ) (k+1) (B i)))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (3*f.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) ≤ Aphase 2)
    (hφjets : ∀ i k q, q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3*f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ k (Function.uncurry
        (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) q‖ ≤ Aphase k * L i ^ (k-Rorig))
    (hband : ∀ i c, c ∈ V → ∀ y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3*f.physicalRadius),
      alo ≤ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ∧
        ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ≤ ahi)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*f.physicalRadius))
    (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (FiniteEvolution.physicalOperator (f.chart p).index
          (normalizedPair ((1/Complex.I) • maskedPhysicalPDO
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 0))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
  let index := (f.chart p).index
  let φc := fun i y c ↦ φ i (physicalCoordinates index y) c
  have hφc i : ContDiff ℝ ∞ (Function.uncurry (φc i)) :=
    (hφ i).comp (((physicalCoordinates index).contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let ac := fun i ↦ pairedChartSource index (a i)
  have hac i : ContDiff ℝ ∞ (ac i) := pairedChartSource_smooth index (a i) (ha i)
  let Sc := physicalCoordinates index ⁻¹' S
  have hSc : IsCompact Sc := (physicalCoordinates index).toHomeomorph.isCompact_preimage.mpr hS
  have hasc i q (hq : q.1 ∉ Sc) : ac i q = 0 :=
    pairedChartSource_supported index (a i) S (has i) q hq
  have hScU : Sc ⊆ ball ((physicalCoordinates index).symm x) (3*f.physicalRadius) :=
    pairedChartSource_ball index hSU
  have hsource := pairedChartSource_fourier index a Adata K Rsource V Csource hfourier
  have hp := algebraic_paired_chart_reserved_bounds f p hΩ hRQ hball hc hdom threshold ht
    output ho hoc hout hν hν1 halo hahi basis hV hKpar hVK
    Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol hAQ hAB hAphase hDsymbol
    lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQp hBp hcertificate
    φc hφc hcap hφjets hband Sc hSc hScU ac hac hasc Csource hCsource hsource (1/Complex.I : ℂ) 0 false
  let T := fun i ↦ normalizedPair ((1/Complex.I) • maskedPhysicalPDO
    (endpointOutputMask f p output) (chartInputMask f p)
    (selectedAlgebraicSymbol f p (2*threshold) (Q i) (B i) 0))
  have htest i c : graphTestToLp (vectorOriginalDatumTest (ac i) (hac i) hSc (hasc i) [] c) =
      physicalPullbackL2 index (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) :=
    pairedChartSource_test_eq index (a i) (ha i) S hS (has i) c
  have hchart : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i)
        (fun y ↦ φ i (physicalCoordinates index y) c)
        (((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).comp
          (physicalCoordinates index).continuous) (T i)
        (physicalPullbackL2 index
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [T, φc, htest, annularGraphOrientation, Bool.false_eq_true, ↓reduceIte] using hp
  have hphys := hchart.physical hV index
  simpa only [ResponseTransfer.RetainedFactors.demodulatedL2Operator_physicalOperator, FiniteEvolution.physicalOperator_apply,
    Function.comp_def, T, index] using hphys


/-! ## Actual complete same-solver producer

The fixed primitive telescope is the retarded part of the checked all-case
residual constructor, without residual-only W1/endpoint payloads. Every analytic
response field is produced below; none is retained as a hypothesis. Native41/13
instantiates these primitive certificates for the original retained tuple.
-/

open FixedDomainInverse FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer RetainedCharacteristicEnvelopes
open FullSourceEnvelopes RegularSector.Characteristic.ResidualCoordinates
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral AmplitudeBounds SymbolBudgets
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open ResponseTransfer.Complement UniformEvolution IntegratedEnvelope RegularSector.FiniteMasks
open RetainedFactors WholeImageGeometry FullSourceStationary
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open RegularSector.FiniteAssembly RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ConicAmplitude
open CharacteristicPartition ParameterSourceCutoffs FiniteResidualWordProfiles
open FixedDomainInverse.FiniteResidualEnvelopes RegularSector.NormalizedSolver
open ArbitraryAccuracy.SelectedLocalization RegularSector.FiniteEvolution
open RegularSector.FiniteResidual.FiniteIdentity
open CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.PdoRealization


variable {P : Patch (d+1)} {Uref : Set (Euclidean (d+1))} {hUref : IsOpen Uref}
  {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ Mcap : ℝ}
  {K₀ : Set (Euclidean (d+1))}
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 12000 in
/-- Produce the original normalized solver's reserved one-step response by
ACTUALLY applying the order-zero paired retarded constructor at every original
center and the actual order-zero algebraic and inverse elliptic constructors.
Only original finite geometry enters the threshold, chosen BEFORE histories,
operators, source and frequency. The right source cut is the original plateau;
there is no artificial output measurement or assumed solver response
(`app:ch_response:eq:response-graded-reduced`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_physical_history_paired_solver_reserved_bounds
    (T : PatchQuantitativeFamily P Uref hUref)
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap)
    (χp : f.centers → E × Par → ℝ) (hcχp : ∀ p, HasCompactSupport (χp p))
    (evolutionTime speedGap rootSize : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hprotect : ∀ p, LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hbufferTarget : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcBuffer : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ε aperture timeRadius : f.centers → ℝ) (g Rad : f.centers → Bool → ℝ)
    (hε : ∀ p, 0 < ε p) (hεroot : ∀ p, ε p ≤ (f.chart p).rootRadius)
    (hεbuffer : ∀ p, ε p ≤ (f.chart p).bufferRadius/8)
    (hAp : ∀ p, 0 < aperture p) (hg : ∀ p negative, 0 < g p negative)
    (hRad : ∀ p negative, 0 < Rad p negative)
    (htime : ∀ p, 0 < timeRadius p) (htimeε : ∀ p, timeRadius p ≤ ε p)
    (hsrctime : ∀ p, (f.chart p).maskRadius ≤ timeRadius p)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    (V : f.centers → Bool → Set Par) (hV : ∀ p negative, IsOpen (V p negative))
    (hVc : ∀ p negative, IsCompact (closure (V p negative)))
    (hVcov : ∀ p negative, ∀ q ∈ closure (V p negative),
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Vwhole Csrc : Set Par} (hVwhole : IsOpen Vwhole)
    (hVwholec : IsCompact (closure Vwhole))
    (hVwholecov : ∀ q ∈ closure Vwhole,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hCsrc : IsClosed Csrc) (hCsrcV : Csrc ⊆ Vwhole)
    (χinc : f.centers → Bool → Par → ℝ)
    (hχinc : ∀ p negative, ContDiff ℝ ∞ (χinc p negative))
    (hcχinc : ∀ p negative, HasCompactSupport (χinc p negative))
    (hsχinc : ∀ p negative, tsupport (χinc p negative) ⊆ V p negative)
    (aWhole BWhole : f.centers → ℝ) (haWhole : ∀ p, 0 < aWhole p)
    (gapInactive : f.centers → Bool → ℝ)
    (hgapInactive : ∀ p negative, 0 < gapInactive p negative)
    (a₀ B₀ : f.centers → Bool → ℝ) (m Mfreq : f.centers → ℝ)
    (ha₀ : ∀ p negative, 0 < a₀ p negative) (hB₀ : ∀ p negative, 0 < B₀ p negative)
    (hm : ∀ p, 0 < m p) (hm1 : ∀ p, m p ≤ 1) (hMfreq : ∀ p, 1 ≤ Mfreq p)
    (InvBound : f.centers → Bool → ℝ) (hInv : ∀ p negative, 0 ≤ InvBound p negative)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : f.centers → Euclidean d → ℝ) (hang : ∀ p, ContDiff ℝ ∞ (angular p))
    (hangPlateau : ∀ p, ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask (angular p) =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (Damp : f.centers → ℕ → ℝ) (hDamp : ∀ p j, 0 ≤ Damp p j)
    (ra rb : f.centers → ℝ)
    (rectOut rectSource : f.centers → E → ℂ)
    (hrectSource : ∀ p, ContDiff ℝ ∞ (rectSource p))
    (base : f.centers → Fin 2 → ℝ) (cost : f.centers → Fin 2 → ℕ → ℝ)
    (hlocalout : ∀ p y, (output y : ℂ)*rectOut p ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ))
    (hlocalin : ∀ p y, rectSource p ((physicalCoordinates (f.chart p).index).symm y)*(f.inputMask y : ℂ) =
      (f.inputMask y : ℂ))
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Bband : ℝ} (hBband : 1 ≤ Bband)
    {rStar Rstar kMin Rsource : ℕ} (hStar : 8 ≤ rStar)
    (hRstar : fullLowReserve (d+1)+2 < Rstar)
    (hcompression : Rsource + fullLowReserve (d+1) + 4 ≤ Rstar) (hreserve : Rstar+10 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin)
    (basis : OrthonormalBasis ι ℝ CW) {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    let c := fun p ↦ f.chart p
    let z := fun p ↦ ((coordinateSplit (c p).index x).1,
      ((coordinateSplit (c p).index x).2,(coordinateSplit (c p).index p.val.val).2))
    let U := fun p ↦ elapsedPhysicalBox (z p) (ε p/2)
    let O := fun p negative ↦ retainedOpenAnnularFrequencyCarrier (c p).radialSection (z p).2.2
      (ε p/2) (aperture p) (g p negative) (Rad p negative)
    let D := fun p negative ↦ retainedOpenIntegrationDomain (z p) (ε p) (O p negative)
    let Z := fun p negative ↦ Ioo (-2*timeRadius p) (2*timeRadius p) ×ˢ (U p ×ˢ V p negative)
    let KP := fun p negative ↦ closure (elapsedPhysicalBox (z p) (ε p)) ×ˢ closure (V p negative)
    let KPwhole := fun p ↦ closure (elapsedPhysicalBox (z p) (ε p)) ×ˢ closure Vwhole
    let PInactive := fun p negative ↦ Csrc ∩ tsupport (fun b ↦ 1-χinc p negative b)
    let Ksigned := fun p negative ↦ fullSourceSignedCarrier (z p) (ε p)
      (closure (V p negative)) (O p negative)
    let β := fun p ↦ selectedEndpointMultiplier f p threshold
    (∀ p, MapsTo (primaryCoordinateChange (c p).index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (U p)) →
    (∀ p, tsupport (f.angularMask p ∘ physicalCoordinates (c p).index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone (c p).radialSection (z p).2.2 (ε p/4) (aperture p/2)) →
    (∀ p negative, retainedAnnularFrequencyCarrier (c p).radialSection (z p).2.2
      (ε p/2) (aperture p)
      (retainedSelectorGap (z p).2.2 (ε p/2) (aperture p) (a₀ p negative/(2*Mfreq p)))
      (2*(2*B₀ p negative/m p)) ⊆ O p negative) →
    (∀ p, RetainedConstruction.DiagonalFrequencyCoverage (c p).radialSection (z p).2.2
      ((c p).bufferRadius/2) (ra p) (rb p) (β p)) →
    (∀ p y, endpointOutputMask f p output y ≠ 0 → (c p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) →
    (∀ p negative, ∀ q ∈ KP p negative, χp p =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    (∀ p, ∀ q ∈ KPwhole p, χp p =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧
    ∀ (R₀ : I → ℝ) (n : I → ℕ)
      (u : ∀ i, Fin (n i) → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
      (ell : ∀ i, Fin (n i) → ℕ), (∀ i, S₀ ≤ R₀ i) →
      (∀ i, RevisedGlobal.IsAdmissibleHistory Bband (R₀ i) kMin (u i) (ell i)) →
    ∀ Q : I → {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold},
      (∀ i, (Q i).1 = extendedProjectedStress ext (RevisedGlobal.finiteMap Gref.map (u i))) →
    let B := fun i ↦ reducedZerothProjection (d+1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (RevisedGlobal.finiteMap Gref.map (u i))
    let L := fun i ↦ currentCoefficientScale (R₀ i) (n i)
    let sourcePhase := fun p negative i ↦ if negative then
      T.negativeFullSourcePhaseInCoordinates (c p).index (Q i)
      else T.fullSourcePhaseInCoordinates (c p).index (Q i)
    ∀ (h : f.centers → I → RootState (Euclidean d) → ℝ)
      (Φ : f.centers → I → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (chart : f.centers → I → OpenPartialHomeomorph TC TC) (G : f.centers → I → TC → ℝ),
      (∀ p i, closedBall ((z p).1,z p) (c p).targetRadius ⊆ (chart p i).target) →
      (∀ p i, ContDiffOn ℝ ∞ (twoTimePhase (chart p i)) (chart p i).target) →
      (∀ p i q, q ∈ (chart p i).target → HasFDerivAt (twoTimePhase (chart p i))
        (twoTimePhaseDifferential (h p i) (Φ p i) (chart p i) q) q) →
      (∀ p i q, q ∈ closedBall ((z p).1,z p) (c p).targetRadius →
        ‖twoTimePhaseMixed (chart p i) q - 1‖ ≤ 1/2) →
      (∀ p i j, cNorm (closedBall ((z p).1,z p) (c p).targetRadius) j (twoTimePhase (chart p i)) ≤
        (c p).phaseCost j * (1+cNorm (closedBall x RQ) (j+1) (Q i).1)) →
      (∀ p i q, q ∈ (chart p i).target → ((chart p i).symm q).2.1 = q.2.1) →
    let Fs := fun p i ↦ selectedBufferedAmplitude f p (Q i).1 (B i) (Φ p i) (chart p i)
    let matrix := fun p i k ↦ collared (c p).radialSection (if k=0 then 0 else 1)
      (angular p) (Fs p i k)
    let Ws := fun p i ↦ selectedConicAmplitude f p (Q i).1 (B i) (Φ p i) (chart p i) (angular p)
    (∀ p i k, ContDiff ℝ ∞ (Fs p i k)) → (∀ p i k, ContDiff ℝ ∞ (matrix p i k)) →
    (∀ p i k, tsupport (matrix p i k) ⊆ ConicPhase.domain (c p).radialSection
      ((chart p i).target ∩ (chart p i).symm ⁻¹'
        (ball (z p).1 ((c p).maskRadius/2) ×ˢ
          (ball (z p).1 ((c p).maskRadius/2) ×ˢ ball (z p).2 ((c p).maskRadius/2))))) →
    (∀ p i q, q ∈ tsupport (matrix p i 0) ∪ tsupport (matrix p i 1) →
      G p i =ᶠ[𝓝 q] phase (c p).radialSection (chart p i)) →
    (∀ p i q, (c p).timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → matrix p i 2 q ≠ 0 →
      G p i =ᶠ[𝓝 q] phase (c p).radialSection (chart p i)) →
    (∀ p i k j, BoundedTwoTimeOrderSeminorm (if k=0 then 0 else 1)
      (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (Ws p i k) ∧
      twoTimeOrderSeminorm (if k=0 then 0 else 1)
        (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (Ws p i k) ≤
        Damp p j * (1+cNorm (closedBall x RQ) (j+10) (Q i).1+cNorm (closedBall x RQ) (j+9) (B i))) →
    (∀ p negative i q, q ∈ KP p negative →
      a₀ p negative ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ≤ B₀ p negative) →
    (∀ p i q, q ∈ KPwhole p →
      aWhole p ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ≤ BWhole p) →
    (∀ p i t, t ∈ Icc 0 (ε p) → ∀ y ∈ U p,
      ∀ ξ ∈ retainedFrequencyDomain (c p).radialSection (z p) (ε p) (aperture p) (1/2),
        m p*‖ξ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase (c p).radialSection (chart p i)) t v ξ) y‖ ∧
        ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase (c p).radialSection (chart p i)) t v ξ) y‖ ≤ Mfreq p*‖ξ‖) →
    ∀ Op : f.centers → I → Fin 2 → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
      (∀ p i o, RetainedSignedRetardedBounds (closedBall x RQ) (Q i).1 (B i) (3*(c p).maskRadius/4)
        ((z p).1-(c p).maskRadius/2) (fun t s y ξ ↦ G p i (t,(s,(y,ξ))))
        (if o=0 then Ws p i 0+Ws p i 1 else Ws p i 2) (rectOut p) (rectSource p) (β p)
        (hrectSource p) o.val (base p o) (cost p o) (Op p i o)) →
    ∀ κ : f.centers → Bool → I → (ℝ × (E × Par)) → CW,
    let raw := fun p negative i ↦ fullSourceJointPhase false
      (curriedPhase (c p).radialSection (chart p i)) (sourcePhase p negative i)
    (∀ p negative i, ContDiffOn ℝ ∞ (raw p negative i) (Z p negative ×ˢ D p negative)) →
    (∀ p negative i, ContDiffOn ℝ ∞ (κ p negative i) (Z p negative)) →
    (∀ p negative i q, q ∈ Z p negative → κ p negative i q ∈ D p negative ∧
      gradient (fun w ↦ raw p negative i (q,w)) (κ p negative i q) = 0 ∧
      raw p negative i (q,κ p negative i q) = 0) →
    (∀ p negative i q, q ∈ Z p negative → ∀ w ∈ closure (D p negative),
      let phase := fun b w ↦ raw p negative i ((q.1,b),w)
      IsUnit (averagedPhaseHessian phase (fun b ↦ κ p negative i (q.1,b)) q.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian phase (fun b ↦ κ p negative i (q.1,b)) q.2 w)‖ ≤
          InvBound p negative) →
    (∀ p negative i q, q ∈ Z p negative → ∀ w ∈ closure (D p negative),
      ∀ t ∈ uIcc (0 : ℝ) q.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((t,q.2),κ p negative i q + a • (w-κ p negative i q)) ∈ Ksigned p negative) →
    (∀ p negative i b, b ∈ Vwhole → b ∈ PInactive p negative →
      ∀ t ∈ Icc 0 (3*(c p).maskRadius/4), ∀ y ∈ U p, ∀ ξ ∈ tsupport (β p),
      gapInactive p negative ≤
        dist (NormedSpace.normalize (gradient (fun y ↦ sourcePhase p negative i y b) y))
          (NormedSpace.normalize ξ)) →
    ∀ (lam K Adata : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ Adata i) →
    ∀ (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i))),
      (∀ p i b y, φ i (physicalCoordinates (c p).index y) b = χp p (y,b)*sourcePhase p false i y b) →
    ∀ (χout χin : E → ℝ) (hcχout : HasCompactSupport χout)
      (hχin : Continuous χin) (hbχin : ∀ y, ‖χin y‖ ≤ 1),
      (∀ y ∈ tsupport χout, χin y = 1) →
      (∀ p, physicalCoordinates (c p).index ⁻¹' tsupport χout ⊆ U p) →
      (tsupport χout ⊆ ball x (3*f.physicalRadius)) →
    ∀ (hK₀ : IsCompact K₀) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
    (hΩ : IsOpen Ω) → (hRQ : 0 ≤ RQ) → (hball : closedBall x RQ ⊆ Ω) →
    (hft : f.radialThreshold ≤ threshold) →
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col (cubeStress (d+1)) p.val.val c.root
        c.coefficientRadius c.rootRadius c.minorGap c.transportGap) →
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall (cubeStress (d+1)) f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
          complementDomain c.index (fun _ : E ↦ A')
            (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root)
            c.row c.col (normalizedRootDomain c)) →
    ∀ (AQ AB Aphase Dalgebraic : ℕ → ℝ),
      (∀ j, 0 ≤ AQ j) → (∀ j, 0 ≤ AB j) → (∀ j, 0 ≤ Aphase j) →
      (∀ j, 0 ≤ Dalgebraic j) →
      (∀ i, ContDiffOn ℝ ∞ (Q i).1 Ω) → (∀ i, ContDiffOn ℝ ∞ (B i) Ω) →
      (∀ i, MapsTo (Q i).1 Ω (closedBall (cubeStress (d+1)) f.coefficientRadius)) →
      (∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i).1 ≤ Mcap) →
      (∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ Mcap) →
      (∀ i j, cNorm (closedBall x RQ) j (Q i).1 ≤ AQ j * L i^(j-rStar)) →
      (∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i^(j-rStar)) →
      (∀ p i (o : Fin 2), ∃ R N,
        GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i).1 (B i) o)) R N ∧
        ∀ j ξ is, is.length ≤ j → ∀ z,
          (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*threshold) (Q i).1 (B i) o) ξ) z‖ ≤
            Dalgebraic j * (1+cNorm (closedBall x RQ) (j+1) (Q i).1+cNorm (closedBall x RQ) (j+1) (B i))) →
    ∀ (alo ahi : ℝ), 0 < alo → 0 < ahi →
      (∀ p i, cNorm
        (closedBall ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius) ×ˢ closure Vwhole) 2
        (Function.uncurry (fun y b ↦ φ i (physicalCoordinates (c p).index y) b)) ≤ Aphase 2) →
      (∀ p i j q, q ∈
        closedBall ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius) ×ˢ closure Vwhole →
        ‖iteratedFDeriv ℝ j (Function.uncurry (fun y b ↦ φ i (physicalCoordinates (c p).index y) b)) q‖ ≤
          Aphase j * L i^(j-Rstar)) →
      (∀ p i b, b ∈ Vwhole → ∀ y ∈
        ball ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius),
        alo ≤ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (c p).index z) b) y‖ ∧
          ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (c p).index z) b) y‖ ≤ ahi) →
      (∀ i, cNorm (closedBall x (3*f.physicalRadius) ×ˢ closure Vwhole) 2
        (Function.uncurry (φ i)) ≤ Aphase 2) →
      (∀ i j q, q ∈ closedBall x (3*f.physicalRadius) ×ˢ closure Vwhole →
        ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i^(j-Rstar)) →
      (∀ i b, b ∈ Vwhole → ∀ y ∈ ball x (3*f.physicalRadius),
        alo ≤ ‖fderiv ℝ (fun z ↦ φ i z b) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z b) y‖ ≤ ahi) →
    ∀ (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0),
      (∀ i b, b ∉ Csrc → ∀ y, a i (y,b) = 0) →
    ∀ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) →
      (∀ i b, b ∈ Vwhole → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) b w
        ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s*Adata i*K i^(s+l-Rsource)) →
    let solver := fun i ↦ pairedSolver f hK₀ threshold (Q i).1 (B i) output ho.continuous hob
      ((sourceCutMultiplier output ho.continuous hob).comp
        ((finitePhysicalOperator (fun p ↦ (c p).index) (fun p ↦ Op p i 0)).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib)))
    ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y b)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        ((solver i).comp (sourceCutMultiplier χin hχin hbχin))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b)))
      Adata K Rsource := by
  classical
  intro c z U O D Z KP KPwhole PInactive Ksigned β
    hmaskBox hcone hsel hcoverage htimePlateau heχp heχpWhole
  have hretarded (p : f.centers) := exists_physical_history_paired_retarded_reserved_bounds
    (I := I) (BWhole := BWhole p) T (χp p) (hcχp p) f p
    (hprotect p) (hbufferTarget p) (hsrcBuffer p) (g p) (Rad p)
    (hε p) (hεroot p) (hεbuffer p) (hAp p) (hg p) (hRad p)
    (htime p) (htimeε p) (hsrctime p) hphysical (V p) (hV p) (hVc p) (hVcov p)
    hVwhole hVwholec hVwholecov hCsrc hCsrcV (χinc p) (hχinc p) (hcχinc p) (hsχinc p)
    (haWhole p) (gapInactive p) (hgapInactive p) (a₀ p) (B₀ p) (ha₀ p) (hB₀ p)
    (hm p) (hm1 p) (hMfreq p) (InvBound p) (hInv p)
    output ho hoc hos hob threshold hthreshold (angular p) (hang p) (hangPlateau p)
    (Damp p) (hDamp p) (rectOut p) (rectSource p) (hrectSource p) (base p) (cost p)
    (hlocalout p) (hlocalin p) Gref hr hrR hR ext hextcenter hextradius hBband
    hStar hRstar hcompression hreserve horder basis hν hν1
    (hmaskBox p) (hcone p) (hsel p) (hcoverage p) (htimePlateau p) (heχp p) (heχpWhole p)
  choose Sp hSp hret using hretarded
  have hSp0 (p : f.centers) : 0 ≤ Sp p := by linarith [hSp p]
  let Smax : NNReal := Finset.univ.sup (fun p : f.centers ↦ ⟨Sp p, hSp0 p⟩)
  let S₀ : ℝ := max 2 (Smax : ℝ)
  have hS₀ : 2 ≤ S₀ := le_max_left _ _
  have hSpS (p : f.centers) : Sp p ≤ S₀ := by
    have h : (⟨Sp p, hSp0 p⟩ : NNReal) ≤ Smax :=
      Finset.le_sup (f := fun p : f.centers ↦ (⟨Sp p, hSp0 p⟩ : NNReal)) (Finset.mem_univ p)
    exact (show Sp p ≤ (Smax : ℝ) from h).trans (le_max_right _ _)
  refine ⟨S₀,hS₀,?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L sourcePhase h Φ chart G
    hbuffer hsm hdiff hnear hphase hsourceTime Fs matrix Ws
    hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hsourceBandWhole hradial
    Op hOp κ raw hraw hκ hstat hHess hsegments hangle
    lam K Adata hlam hLK hscale hAdata φ hφ heq
    χout χin hcχout hχin hbχin hplateau hSUchart hSU
    hK₀ hib hΩ hRQ hball hft hc hdom
    AQ AB Aphase Dalgebraic hAQ hAB hAphase hDalgebraic
    hQΩ hBΩ hmap hQl hBl hQp hBp halgebraic
    alo ahi halo hahi hcapChart hφjetsChart hbandChart hcap hφjets hband
    a ha has hparam Csource hCsource hfourier solver
  have hL (i : I) : 1 ≤ L i :=
    one_le_currentCoefficientScale (by linarith [hS₀.trans (hR₀ i)]) (n i)
  have hRorig : Rsource + fullLowReserve (d+1) + 3 ≤ Rstar := by omega
  have hQp' (i : I) (j : ℕ) :
      cNorm (closedBall x RQ) j (Q i).1 ≤ AQ j * L i^(j-Rstar) :=
    (hQp i j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hL i) (by omega)) (hAQ j))
  have hBp' (i : I) (j : ℕ) :
      cNorm (closedBall x RQ) j (B i) ≤ AB j * L i^(j-Rstar) :=
    (hBp i j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hL i) (by omega)) (hAB j))
  have hretbound (p : f.centers) : ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y b)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (FiniteEvolution.physicalOperator (c p).index
          (normalizedPair (selectedCommonChartRetarded f p output ho.continuous hob hib (Op p i 0))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b)))
      Adata K Rsource := by
    have hprimary (i : I) : ContDiff ℝ ∞
        (fun q : E × Par ↦ χp p q * sourcePhase p false i q.1 q.2) := by
      have he : (fun q : E × Par ↦ χp p q * sourcePhase p false i q.1 q.2) =
          (fun q : E × Par ↦ φ i (physicalCoordinates (c p).index q.1) q.2) := by
        funext q
        exact (heq p i q.2 q.1).symm
      rw [he]
      exact (hφ i).comp
        (((physicalCoordinates (c p).index).contDiff.comp contDiff_fst).prodMk contDiff_snd)
    let ac := fun i ↦ pairedChartSource (c p).index (a i)
    have hac i := pairedChartSource_smooth (c p).index (a i) (ha i)
    have hasc i := pairedChartSource_supported (c p).index (a i) (tsupport χout) (has i)
    have hSc := (physicalCoordinates (c p).index).toHomeomorph.isCompact_preimage.mpr hcχout.isCompact
    have hparamc i q (hq : q.2 ∉ Csrc) : ac i q = 0 :=
      hparam i q.2 hq (physicalCoordinates (c p).index q.1)
    have hfourierc := pairedChartSource_fourier (c p).index a Adata K Rsource Vwhole Csource hfourier
    have hp := hret p R₀ n u ell (fun i ↦ (hSpS p).trans (hR₀ i)) hu Q hQ
      (h p) (Φ p) (chart p) (G p) (hbuffer p) (hsm p) (hdiff p) (hnear p)
      (hphase p) (hsourceTime p) (hFs p) (hmatrix p) (hsupport p) (hGsolver p)
      (hGres p) (hbudget p) (hsourceBand p) (hsourceBandWhole p) (hradial p)
      (Op p) (hOp p) (κ p) (hraw p) (hκ p) (hstat p) (hHess p) (hsegments p) (hangle p)
      lam K Adata hlam hLK hscale hAdata (physicalCoordinates (c p).index ⁻¹' tsupport χout)
      hSc (hSUchart p) ac hac hasc Csource hparamc hCsource hfourierc hprimary 0 (1 : ℂ)
    have hdatum i b : graphTestToLp
        (vectorOriginalDatumTest (ac i) (hac i) hSc (hasc i) [] b) =
        physicalPullbackL2 (c p).index
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b)) :=
      pairedChartSource_test_eq (c p).index (a i) (ha i) (tsupport χout) hcχout.isCompact (has i) b
    have hchart : ReservedLetterBounds Vwhole
        (fun i b ↦ demodulatedL2Operator (lam i)
          (fun y ↦ φ i (physicalCoordinates (c p).index y) b)
          (((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).comp
            (physicalCoordinates (c p).index).continuous)
          (normalizedPair (selectedCommonChartRetarded f p output ho.continuous hob hib (Op p i 0)))
          (physicalPullbackL2 (c p).index
            (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b))))
        Adata K Rsource := by
      simpa only [heq, hdatum, one_smul, Fin.val_zero, Nat.cast_zero, neg_zero,
        zpow_zero, one_mul, selectedCommonChartRetarded] using hp
    have hphys := hchart.physical hVwhole (c p).index
    simpa only [RetainedFactors.demodulatedL2Operator_physicalOperator,
      FiniteEvolution.physicalOperator_apply, Function.comp_def] using hphys
  have hnormal : ∀ i p, ∃ R N, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*threshold) (Q i).1 (B i) 0)) R N := by
    intro i p
    obtain ⟨R,N,hN,_⟩ := halgebraic p i 0
    exact ⟨R,N,hN⟩
  choose Rnormal Cnormal hnormal using hnormal
  have huncut : ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y b)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const)) (solver i)
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b)))
      Adata K Rsource := by
    exact pairedSolver_reserved_bounds_of_actual_letters f hK₀ threshold (fun i ↦ (Q i).1) B
      output ho.continuous hob hib hos Rnormal Cnormal hnormal (fun i p ↦ Op p i 0)
      hVwhole lam Adata K Rsource hlam hAdata
      (fun i ↦ zero_le_one.trans ((hL i).trans (hLK i))) φ
      (fun i b ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (fun i b ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b))
      hretbound
      (fun p ↦ algebraic_paired_solver_reserved_bounds f p hΩ hRQ hball hc hdom
        threshold hft output ho hoc hos hν hν1 halo hahi basis hVwhole hVwholec subset_closure
        Rsource Rstar rStar hRorig hreserve AQ AB Aphase Dalgebraic hAQ hAB hAphase hDalgebraic
        lam L K Adata hlam hL hLK hscale hAdata (fun i ↦ (Q i).1) B
        hQΩ hBΩ hmap hQp hBp (halgebraic p) φ hφ (hcapChart p) (hφjetsChart p) (hbandChart p)
        (tsupport χout) hcχout.isCompact hSU a ha has Csource hCsource hfourier)
      (elliptic_paired_solver_reserved_bounds f hK₀ hΩ hball output ho hoc hos hob threshold hft
        basis hVwhole hVwholec subset_closure Rsource Rstar hRorig AQ AB Aphase hAQ hAB hAphase
        hν hν1 halo hahi lam L K Adata hlam hL hLK hscale hAdata
        (fun i ↦ (Q i).1) B hQΩ hBΩ hmap hQl hBl hQp' hBp' φ hφ hcap hφjets hband
        (tsupport χout) hcχout.isCompact hSU a ha has Csource hfourier)
  exact reserved_bounds_input_plateau solver lam Adata K Rsource φ
    (fun i b ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    (tsupport χout) hcχout.isCompact a ha has χin hχin hbχin hplateau huncut

private theorem solver_reserved_bounds_native_step
    {V : Set Par} {g : I → Par → H} {A K : I → ℝ} {reserve : ℕ}
    (h : ReservedLetterBounds V g A K reserve) :
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧
          vectorFourierSobolevNorm (s : ℝ) value ≤ C * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
  intro ps hps s
  obtain ⟨C,hC,hbound⟩ := h.2 ps hps s
  exact ⟨C,hC,fun q ↦ hbound q.1 q.2 q.2.property⟩

end JanetCartan.PhysicalPrimary
end

public meta section
set_option maxHeartbeats 2400000
set_option maxRecDepth 32000
namespace JanetCartan.PhysicalPrimary.SolverStepConstruction
open Lean Meta Elab Command

private partial def nativeTelescope {α : Type} (type : Expr)
    (k : Array Expr → Expr → MetaM α) (xs : Array Expr := #[]) : MetaM α := do
  match type with
  | .mdata _ body => nativeTelescope body k xs
  | .letE _ _ value body _ => nativeTelescope (body.instantiate1 value) k xs
  | .forallE name dom body bi =>
    withLocalDecl name bi dom fun x ↦ nativeTelescope (body.instantiate1 x) k (xs.push x)
  | _ => k xs type

/-- Preserve every primitive input and the prehistory maximum threshold from
our actual three-producer theorem; project only its already-proved profile to
the exact native `q : I × Vwhole` solver step. -/
elab "emit_actual_paired_solver_hstep" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalPrimary.exists_physical_history_paired_solver_reserved_bounds
  let target := `JanetCartan.PhysicalPrimary.exists_physical_history_paired_solver_hstep
  let info ← getConstInfo source
  nativeTelescope info.type fun fixed outer => do
    unless outer.isAppOfArity ``Exists 2 do throwError "solver prehistory threshold existential changed"
    let native := mkAppN (mkConst source (info.levelParams.map Level.param)) fixed
    let sourceArgs := outer.getAppArgs
    let callback ← withLocalDeclD `S₀ sourceArgs[0]! fun S₀ => do
      let specification := (mkApp sourceArgs[1]! S₀).headBeta
      withLocalDeclD `nativeSpec specification fun nativeSpec => do
        unless specification.isAppOfArity ``And 2 do throwError "solver threshold conjunction changed"
        let continuation := .proj ``And 1 nativeSpec
        let mapped ← nativeTelescope specification.getAppArgs[1]! fun data result => do
          unless result.isAppOf `JanetCartan.PhysicalEllipticWords.ReservedLetterBounds do
            throwError "terminal same-solver profile changed"
          let original := mkAppN continuation data
          let step ← mkAppM ``JanetCartan.PhysicalPrimary.solver_reserved_bounds_native_step #[original]
          mkLambdaFVars data step
        let pair ← mkAppM ``And.intro #[.proj ``And 0 nativeSpec,mapped]
        let predicate ← mkLambdaFVars #[S₀] (← inferType pair)
        let result ← mkAppOptM ``Exists.intro #[some sourceArgs[0]!,some predicate,some S₀,some pair]
        mkLambdaFVars #[S₀,nativeSpec] result
    let result ← mkAppM ``Exists.elim #[native,callback]
    let value ← instantiateMVars (← mkLambdaFVars fixed result)
    let type ← instantiateMVars (← inferType value)
    if value.hasSorry || type.hasSorry || value.hasMVar || type.hasMVar ||
        value.hasFVar || type.hasFVar then
      throwError "incomplete or dimension-polymorphic native solver application"
    addDecl (.thmDecl {name := target,levelParams := info.levelParams,type,value}) (forceExpose := true)
  logInfo "kernel-checked actual retarded0/algebraic0/elliptic-inverse hsolverStep, with every primitive input, native q:I×Vwhole indexing, unchanged source reserve and prehistory finite maximum"

end JanetCartan.PhysicalPrimary.SolverStepConstruction
end

open JanetCartan.PhysicalPrimary.SolverStepConstruction
emit_actual_paired_solver_hstep
