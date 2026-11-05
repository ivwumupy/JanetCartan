module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Analysis.Microlocal.EllipticComplement.CommonOutput

/-!
# Normalization of the actual two-branch tested equation

The elliptic equation is instantiated on the same supplied family and the
characteristic measurement plateau. The characteristic premise below is the
literal output of `exists_finite_protected_direct_operator_bounds_and_equations_of_selected_collar`;
applying that producer and retaining its witnesses remains an obligation of
the complete constructor. Both source and gain-one residual are normalized
together (`energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks.ActualFamily EllipticComplement FiniteAssembly Realization
open Characteristic.EvolutionIntegral FourierIntegral FourierIntegral.LowBounds
open Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)

/-- Half-normalization and literal conjugation preserve a tested equation
for the same real physical coefficients (`energy-complete-residual`). -/
theorem normalizedPair_tested
    (A : E → Fin (d+1) → Mat) (B : E → Mat)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun y ↦ B y i j))
    (S G : H →L[ℂ] H) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (j : Fin (d+1))
    (ht : ∀ u : H, physicalTestAction A B (fun y ↦ (S u y).ofLp) φ j =
      ∫ y, φ y • G u y j) (u : H) :
    physicalTestAction A B (fun y ↦ (normalizedPair S u y).ofLp) φ j =
      ∫ y, φ y • normalizedPair G u y j := by
  apply physicalPairedSectorSum_test A B hA hB {()}
    (fun _ : Unit ↦ (1/2 : ℂ) • S) (fun _ : Unit ↦ (1/2 : ℂ) • G) hφ hc j _ u
  intro _ _ v
  let T := physicalTestActionLp A B hA hB φ hφ hc j
  let F := testCoordinatePairing φ (hφ.continuous.memLp_of_hasCompactSupport hc) j
  have he (w : H) : T (S w) = F (G w) := by
    simpa only [T, F, physicalTestActionLp_apply, testCoordinatePairing,
        LinearMap.coe_mk, AddHom.coe_mk] using ht w
  rw [← physicalTestActionLp_apply A B hA hB φ hφ hc j]
  change T ((1/2 : ℂ) • S (graphTestToLp v)) = F ((1/2 : ℂ) • G (graphTestToLp v))
  rw [map_smul, map_smul, he]

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Add the ACTUAL elliptic equation to the retained characteristic equation
on its original plateau, then normalize all three operators. The additional
output cutoff remains on the elliptic branch; its derivative is removed only
by `hone` on the measurement set (`sector-theorem-identity`). -/
theorem pairedSolver_tested_of_characteristic
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    {L : ℝ} (hL : f.radialThreshold ≤ L)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (hsub : U ⊆ ball x f.physicalRadius)
    (hone : ∀ y ∈ U, output y = 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded retardedPW₁ : H →L[ℂ] H)
    (hchar : ∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (selectedFiniteDirectSolver f L Q B output ho hob retarded u y).ofLp) φ j =
        ∫ y, φ y • ((sourceCutMultiplier (r := d+1) output ho hob).comp (selectedFiniteSourcePDO f L) +
          selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁) u y j) :
    ∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (pairedSolver f hK L Q B output ho hob retarded u y).ofLp) φ j =
        ∫ y, φ y • (pairedSource f hK L output ho hob +
          pairedResidual f hK L Q B output ho hob W₁ retardedPW₁) u y j := by
  obtain ⟨A, B', hA, hB', hcoeff⟩ := exists_elliptic_test_coefficients f hΩ Q B hQ hB
  have hell := commonOutput_ellipticSolver_tested f hK hΩ hRQΩ output ho hob hU hsub hone
    hL Q B hQ hB hmap hQl hBl
  intro u φ hφ hc hs j
  let O := sourceCutMultiplier (r := d+1) output ho hob
  let S := selectedFiniteDirectSolver f L Q B output ho hob retarded
  let R := selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁
  let AS := O.comp (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L)
  let RS := R + O.comp (ellipticResidual f hK L Q B)
  have he (w : H) := physicalTestAction_eq_of_coefficients_on_support A
    (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B' B
    (fun y ↦ (w y).ofLp) φ
    (fun y hy ↦ (hcoeff y (ball_subset_closedBall (hsub (hs hy)))).1)
    (fun y hy ↦ (hcoeff y (ball_subset_closedBall (hsub (hs hy)))).2) j
  have ht (w : H) : physicalTestAction A B'
      (fun y ↦ ((S + O.comp (ellipticSolver f hK L Q)) w y).ofLp) φ j =
        ∫ y, φ y • (AS+RS) w y j := by
    let T := physicalTestActionLp A B' hA hB' φ hφ hc j
    let F := testCoordinatePairing φ (hφ.continuous.memLp_of_hasCompactSupport hc) j
    have hc' : T (S w) = F ((O.comp (selectedFiniteSourcePDO f L)+R) w) := by
      simpa only [T, F, physicalTestActionLp_apply, testCoordinatePairing,
        LinearMap.coe_mk, AddHom.coe_mk] using
        (he (S w)).trans (hchar w φ hφ hc hs j)
    have he' : T (O.comp (ellipticSolver f hK L Q) w) =
        F (O.comp (ellipticSourcePDO f hK L + ellipticResidual f hK L Q B) w) := by
      simpa only [T, F, physicalTestActionLp_apply, testCoordinatePairing,
        LinearMap.coe_mk, AddHom.coe_mk] using
        (he (O.comp (ellipticSolver f hK L Q) w)).trans (hell w φ hφ hc hs j)
    rw [← physicalTestActionLp_apply A B' hA hB' φ hφ hc j]
    change T (S w + O (ellipticSolver f hK L Q w)) = F ((AS+RS) w)
    simp only [ContinuousLinearMap.comp_apply] at he'
    rw [map_add, hc', he', ← map_add]
    congr 1
    simp only [AS, RS, add_apply, ContinuousLinearMap.comp_apply, map_add]
    abel
  have hp := normalizedPair_tested A B' hA hB' (S+O.comp (ellipticSolver f hK L Q))
    (AS+RS) φ hφ hc j ht u
  rw [he] at hp
  have hsum : normalizedPair (AS+RS) = pairedSource f hK L output ho hob +
      pairedResidual f hK L Q B output ho hob W₁ retardedPW₁ :=
    normalizedPair_add AS RS
  rw [hsum] at hp
  exact hp

/-- The same actual two-branch equation for real inputs and the literal
real compression, with source and residual still separate
(`real-sector-normalization`, `sector-theorem-identity`). -/
theorem realSolver_tested_of_paired
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded retardedPW₁ : H →L[ℂ] H)
    (φ : E → ℝ) (j : Fin (d+1))
    (ht : ∀ u : H, physicalTestAction
      (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (pairedSolver f hK L Q B output ho hob retarded u y).ofLp) φ j =
      ∫ y, φ y • (pairedSource f hK L output ho hob +
        pairedResidual f hK L Q B output ho hob W₁ retardedPW₁) u y j) (u : RH) :
    physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
      (fun y ↦ (l2ComplexInclusion volume (realSolver f hK L Q B output ho hob retarded u) y).ofLp)
      φ j = ∫ y, φ y • l2ComplexInclusion volume
        ((realSource f hK L output ho hob + realResidual f hK L Q B output ho hob W₁ retardedPW₁) u) y j := by
  have hs : l2ComplexInclusion volume (realSolver f hK L Q B output ho hob retarded u) =
      pairedSolver f hK L Q B output ho hob retarded (l2ComplexInclusion volume u) :=
    inclusion_realCompression_normalizedPair
      (selectedFiniteDirectSolver f L Q B output ho hob retarded +
        (sourceCutMultiplier (r := d+1) output ho hob).comp (ellipticSolver f hK L Q)) u
  have hg : l2ComplexInclusion volume
      ((realSource f hK L output ho hob + realResidual f hK L Q B output ho hob W₁ retardedPW₁) u) =
      (pairedSource f hK L output ho hob + pairedResidual f hK L Q B output ho hob W₁ retardedPW₁)
        (l2ComplexInclusion volume u) := by
    simp only [add_apply, map_add]
    exact congrArg₂ (· + ·)
      (inclusion_realCompression_normalizedPair
        ((sourceCutMultiplier (r := d+1) output ho hob).comp
          (selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L)) u)
      (inclusion_realCompression_normalizedPair
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retardedPW₁ +
          (sourceCutMultiplier (r := d+1) output ho hob).comp (ellipticResidual f hK L Q B)) u)
  rw [hs, hg]
  exact ht _

end JanetCartan.RegularSector.NormalizedSolver
