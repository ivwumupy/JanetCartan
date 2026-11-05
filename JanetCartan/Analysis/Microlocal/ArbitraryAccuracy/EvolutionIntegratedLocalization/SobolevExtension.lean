module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SobolevKernels
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.Summation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

/-!
# Cartesian Sobolev extension of the elapsed shell sum

The derivative majorants constructed in `KernelMajorants` give a bounded
operator on the existing Cartesian completion. Every completed derivative
is identified with the integral of the actual summed shell derivatives.
The zeroth derivative is the physical elapsed shell action with the fixed
auxiliary output cutoff still displayed (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells CartesianJets
open FiniteChain.Retarded.KernelSobolev AmplitudeBound RetardedSobolev.Spaces
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization.SobolevRealization
variable {d q m : ℕ}
local notation "E" => Euclidean (d + 1)
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

section Extension
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] (Euclidean (d + 1)))
  (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ)
  (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : (Euclidean (d + 1)) → ℂ)
  (mi mo : LocalizerSymbol (d + 1))
  (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
  (his : HasCompactSupport mi)
  (hS : ∀ r u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞
    (fun p : ℝ × ((Euclidean (d + 1)) × (Euclidean (d + 1))) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2) (r, u, ξ))
  (hA : ContDiff ℝ ∞ (fun p : ℝ × (((Euclidean (d + 1)) × (Euclidean (d + 1))) × (Euclidean (d + 1))) ↦
    orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
  (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
  (ψ : (Euclidean (d + 1)) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)

local notation "K" => (fun (p : ℕ × ℕ) (a c : Fin q) ↦
  supportedElapsedShellEntry J backward hρ Δ Ψ b χout χsource β mi mo
    hout hsource his hS hA hi ho ψ hψ hsψ p.1 p.2 a c)
local notation "KP" => (fun (p : ℕ × ℕ) ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
  χout χsource β mi mo (graphCutoff p.1) (outputCutoff p.2))
local notation "sI" => (fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' (Prod.fst '' tsupport mi)
local notation "sO" => Prod.swap ⁻¹' (J ⁻¹' tsupport ψ)

/-- The summable physical derivative bounds produced by `KernelMajorants`
construct all matrix channels on the Cartesian Sobolev completion. The
cutoff profile is derived from the actual fixed smooth cutoff. Every
completed jet is identified, so no regularity of the infinite sum is assumed
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedShell_matrix_extension
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ p, 0 ≤ B l p) (hs : ∀ l ≤ m, Summable (B l))
    (hb : ∀ p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ KP p z y) x v‖ ≤ B l p) :
    ∃ Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
        Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)),
      ‖matrixOperator Op‖ ≤ (q : ℝ) * q *
        (jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l ↦ ∑' p, B l p) m *
          compactSupportFactor volume volume sI sO) ∧
      (∀ a c f, HasSum (fun p ↦ ofTest m volume (kernelIntegralLinear (K p a c) volume f))
        (Op a c (ofTest 0 volume f))) ∧
      ∀ a c f (i : JetIndex d m), (Op a c (ofTest 0 volume f)).val i =ᵐ[volume]
        fun x ↦ ∫ y, (∑' p, kernelJet (K p a c) i x y) * f.val (y.2, y.1) := by
  have hk p : ContDiff ℝ ∞ (Function.uncurry (KP p)) :=
    contDiff_elapsedPhysicalShellKernel_joint backward hρ Δ Ψ b χout χsource β mi mo
      hout hsource his hS hA hi ho p.1 p.2
  let C := fun p ↦ jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l ↦ B l p) m
  obtain ⟨hC, hCs, hsum, hjet⟩ := summable_cutMatrixEntry_jet_majorant J hψ hsψ KP hk B hB hs hb
  choose Op hn ht _ hj using fun a c ↦ exists_commonSupport_shell_extensions
    (fun p ↦ K p a c) volume volume sI (J ⁻¹' tsupport ψ)
    (fun _ ↦ rfl) (fun _ ↦ rfl) C hC hCs (fun p ↦ hjet p a c)
  refine ⟨Op, ?_, ht, hj⟩
  have hsumC : (∑' p, C p) =
      jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l ↦ ∑' p, B l p) m := hsum
  simpa only [Fintype.card_fin, hsumC] using norm_matrixOperator_le_of_entry_bound Op _ hn

variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
include hJ

/-- Exact physical action of the supported elapsed kernel entry. The volume
change uses the same coordinate convention as the existing graph completion
(`app:ch_regular:eq:chain-tail`). -/
theorem kernelIntegral_supportedElapsedShellEntry_physical
    (j k : ℕ) (a c : Fin q) (f : ℝ × (Fin d → ℝ) → ℂ) (x : ℝ × (Fin d → ℝ)) :
    kernelIntegral (K (j, k) a c) volume f x =
      (ψ (J x) : ℂ) * ∫ y, KP (j, k) (J x) y a c * f (J.symm y) := by
  have he := hJ.integral_comp (graphInputCoordinates J).toHomeomorph.measurableEmbedding
    (fun y ↦ (ψ (J x) : ℂ) * KP (j, k) (J x) y a c * f (J.symm y))
  simpa only [kernelIntegral, supportedElapsedShellEntry, graphInputCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodComm_apply,
    ContinuousLinearEquiv.symm_apply_apply, Prod.swap, mul_assoc, integral_const_mul] using he

private theorem sum_kernelIntegral_elapsedShell_physical
    (p : ℕ × ℕ) (a : Fin q) (f : Fin q → Test d) (x : ℝ × (Fin d → ℝ)) :
    (∑ c, kernelIntegral (K p a c) volume (f c).val x) =
      (ψ (J x) : ℂ) * (∫ y, (KP p (J x) y).mulVec (physicalTestField J f y)) a := by
  simp_rw [kernelIntegral_supportedElapsedShellEntry_physical J backward hρ Δ Ψ b
    χout χsource β mi mo hout hsource his hS hA hi ho ψ hψ hsψ hJ, ← Finset.mul_sum]
  congr 1
  have hk : Continuous (KP p (J x)) :=
    (contDiff_elapsedPhysicalShellKernel_joint backward hρ Δ Ψ b χout χsource β mi mo
      hout hsource his hS hA hi ho p.1 p.2).continuous.comp (f := fun y : E ↦ (J x, y))
        (continuous_const.prodMk continuous_id)
  have hint c : Integrable (fun y ↦ KP p (J x) y a c * (f c).val (J.symm y)) :=
    (((matrixEntryEvaluation a c).continuous.comp hk).mul
      ((f c).property.1.continuous.comp J.symm.continuous)).integrable_of_hasCompactSupport
        ((f c).property.2.comp_homeomorph J.symm.toHomeomorph).mul_left
  have hv : Integrable (fun y ↦ (KP p (J x) y).mulVec (physicalTestField J f y)) :=
    (hk.matrix_mulVec (contDiff_physicalTestField J f).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hasCompactSupport_physicalTestField J f)
        (fun y hy ↦ by rw [image_eq_zero_of_notMem_tsupport hy]; simp))
  have he := (ContinuousLinearMap.proj a : (Fin q → ℂ) →L[ℂ] ℂ).integral_comp_comm hv
  exact (integral_finsetSum Finset.univ (fun c _ ↦ hint c)).symm.trans he

/-- The sum of the completed zeroth jets is exactly the supported physical
elapsed shell sum. The global scalar majorant is supplied by `GlobalMajorant`;
the local jet majorant is supplied by `KernelMajorants` and `CartesianJets`.
This is an identity of actual integrals, not an assumed uncut test action
(`app:ch_regular:eq:chain-tail`). -/
theorem sum_summedElapsedShell_zerothJet_physical
    (hSc : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ p (a c : Fin q) (i : JetIndex d m) x y, ‖kernelJet (K p a c) i x y‖ ≤ C p)
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀)
    (hb₀ : ∀ p x y, ‖KP p x y‖ ≤ C₀ p)
    (f : Fin q → Test d) (a : Fin q) (x : (Fin d → ℝ) × ℝ) :
    (∑ c, ∫ y, (∑' p, kernelJet (K p a c) (zeroIndex d m) x y) * (f c).val (y.2, y.1)) =
      (ψ (J (x.2, x.1)) : ℂ) *
        (∫ y, (∑' p, KP p (J (x.2, x.1)) y).mulVec (physicalTestField J f y)) a := by
  have hsum := hasSum_sum (s := Finset.univ) (fun c _ ↦
    hasSum_kernelIntegral_jet (fun p ↦ K p a c) volume C hs
      (fun p ↦ hb p a c) (f c) (zeroIndex d m) x)
  simp only [jet_zeroIndex] at hsum
  have hp := hasSum_elapsedPhysicalShellKernel_test backward ρ Δ Ψ b χout χsource β mi mo
    (fun p : ℕ × ℕ ↦ graphCutoff p.1) (fun p : ℕ × ℕ ↦ outputCutoff p.2)
    hSc hA.continuous hi.continuous ho.continuous
    (fun p ↦ (contDiff_graphCutoff p.1).continuous) (fun p ↦ (contDiff_outputCutoff p.2).continuous)
    (fun r p ↦ elapsedShellCarriers backward hρ b χout χsource β mi hout hsource his r p.1 p.2)
    (fun _ _ ↦ rfl) C₀ hs₀ hb₀ (physicalTestField J f)
    ((contDiff_physicalTestField J f).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_physicalTestField J f)) (J (x.2, x.1))
  simp_rw [sum_kernelIntegral_elapsedShell_physical J backward hρ Δ Ψ b χout χsource β mi mo
    hout hsource his hS hA hi ho ψ hψ hsψ hJ] at hsum
  exact hsum.unique ((Pi.hasSum.mp hp a).mul_left (ψ (J (x.2, x.1)) : ℂ))

include hρ hout hsource his hS hA hi ho

/-- The matrix extension's zeroth jet is the actual physical elapsed shell
action with the fixed cutoff. All input and output derivatives were constructed
from pointwise shell bounds; no integrated operator estimate or uncut test
action is a premise (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedShell_matrix_physical_extension
    (hSc : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ p, 0 ≤ B l p) (hs : ∀ l ≤ m, Summable (B l))
    (hb : ∀ p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ KP p z y) x v‖ ≤ B l p)
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀) (hb₀ : ∀ p x y, ‖KP p x y‖ ≤ C₀ p) :
    ∃ Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
        Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)),
      ‖matrixOperator Op‖ ≤ (q : ℝ) * q *
        (jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l ↦ ∑' p, B l p) m *
          compactSupportFactor volume volume sI sO) ∧
      ∀ (f : Fin q → Test d) (a : Fin q),
        (matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m) =ᵐ[volume]
          fun x ↦ (ψ (J (x.2, x.1)) : ℂ) *
            (∫ y, (∑' p, KP p (J (x.2, x.1)) y).mulVec (physicalTestField J f y)) a := by
  obtain ⟨Op, hn, _, hj⟩ := exists_elapsedShell_matrix_extension J backward hρ Δ Ψ b
    χout χsource β mi mo hout hsource his hS hA hi ho ψ hψ hsψ B hB hs hb
  have hk p : ContDiff ℝ ∞ (Function.uncurry (KP p)) :=
    contDiff_elapsedPhysicalShellKernel_joint backward hρ Δ Ψ b χout χsource β mi mo
      hout hsource his hS hA hi ho p.1 p.2
  obtain ⟨_, hCs, _, hjet⟩ := summable_cutMatrixEntry_jet_majorant J hψ hsψ KP hk B hB hs hb
  refine ⟨Op, hn, ?_⟩
  intro f a
  let P : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)) := completedJet m (zeroIndex d m)
  have he : (matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m) =
      ∑ c, (Op a c (ofTest 0 volume (f c))).val (zeroIndex d m) := by
    change P (matrixOperator Op (completedTestVector 0 f) a) = _
    rw [matrixOperator_apply, map_sum]
    rfl
  rw [he]
  have hj' : ∀ᵐ x ∂volume, ∀ c, (Op a c (ofTest 0 volume (f c))).val (zeroIndex d m) x =
      ∫ y, (∑' p, kernelJet (K p a c) (zeroIndex d m) x y) * (f c).val (y.2, y.1) :=
    ae_all_iff.mpr (fun c ↦ hj a c (f c) (zeroIndex d m))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun c ↦ (Op a c (ofTest 0 volume (f c))).val (zeroIndex d m)), hj'] with x hx hxx
  rw [hx]
  simp_rw [hxx]
  exact sum_summedElapsedShell_zerothJet_physical J backward hρ Δ Ψ b χout χsource β
    mi mo hout hsource his hS hA hi ho ψ hψ hsψ hJ hSc _ hCs hjet C₀ hs₀ hb₀ f a x

/-- Realize the summed elapsed shells in actual spacetime Fourier Hᵐ. The
explicit fixed cutoff/coordinate constant multiplies the same graded
`ρ^(m+e) L^bLoss (L/ρ)^N` bound. The only quantitative inputs are the literal
kernel-jet majorants from `KernelMajorants` and the crude global majorant
from `GlobalMajorant`. The physical cutoff remains displayed for subsequent
removal by `OutputSupport`; this theorem does not claim the unconditional
localization estimate (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedShell_fourier_realization_of_jet_majorants
    (hSc : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ p, 0 ≤ B l p) (hs : ∀ l ≤ m, Summable (B l))
    (hb : ∀ p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ KP p z y) x v‖ ≤ B l p)
    (C₀ : ℕ × ℕ → ℝ) (hs₀ : Summable C₀) (hb₀ : ∀ p x y, ‖KP p x y‖ ≤ C₀ p)
    {L : ℝ} (hρone : 1 ≤ ρ) (hL : 0 ≤ L) (e : ℝ) (bLoss N : ℕ)
    (D : ℕ → ℝ) (hD : ∀ l ≤ m, 0 ≤ D l)
    (hgrades : ∀ l ≤ m, (∑' p, B l p) ≤ D l * ρ ^ ((l : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N) :
    ∃ T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
      (∀ u, Pseudodifferential.MemVectorFourierSobolev (m : ℝ) (T u) ∧
        Pseudodifferential.vectorFourierSobolevNorm (m : ℝ) (T u) ≤
          (fourierComparisonConstant J m * ((q : ℝ) * q) *
            jetMajorant J (cutoffDerivativeProfile hψ hsψ) D m *
            compactSupportFactor volume volume sI sO) *
              ρ ^ ((m : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N * ‖u‖) ∧
      ∀ (f : Fin q → Test d) (a : Fin q),
        Pseudodifferential.finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
          fun x ↦ (ψ x : ℂ) * (∫ y, (∑' p, KP p x y).mulVec (physicalTestField J f y)) a := by
  obtain ⟨Op, hn, ht⟩ := exists_elapsedShell_matrix_physical_extension J backward hρ Δ Ψ b
    χout χsource β mi mo hout hsource his hS hA hi ho ψ hψ hsψ hJ hSc B hB hs hb C₀ hs₀ hb₀
  have hg := jetMajorant_le_grades J (cutoffDerivativeProfile_nonneg hψ hsψ) hD
    hρone hL (show (0 : ℝ) ≤ 1 by norm_num) e bLoss N
    (fun l hl ↦ (hgrades l hl).trans_eq (mul_one _).symm)
  simp only [mul_one] at hg
  refine ⟨matrixRealization J hJ Op, ?_, ?_⟩
  · intro u
    have hf := matrixRealization_fourier_bound J hJ Op u
    refine ⟨hf.1, hf.2.trans ?_⟩
    calc
      _ ≤ fourierComparisonConstant J m *
          ((q : ℝ) * q * (jetMajorant J (cutoffDerivativeProfile hψ hsψ)
            (fun l ↦ ∑' p, B l p) m * compactSupportFactor volume volume sI sO)) * ‖u‖ := by
        gcongr
        exact (fourierComparisonConstant_pos J m).le
      _ ≤ fourierComparisonConstant J m *
          ((q : ℝ) * q * ((jetMajorant J (cutoffDerivativeProfile hψ hsψ) D m *
            ρ ^ ((m : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N) *
              compactSupportFactor volume volume sI sO)) * ‖u‖ := by
        gcongr
        · exact (fourierComparisonConstant_pos J m).le
        · exact compactSupportFactor_nonneg _ _ _ _
      _ = _ := by ring
  · intro f a
    apply (matrixRealization_test_action J hJ Op f a).trans
    have h := (graphInputCoordinates_symm_measurePreserving J hJ).quasiMeasurePreserving.ae_eq_comp
      (ht f a)
    have he (p : (Fin d → ℝ) × ℝ) : J (p.2, p.1) = graphInputCoordinates J p := rfl
    simpa only [Function.comp_def, he, ContinuousLinearEquiv.apply_symm_apply] using h

end Extension
end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
