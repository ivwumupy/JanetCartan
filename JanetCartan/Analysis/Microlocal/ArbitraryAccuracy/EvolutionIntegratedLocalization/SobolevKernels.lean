module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellKernels
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.CartesianJets

/-!
# Supported Cartesian kernels of the actual elapsed shells

For `app:ch_regular:eq:chain-tail`, the existing Cartesian completion needs
smoothness in both external bases, not only output differentiation. Compact
primitive integration proves that smoothness here. The two physical masks
supply common base carriers for every elapsed time and frequency shell. The
phase is required to be smooth only off the graph-frequency origin.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.KernelSobolev
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => JointVariables E
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
attribute [local fun_prop] ContDiff.inner ContDiffAt.inner
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The original two masks and input localizer give the same base carriers
for all elapsed shells, including in the literal adjoint orientation.
Consumer: `supportedElapsedShellEntry` (`app:ch_regular:eq:chain-tail`). -/
def elapsedShellCarriers (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0)
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi : LocalizerSymbol (d + 1))
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (hi : HasCompactSupport mi) (r : ℝ) (j k : ℕ) :
    RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (graphCutoff j) (outputCutoff k) :=
  physicalInputCarriers
    (cutoffPairCarriers (orientedElapsedAmplitude backward b χout χsource β r) mi
      (tsupport χout ×ˢ tsupport χsource) (Prod.fst '' tsupport mi)
      (Prod.snd '' tsupport mi) (hout.prod hsource)
      (hi.image continuous_fst) (hi.image continuous_snd)
      (by
        intro u z ξ hz
        have he : elapsedAmplitude b χout χsource β r u z ξ = 0 := by
          apply elapsedAmplitude_eq_zero_of_mask
          by_cases hu : u ∈ tsupport χout
          · exact Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport (fun h ↦ hz ⟨hu, h⟩)))
          · exact Or.inl (image_eq_zero_of_notMem_tsupport hu)
        cases backward <;> simp [orientedElapsedAmplitude, he])
      (by
        intro y η h
        exact image_eq_zero_of_notMem_tsupport
          (fun hh ↦ h ⟨⟨(y, η), hh, rfl⟩, ⟨(y, η), hh, rfl⟩⟩)) j k) hρ

private theorem contDiff_parameter_jointIntegrand
    (backward : Bool) (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude (d + 1) q)
    (mi mo : LocalizerSymbol (d + 1)) (χA χo : E → ℝ)
    (hS : ∀ r u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞
      (fun p : ℝ × (E × E) ↦ S p.1 p.2.1 p.2.2) (r, u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦ A p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : E) ∉ tsupport χA) :
    ContDiff ℝ ∞ (fun p : (ℝ × (E × E)) × P ↦
      regularizedJointIntegrand backward (S p.1.1) (A p.1.1) mi mo χA χo
        p.1.2.1 p.1.2.2 p.2) := by
  change E × E → ℝ at mi mo
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2.2.1 = 0
  · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ ↦ (0 : Matrix (Fin q) (Fin q) ℂ))
    have hn : ∀ᶠ z : (ℝ × (E × E)) × P in 𝓝 p, z.2.2.1 ∉ tsupport χA :=
      ((isClosed_tsupport χA).isOpen_compl.preimage (by fun_prop)).mem_nhds (by simpa [hp])
    filter_upwards [hn] with z hz
    simp [regularizedJointIntegrand, regularizedJointAmplitude,
      image_eq_zero_of_notMem_tsupport hz]
  · have hs : ContDiffAt ℝ ∞ (fun z : (ℝ × (E × E)) × P ↦
        S z.1.1 z.2.1.1 z.2.2.1) p :=
      (hS p.1.1 p.2.1.1 p.2.2.1 hp).comp p
        (contDiffAt_fst.fst.prodMk (contDiffAt_snd.fst.fst.prodMk contDiffAt_snd.snd.fst))
    have ha : ContDiffAt ℝ ∞ (fun z : (ℝ × (E × E)) × P ↦
        A z.1.1 z.2.1.1 z.2.1.2 z.2.2.1) p := hA.contDiffAt.comp p
      (contDiffAt_fst.fst.prodMk (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd.fst))
    have hphase : ContDiffAt ℝ ∞ (fun z : (ℝ × (E × E)) × P ↦
        jointPhase backward (S z.1.1) z.1.2.1 z.1.2.2 z.2) p := by
      cases backward <;>
        simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase] <;>
        fun_prop
    have hb : ContDiff ℝ ∞ (fun z : (ℝ × (E × E)) × P ↦
        χA z.2.2.1 * χo z.2.2.2.2 * (1 - mo (z.1.2.1, z.2.2.2.2)) *
          mi (z.1.2.2, z.2.2.2.1)) := by fun_prop
    exact ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hphase)).cexp).smul
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hb.contDiffAt).smul ha)

/-- Joint smoothness of the literal bounded elapsed shell follows from the
original joint primitive regularity and compact masks. In particular no
smoothness of an unregularized kernel or integrated operator is a premise.
Consumer: the Cartesian Sobolev extension (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_elapsedPhysicalShellKernel_joint
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (his : HasCompactSupport mi)
    (hS : ∀ r u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞
      (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2) (r, u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo) (j k : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (elapsedPhysicalShellKernel backward ρ Δ Ψ b
      χout χsource β mi mo (graphCutoff j) (outputCutoff k))) := by
  let c := elapsedShellCarriers backward hρ b χout χsource β mi hout hsource his
  let f := fun p : (ℝ × (E × E)) × P ↦ regularizedJointIntegrand backward
    (elapsedPhase Ψ p.1.1) (orientedElapsedAmplitude backward b χout χsource β p.1.1)
    (fun z ↦ mi (z.1, ρ⁻¹ • z.2)) (fun z ↦ mo (z.1, ρ⁻¹ • z.2))
    (graphCutoff j) (outputCutoff k) p.1.2.1 p.1.2.2 p.2
  have hf : ContDiff ℝ ∞ f := contDiff_parameter_jointIntegrand backward _ _ _ _ _ _ hS hA
    (hi.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹)))
    (ho.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹)))
    (contDiff_graphCutoff j) (contDiff_outputCutoff k) (zero_notMem_tsupport_graphCutoff j)
  have hz : ∀ z p, p ∉ (c 0 j k).jointCarrier → f (z, p) = 0 := by
    intro z p hp
    exact (c z.1 j k).integrand_zero backward (elapsedPhase Ψ z.1) _ z.2.1 z.2.2 p
      (fun h ↦ hp h.1)
  have hk : ContDiff ℝ ∞ (fun z : ℝ × (E × E) ↦
      jointNormalization (d + 1) • ∫ p, f (z, p)) :=
    (contDiff_integral_commonCarrier (μ := volume) hf
      (c 0 j k).compact_jointCarrier hz).const_smul _
  have hkr : ContDiff ℝ ∞ (fun p : (E × E) × ℝ ↦ regularizedJointKernel backward
      (elapsedPhase Ψ p.2) (orientedElapsedAmplitude backward b χout χsource β p.2)
      (fun z ↦ mi (z.1, ρ⁻¹ • z.2)) (fun z ↦ mo (z.1, ρ⁻¹ • z.2))
      (graphCutoff j) (outputCutoff k) p.1.1 p.1.2) :=
    hk.comp (f := fun p : (E × E) × ℝ ↦ (p.2, p.1))
      (contDiff_snd.prodMk contDiff_fst)
  change ContDiff ℝ ∞ (fun p : E × E ↦ ∫ r in Icc 0 Δ,
    regularizedJointKernel backward (elapsedPhase Ψ r)
      (orientedElapsedAmplitude backward b χout χsource β r)
      (fun z ↦ mi (z.1, ρ⁻¹ • z.2)) (fun z ↦ mo (z.1, ρ⁻¹ • z.2))
      (graphCutoff j) (outputCutoff k) p.1 p.2)
  rw [← contDiffOn_univ]
  exact JanetCartan.contDiffOn_compactParameterIntegral (U := univ) (V := univ)
    isOpen_univ isOpen_univ isCompact_Icc (subset_univ _) hkr.contDiffOn

/-- The elapsed kernel keeps the original source-localizer base support.
No frequency or time endpoint is dropped (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedPhysicalShellKernel_zero_off_input
    (backward : Bool) (ρ Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : E → ℝ) (x y : E) (hy : y ∉ Prod.fst '' tsupport mi) :
    elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo χA χo x y = 0 := by
  have hz (η : E) : mi (y, η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy ⟨(y, η), h, rfl⟩)
  simp [elapsedPhysicalShellKernel, regularizedJointKernel, regularizedJointIntegrand,
    regularizedJointAmplitude, hz]

section Supported
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

/-- A supported Cartesian matrix entry of the literal elapsed shell. The
auxiliary output cutoff is retained explicitly; it is not silently removed
from finite output-frequency kernels (`app:ch_regular:eq:chain-tail`). -/
def supportedElapsedShellEntry (j k : ℕ) (a c : Fin q) : SupportedSmoothKernel d d where
  toFun x y := (ψ (J x) : ℂ) * elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
    mi mo (graphCutoff j) (outputCutoff k) (J x) (J (y.2, y.1)) a c
  smooth := contDiff_cutMatrixEntry_coordinates J _
    (contDiff_elapsedPhysicalShellKernel_joint backward hρ Δ Ψ b χout χsource β mi mo
      hout hsource his hS hA hi ho j k) ψ hψ a c
  inputSupport := (fun y ↦ J (y.2, y.1)) ⁻¹' (Prod.fst '' tsupport mi)
  outputSupport := J ⁻¹' tsupport ψ
  compact_inputSupport :=
    ((Homeomorph.prodComm _ _).trans J.toHomeomorph).isCompact_preimage.mpr
      (his.image continuous_fst)
  compact_outputSupport := J.toHomeomorph.isCompact_preimage.mpr hsψ
  zero_off_input x y hy := by
    rw [elapsedPhysicalShellKernel_zero_off_input backward ρ Δ Ψ b χout χsource β
      mi mo _ _ _ _ hy]
    simp
  zero_off_output x y hx := by
    have hz : ψ (J x) = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [hz, Complex.ofReal_zero, zero_mul]

end Supported

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
