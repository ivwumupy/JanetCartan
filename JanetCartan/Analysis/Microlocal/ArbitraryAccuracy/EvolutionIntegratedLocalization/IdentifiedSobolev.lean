module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedSobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OutputSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.RealizedIdentities

/-!
# The Sobolev bound belongs to the original bounded elapsed operator

This assembles the completed shell action, Fourier comparison, actual strong
identification and physical cutoff removal. Quantitative inputs are the
pointwise shell-jet majorants produced by `KernelMajorants` and the crude
global majorant produced by `GlobalMajorant`, not an integrated operator
bound. Their uniform primitive finite-family instantiation remains explicit.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells CartesianJets
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization.SobolevRealization Pseudodifferential
open LowBounds LowBounds.FrequencyCutoff FiniteChain.Retarded.KernelSobolev
variable {d q m : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

/-- The literal localized elapsed integral and its Hilbert adjoint satisfy
the Fourier Hᵐ estimate derived from their actual shell jets. Both outside
localizers and the original masks are retained. Finite realizations, LOW
bounds, measurability and per-time strong limits are precisely the graph
producer's outputs. Kernel majorants are supplied by `KernelMajorants` /
`GlobalMajorant`; `exists_finiteFamily_elapsed_output_cutoff` supplies `ψ`.
No uncut test action, integrated operator bound or cutoff-removal identity
is assumed. This closes the operator-identification step, conditional on
instantiating those proved quantitative kernel producers with common
primitive profiles (`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem exists_identified_elapsedGraphIntegral_fourier_bound
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    (hSc : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hS : ∀ r ∈ Icc 0 Δ, ∀ u ξ, ξ ≠ 0 →
      ContDiffAt ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (u, ξ))
    (hA : ∀ backward, ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    {Jphase W : Set (SymbolBudgets.TwoTimePoint d)}
    (hJphase : IsClosed Jphase) (hW : IsOpen W) (hJW : Jphase ⊆ W)
    (hPhase : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    (hPhaseSupport : ∀ r ∈ Icc 0 Δ, ∀ u z ξ,
      elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
        ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ Jphase)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hψmask : ∀ (backward : Bool) x,
      x ∈ (if backward then tsupport χsource else tsupport χout) → ψ x = 1)
    (hψmo : ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1)
    (F : Set E) (hF : IsClosed F) (hzero : (0 : E) ∉ F) (hβF : tsupport β ⊆ F)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (A : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (Treg : ℕ → ℝ → H →L[ℂ] H)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {LOW : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (C₀ : Bool → (ℕ × ℕ) → ℝ) (hs₀ : ∀ backward, Summable (C₀ backward))
    (hb₀ : ∀ backward p x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
      mi mo (graphCutoff p.1) (outputCutoff p.2) x y‖ ≤ C₀ backward p)
    (B : Bool → ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ backward l, l ≤ m → ∀ p, 0 ≤ B backward l p)
    (hs : ∀ backward l, l ≤ m → Summable (B backward l))
    (hb : ∀ backward p x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m, ∀ v : Fin l → E,
      (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ l (fun z ↦ elapsedPhysicalShellKernel backward
        ρ Δ Ψ b χout χsource β mi mo (graphCutoff p.1) (outputCutoff p.2) z y) x v‖ ≤ B backward l p)
    (e : ℝ) (bLoss N : ℕ) (D : Bool → ℕ → ℝ) (hD : ∀ backward l, l ≤ m → 0 ≤ D backward l)
    (hgrades : ∀ backward l, l ≤ m → (∑' p, B backward l p) ≤
      D backward l * ρ ^ ((l : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N) :
    ∃ Mi Mo Q : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ‖Q‖ ≤ Δ * LOW ∧ (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
      (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
      ∀ (backward : Bool) u,
        MemVectorFourierSobolev (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ≤
          (fourierComparisonConstant J m * ((q : ℝ) * q) *
            jetMajorant J (cutoffDerivativeProfile hψ hsψ) (D backward) m *
            compactSupportFactor volume volume
              ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' (Prod.fst '' tsupport mi))
              (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))) *
                ρ ^ ((m : ℝ) + e) * L ^ bLoss * (L / ρ) ^ N * ‖u‖ := by
  have hρ0 : ρ ≠ 0 := (zero_lt_one.trans_le hρ).ne'
  obtain ⟨Mi, Mo, Q, hMi, hMo, hQnorm, hQ, hQA, _, hident⟩ :=
    exists_localized_elapsedGraphIntegral_shell_identification hρ0 Δ hΔ Ψ b χout χsource β
      mi mo hi ho.continuous his hos hout hsource hSc (fun backward ↦ (hA backward).continuous)
      hS
      (fun backward r _ ↦ (hA backward).comp (contDiff_const.prodMk contDiff_id))
      F hF hzero hβF χ hχeq Treg hreal hrealAdj hm hmAdj hbound hlim hlimAdj
  refine ⟨Mi, Mo, Q, hMi, hMo, hQnorm, hQ, hQA, ?_⟩
  intro backward
  let T := fun r ↦ if backward then (elapsedGraph Ψ b χout χsource β r).adjoint
    else elapsedGraph Ψ b χout χsource β r
  let R := fun j r ↦ if backward then (Treg j r).adjoint else Treg j r
  have hrm : ∀ j u, AEStronglyMeasurable (fun r ↦ R j r u) (volume.restrict (Icc 0 Δ)) := by
    cases backward <;> assumption
  have hrb : ∀ j r, r ∈ Icc 0 Δ → ‖R j r‖ ≤ LOW := by
    cases backward
    · exact hbound
    · simpa only [R, ite_true, ContinuousLinearMap.adjoint.norm_map] using hbound
  have hrl : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ R j r u) atTop (𝓝 (T r u)) := by
    cases backward <;> assumption
  have htm (u : H) : AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ R j r u) (fun j ↦ hrm j u)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hrl r hr u
  have hLOW : 0 ≤ LOW := (norm_nonneg (Treg 0 0)).trans (hbound 0 0 ⟨le_rfl, hΔ⟩)
  have htb : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ LOW := by
    intro r hr
    apply ContinuousLinearMap.opNorm_le_bound _ hLOW
    intro u
    apply le_of_tendsto (hrl r hr u).norm
    exact Eventually.of_forall (fun j ↦ (R j r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hrb j r hr) (norm_nonneg u)))
  have hcutr (r : ℝ) (hr : r ∈ Icc 0 Δ) (u : H) :
      sourceCutMultiplier ψ hψ.continuous hψb (T r u) = T r u :=
    sourceCutMultiplier_orientedElapsedGraph_eq backward r Ψ b χout χsource β ψ
      hψ.continuous hψb (hψmask backward) χ (fun j ↦ Treg j r)
      (fun j ↦ hreal j r hr) (fun j ↦ hrealAdj j r hr) (hrl r hr) u
  have hQI (u : H) : (if backward then Q.adjoint else Q) u =
      strongIntegral T Δ LOW htm htb u := by
    cases backward
    · exact hQ u
    · exact hQA u
  let A : H →L[ℂ] H := (1 - Mo).comp ((if backward then Q.adjoint else Q).comp Mi)
  have hcut (u : H) : sourceCutMultiplier ψ hψ.continuous hψb (A u) = A u := by
    change sourceCutMultiplier ψ hψ.continuous hψb ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) =
      (1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))
    rw [hQI]
    exact sourceCutMultiplier_localized_strongIntegral_eq T Δ LOW htm htb Mi Mo ρ mo hMo
      ψ hψ.continuous hψb hψmo hcutr u
  obtain ⟨S, hSob, htest⟩ := exists_elapsedShell_fourier_realization_of_supported_jet_majorants J hJ
    backward hρ hL Δ Ψ b χout χsource β mi mo hout hsource his (hA backward) hi ho
    hJphase hW hJW hPhase hPhaseSupport ψ hψ hsψ
    (B backward) (hB backward) (hs backward) (hb backward) (C₀ backward) (hs₀ backward)
    (hb₀ backward) e bLoss N (D backward) (hD backward) (hgrades backward)
  have hAS : S = A := by
    apply EvolutionLocalization.eq_of_physical_test_action J hJ
    intro f a
    have ha : A (physicalTestToL2 J hJ f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (∫ y, (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
          mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec (physicalTestField J f y)) := by
      rw [physicalTestToL2_eq_graphTestToLp]
      exact hident backward (C₀ backward) (hs₀ backward) (fun j k ↦ hb₀ backward (j, k))
        (physicalGraphTest J f)
    have hc := sourceCutMultiplier_coeFn ψ hψ.continuous hψb (A (physicalTestToL2 J hJ f))
    rw [hcut] at hc
    have hac : A (physicalTestToL2 J hJ f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        ((ψ x : ℂ) • ∫ y, (∑' p : ℕ × ℕ, elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
          mi mo (graphCutoff p.1) (outputCutoff p.2) x y).mulVec (physicalTestField J f y)) := by
      filter_upwards [hc, ha] with x hx hy
      rw [hx, hy]
      rfl
    exact (htest f a).trans (((finiteL2CoordinateIsometry_ae_iff volume _ _).mp hac a).symm)
  intro u
  simpa only [hAS, A, ContinuousLinearMap.comp_apply] using hSob u

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
