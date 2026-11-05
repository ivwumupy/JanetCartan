module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceOperator
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencySobolev
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.VectorDuality

/-!
# The protected full complex source

Join the selected characteristic source symbol to the elliptic source on a
fixed angular neighborhood. Neither mask nor either physical multiplier is
halved. This is the complex source before the separate real pairing.
Source: `app:ch_regular_base:sec:energy-construction`, `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open FiniteMasks FiniteMasks.ActualFamily Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral FinitePdo FiniteAssembly FourierIntegral LowBounds Pseudodifferential
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The actual selected matrix source plus the elliptic matrix source is
the identity at high frequency near the protected compact. Through the collar
the missing term is exactly the original radial low cutoff (`resolved-angular-tail`). -/
theorem exists_selectedSourceSymbols_elliptic_partition :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ∀ L ≥ f.radialThreshold,
      ∀ y ∈ closedBall x (4*f.physicalRadius), ∀ ξ : E, NormedSpace.normalize ξ ∈ V →
      let a := (∑ p, selectedSourceSymbol f p (2*L)
        ((physicalCoordinates (f.chart p).index).symm y)
        ((physicalCoordinates (f.chart p).index).symm ξ)) + ellipticSourceSymbol f hK L y ξ
      (a + (FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ξ) : ℂ) • (1 : CMat) = 1) ∧
        (4*L ≤ ‖ξ‖ → a = 1) := by
  obtain ⟨V, hV, hKV, hv⟩ := exists_ellipticSourceMask_partition_near f hK
  refine ⟨V, hV, hKV, ?_⟩
  intro L hL y hy ξ hξ a
  obtain ⟨hlow, hhi⟩ := hv L (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans hL)) ξ hξ
  dsimp only [a, ellipticSourceSymbol]
  simp_rw [selectedSourceSymbol_on_common_ball_enlarged f _ hL hy]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← add_smul, ← Complex.ofReal_add, ← add_smul,
    ← Complex.ofReal_add, hlow, Complex.ofReal_one, one_smul]
  exact ⟨rfl, fun h ↦ by rw [hhi h, Complex.ofReal_one, one_smul]⟩

/-- On the caller's actual compact of signed directions there is one
*symmetric* angular neighborhood of the full, unpaired plateau. No symmetry
of individual selected masks is required (`app:rem:exhaustive-signed-pairs`,
`sector-theorem-identity`). -/
theorem exists_signed_ellipticSourceMask_plateau {γ : ℝ}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) (SignedPairs.angularSet (d+1) γ) M) :
    ∃ V : Set E, IsOpen V ∧ SignedPairs.angularSet (d+1) γ ⊆ V ∧
      (∀ η ∈ V, -η ∈ V) ∧ ∀ L ≥ f.radialThreshold, ∀ ξ : E, NormedSpace.normalize ξ ∈ V →
        4*L ≤ ‖ξ‖ → (∑ p, dilatedConicMask (f.angularMask p) (2*L) ξ) +
          ellipticSourceMask f (SignedPairs.isCompact_angularSet _ _) L ξ = 1 := by
  obtain ⟨V, hV, hKV, hp⟩ := exists_ellipticSourceMask_partition_near f
    (SignedPairs.isCompact_angularSet _ _)
  refine ⟨V ∩ (fun η : E ↦ -η) ⁻¹' V, hV.inter (hV.preimage continuous_neg),
    fun η hη ↦ ⟨hKV hη, hKV (SignedPairs.neg_mem_angularSet hη)⟩,
    fun η hη ↦ ⟨hη.2, by simpa only [mem_preimage, neg_neg] using hη.1⟩, ?_⟩
  intro L hL ξ hξ
  exact (hp L (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans hL)) ξ hξ.1).2

/-- Literal forward and reverse Fourier composition of the new source,
including both existing physical masks (`resolved-angular-tail`, `measured-adjoint`). -/
theorem ellipticSourcePDO_fourier_composition (L : ℝ) :
    let b := ellipticSourceMask f hK L
    let hb := (ellipticSourceMask_properties f hK L).1.continuous
    let hbb := fun ξ ↦ (Real.norm_of_nonneg ((ellipticSourceMask_properties f hK L).2 ξ).1).trans_le
      ((ellipticSourceMask_properties f hK L).2 ξ).2
    let F := scalarPhysicalFrequencyOperator (r := d+1) b hb hbb
    let O := sourceCutMultiplier (r := d+1) f.outputMask f.outputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
    let I := sourceCutMultiplier (r := d+1) f.inputMask f.inputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
    ellipticSourcePDO f hK L = O.comp (F.comp I) ∧
      (ellipticSourcePDO f hK L).adjoint = I.comp (F.comp O) := by
  intro b hb hbb F O I
  have he : ellipticSourcePDO f hK L = O.comp (F.comp I) :=
    maskedPhysicalPDO_scalarFrequency_eq b hb hbb
      (hasTemperateGrowth_complex_dilatedConicMask (ellipticAngularMask_spec f hK).1 _)
      _ _ f.outputMask_smooth.continuous f.inputMask_smooth _ _
  refine ⟨he, ?_⟩
  rw [he, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    show F.adjoint = F from scalarPhysicalFrequencyOperator_adjoint b hb hbb]
  simp only [O, I, sourceCutMultiplier_adjoint, ContinuousLinearMap.comp_assoc]

/-- The elliptic source preserves every integer Sobolev order in both
orientations, with constants independent of the radial threshold and fields
(`resolved-angular-tail`, `measured-adjoint`). -/
theorem exists_ellipticSourcePDO_order_zero_constants :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ L : ℝ, ∀ n : ℕ, ∀ V : H →L[ℂ] H,
      (V = ellipticSourcePDO f hK L ∨ V = (ellipticSourcePDO f hK L).adjoint) →
      (∀ u, MemVectorFourierSobolev (n : ℝ) u → MemVectorFourierSobolev (n : ℝ) (V u) ∧
        vectorFourierSobolevNorm (n : ℝ) (V u) ≤ C n * vectorFourierSobolevNorm (n : ℝ) u) ∧
      ∀ u, MemVectorFourierSobolev (-(n : ℝ)) (V u) ∧ vectorFourierSobolevNorm (-(n : ℝ)) (V u) ≤
        ((d+1 : ℝ)*(d+1)*C n)*vectorFourierSobolevNorm (-(n : ℝ)) u := by
  let ho := fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2
  let hs := fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2
  choose Co hCo hO using fun n ↦ exists_sourceCutMultiplier_fourierSobolev_bound (r := d+1)
    _ f.outputMask_smooth f.outputMask_compact ho n
  choose Cs hCs hS using fun n ↦ exists_sourceCutMultiplier_fourierSobolev_bound (r := d+1)
    _ f.inputMask_smooth f.inputMask_compact hs n
  refine ⟨fun n ↦ Co n * Cs n, fun n ↦ mul_nonneg (hCo n) (hCs n), ?_⟩
  intro L n
  let b := ellipticSourceMask f hK L
  have hb := ellipticSourceMask_properties f hK L
  have hbb (ξ : E) : ‖b ξ‖ ≤ 1 := (Real.norm_of_nonneg (hb.2 ξ).1).trans_le (hb.2 ξ).2
  obtain ⟨hf, ha⟩ := ellipticSourcePDO_fourier_composition f hK L
  have hpos (V : H →L[ℂ] H)
      (hV : V = ellipticSourcePDO f hK L ∨ V = (ellipticSourcePDO f hK L).adjoint) (u : H)
      (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev (n : ℝ) (V u) ∧
        vectorFourierSobolevNorm (n : ℝ) (V u) ≤ (Co n * Cs n)*vectorFourierSobolevNorm (n : ℝ) u := by
    rcases hV with rfl | rfl
    · rw [hf]
      obtain ⟨hsu, hsn⟩ := hS n u hu
      obtain ⟨hm, hn⟩ := scalarPhysicalFrequencyOperator_fourierSobolev_bound b hb.1.continuous hbb
        (n : ℝ) _ hsu
      obtain ⟨hom, hon⟩ := hO n _ hm
      exact ⟨hom, (hon.trans (mul_le_mul_of_nonneg_left (hn.trans hsn) (hCo n))).trans_eq
        (mul_assoc _ _ _).symm⟩
    · rw [ha]
      obtain ⟨hou, hon⟩ := hO n u hu
      obtain ⟨hm, hn⟩ := scalarPhysicalFrequencyOperator_fourierSobolev_bound b hb.1.continuous hbb
        (n : ℝ) _ hou
      obtain ⟨hsm, hsn⟩ := hS n _ hm
      exact ⟨hsm, (hsn.trans (mul_le_mul_of_nonneg_left (hn.trans hon) (hCs n))).trans_eq (by ring)⟩
  intro V hV
  have hadj : V.adjoint = ellipticSourcePDO f hK L ∨ V.adjoint = (ellipticSourcePDO f hK L).adjoint := by
    rcases hV with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (ContinuousLinearMap.adjoint_adjoint _)
  refine ⟨hpos V hV, fun u ↦ ?_⟩
  simpa only [zero_mul, add_zero, mul_one, Nat.cast_add, Nat.cast_one] using
    negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg n) (Nat.cast_nonneg n)
      (mul_nonneg (hCo n) (hCs n)) (le_refl (0 : ℝ)) V
      (fun v hv ↦ by simpa only [zero_mul, add_zero] using hpos V.adjoint hadj v hv) u

end JanetCartan.RegularSector.EllipticComplement
