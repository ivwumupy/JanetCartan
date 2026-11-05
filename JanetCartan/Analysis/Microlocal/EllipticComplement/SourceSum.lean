module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.ProtectedSource
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification.Fourier

/-!
# One masked Fourier realization of the full complex source

This is the unpaired sum at exactly the original enlarged threshold. It can
be used in the complete source discrepancy without assuming that the
choice-defined canonical PDO is additive in arbitrary amplitudes.
Source: `app:ch_regular_base:prop:complete-residual`, `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open FiniteMasks FiniteMasks.ActualFamily Characteristic.EvolutionIntegral
open FiniteAssembly FourierIntegral LowBounds
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The angular symbol of the completed *complex* source: a bounded smooth
partition globally and a plateau near the protected compact only
(`app:ch_regular_base:thm:sector`). -/
def fullSourceAngularMask (η : E) : ℝ := (∑ p, f.angularMask p η) + ellipticAngularMask f hK η

/-- The angular mask used by the normalized complete source has compact
support before reflection. Both summands use the same selected family
(`app:ch_regular_base:thm:sector`, `resolved-angular-tail`). -/
theorem hasCompactSupport_fullSourceAngularMask :
    HasCompactSupport (fullSourceAngularMask f hK) := by
  have h : HasCompactSupport (∑ p, f.angularMask p) :=
    HasCompactSupport.finset_sum fun p _ ↦ f.angularMask_compact p
  have he : fullSourceAngularMask f hK = (∑ p, f.angularMask p) + ellipticAngularMask f hK := by
    funext η
    simp only [fullSourceAngularMask, Pi.add_apply, Finset.sum_apply]
  rw [he]
  exact h.add (ellipticAngularMask_spec f hK).2.1

/-- All properties of the full angular mask needed for its terminal Fourier
multiplier; it is one as a germ near `K` (`resolved-angular-tail`). -/
theorem fullSourceAngularMask_properties :
    ContDiff ℝ ∞ (fullSourceAngularMask f hK) ∧
      (∀ η, fullSourceAngularMask f hK η ∈ Icc (0 : ℝ) 1) ∧
      K ⊆ interior {η | fullSourceAngularMask f hK η = 1} := by
  have hb := ellipticAngularMask_spec f hK
  refine ⟨(ContDiff.sum fun p _ ↦ f.angularMask_smooth p).add hb.1, ?_, hb.2.2.2.1⟩
  intro η
  exact ⟨add_nonneg (Finset.sum_nonneg fun p _ ↦ (f.angularMask_range p η).1) (hb.2.2.1 η).1,
    by unfold fullSourceAngularMask; linarith [(hb.2.2.1 η).2]⟩

/-- The sum of the two canonical source operators is exactly the single
original-coordinate masked PDO of the full angular mask. This preserves
physical-frequency normalization and the input/output multiplier order;
no symmetry or plus-pair normalization is imposed (`prop:complete-residual`). -/
theorem selectedFiniteSourcePDO_add_ellipticSourcePDO {L : ℝ} (hL : f.radialThreshold ≤ L) :
    selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L =
      maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ))
        (fun _ ξ ↦ (dilatedConicMask (fullSourceAngularMask f hK) (2*L) ξ : ℂ) • (1 : CMat)) := by
  let a := fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) (2*L) ξ
  let b := ellipticSourceMask f hK L
  let c := dilatedConicMask (fullSourceAngularMask f hK) (2*L)
  have hac : Continuous a := continuous_finsetSum _ fun p _ ↦
    (contDiff_dilatedConicMask (f.angularMask_smooth p) _).continuous
  have hbc : Continuous b := (ellipticSourceMask_properties f hK L).1.continuous
  have hfull := fullSourceAngularMask_properties f hK
  have hcc : Continuous c := (contDiff_dilatedConicMask hfull.1 _).continuous
  have ha (ξ : E) : ‖a ξ‖ ≤ 1 := by
    have h := actualFamily_sum_dilatedConicMask_mem_Icc (withEnlargedThreshold f L hL) ξ
    exact (Real.norm_of_nonneg h.1).trans_le h.2
  have hb (ξ : E) : ‖b ξ‖ ≤ 1 :=
    (Real.norm_of_nonneg ((ellipticSourceMask_properties f hK L).2 ξ).1).trans_le
      ((ellipticSourceMask_properties f hK L).2 ξ).2
  have hc (ξ : E) : ‖c ξ‖ ≤ 1 := by
    have h := conicMask_mem_Icc hfull.2.1 ((2*L)⁻¹ • ξ)
    exact (Real.norm_of_nonneg h.1).trans_le h.2
  have hab : ∀ ξ, a ξ + b ξ = c ξ := by
    intro ξ
    simp only [a, b, c, fullSourceAngularMask, ellipticSourceMask, dilatedConicMask, conicMask,
      CompatibleResponse.radialSourceCutoff, Finset.mul_sum, mul_add]
  let g (i : Bool) := if i then a else b
  have hgc (i : Bool) : Continuous (g i) := by cases i <;> first | exact hac | exact hbc
  have hgb (i : Bool) (ξ : E) : ‖g i ξ‖ ≤ 1 := by cases i <;> first | exact ha ξ | exact hb ξ
  have hsum : (fun ξ ↦ ∑ i, g i ξ) = c := by funext ξ; simpa [g, Fintype.sum_bool] using hab ξ
  have hsb (ξ : E) : ‖∑ i, g i ξ‖ ≤ 1 := (congrArg norm (congrFun hsum ξ)).trans_le (hc ξ)
  have hF : scalarPhysicalFrequencyOperator (r := d+1) a hac ha +
      scalarPhysicalFrequencyOperator b hbc hb = scalarPhysicalFrequencyOperator c hcc hc := by
    have h := scalarPhysicalFrequencyOperator_sum (q := d+1) g hgc hgb hsb
    simp only [Fintype.sum_bool] at h
    have he : (fun ξ ↦ a ξ + b ξ) = c := funext hab
    simpa only [show g true = a from rfl, show g false = b from rfl, he] using h
  let ho := fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2
  let hs := fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2
  let O := sourceCutMultiplier (r := d+1) f.outputMask f.outputMask_smooth.continuous ho
  let I := sourceCutMultiplier (r := d+1) f.inputMask f.inputMask_smooth.continuous hs
  have hP : selectedFiniteSourcePDO f L = O.comp ((scalarPhysicalFrequencyOperator a hac ha).comp I) :=
    (selectedFiniteSourcePDO_eq_actualAngularPDO f L hL).trans
      (actualAngularPDO_eq_fourier_composition (r := d+1) (withEnlargedThreshold f L hL)).2.2.1
  have hE : ellipticSourcePDO f hK L = O.comp ((scalarPhysicalFrequencyOperator b hbc hb).comp I) :=
    (ellipticSourcePDO_fourier_composition f hK L).1
  rw [hP, hE, maskedPhysicalPDO_scalarFrequency_eq c hcc hc
    (hasTemperateGrowth_complex_dilatedConicMask hfull.1 _) _ _
    f.outputMask_smooth.continuous f.inputMask_smooth ho hs, ← hF]
  ext1 u
  exact (O.map_add _ _).symm

end JanetCartan.RegularSector.EllipticComplement
