module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PrimitiveInverse

/-!
# Joint coefficient and full-covector derivatives of the retained inverse

The physical-slice estimate in `AlgebraicSymbols.PrimitiveInverse` does not
control covariable derivatives. Here the same coefficient function is kept
joint, on the same supplied spectral interval. No interval is selected or
shrunk. These are prerequisites for the branch-three symbol grades consumed by
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`, in
`app:ch_regular:eq:high-amplitude` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicSymbols
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- The literal `bminus` before substituting the coefficient field. Both the
coefficient and the full covector remain variables, including the off-root
time component (`app:ch_regular_base:eq:complement-inverse`). -/
def coefficientBminus (i r c : Fin (d + 1)) (H : Coeff × Euclidean d → ℝ)
    (p : Coeff × E) : CMat :=
  (minorComplementInverse
    (coefficientRootPencil (coordinateSplit i) H (p.1, spatialPart p.2))
    (pencil p.1 ((coordinateSplit i).symm (1, 0))) r c
    (p.2 0 - H (p.1, spatialPart p.2))).map Complex.ofReal

/-- Exact substitution of the original coefficient field into the joint
inverse, for the SAME root (`app:ch_regular_base:eq:complement-inverse`). -/
theorem bminus_fieldRoot_eq_coefficientBminus (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) (Q : E → Coeff) (y ξ : E) :
    bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ =
      coefficientBminus i r c H (Q (physicalCoordinates i y), ξ) := rfl

/-- The compact full-covector carrier for the already retained interval.
The time frequency is `H(A,η)+e`, with the original `|e| ≤ ε` condition
(`app:ch_regular_base:eq:complement-inverse`). -/
def coefficientSpectralCarrier (KA : Set Coeff) (Kη : Set (Euclidean d))
    (H : Coeff × Euclidean d → ℝ) (ε : ℝ) : Set (Coeff × E) :=
  {p | (p.1, spatialPart p.2) ∈ KA ×ˢ Kη ∧
    |p.2 0 - H (p.1, spatialPart p.2)| ≤ ε}

/-- Compactness of the whole retained spectral carrier, before restricting
to any physical slice (`app:ch_regular:eq:high-amplitude`). -/
theorem isCompact_coefficientSpectralCarrier
    {KA : Set Coeff} (hKA : IsCompact KA)
    {Kη : Set (Euclidean d)} (hKη : IsCompact Kη)
    (H : Coeff × Euclidean d → ℝ) (hH : ContinuousOn H (KA ×ˢ Kη)) (ε : ℝ) :
    IsCompact (coefficientSpectralCarrier KA Kη H ε) := by
  let S := (KA ×ˢ Kη) ×ˢ closedBall (0 : ℝ) ε
  let J : (Coeff × Euclidean d) × ℝ → Coeff × E :=
    fun p ↦ (p.1.1, timeSpacePoint (H p.1 + p.2) p.1.2)
  have hS : IsCompact S := (hKA.prod hKη).prod (isCompact_closedBall _ _)
  have hJ : ContinuousOn J S :=
    continuousOn_fst.fst.prodMk
      ((coordinateSplit 0).symm.continuous.comp_continuousOn
        (((hH.comp continuousOn_fst (fun _ hp ↦ hp.1)).add continuousOn_snd).prodMk
          continuousOn_fst.snd))
  have he : J '' S = coefficientSpectralCarrier KA Kη H ε := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (u.1.1, spatialPart (timeSpacePoint _ _)) ∈ KA ×ˢ Kη ∧ _
      simpa [S, J, mem_closedBall, Real.dist_eq, Real.norm_eq_abs] using hu
    · intro hp
      refine ⟨((p.1, spatialPart p.2), p.2 0 - H (p.1, spatialPart p.2)),
        ⟨hp.1, ?_⟩, ?_⟩
      · simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hp.2
      · dsimp [J]
        rw [add_sub_cancel]
        exact congrArg (fun v ↦ (p.1, v)) (timeSpaceMeasurableEquiv.symm_apply_apply p.2)
  rw [← he]
  exact hS.image_of_continuousOn hJ

/-- Joint smoothness at a point of the actual complement domain. This uses
the original root germ and invertible completion, without an inverse-jet
assumption (`app:ch_regular_base:eq:complement-inverse`). -/
theorem contDiffAt_coefficientBminus (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) {p : Coeff × E}
    (hH : ContDiffAt ℝ ∞ H (p.1, spatialPart p.2))
    (hp : ((coefficientRootPencil (coordinateSplit i) H (p.1, spatialPart p.2),
      pencil p.1 ((coordinateSplit i).symm (1, 0))),
        p.2 0 - H (p.1, spatialPart p.2)) ∈ minorComplementDomain r c) :
    ContDiffAt ℝ ∞ (coefficientBminus i r c H) p := by
  have hη : ContDiff ℝ ∞ (fun p : Coeff × E ↦ spatialPart p.2) :=
    ((coordinateSplit 0).contDiff.comp contDiff_snd).snd
  have hroot := hH.comp p (contDiffAt_fst.prodMk hη.contDiffAt)
  have hP : ContDiffAt ℝ ∞
      (fun p : Coeff × E ↦ coefficientRootPencil (coordinateSplit i) H
        (p.1, spatialPart p.2)) p :=
    contDiff_pencil.contDiffAt.comp p
      (contDiffAt_fst.prodMk ((coordinateSplit i).symm.contDiff.contDiffAt.comp p
        (hroot.prodMk hη.contDiffAt)))
  have hA : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦
      pencil p.1 ((coordinateSplit i).symm (1, 0))) p :=
    contDiff_pencil.contDiffAt.comp p (contDiffAt_fst.prodMk contDiffAt_const)
  have he : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦
      p.2 0 - H (p.1, spatialPart p.2)) p :=
    (((coordinateSplit 0).contDiff.comp contDiff_snd).fst.contDiffAt).sub hroot
  have houter := contDiffAt_minorComplementInverse_coefficients r c (m := ∞)
    (p := ((coefficientRootPencil (coordinateSplit i) H (p.1, spatialPart p.2),
      pencil p.1 ((coordinateSplit i).symm (1, 0))),
        p.2 0 - H (p.1, spatialPart p.2))) hp.1.1 hp.1.2 hp.2
  have hreal := houter.comp p ((hP.prodMk hA).prodMk he)
  exact contDiff_matrix_map_ofReal.contDiffAt.comp p hreal

/-- All coefficient/full-covector jets on the SAME retained spectral interval.
The hypotheses are the compact root buffers and complement-domain certificate
produced by `AlgebraicChart.exists_localChart_algebraic_collar` during the
finite selection. In particular, `ε` is supplied, not reselected. The profile
precedes `Q`, the slow scale, source frequency and accuracy. This supplies the
inverse factor of the branch-three joint grade in
`app:ch_regular:eq:high-amplitude`. -/
theorem exists_coefficientBminus_joint_bounds
    (i r c : Fin (d + 1)) {KA : Set Coeff} (hKA : IsCompact KA)
    {Kη : Set (Euclidean d)} (hKη : IsCompact Kη)
    (H : Coeff × Euclidean d → ℝ)
    (hH : ∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ H p)
    (ε M μ ν : ℝ)
    (hprimitive : ∀ p ∈ KA ×ˢ Kη,
      (coefficientRootPencil (coordinateSplit i) H p,
        pencil p.1 ((coordinateSplit i).symm (1, 0))) ∈ minorCoefficientClass r c M μ ν)
    (hdomain : minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) ε ⊆
      minorComplementDomain r c) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ p ∈ coefficientSpectralCarrier KA Kη H ε,
        ContDiffAt ℝ ∞ (coefficientBminus i r c H) p) ∧
      ∀ k p, p ∈ coefficientSpectralCarrier KA Kη H ε →
        ‖iteratedFDeriv ℝ k (coefficientBminus i r c H) p‖ ≤ C k := by
  let T := coefficientSpectralCarrier KA Kη H ε
  have hT : IsCompact T := isCompact_coefficientSpectralCarrier hKA hKη H
    (fun p hp ↦ (hH p hp).continuousAt.continuousWithinAt) ε
  have hs p (hp : p ∈ T) : ContDiffAt ℝ ∞ (coefficientBminus i r c H) p := by
    apply contDiffAt_coefficientBminus i r c H (hH _ hp.1)
    apply hdomain
    refine ⟨hprimitive _ hp.1, ?_⟩
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hp.2
  refine ⟨fun k ↦ 1 + cNorm T k (coefficientBminus i r c H),
    fun k ↦ by linarith [cNorm_nonneg T k (coefficientBminus i r c H)], hs, ?_⟩
  intro k p hp
  exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hT
    (fun p hp ↦ (hs p hp).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) hp le_rfl).trans
      (le_add_of_nonneg_left zero_le_one)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
