module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Bounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension

/-!
# Uniform off-root estimates for the actual algebraic inverse

The root is the SAME `RootFamily.fieldRoot` used by the transported columns.
The common spectral interval is constructed from the original bounded pencil,
adjugate minor and unnormalized transport coefficient. The inverse is always
`ResidualCoordinates.bminus`; no substitute inverse or inverse budget is an
input. Compact-range tame composition gives one high original coefficient norm.

Consumers: `directPDOSymbols` indices zero and three, in
`app:ch_regular_base:eq:complement-symbol` and
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- Complexification preserves joint smoothness of the actual real inverse
and physical coefficients in `app:ch_regular_base:eq:energy-complete-residual`.
This uses the Frobenius matrix topology throughout. -/
theorem contDiff_matrix_map_ofReal :
    ContDiff ℝ ∞ (fun M : Mat ↦ M.map Complex.ofReal) := by
  have he : (fun M : Mat ↦ M.map Complex.ofReal) = fun M ↦
      ∑ j, ∑ k, (M j k : ℂ) • (Matrix.single j k 1 : CMat) := by
    funext M
    ext j k
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  rw [he]
  exact ContDiff.sum fun j _ ↦ ContDiff.sum fun k _ ↦
    (Complex.ofRealCLM.contDiff.comp
      (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff).smul contDiff_const

private theorem cNorm_constant_le (K : Set E) (m : ℕ) (ξ : E) :
    cNorm K m (fun _ : E ↦ ξ) ≤ (m + 1 : ℝ) * ‖ξ‖ := by
  have hb (j : ℕ) (_hj : j ≤ m) (x : E) (_hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j (fun _ : E ↦ ξ) x‖ ≤ ‖ξ‖ := by
    by_cases hj : j = 0
    · subst j
      exact le_of_eq (norm_iteratedFDeriv_zero)
    · simp [iteratedFDeriv_const_of_ne hj]
  simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ norm_nonneg ξ) hb

/-- The precise normalized spectral-band condition required of the original
right multiplier. It refers to the SAME branch and the actual normalized
covector, and is not inferred from membership in a root-uniqueness band.
The finite-sector parent must produce this containment for its common masks.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def NormalizedSpectralSupport (ℓ : Euclidean d →L[ℝ] ℝ)
    (h : RootState (Euclidean d) → ℝ) (X : Set E) (ε : ℝ) (β : E → ℂ) : Prop :=
  ∀ x ∈ X, ∀ ξ ∈ tsupport β,
    |normalizeCovector ℓ ξ 0 - h (rootState x (spatialPart (normalizeCovector ℓ ξ)))| ≤ ε

/-- A common positive off-root interval, determinant gap and single-high
bounds for the LITERAL inverse with the SAME coefficient root. All choices
precede `Q`. The only matrix bounds/gaps are on the original normalized root
pencil and time coefficient; no completed determinant or inverse estimate is
assumed. The derivative reserve here is zero.

The normalized spatial buffer `Kη` and coefficient buffer `KA` are fixed
compact sets with ambient smooth root germs. The spectral condition on `ξ`
is uniform in the entire physical norm ball, as needed when bounding its
physical derivatives. Consumer: the supported symbols in
`app:ch_regular_base:eq:complement-symbol`. -/
theorem exists_bminus_fieldRoot_cNorm_bounds
    (i r c : Fin (d + 1)) (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (xQ : E) (RQ : ℝ)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x ρ) (closedBall xQ RQ))
    {KA : Set Coeff} (hKA : IsCompact KA) {Kη : Set (Euclidean d)} (hKη : IsCompact Kη)
    (H : Coeff × Euclidean d → ℝ)
    (hH : ∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ H p)
    (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hprimitive : ∀ p ∈ KA ×ˢ Kη,
      ‖coefficientRootPencil (coordinateSplit i) H p‖ ≤ M ∧
      ‖pencil p.1 ((coordinateSplit i).symm (1, 0))‖ ≤ M ∧
      (coefficientRootPencil (coordinateSplit i) H p).det = 0 ∧
      μ ≤ |(coefficientRootPencil (coordinateSplit i) H p).adjugate r c| ∧
      ν ≤ |minorTransportCoefficient (coefficientRootPencil (coordinateSplit i) H p)
        (pencil p.1 ((coordinateSplit i).symm (1, 0))) r c|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass r c M μ ν, ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det|) ∧
      (minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) ε ⊆
        minorComplementDomain r c) ∧
      ∀ (Ω : Set E), IsOpen Ω → closedBall xQ RQ ⊆ Ω →
        ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω → MapsTo Q (closedBall xQ RQ) KA →
          ∀ ξ : E, spatialPart ξ ∈ Kη →
            (∀ y ∈ closedBall x ρ,
              |ξ 0 - fieldRoot (coordinateSplit i) Q H (rootState y (spatialPart ξ))| ≤ ε) →
            (∀ y ∈ closedBall x ρ, ContDiffAt ℝ ∞
              (fun y ↦ bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) y) ∧
            ∀ m, cNorm (closedBall x ρ) m
              (fun y ↦ bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) ≤
                C m * (1 + cNorm (closedBall xQ RQ) m Q) := by
  obtain ⟨ε, hε, δ, hδ, _, _, hgap, hdomain, _⟩ :=
    exists_minorComplementInverse_primitive_tame x hρ r c M hμ hν
  let S := (KA ×ˢ Kη) ×ˢ closedBall (0 : ℝ) ε
  let J : (Coeff × Euclidean d) × ℝ → Coeff × E :=
    fun p ↦ (p.1.1, timeSpacePoint (H p.1 + p.2) p.1.2)
  let T := J '' S
  have hS : IsCompact S := (hKA.prod hKη).prod (isCompact_closedBall _ _)
  have hHcont : ContinuousOn H (KA ×ˢ Kη) := fun p hp ↦ (hH p hp).continuousAt.continuousWithinAt
  have hJ : ContinuousOn J S := by
    exact continuousOn_fst.fst.prodMk
      ((coordinateSplit 0).symm.continuous.comp_continuousOn
        (((hHcont.comp continuousOn_fst (fun _ hp ↦ hp.1)).add continuousOn_snd).prodMk
          continuousOn_fst.snd))
  have hT : IsCompact T := hS.image_of_continuousOn hJ
  let G : Coeff × E → CMat := fun p ↦
    (minorComplementInverse (coefficientRootPencil (coordinateSplit i) H (p.1, spatialPart p.2))
      (pencil p.1 ((coordinateSplit i).symm (1, 0))) r c
      (p.2 0 - H (p.1, spatialPart p.2))).map Complex.ofReal
  have hG : ∀ p ∈ T, ContDiffAt ℝ ∞ G p := by
    rintro _ ⟨u, hu, rfl⟩
    have hp : (J u).1 = u.1.1 := rfl
    have hη : spatialPart (J u).2 = u.1.2 := spatialPart_timeSpacePoint _ _
    have hτ : (J u).2 0 - H ((J u).1, spatialPart (J u).2) = u.2 := by
      simp [J]
    have hparam : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦ (p.1, spatialPart p.2)) (J u) :=
      contDiffAt_fst.prodMk (((coordinateSplit 0).contDiff.comp contDiff_snd).snd.contDiffAt)
    have hroot : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦ H (p.1, spatialPart p.2)) (J u) := by
      apply ContDiffAt.comp (J u) _ hparam
      simpa only [hp, hη] using hH u.1 hu.1
    have hP : ContDiffAt ℝ ∞
        (fun p : Coeff × E ↦ coefficientRootPencil (coordinateSplit i) H
          (p.1, spatialPart p.2)) (J u) :=
      contDiff_pencil.contDiffAt.comp (J u)
        (contDiffAt_fst.prodMk ((coordinateSplit i).symm.contDiff.contDiffAt.comp (J u)
          (hroot.prodMk (((coordinateSplit 0).contDiff.comp contDiff_snd).snd.contDiffAt))))
    have hA : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦
        pencil p.1 ((coordinateSplit i).symm (1, 0))) (J u) :=
      contDiff_pencil.contDiffAt.comp (J u) (contDiffAt_fst.prodMk contDiffAt_const)
    have he : ContDiffAt ℝ ∞ (fun p : Coeff × E ↦
        p.2 0 - H (p.1, spatialPart p.2)) (J u) :=
      (((coordinateSplit 0).contDiff.comp contDiff_snd).fst.contDiffAt).sub hroot
    have hclass : (coefficientRootPencil (coordinateSplit i) H u.1,
        pencil u.1.1 ((coordinateSplit i).symm (1, 0))) ∈ minorCoefficientClass r c M μ ν :=
      hprimitive u.1 hu.1
    have hd : ((coefficientRootPencil (coordinateSplit i) H u.1,
        pencil u.1.1 ((coordinateSplit i).symm (1, 0))), u.2) ∈ minorComplementDomain r c :=
      hdomain ⟨hclass, hu.2⟩
    have houter := contDiffAt_minorComplementInverse_coefficients r c (m := ∞)
      (p := ((coefficientRootPencil (coordinateSplit i) H u.1,
        pencil u.1.1 ((coordinateSplit i).symm (1, 0))), u.2)) hd.1.1 hd.1.2 hd.2
    have houter' : ContDiffAt ℝ ∞ (fun v : (Mat × Mat) × ℝ ↦
        minorComplementInverse v.1.1 v.1.2 r c v.2)
        ((coefficientRootPencil (coordinateSplit i) H ((J u).1, spatialPart (J u).2),
          pencil (J u).1 ((coordinateSplit i).symm (1, 0))),
            (J u).2 0 - H ((J u).1, spatialPart (J u).2)) := by
      rw [hτ, hp, hη]
      exact houter
    have hreal := houter'.comp (J u) ((hP.prodMk hA).prodMk he)
    exact contDiff_matrix_map_ofReal.contDiffAt.comp (J u) hreal
  obtain ⟨N, hN⟩ := hT.isBounded.exists_norm_le
  let N₀ := max 0 N
  have hN₀ : 0 ≤ N₀ := le_max_left _ _
  choose A hA hcomp using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn x hρ hT
      (le_refl m) (fun p hp ↦ (hG p hp).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  let L := (physicalCoordinates i).toContinuousLinearMap
  let cost := fun m ↦ 1 + linearNormCost L m + (m + 1 : ℝ) * N₀
  have hcost m : 0 < cost m := by
    have := linearNormCost_pos L m
    have : 0 ≤ (m + 1 : ℝ) * N₀ := mul_nonneg (by positivity) hN₀
    dsimp [cost]
    linarith [linearNormCost_pos L m]
  refine ⟨ε, hε, δ, hδ, fun m ↦ A m * cost m,
    fun m ↦ mul_pos (hA m) (hcost m), hgap, hdomain, ?_⟩
  intro Ω hΩ hKQ Q hQ hQrange ξ hξη hband
  let U := L ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage L.continuous
  have hKU : closedBall x ρ ⊆ U := fun y hy ↦ hKQ (hphysical hy)
  let f : E → Coeff × E := fun y ↦ (Q (L y), ξ)
  have hf : ContDiffOn ℝ ∞ f U :=
    (hQ.comp L.contDiff.contDiffOn (fun _ hy ↦ hy)).prodMk contDiffOn_const
  have hfT : MapsTo f (closedBall x ρ) T := by
    intro y hy
    refine ⟨((Q (L y), spatialPart ξ), ξ 0 - H (Q (L y), spatialPart ξ)),
      ⟨⟨hQrange (hphysical hy), hξη⟩, ?_⟩, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, fieldRoot,
        rootState, L, ContinuousLinearEquiv.coe_coe, physicalCoordinates_apply] using hband y hy
    · dsimp [J, f]
      rw [add_sub_cancel]
      exact congrArg (fun v ↦ (Q (L y), v)) (timeSpaceMeasurableEquiv.symm_apply_apply ξ)
  have hident : G ∘ f =
      (fun y ↦ bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) := by
    funext y
    rfl
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [← hident]
    exact (hG (f y) (hfT hy)).comp y (hf.contDiffAt (hU.mem_nhds (hKU hy)))
  intro m
  have hξ : ‖ξ‖ ≤ N₀ :=
    (norm_snd_le (f x)).trans ((hN (f x) (hfT (mem_closedBall_self hρ.le))).trans
      (le_max_right _ _))
  have hQp := cNorm_comp_linear_le L (isCompact_closedBall xQ RQ) hΩ hKQ hQ hphysical m
  have hpair := cNorm_prodMk_le_on (closedBall x ρ) (isCompact_closedBall _ _) m
    (f := Q ∘ L) (g := fun _ : E ↦ ξ)
    (fun y hy ↦ (hf.fst.contDiffAt (hU.mem_nhds (hKU hy))).of_le
      (show (m : ℕ∞ω) ≤ ∞ by simp)) (fun _ _ ↦ contDiffAt_const)
  have hconst : cNorm (closedBall x ρ) m (fun _ : E ↦ ξ) ≤ (m + 1 : ℝ) * N₀ :=
    (cNorm_constant_le _ m ξ).trans (mul_le_mul_of_nonneg_left hξ (by positivity))
  have hinner : cNorm (closedBall x ρ) m f ≤
      linearNormCost L m * cNorm (closedBall xQ RQ) m Q + (m + 1 : ℝ) * N₀ := by
    exact hpair.trans (add_le_add hQp hconst)
  have hbound := hcomp m U hU hKU f hf hfT
  rw [hident] at hbound
  apply hbound.trans
  have hq := cNorm_nonneg (closedBall xQ RQ) m Q
  have hhigh : 1 + cNorm (closedBall x ρ) m f ≤
      cost m * (1 + cNorm (closedBall xQ RQ) m Q) := by
    dsimp [cost]
    nlinarith [linearNormCost_pos L m,
      mul_nonneg (mul_nonneg (show 0 ≤ (m + 1 : ℝ) by positivity) hN₀) hq]
  exact (mul_le_mul_of_nonneg_left hhigh (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
