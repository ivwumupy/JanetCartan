module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameBufferedFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility

/-!
# Finite-order continuity of the actual tame family

For `app:lem:common-hamilton-phase`, construct both families inside one uniform
transverse state ball and identify their inverse coordinates on a common target
using root, ODE and inverse uniqueness. The phase with the sharp one-high bound
therefore also has the asserted scalar-symbol `C^(m+1)` to phase `C^m` continuity.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
local instance tameContinuousNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tameContinuousNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

set_option maxHeartbeats 1600000 in
/-- The same actual Hamilton phases have sharp joint one-high estimates and
finite-order continuity (`app:lem:common-hamilton-phase`). Every construction
input is discharged from the fixed transverse symbol data. All domains,
constants and charts precede the requested derivative order and tolerance.
The symbol norms use the original compact state ball even though the flows
are constructed in a smaller transverse ball. The remaining conic/mixed-gap
assembly is separate from this local assertion. -/
theorem exists_commonTameContinuousHamiltonPhases
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r ρ δ R' : ℝ) (B : ℕ → ℝ)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
      (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀),
      0 < r ∧ 0 < ρ ∧ 0 < δ ∧ 0 < R' ∧ R' < R ∧ (∀ m, 0 < B m) ∧
      ball (j s₀.1, s₀.2) (2 * ρ) ⊆ C₀.target ∧
      ContDiffOn ℝ ∞ (phase C₀.coordinates) (ball (j s₀.1, s₀.2) (2 * ρ)) ∧
      ∃ (F : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → HamiltonFlow H.1 U)
        (C : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → ProjectionChart (F H)),
        (∀ H,
          (F H).sectionMap = j.toContinuousLinearMap ∧
          ball (j s₀.1, s₀.2) (2 * ρ) ⊆ (C H).target ∧
          (C H).source = ball ((0 : ℝ), s₀) (3 * r) ∩
            (F H).augmentedProjection ⁻¹' (C H).target ∧
          (C H).source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ball ((0 : ℝ), s₀) (3 * r) ⊆ (F H).time ×ˢ (F H).parameters ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ (F H).augmentedProjection q) -
              ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) ∧
          (∀ q ∈ (F H).time ×ˢ (F H).parameters,
            ((F H).position q, (F H).momentum q) ∈ closedBall z₀ R') ∧
          (∀ z ∈ closedBall z₀ R', ⟪H.1.hp z, ν⟫_ℝ ≠ 0) ∧
          ContDiffOn ℝ ∞ (F H).position ((F H).time ×ˢ (F H).parameters) ∧
          ContDiffOn ℝ ∞ (F H).momentum ((F H).time ×ˢ (F H).parameters) ∧
          ContDiffOn ℝ ∞ (C H).coordinates (ball (j s₀.1, s₀.2) (2 * ρ)) ∧
          ContDiffOn ℝ ∞ (phase (C H).coordinates) (ball (j s₀.1, s₀.2) (2 * ρ)) ∧
          (∀ z ∈ ball (j s₀.1, s₀.2) (2 * ρ),
            HasFDerivAt (phase (C H).coordinates)
              (phaseDifferential ((F H).momentum (chartLift (C H).coordinates z))
                ((C H).coordinates z)) z ∧
            H.1.h (z.1, gradient (fun x ↦ phase (C H).coordinates (x, z.2)) z.1) = z.2.1) ∧
          (∀ m, cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
              (fun q ↦ ((F H).position (q.2, q.1), (F H).momentum (q.2, q.1))) +
            cNorm (closedBall (j s₀.1, s₀.2) ρ) m (C H).coordinates +
            cNorm (closedBall (j s₀.1, s₀.2) ρ) m (phase (C H).coordinates) ≤
              B m * (1 + cNorm (closedBall z₀ R) (m + 1) H.1.h))) ∧
        (∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ H,
          cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.1.h z - H₀.h z) < d →
            cNorm (closedBall (j s₀.1, s₀.2) ρ) m
              (fun z ↦ phase (C H).coordinates z - phase C₀.coordinates z) < ε) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  let y₀ := (j s₀.1, s₀.2)
  obtain ⟨R', δg, c, hR', hRR, hδg, hc, hR'D, hgap⟩ :=
    exists_uniform_transverse_stateBall H₀ hD hDH₀ hH₀ hR hRD ν htrans
  have hmono (f : E × E → ℝ) (hf : ContDiffOn ℝ ∞ f D) (m : ℕ) :
      cNorm (closedBall z₀ R') m f ≤ cNorm (closedBall z₀ R) m f :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hRR.le)
      (isCompact_closedBall _ _)
      (fun z hz ↦ (hf.contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp))
  obtain ⟨r, b, ρt, δt, r₀, a, ct, T, V, B, A, hr, _hb, hρt, hδt, hr₀, _ha,
      _hct, hrT, hrr, hB, _hmap, hV, _hVc, hbox, hfamily⟩ :=
    exists_commonTameBufferedHamiltonPhases H₀ hD hDH₀ hH₀ j ν horth hspan
      hR' hR'D henergy htrans
  obtain ⟨rf, bf, δf, Φ₀, C₀, Af, Vf, hrf, _hbf, hδf, hVf, _hVfc, hyVf,
      hC₀t, _hC₀, hS₀, Ff, Cf, hfprops, hfcont⟩ :=
    exists_commonBufferedHamiltonPhases_finiteOrder H₀ hD hDH₀ hH₀ j ν horth hspan
      hR' hR'D henergy htrans
  obtain ⟨ef, hef, hefV⟩ := Metric.isOpen_iff.mp hVf _ hyVf
  let η := min (3 * r) (3 * rf) /
    (2 * (‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let ρ := min ρt (min ef η) / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρt' : 2 * ρ < ρt := by
    have hh := min_le_left ρt (min ef η); dsimp [ρ]; linarith
  have hρf : 2 * ρ < ef := by
    have hh := (min_le_right ρt (min ef η)).trans (min_le_left ef η)
    dsimp [ρ]; linarith
  have hρη : 2 * ρ < η := by
    have hh := (min_le_right ρt (min ef η)).trans (min_le_right ef η)
    dsimp [ρ]; linarith
  let W := ball y₀ (2 * ρ)
  let K := closedBall y₀ ρ
  have hWV : W ⊆ V := by
    intro z hz
    have hz' := mem_ball.mp hz
    rw [Prod.dist_eq, max_lt_iff] at hz'
    exact hbox ⟨mem_closedBall.mpr (hz'.1.le.trans hρt'.le),
      mem_closedBall.mpr (hz'.2.le.trans hρt'.le)⟩
  have hWVf : W ⊆ Vf := (ball_subset_ball hρf.le).trans hefV
  have hKW : K ⊆ W := closedBall_subset_ball (by linarith)
  have hKbox : K ⊆ closedBall (j s₀.1) ρt ×ˢ closedBall s₀.2 ρt := by
    intro z hz
    have hz' := mem_closedBall.mp hz
    rw [Prod.dist_eq, max_le_iff] at hz'
    exact ⟨mem_closedBall.mpr (hz'.1.trans (by linarith)),
      mem_closedBall.mpr (hz'.2.trans (by linarith))⟩
  let δ := min δg (min δt δf)
  have hδ : 0 < δ := lt_min hδg (lt_min hδt hδf)
  let S := {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
    cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}
  have htSmall (H : S) : cNorm (closedBall z₀ R') 3 (fun z ↦ H.1.h z - H₀.h z) ≤ δt :=
    (hmono _ (H.2.2.1.sub hH₀) 3).trans
      (H.2.2.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
  let Hf (H : S) : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
      cNorm (closedBall z₀ R') 3 (fun z ↦ H.h z - H₀.h z) ≤ δf} :=
    ⟨H.1, H.2.1, H.2.2.1, (hmono _ (H.2.2.1.sub hH₀) 3).trans
      (H.2.2.2.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hex (H : S) := hfamily H.1 H.2.1 H.2.2.1 (htSmall H)
  let F (H : S) := (hex H).choose_spec.choose
  let C (H : S) : ProjectionChart (F H) := (hex H).choose_spec.choose_spec.choose
  have hprops (H : S) := (hex H).choose_spec.choose_spec.choose_spec
  have hadm (H : S) : ball ((0 : ℝ), s₀) (3 * r) ⊆ (F H).time ×ˢ (F H).parameters := by
    have ht := (hprops H).2.1
    have hp := (hprops H).2.2.1
    intro q hq
    have hh := mem_ball.mp hq
    rw [Prod.dist_eq, max_lt_iff, dist_zero_right, Real.norm_eq_abs, abs_lt] at hh
    rw [ht, hp]
    exact ⟨⟨by linarith [hh.1.1], by linarith [hh.1.2]⟩,
      mem_ball.mpr (hh.2.trans (by linarith))⟩
  have htransH (H : S) : ∀ z ∈ closedBall z₀ R', ⟪H.1.hp z, ν⟫_ℝ ≠ 0 :=
    fun z hz ↦ abs_pos.mp (hc.trans_le (hgap H.1 H.2.1 H.2.2.1
      (H.2.2.2.trans (min_le_left _ _)) z hz))
  have heq (H : S) : EqOn (C H).coordinates (Cf (Hf H)).coordinates W := by
    obtain ⟨hj, _ht, _hp, _hg, _hroot, _huniq, _hstart, hrange, _hx, _hm, hCt,
      _hCs, hsource, _hC, _hS, _hinner, _houter, _hpre, hhalf, _hid, _hsection, _hbound⟩ := hprops H
    obtain ⟨_htf, _hpf, hjf, hCtf, hCsf, _hsourcef, _hCf, _hSf, _hinnerf,
      _houterf, _hhalff, hadmf, hrangef⟩ := hfprops (Hf H)
    have hν : ν ≠ 0 := by intro he; apply htrans; rw [he, inner_zero_right]
    have he := (C H).coordinates_eq_on_transverse_overlap (Cf (Hf H)) hD H.2.1 H.2.2.1
      hR'D j ν hν horth hspan hj hjf
      (htransH H)
      (by positivity : 0 < 3 * r) (by positivity : 0 < 3 * rf) A (hadm H) hadmf
      (hsource.trans (ball_subset_ball (by linarith)))
      (by simpa only [hCtf] using hCsf) hhalf hrange hrangef
    intro z hz
    exact he ⟨⟨hCt.symm ▸ hWV hz, hCtf.symm ▸ hWVf hz⟩,
      ball_subset_ball hρη.le hz⟩
  refine ⟨r, ρ, δ, R', B, A, Φ₀, C₀, hr, hρ, hδ, hR', hRR, hB, hC₀t.symm ▸ hWVf,
    hS₀.mono hWVf, F, C, ?_, ?_⟩
  · intro H
    obtain ⟨hj, _ht, _hp, _hg, _hroot, _huniq, _hstart, _hrange, _hx, _hm, hCt,
      _hCs, hsource, hC, hS, _hinner, _houter, _hpre, _hgap, hid, _hsection, hbound⟩ := hprops H
    refine ⟨hj, hCt.symm ▸ hWV, (by rw [show (C H).target = V from hCt]; exact _hCs), hsource,
      hadm H, _hgap, _hrange, htransH H, _hx, _hm, hC.mono hWV, hS.mono hWV,
      fun z hz ↦ hid z (hWV hz), ?_⟩
    intro m
    have hmc := cNorm_mono_set_of_contDiffAt hKbox
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      (fun z hz ↦ (hC.contDiffAt (hV.mem_nhds (hbox hz))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    have hms := cNorm_mono_set_of_contDiffAt hKbox
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      (fun z hz ↦ (hS.contDiffAt (hV.mem_nhds (hbox hz))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    have hb := (hbound m).trans (mul_le_mul_of_nonneg_left
      (show 1 + cNorm (closedBall z₀ R') (m + 1) H.1.h ≤
        1 + cNorm (closedBall z₀ R) (m + 1) H.1.h by linarith [hmono _ H.2.2.1 (m + 1)]) (hB m).le)
    linarith
  · intro m ε hε
    obtain ⟨d, hd, hcont⟩ := hfcont K (isCompact_closedBall _ _) (hKW.trans hWVf) m ε hε
    refine ⟨d, hd, ?_⟩
    intro H hsmall
    have hh := hcont (Hf H) ((hmono _ (H.2.2.1.sub hH₀) (m + 1)).trans_lt hsmall)
    rw [(C H).cNorm_phase_sub_eq_of_coordinates_eqOn (Cf (Hf H)) isOpen_ball hKW
      (heq H) (phase C₀.coordinates) m]
    exact (le_add_of_nonneg_left (cNorm_nonneg _ _ _)).trans_lt hh

end JanetCartan.HamiltonPhase
