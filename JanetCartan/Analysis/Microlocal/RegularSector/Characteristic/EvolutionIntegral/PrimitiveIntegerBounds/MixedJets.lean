module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveMixed

/-!
# Original mixed jets on the normalized phase cover

The raw mixed-jet input of `exists_retardedOperator_of_primitive_data` and
the inverse bound needed by the integer estimates follow from the original
joint phase seminorm. Homogeneity transports this estimate from the fixed
normalized cover to every positive frequency scale. No elapsed-phase estimate
is assumed. Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open SymbolBudgets
variable {d : ℕ}
local notation "P" => ℝ × ℝ × Euclidean d
local notation "E" => Euclidean d

/-- The original joint mixed derivative is a contraction of the joint
second jet. Consumer: the primitive mixed bound for the elapsed graph in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_twoTimePhase_mixed_le_cNorm
    (Ψ : TwoTimePhase d) {J U : Set (TwoTimePoint d)}
    (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) U)
    {p : P} {η : E} (hp : (p, η) ∈ J) {N : ℕ} (hN : 2 ≤ N) :
    ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
      (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p) η‖ ≤ cNorm J N (jointPhase Ψ) := by
  let F := jointPhase Ψ
  let I : P →L[ℝ] P × E := ContinuousLinearMap.inl ℝ P E
  let Q : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  let C : ((P × E) →L[ℝ] ℝ) →L[ℝ] P →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ P (P × E) ℝ).flip I
  have hs : ContDiffAt ℝ ∞ F (p, η) := hΨ.contDiffAt (hU.mem_nhds (hJU hp))
  have he : (fun ζ ↦ fderiv ℝ (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p)
      =ᶠ[𝓝 η] (fun ζ ↦ C (fderiv ℝ F (p, ζ))) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually
      (hU.mem_nhds (hJU hp))] with ζ hζ
    have hd := ((hΨ.contDiffAt (hU.mem_nhds hζ)).differentiableAt (by simp)).hasFDerivAt
    have hi : HasFDerivAt (fun v : P ↦ (v, ζ)) I p :=
      (hasFDerivAt_id p).prodMk (hasFDerivAt_const ζ p)
    exact (hd.comp p hi).fderiv
  have hq : HasFDerivAt (fun ζ : E ↦ (p, ζ)) Q η :=
    (hasFDerivAt_const p η).prodMk (hasFDerivAt_id η)
  have hd := C.hasFDerivAt.comp η
    (((hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp η hq)
  change HasFDerivAt (fun ζ ↦ C (fderiv ℝ F (p, ζ))) _ η at hd
  rw [he.fderiv_eq, hd.fderiv]
  have hb : ‖fderiv ℝ (fderiv ℝ F) (p, η)‖ ≤ cNorm J N F := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun z hz ↦ (hΨ.contDiffAt (hU.mem_nhds (hJU hz))).of_le (by simp)) hp hN
  apply ContinuousLinearMap.opNorm_le_bound _ (cNorm_nonneg _ _ _)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (cNorm_nonneg _ _ _) (norm_nonneg v))
  intro w
  change ‖fderiv ℝ (fderiv ℝ F) (p, η) (0, v) (w, 0)‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) (p, η)‖ * ‖((0, v) : P × E)‖ * ‖((w, 0) : P × E)‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ cNorm J N F * ‖v‖ * ‖w‖ := by
      simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg v)) (norm_nonneg w)

/-- The original mixed joint derivative has degree zero in frequency.
The open position chart retains both time variables, including their buffers.
Consumer: closing the raw mixed premise of the retarded construction.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem twoTimePhase_mixed_dilation_eq
    (Ψ : TwoTimePhase d) {V : Set P} {D : Set E}
    (hV : IsOpen V) (hD : IsOpen D)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ D, t • η ∈ D)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) (V ×ˢ D))
    (hhom : ∀ t : ℝ, 0 < t → ∀ p ∈ V, ∀ η ∈ D,
      Ψ p.1 p.2.1 p.2.2 (t • η) = t * Ψ p.1 p.2.1 p.2.2 η)
    {t : ℝ} (ht : 0 < t) {p : P} (hp : p ∈ V) {η : E} (hη : η ∈ D) :
    fderiv ℝ (fun ζ ↦ fderiv ℝ (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p) (t • η) =
      fderiv ℝ (fun ζ ↦ fderiv ℝ (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p) η := by
  let G : E → P →L[ℝ] ℝ := fun ζ ↦ fderiv ℝ
    (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p
  have hs (ζ) (hζ : ζ ∈ D) : ContDiffAt ℝ ∞ (jointPhase Ψ) (p, ζ) :=
    hΨ.contDiffAt ((hV.prod hD).mem_nhds ⟨hp, hζ⟩)
  have hg (ζ) (hζ : ζ ∈ D) : DifferentiableAt ℝ G ζ := by
    have hh := (hs ζ hζ).comp (ζ, p)
      (f := fun v : E × P ↦ (v.2, v.1)) (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (hh.fderiv (m := ∞) contDiffAt_const (by simp)).differentiableAt (by simp)
  have he : (fun ζ ↦ G (t • ζ)) =ᶠ[𝓝 η] (fun ζ ↦ t • G ζ) := by
    filter_upwards [hD.mem_nhds hη] with ζ hζ
    have he' : (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 (t • ζ)) =ᶠ[𝓝 p]
        (fun v : P ↦ t • Ψ v.1 v.2.1 v.2.2 ζ) :=
      eventuallyEq_of_mem (hV.mem_nhds hp) (fun v hv ↦ hhom t ht v hv ζ hζ)
    have hd := ((hs ζ hζ).comp p (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by simp)
    exact (hd.hasFDerivAt.const_smul t |>.congr_of_eventuallyEq he').fderiv
  have hl := (hg (t • η) (hcone t ht η hη)).hasFDerivAt.comp η
    ((hasFDerivAt_id η).const_smul t)
  have hr := (hg η hη).hasFDerivAt.const_smul t
  have hh := (hl.congr_of_eventuallyEq he.symm).unique hr
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := congrArg (fun L : E →L[ℝ] P →L[ℝ] ℝ ↦ L v w) hh
  apply mul_left_cancel₀ ht.ne'
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using hv

/-- A fixed normalized cover and an original phase seminorm supply the raw
mixed-jet budget at every frequency. This is the missing producer for the
`Bmix` premise of `exists_retardedOperator_of_primitive_data`, and for the
temporal shear bound in `exists_elapsedPhase_mixed_bounds`.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem norm_twoTimePhase_mixed_le_of_normalized_cover
    (Ψ : TwoTimePhase d) {V : Set P} {D : Set E}
    (hV : IsOpen V) (hD : IsOpen D)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ D, t • η ∈ D)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) (V ×ˢ D))
    (hhom : ∀ t : ℝ, 0 < t → ∀ p ∈ V, ∀ η ∈ D,
      Ψ p.1 p.2.1 p.2.2 (t • η) = t * Ψ p.1 p.2.1 p.2.2 η)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hs : ContDiffOn ℝ ∞ (jointPhase Ψ) U)
    {p : P} (hp : p ∈ V) {η : E}
    (hcover : ∃ t : ℝ, 0 < t ∧ ∃ ζ ∈ D, (p, ζ) ∈ J ∧ η = t • ζ)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
      (fun v : P ↦ Ψ v.1 v.2.1 v.2.2 ζ) p) η‖ ≤ cNorm J N (jointPhase Ψ) := by
  obtain ⟨t, ht, ζ, hζ, hz, rfl⟩ := hcover
  rw [twoTimePhase_mixed_dilation_eq Ψ hV hD hcone hΨ hhom ht hp hζ]
  exact norm_twoTimePhase_mixed_le_cNorm Ψ hJ hU hJU hs hz hN

/-- Degree-one normalization preserves the original phase on its buffered
homogeneous chart. Consumer: the dyadic whole-image reserve for the elapsed
graph (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem joint_normalizedTwoTimePhase_eqOn
    (Ψ : TwoTimePhase d) {U : Set (TwoTimePoint d)}
    (hhom : ∀ t : ℝ, 0 < t → ∀ p ∈ U,
      Ψ p.1.1 p.1.2.1 p.1.2.2 (t • p.2) = t * jointPhase Ψ p)
    {t : ℝ} (ht : 0 < t) :
    EqOn (jointPhase (normalizedTwoTimePhase t Ψ)) (jointPhase Ψ) U := by
  intro p hp
  change t⁻¹ * Ψ p.1.1 p.1.2.1 p.1.2.2 (t • p.2) = _
  rw [hhom t ht p hp, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]

/-- All normalized phase jets equal the original jets on the same fixed
buffered cover. This discharges the normalized phase budget of the actual
whole-image constructor, from primitive homogeneity.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem cNorm_normalizedTwoTimePhase_eq
    (Ψ : TwoTimePhase d) {J U : Set (TwoTimePoint d)}
    (hU : IsOpen U) (hJU : J ⊆ U)
    (hhom : ∀ t : ℝ, 0 < t → ∀ p ∈ U,
      Ψ p.1.1 p.1.2.1 p.1.2.2 (t • p.2) = t * jointPhase Ψ p)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    cNorm J N (jointPhase (normalizedTwoTimePhase t Ψ)) = cNorm J N (jointPhase Ψ) := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro p hp
  exact congrArg norm ((eventuallyEq_of_mem (hU.mem_nhds (hJU hp))
    (joint_normalizedTwoTimePhase_eqOn Ψ hhom ht)).iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
