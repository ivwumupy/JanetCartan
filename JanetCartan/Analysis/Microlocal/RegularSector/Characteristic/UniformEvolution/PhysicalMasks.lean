module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction

/-!
# Physical masks and the literal lower-time support

The inverse-coordinate identities and conic support are literal conclusions
of `UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`.
They give the sharper lower endpoint `z.1-src/2` without changing any
amplitude. Fixed output masks inside the retained time plateau give a slab
of length `3*src/4`, and fixed source masks stay before Fourier multiplication.
The comparison of this slab with the phase buffer is a separate obligation.
Consumer: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase EvolutionIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- One radius comparison follows from the retained chart alone: the chart
preserves output time and maps the entire closed source ball into the amplitude
buffer. This does not assert a comparison with the separate phase radius
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem sourceRadius_le_amplitudeRadius_half
    (z : Z) {src ρ : ℝ} (hsrc : 0 ≤ src)
    (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T)
    (hC : (C : T → T) = twoTimeProjection Φ)
    (hflow : MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2))) :
    src ≤ ρ / 2 := by
  have hp : (z.1 + src, z) ∈ closedBall (z.1, z) src := by
    simp only [mem_closedBall, Prod.dist_eq, dist_self, Real.dist_eq,
      add_sub_cancel_left, abs_of_nonneg hsrc, max_le_iff]
    exact ⟨le_rfl, hsrc⟩
  have hball := hflow hp
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hball
  have ht := hball.1
  change dist (C (z.1 + src, z)).1 z.1 ≤ ρ / 2 at ht
  rw [hC] at ht
  simpa only [twoTimeProjection, Real.dist_eq, add_sub_cancel_left,
    abs_of_nonneg hsrc] using ht

/-- The actual conic support gives the sharper lower-time buffer for each
of `W₀,W₁,PW₁`. Only the producer's inverse source-time identity and support
inclusion are used; no new truncation is made (`fixed-time-representation`). -/
theorem retained_amplitude_zero_before_source_half
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (src : ℝ)
    (C : OpenPartialHomeomorph T T)
    (hsourceTime : ∀ p ∈ C.target, (C.symm p).2.1 = p.2.1)
    (W : T → Mat)
    (hsupport : tsupport W ⊆ ConicPhase.domain ℓ
      (C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
        (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))))
    {p : T} (hp : p.2.1 ≤ z.1 - src / 2) : W p = 0 := by
  by_contra hn
  have h := hsupport (subset_tsupport W hn)
  have ht := h.2.2.2.1
  rw [hsourceTime _ h.2.1] at ht
  change dist p.2.1 z.1 < src / 2 at ht
  rw [Real.dist_eq, abs_lt] at ht
  linarith [ht.1]

/-- Construct both physical masks before the varying coefficient field. The
output has a nonempty plateau at the original physical centre, is supported
inside the retained box and inside the producer's time plateau, and therefore
uses the literal lower endpoint `z.1-src/2`. The source compact and open domain
are those supplied by the finite physical cover (`retarded-kernel`). -/
theorem exists_retained_physical_masks
    (z : Z) {ε src : ℝ} (hε : 0 < ε) (hsrc : 0 < src)
    (κ : ℝ → ℝ)
    (hκ : closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1})
    {Ksource Usource : Set E} (hKsource : IsCompact Ksource)
    (hUsource : IsOpen Usource) (hKU : Ksource ⊆ Usource) :
    ∃ χout χsource : E → ℝ,
      ContDiff ℝ ∞ χout ∧ ContDiff ℝ ∞ χsource ∧
      HasCompactSupport χout ∧ HasCompactSupport χsource ∧
      (∀ x, χout x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, χsource x ∈ Icc (0 : ℝ) 1) ∧
      timeSpacePoint z.1 z.2.1 ∈ interior {x | χout x = 1} ∧
      Ksource ⊆ interior {x | χsource x = 1} ∧
      tsupport χout ⊆ elapsedPhysicalBox z (ε / 2) ∧ tsupport χsource ⊆ Usource ∧
      (∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1)) ∧
      (∀ x, χout x ≠ 0 → x 0 ∈ Icc (z.1 - src / 2)
        ((z.1 - src / 2) + 3 * src / 4)) ∧
      ∃ R > (0 : ℝ),
        (∀ x ∈ elapsedPhysicalBox z (ε / 2), ‖x‖ ≤ R) ∧
        (∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R) ∧
        R / (4 * R) < 1 / 2 := by
  let Uout := elapsedPhysicalBox z (ε / 2) ∩ {x : E | x 0 ∈ ball z.1 (src / 4)}
  have hUout : IsOpen Uout := (isOpen_elapsedPhysicalBox z (ε / 2)).inter
    (isOpen_ball.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous)
  have hz : timeSpacePoint z.1 z.2.1 ∈ Uout := by
    change (dist (timeSpacePoint z.1 z.2.1 0) z.1 < ε / 2 ∧
      dist (spatialPart (timeSpacePoint z.1 z.2.1)) z.2.1 < ε / 2) ∧
      dist (timeSpacePoint z.1 z.2.1 0) z.1 < src / 4
    simp only [timeSpacePoint_time, spatialPart_timeSpacePoint, dist_self]
    exact ⟨⟨by positivity, by positivity⟩, by positivity⟩
  obtain ⟨χout, ho, hor, hoc, hos, hop⟩ :=
    CompatibleResponse.exists_compact_family_cutoff
      (isCompact_singleton (x := timeSpacePoint z.1 z.2.1)) hUout (singleton_subset_iff.mpr hz)
  obtain ⟨χsource, hs, hsr, hsc, hss, hsp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hKsource hUsource hKU
  refine ⟨χout, χsource, ho, hs, hoc, hsc, hor, hsr, hop (mem_singleton _), hsp,
    fun x hx ↦ (hos hx).1, hss, ?_, ?_, ?_⟩
  · intro x hx
    have ht := hκ (ball_subset_closedBall (hos hx).2)
    filter_upwards [isOpen_interior.mem_nhds ht] with t ht
    exact interior_subset (s := {t | κ t = 1}) ht
  · intro x hx
    have ht := (hos (subset_tsupport χout hx)).2
    change dist (x 0) z.1 < src / 4 at ht
    rw [Real.dist_eq, abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · obtain ⟨B, hB⟩ := hsc.exists_bound_of_continuousOn continuous_id.continuousOn
    let R := |B| + |z.1| + ‖z.2.1‖ + ε + 1
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨R, hR, ?_, ?_, ?_⟩
    · intro x hx
      have hn := norm_le_on_elapsedPhysicalBox hx
      dsimp [R]
      linarith [abs_nonneg B]
    · intro y hy i
      have hn := (PiLp.norm_apply_le y i).trans (hB y hy)
      rw [Real.norm_eq_abs] at hn
      dsimp [R]
      linarith [le_abs_self B, abs_nonneg z.1, norm_nonneg z.2.1]
    · apply (div_lt_iff₀ (by positivity : 0 < 4 * R)).mpr
      linarith

end JanetCartan.RegularSector.Characteristic.UniformEvolution
