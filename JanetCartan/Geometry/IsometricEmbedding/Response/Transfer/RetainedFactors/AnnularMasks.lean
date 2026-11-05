module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularCarriers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhysicalMasks

/-!
# Actual physical masks and the complete retained annular carrier

Apply the original physical-mask constructor inside one retained box. The
SAME masks then have both the retarded endpoint properties and support in the
convex annular carrier. The original radius comparisons put the entire
`3 * src / 4` interval in the phase buffer. They do not, by themselves, put
it inside the separate perturbative Hessian radius.
Consumer: the same-mask retarded construction and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution
open DirectEvolution AnnularComplement RegularSector.FiniteMasks
open EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)

/-- The producer's actual radius comparisons retain the WHOLE original
elapsed interval in the phase buffer. No cutoff or elapsed tail is removed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_full_elapsed_interval_subset {b ρ src : ℝ}
    (hsrc : 0 < src) (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) :
    Icc (0 : ℝ) (3 * src / 4) ⊆ Icc 0 (retainedRadius b ρ) := by
  intro t ht
  refine ⟨ht.1, ht.2.trans ?_⟩
  rw [retainedRadius, min_eq_right hρb]
  linarith

/-- Enlarging the integration carrier retains the SAME masks and whole
elapsed contribution. This permits a buffer for the moving critical point;
it changes no physical factor (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedClosedCarrier_mono_radius (z : Z) {ε δ : ℝ} (hεδ : ε ≤ δ)
    (P : Set (Euclidean 3)) (D : Set E) :
    retainedClosedCarrier z ε P D ⊆ retainedClosedCarrier z δ P D := by
  have hX : elapsedPhysicalBox z (ε / 2) ⊆ elapsedPhysicalBox z (δ / 2) := by
    intro x hx
    exact ⟨ball_subset_ball (show ε / 2 ≤ δ / 2 by linarith) hx.1,
      ball_subset_ball (show ε / 2 ≤ δ / 2 by linarith) hx.2⟩
  intro v hv
  exact ⟨⟨⟨hv.1.1.1, hv.1.1.2.trans hεδ⟩, closure_mono hX hv.1.2.1, hv.1.2.2⟩,
    closure_mono hX hv.2.1, hv.2.2⟩

/-- Construct the physical masks once, with their original output plateau,
source plateau and BOTH retarded endpoints. The actual full annular amplitudes
then lie in a single compact convex source/covector carrier for the ENTIRE
elapsed interval. The angular hypothesis is precisely the sphere-support
hypothesis of `exists_retained_local_solver_and_residual`, at its original
inner aperture. The source compact is fixed inside the common physical box.

The returned masks can be passed directly to
`exists_retained_signed_retarded_operators`; selecting independent masks again
would require an additional equality proof. Constants and masks here precede
the coefficient histories, matrix amplitudes, frequency, order and accuracy
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_retained_annular_physical_masks
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {b ρ src aperture : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hsrc : 0 < src)
    (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) (hAp : 0 < aperture)
    (κ : ℝ → ℝ) (hκ : closedBall z.1 (src / 4) ⊆ interior {t | κ t = 1})
    {Ksource : Set E} (hKs : IsCompact Ksource)
    (hKX : Ksource ⊆ elapsedPhysicalBox z (retainedRadius b ρ / 2))
    (mask : E → ℝ)
    (hmask : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (retainedRadius b ρ / 4) (aperture / 2))
    {ra rb : ℝ} (hra : 0 < ra) (hrb : 0 < rb) :
    ∃ χout χsource : E → ℂ,
      ContDiff ℝ ∞ χout ∧ ContDiff ℝ ∞ χsource ∧
      HasCompactSupport χout ∧ HasCompactSupport χsource ∧
      timeSpacePoint z.1 z.2.1 ∈ interior {x | χout x = 1} ∧
      Ksource ⊆ interior {x | χsource x = 1} ∧
      tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius b ρ / 2) ∧
      tsupport χsource ⊆ elapsedPhysicalBox z (retainedRadius b ρ / 2) ∧
      (∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1)) ∧
      (∀ x, χout x ≠ 0 → x 0 ∈ Icc (z.1 - src / 2)
        ((z.1 - src / 2) + 3 * src / 4)) ∧
      ∃ R > (0 : ℝ),
        (∀ x ∈ elapsedPhysicalBox z (retainedRadius b ρ / 2), ‖x‖ ≤ R) ∧
        (∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R) ∧
      ∃ D : Set E, IsCompact D ∧ Convex ℝ D ∧ ∃ gap > (0 : ℝ),
        (∀ θ ∈ D, spatialPart θ ∈ angularCone ℓ z.2.2 (retainedRadius b ρ) ∧
          gap ≤ ‖spatialPart θ‖ ∧ ‖θ‖ ≤ 2 * rb) ∧
        ∀ threshold > (0 : ℝ), ∀ (r : ℕ) (A : TwoTimeAmplitude d r)
          (P : Set (Euclidean 3)) (t lam : ℝ),
          t ∈ Icc 0 (3 * src / 4) → 0 < lam → ∀ order : ℤ,
          ∀ v ∈ tsupport (Function.uncurry (AnnularSobolev.normalizedAnnularElapsedAmplitude
            (P := Euclidean 3) A χout χsource
            (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
            (fun θ ↦ (annularSelector ra rb hra hrb θ : ℂ)) t lam order)),
            v.1.2 ∈ P →
            ((t, v.1), v.2) ∈ retainedClosedCarrier z (retainedRadius b ρ) P D := by
  let ε := retainedRadius b ρ
  have hε : 0 < ε := (retainedRadius_bounds hb hρ).1
  obtain ⟨χo, χs, ho, hs, hoc, hsc, _, _, hop, hsp, hos, hss, hplateau, hslab,
    R, hR, hXbound, hYbound, _⟩ := exists_retained_physical_masks z hε hsrc κ hκ hKs
      (isOpen_elapsedPhysicalBox z (ε / 2)) hKX
  let χout : E → ℂ := fun x ↦ (χo x : ℂ)
  let χsource : E → ℂ := fun x ↦ (χs x : ℂ)
  have hso : tsupport χout ⊆ tsupport χo := tsupport_comp_subset Complex.ofReal_zero _
  have hss' : tsupport χsource ⊆ tsupport χs := tsupport_comp_subset Complex.ofReal_zero _
  have hmask' : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 ((ε / 2) / 2) (aperture / 2) := by
    simpa only [ε, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hmask
  obtain ⟨D, hD, hDc, gap, hgap, hgeom, hsupport⟩ :=
    exists_retained_annular_frequency_carrier ℓ z.2.2 (half_pos hε) hAp hra hrb mask hmask'
  refine ⟨χout, χsource, Complex.ofRealCLM.contDiff.comp ho,
    Complex.ofRealCLM.contDiff.comp hs,
    hoc.of_isClosed_subset (isClosed_tsupport _) hso,
    hsc.of_isClosed_subset (isClosed_tsupport _) hss', ?_, ?_, hso.trans hos,
    hss'.trans hss, fun x hx ↦ hplateau x (hso hx), ?_, R, hR, hXbound,
    fun y hy i ↦ hYbound y (hss' hy) i, D, hD, hDc, gap, hgap, ?_, ?_⟩
  · simpa only [χout, Complex.ofReal_eq_one] using hop
  · simpa only [χsource, Complex.ofReal_eq_one] using hsp
  · intro x hx
    exact hslab x (by simpa only [χout, ne_eq, Complex.ofReal_eq_zero] using hx)
  · intro θ hθ
    have hh := hgeom θ hθ
    exact ⟨⟨hh.1.1.1, ball_subset_ball (by linarith : ε / 2 ≤ ε) hh.1.1.2⟩,
      hh.2⟩
  · intro threshold ht r A P t lam htime hlam order v hv hc
    have hfull := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource
      (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
      (fun θ ↦ (annularSelector ra rb hra hrb θ : ℂ)) t hlam.ne' order hv
    exact ⟨⟨retained_full_elapsed_interval_subset hsrc hρb hsrcρ htime,
      subset_closure (hos (hso hfull.1)), hc⟩,
      subset_closure (hss (hss' hfull.2.1)),
      hsupport threshold ht r A χout χsource t lam hlam order v hv⟩

end JanetCartan.ResponseTransfer.RetainedFactors
