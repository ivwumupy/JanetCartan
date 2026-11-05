module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhysicalResidual

/-!
# The literal retained solver and full residual

This is the local same-witness endpoint for the sector's finite patch
selection. It constructs both physical masks, the nested spatial amplitude
mask and the right multiplier before varying `Q,B`. It then constructs the
order-zero operator for the literal `W₀+W₁` and the order-minus-one operator
for the literal full residual matrix `PW₁`, including the zeroth coefficient.
Both operators use the original supported auxiliary phase `G`.

Every analytic hypothesis after the fixed mask choices is a projection of
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii`:
the same chart's closed-buffer phase data and inverse source-time identity,
the three literal collared amplitude budgets, and the two supported phase
germs. No graph estimate, successful realization, or separately selected
chart is assumed. The parent applies that producer with the returned angular
mask and radial band and retains its witnesses. Finite patch selection is
outside this local deduction.

Sources: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`, and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 6400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase ConicAmplitude AmplitudeBounds UniformAmplitudes
open FourierIntegral EvolutionIntegral SymbolBudgets FiniteMasks ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- Construct both signed retarded operators on the literal retained pencil
amplitudes. The SAME `C,Φ,h,σ,κ,ℓ` occur in every formula. The two radius
comparisons and the time plateau are retained outputs of `ConicConstruction`;
the angular carrier and source compact are the finite-cover parent's fixed
geometric inputs. Constants and the single finite low order precede varying
`Q,B`, all Sobolev orders and any accuracy. The normalized amplitude estimates
below are precisely the producer's three published outputs on the returned
band, not new symbol assumptions (`retarded-kernel`, `energy-complete-residual`). -/
theorem exists_retained_local_solver_and_residual
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {b ρ src aperture : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hsrc : 0 < src)
    (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ/4) (hAp : 0 < aperture)
    (κ : ℝ → ℝ) (hκ : closedBall z.1 (src/4) ⊆ interior {t | κ t = 1})
    {Ksource Usource : Set E} (hKs : IsCompact Ksource)
    (hUs : IsOpen Usource) (hKUs : Ksource ⊆ Usource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (retainedRadius b ρ / 4) (aperture / 2))
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ (angular : Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      ContDiff ℝ ∞ angular ∧ (∀ η, angular η ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport angular ∧
      tsupport angular ⊆ angularCone ℓ z.2.2 (retainedRadius b ρ / 2) ∧
      (∀ η ∈ tsupport angular, 0 < ℓ η) ∧
    ∃ χout χsource : E → ℂ, ∃ _ho : ContDiff ℝ ∞ χout, ∃ hs : ContDiff ℝ ∞ χsource,
      HasCompactSupport χout ∧ HasCompactSupport χsource ∧
      KernelIdentification.timeSpacePoint z.1 z.2.1 ∈ interior {x | χout x = 1} ∧
      Ksource ⊆ interior {x | χsource x = 1} ∧
      tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius b ρ / 2) ∧
      tsupport χsource ⊆ Usource ∧
      (∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1)) ∧
    ∀ L' ≥ L,
      (∀ ξ ∈ tsupport (fun ξ ↦ (dilatedConicMask mask L' ξ : ℂ)),
        conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1)) ∧
    ∃ ra > (0 : ℝ), ∃ rb > ra,
    ∀ D : ℕ → ℝ, (∀ m, 0 < D m) →
    ∃ A₀ > (0 : ℝ), ∃ A₁ > (0 : ℝ), ∃ A Bnd : ℕ → ℝ,
      (∀ s, 0 < A s) ∧ (∀ s, 0 < Bnd s) ∧
    ∀ (i r c : Fin (d+1)) (σ : Z → ℝ)
      (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      cNorm KQ (retardedCoefficientOrder d) Q ≤ M →
      cNorm KQ (retardedCoefficientOrder d) B ≤ M →
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
      closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p) →
      (∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1/2) →
      (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
        phaseCost m * (1 + cNorm KQ (m+1) Q)) →
      (∀ p ∈ C.target, (C.symm p).2.1 = p.2.1) →
    let V := C.target ∩ C.symm ⁻¹'
      (ball z.1 (src/2) ×ˢ (ball z.1 (src/2) ×ˢ ball z.2 (src/2)))
    let Fs := fun j ↦ bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
    let W := fun j : Fin 3 ↦ collared ℓ (if j = 0 then 0 else 1) angular (Fs j)
    (∀ j : Fin 3, ContDiff ℝ ∞ (W j) ∧ tsupport (W j) ⊆ ConicPhase.domain ℓ V ∧
      ∀ m, BoundedTwoTimeOrderSeminorm (if j = 0 then 0 else 1)
        (bufferedJetSet ℓ z (ρ/2) ra rb) m (curryCharacteristicMatrix (W j)) ∧
        twoTimeOrderSeminorm (if j = 0 then 0 else 1) (bufferedJetSet ℓ z (ρ/2) ra rb) m
          (curryCharacteristicMatrix (W j)) ≤ D m *
            (1 + cNorm KQ (m+10) Q + cNorm KQ (m+9) B)) →
    (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
      (fun k ↦ W 2 p k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit i) p.2.1 p.2.2.2 y) k j)
          ((coordinateSplit i).symm (p.1, p.2.2.1))) →
    ∀ G : T → ℝ,
      (∀ p ∈ tsupport (W 0) ∪ tsupport (W 1), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) →
      (∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W 2 p ≠ 0 →
        G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) →
    ∃ Solver Residual : SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
      RetainedSignedRetardedBounds KQ Q B (3*src/4) (z.1-src/2)
        (fun t s y η ↦ G (t, (s, (y, η))))
        (curryCharacteristicMatrix (W 0) + curryCharacteristicMatrix (W 1))
        χout χsource (fun ξ ↦ (dilatedConicMask mask L' ξ : ℂ)) hs 0 A₀ A Solver ∧
      RetainedSignedRetardedBounds KQ Q B (3*src/4) (z.1-src/2)
        (fun t s y η ↦ G (t, (s, (y, η)))) (curryCharacteristicMatrix (W 2))
        χout χsource (fun ξ ↦ (dilatedConicMask mask L' ξ : ℂ)) hs 1 A₁ Bnd Residual ∧
      RetainedSignedRetardedBounds KQ Q B (3*src/4) (z.1-src/2)
        (fun t s y η ↦ G (t, (s, (y, η))))
        (twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth i B y).map Complex.ofReal) (curryCharacteristicMatrix (W 1)))
        χout χsource (fun ξ ↦ (dilatedConicMask mask L' ξ : ℂ)) hs 1 A₁ Bnd Residual := by
  have hε := (retainedRadius_bounds hb hρ).1
  obtain ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos, hnested⟩ :=
    exists_retained_nested_conicMask ℓ z hε mask hm hcarrier
  obtain ⟨χo, χs, ho, hs, hoc, hsc, _, _, hop, hsp, hos, hss, hplateau, hslab,
    R, hR, hXbound, hYbound, _⟩ := exists_retained_physical_masks z hε hsrc κ hκ hKs hUs hKUs
  let χout : E → ℂ := fun x ↦ (χo x : ℂ)
  let χsource : E → ℂ := fun x ↦ (χs x : ℂ)
  have ho' : ContDiff ℝ ∞ χout := Complex.ofRealCLM.contDiff.comp ho
  have hs' : ContDiff ℝ ∞ χsource := Complex.ofRealCLM.contDiff.comp hs
  have hso : tsupport χout ⊆ tsupport χo := tsupport_comp_subset Complex.ofReal_zero _
  have hss' : tsupport χsource ⊆ tsupport χs := tsupport_comp_subset Complex.ofReal_zero _
  have hoc' : HasCompactSupport χout := hoc.of_isClosed_subset (isClosed_tsupport _) hso
  have hsc' : HasCompactSupport χsource := hsc.of_isClosed_subset (isClosed_tsupport _) hss'
  have hκout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1) :=
    fun x hx ↦ hplateau x (hso (subset_tsupport χout hx))
  refine ⟨angular, L, hL, hang, hangr, hangc, hangs, hangpos,
    χout, χsource, ho', hs', hoc', hsc', ?_, ?_, hso.trans hos, hss'.trans hss,
    fun x hx ↦ hplateau x (hso hx), ?_⟩
  · simpa only [χout, Complex.ofReal_eq_one] using hop
  · simpa only [χsource, Complex.ofReal_eq_one] using hsp
  intro L' hLL
  obtain ⟨_, _, hβsub, hp⟩ := hnested L' hLL
  refine ⟨hp, ?_⟩
  obtain ⟨ra, hra, rb, hrab, hconstruct⟩ := exists_retained_signed_retarded_operators
    (q := d+1) ℓ z hb hρ hsrc hρb hsrcρ hAp χout χsource ho' hs' hoc' hsc'
    (hso.trans hos) (fun x hx ↦ hslab x (by simpa only [χout, ne_eq, Complex.ofReal_eq_zero] using hx))
    R hR hXbound (fun y hy ↦ hYbound y (hss' hy)) mask hm hcarrier L' (hL.trans hLL)
    hβsub phaseCost hphaseCost M hM
  refine ⟨ra, hra, rb, hrab, ?_⟩
  intro D hD
  obtain ⟨A₀, hA₀, A, hA, hsolver⟩ :=
    hconstruct (fun m ↦ 2 * D m) (fun m ↦ mul_pos (by norm_num) (hD m)) 0 (Or.inl rfl)
  obtain ⟨A₁, hA₁, Bnd, hBnd, hresidual⟩ := hconstruct D hD 1 (Or.inr rfl)
  refine ⟨A₀, hA₀, A₁, hA₁, A, Bnd, hA, hBnd, ?_⟩
  intro i r c σ KQ Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime V Fs W hW hphysical G hG hGres
  have hWsum : ContDiff ℝ ∞ (W 0 + W 1) := (hW 0).1.add (hW 1).1
  have hWsumSupport : tsupport (W 0 + W 1) ⊆ ConicPhase.domain ℓ V :=
    (tsupport_add (W 0) (W 1)).trans (union_subset (hW 0).2.1 (hW 1).2.1)
  have hjoint (j : Fin 3) : ContDiff ℝ ∞ (jointAmplitude (curryCharacteristicMatrix (W j))) :=
    (hW j).1.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have hsum m := solver_coefficient_bound KQ Q B (isCompact_bufferedJetSet ℓ z (ρ/2) ra rb)
    (hjoint 0) (hjoint 1) D (hW 0).2.2 (hW 1).2.2 m
  obtain ⟨Solver, hSolver⟩ := hsolver KQ Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase
    hsourceTime (W 0 + W 1) hWsum hWsumSupport hsum
  obtain ⟨Residual, hResidual⟩ := hresidual KQ Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase
    hsourceTime (W 2) (hW 2).1 (hW 2).2.1 (hW 2).2.2
  have hResidualSupported := retained_residual_bounds_supported_phase KQ Q B ℓ C (W 2) G κ hGres
    χout χsource _ hκout hs' _ _ A₁ Bnd Residual hResidual
  refine ⟨Solver, Residual,
    retained_solver_bounds_supported_phase KQ Q B ℓ C (W 0) (W 1) G hG
      χout χsource _ hs' _ _ A₀ A Solver hSolver,
    hResidualSupported, ?_⟩
  exact retained_signed_bounds_amplitude_congr KQ Q B _ (curryCharacteristicMatrix (W 2)) _
    χout χsource _ (fun x hx s η ↦
      retained_residual_eq_twoTimePhysicalApply i Q B (W 1) (W 2) κ (hW 1).1 hphysical
        x (hκout x hx) s η) hs' _ _ A₁ Bnd 1 Residual hResidualSupported

end JanetCartan.RegularSector.Characteristic.UniformEvolution
