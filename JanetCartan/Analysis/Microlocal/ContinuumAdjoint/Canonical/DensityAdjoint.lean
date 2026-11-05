module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.LocalAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RealAdjoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar

/-!
# Uniform real adjoint and density for the actual local positive scalar

The original density class supplies the initial-scalar bound on the SAME flow
ball. The global phase, supported normal, amplitude profiles and literal adjoint
are constructed by `LocalAdjoint`. Their real adjoint retains both quadratures.
The actual full-frequency density is bounded before and after the fixed cutoff,
whose plateau contains every supported footpoint. No raw-adjoint or multiplier
bound is an input.

The local operator is uniquely determined by its literal adjoint kernel.
Identification with the finite row requires that row's SAME kernel witnesses;
the finite-family/reference assembly is not asserted by this local theorem.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-realification` and
`app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DerivativeKernels PhaseExtension DensityMultiplier
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Uniform local construction for the manuscript's initial scalar
`σ * sqrt (1 + v₀)`. All constants and cutoffs precede the varying immersion and
density. The real adjoint is the literal adjoint of the unique complex operator
with this integral kernel. The cutoff equals one at every supported footpoint;
the density bound holds with and without it, with the one extra input derivative
and reserve `2*(n+1)+14` (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_projected_uniform_densityAdjoint (hn : 2 ≤ n)
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ row col : Fin n, ∃ R a b δ : ℝ,
      0 < R ∧ ∃ ha : 0 < a, ∃ hcell : 4*a < 1/2, ∃ hb : 0 < b,
      0 < δ ∧ ∃ χy : ContDiffBump (0 : CarrierVariable n), ∃ Cbound Lbound : ℕ → ℝ,
        (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K (2*(n+1)+13) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          (p.2, CanonicalCarrier.transportPosition T Q p))
          (supportedChart z₀ a) (interior {q | χy q = 1}) ∧
        ∃ Φ Y : ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3,
          ∀ v₀ : Euclidean (n-1) × Euclidean 3 → ℝ,
            ContDiffOn ℝ ∞ v₀ (ball ((0 : Euclidean (n-1)), z₀) (R/4)) →
            (∀ p ∈ ball ((0 : Euclidean (n-1)), z₀) (R/4), 0 < 1 + v₀ p) →
            (∀ p ∈ closedBall ((0 : Euclidean (n-1)), z₀) (R/8),
              1 + v₀ p ∈ Icc (1/2 : ℝ) (3/2)) →
            cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) (2*(n+1)) v₀ ≤ 1 →
            let initial := fun p ↦ positiveDensityAmplitude σ (v₀ p)
            let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
            let d := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
              (CanonicalConic.angularMask z₀ (NormedSpace.normalize ηb) ha hb)
              FixedCutoffs.highFrequency
            ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
              (∀ w, U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
              (∀ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ w, V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → V = U) ∧
              ∃ hraw : ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
                MemRawSobolev s ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 s v)),
              (∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
                rawSobolevNorm s ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 s v)) ≤
                  Cbound s * (‖v‖ +
                    (1 + cNorm K (s+2*(n+1)+13) F +
                      cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                        (s+2*(n+1)+13) initial) * ‖PeriodicSobolevSpace.toL2 s v‖)) ∧
              ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (Euclidean n) (s+1),
                let f := (carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 (s+1) v)
                let hf := (hraw (s+1) v).mono (by omega : 1 ≤ s+1)
                let H := 1 + cNorm K (s+2*(n+1)+14) F +
                  cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                    (s+2*(n+1)+14) initial
                MemPhysicalSobolev s (physicalComplexifyL2
                  (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ∧
                MemPhysicalSobolev s (physicalComplexifyL2
                  (density z₀ (NormedSpace.normalize ηb) ha hb χy f hf)) ∧
                physicalSobolevNorm s (physicalComplexifyL2
                  (densityUncut z₀ (NormedSpace.normalize ηb) ha hb f hf)) ≤
                    Lbound s * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 (s+1) v‖) ∧
                physicalSobolevNorm s (physicalComplexifyL2
                  (density z₀ (NormedSpace.normalize ηb) ha hb χy f hf)) ≤
                    Lbound s * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 (s+1) v‖) := by
  obtain ⟨Cscalar, _hCscalar, hscalarBound⟩ :=
    CanonicalCarrier.exists_density_initial_scalar_bound n (2*(n+1))
  obtain ⟨row, col, R, a, b, δ, hR, ha, hcell, hb, hδ, χy, Cbound, hCbound, hlocal⟩ :=
    exists_projected_uniform_local_carrierAdjoint T hn hP hz₀ hk hinc hd hK hKU hball
      hM hκmet hκ (σ * Cscalar)
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  choose L hL hdensity using fun s ↦
    exists_density_bounds z₀ (NormedSpace.normalize ηb) ha hb χy s
  refine ⟨row, col, R, a, b, δ, hR, ha, hcell, hb, hδ, χy,
    (fun s ↦ 2 * Cbound s), (fun s ↦ L s * (2 * Cbound (s+1))),
    (fun s ↦ mul_nonneg (by norm_num) (hCbound s)),
    (fun s ↦ mul_nonneg (hL s) (mul_nonneg (by norm_num) (hCbound (s+1)))), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, hplateau, Φ, Y, hscalar⟩ := hlocal F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, hplateau, Φ, Y, ?_⟩
  intro v₀ hv₀ hpos hinterval hvlow
  obtain ⟨hinitial, _hpositive, _hsquare, hIlow⟩ :=
    hscalarBound _ hR hσ v₀ hv₀ hpos hinterval hvlow
  obtain ⟨A, hA, hrawA⟩ := hscalar _ hinitial hIlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let d := CanonicalCarrier.data T Q F row col Φ Y
    (fun p ↦ positiveDensityAmplitude σ (v₀ p)) ha hcell
    (CanonicalConic.angularMask z₀ (NormedSpace.normalize ηb) ha hb)
    FixedCutoffs.highFrequency
  let U := A.adjoint
  have hU : U.adjoint = A := ContinuousLinearMap.adjoint_adjoint A
  have hrep w : U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w := by
    rw [hU]
    exact hA w
  have hreal (s : ℕ) (v : PeriodicSobolevSpace n (Euclidean n) s) :=
    carrierChannel_adjoint_raw_bound _ U A hA hrep (hCbound s)
      (show 0 ≤ 1 + cNorm K (s+2*(n+1)+13) F +
        cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) (s+2*(n+1)+13)
          (fun p ↦ positiveDensityAmplitude σ (v₀ p)) from
        add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..)) (cNorm_nonneg ..))
      (hrawA s) v
  refine ⟨U, hrep, ?_, (fun s v ↦ (hreal s v).1), (fun s v ↦ (hreal s v).2), ?_⟩
  · intro V hV
    have he := literalCarrierAdjointOperator_unique _ V.adjoint U.adjoint hV hrep
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      congrArg ContinuousLinearMap.adjoint he
  · intro s v
    obtain ⟨_, huncut, hcut⟩ := hdensity s _ (hreal (s+1) v).1
    refine ⟨huncut.1, hcut.1, ?_, ?_⟩
    · calc
        _ ≤ L s * rawSobolevNorm (s+1)
            ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 (s+1) v)) := huncut.2
        _ ≤ L s * ((2 * Cbound (s+1)) * (‖v‖ +
            (1 + cNorm K ((s+1)+2*(n+1)+13) F +
              cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                ((s+1)+2*(n+1)+13) (fun p ↦ positiveDensityAmplitude σ (v₀ p))) *
              ‖PeriodicSobolevSpace.toL2 (s+1) v‖)) :=
          mul_le_mul_of_nonneg_left (hreal (s+1) v).2 (hL s)
        _ = _ := by
          rw [show (s+1)+2*(n+1)+13 = s+2*(n+1)+14 by omega]
          ring
    · calc
        _ ≤ L s * rawSobolevNorm (s+1)
            ((carrierChannel U).adjoint (PeriodicSobolevSpace.toL2 (s+1) v)) := hcut.2
        _ ≤ L s * ((2 * Cbound (s+1)) * (‖v‖ +
            (1 + cNorm K ((s+1)+2*(n+1)+13) F +
              cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                ((s+1)+2*(n+1)+13) (fun p ↦ positiveDensityAmplitude σ (v₀ p))) *
              ‖PeriodicSobolevSpace.toL2 (s+1) v‖)) :=
          mul_le_mul_of_nonneg_left (hreal (s+1) v).2 (hL s)
        _ = _ := by
          rw [show (s+1)+2*(n+1)+13 = s+2*(n+1)+14 by omega]
          ring

end JanetCartan.ContinuumAdjoint.Canonical
