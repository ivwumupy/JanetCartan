module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveFamily
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

/-!
# The bounded retarded operator from original phase and symbol data

The elapsed graph family is constructed, its low amplitude budget is proved
from the original spatial symbol, and both orbit measurability statements
and literal kernel limits follow from these actual regularizations. All
physical masks and the lower endpoint are retained. This closes the low
realization portion of `app:ch_regular_base:lem:retarded-kernel`; higher
Sobolev estimates are a separate obligation.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets KernelIdentification FullLowBounds WholeImageGeometry
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open LowBounds FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)

/-- The full masks give the actual amplitude's admissibility. Consumer:
`exists_retardedOperator_of_primitive_data`, in the fixed-time representation. -/
theorem elapsedAmplitude_forwardAdmissible
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hb : ContDiff ℝ ∞ (jointAmplitude b))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (r : ℝ) : ForwardAmplitudeAdmissible
      (tsupport χout) (tsupport χsource) (tsupport β) (elapsedAmplitude b χout χsource β r) := by
  refine ⟨?_, ?_⟩
  · exact (contDiff_uncurry_elapsedAmplitude b χout χsource β hb ho hs hβ r).comp
      ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  · intro x y ξ h
    apply elapsedAmplitude_eq_zero_of_mask
    rcases h with h | h | h
    · exact Or.inl (image_eq_zero_of_notMem_tsupport h)
    · exact Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport h))
    · exact Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport h))

/-- Construct the bounded retarded operator from primitive spatial geometry
and original symbol budgets. The same low constant works for every phase and
amplitude satisfying the fixed budgets and for both spatial orders. Neither
low graph bounds, regularizations, test actions nor measurability are inputs.
The uncut action and literal adjoint are the strong limits of the physical
retarded kernels with all masks; the latter reverses the time triangle.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_retardedOperator_of_primitive_data
    (R ℓ Bmix Btime Bphase Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2) {ε : ℝ} (hε : 0 < ε)
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hβzero : (0 : E) ∉ tsupport β)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t)
    (hβbound : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1)) (jointMultiplier β))
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) :
    ∃ a > 0, ∃ b > a, ∃ C > 0,
      ∀ (Xouter : Set E) (Douter : Set (Euclidean d)) (X Dnormal : Set E),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Douter →
        tsupport χout ⊆ X → tsupport β ⊆ Dnormal → (∀ x ∈ X, ‖x‖ ≤ R) →
        (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
      ∀ K : Set (Point (d + 1)), IsCompact K →
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ ≤ Btime →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          phasePairInclusion p ∈ K) →
        (∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J) →
      ∀ Ψ : TwoTimePhase d,
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ContDiffAt ℝ ∞ (jointPhase Ψ) ((x 0, x 0-r, spatialPart x), η)) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Douter, ∀ t : ℝ, 0 < t →
          Ψ (x 0) (x 0-r) (spatialPart x) (t • η) =
            t * Ψ (x 0) (x 0-r) (spatialPart x) η) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Douter,
          ‖fderiv ℝ (fun η ↦ fderiv ℝ
            (fun p : ℝ × ℝ × Euclidean d ↦ Ψ p.1 p.2.1 p.2.2 η)
            (x 0, x 0-r, spatialPart x)) η‖ ≤ Bmix) →
        (∀ j : ℕ, ContDiffOn ℝ ∞
          (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) U) →
        (∀ j : ℕ, cNorm J (wholeImagePhaseReserve (d + 1))
          (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) ≤ Bphase) →
      ∀ (o : ℕ) (M : ℝ) (b : TwoTimeAmplitude d q),
        ContDiff ℝ ∞ (jointAmplitude b) →
        BoundedTwoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b →
        twoTimeOrderSeminorm o J (fullLowReserve (d + 1)) b ≤ M →
      ∀ a₀ : ℝ, (∀ x, χout x ≠ 0 → x 0 ∈ Icc a₀ (a₀ + Δ)) →
        (∀ t s y η, s ≤ a₀ → b t s y η = 0) →
      (∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C * M) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
        (volume.restrict (Icc 0 Δ))) ∧
      ∃ χ : ℕ → E → ℂ, ∃ hχ : ∀ j, ContDiff ℝ ∞ (χ j),
        ∃ hχcs : ∀ j, HasCompactSupport (χ j),
      (∀ A : FullAmplitude (d + 1) q, (∀ x y ξ, ξ ∉ tsupport β → A x y ξ = 0) →
        ∀ j, frequencyCutFullAmplitude (χ j) A =
          frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
      (∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
        ∃ R : ℕ → SpacetimeL2 d q,
          (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (χout x • graphOperator (Ψ (x 0) (x 0-r))
              (fun y _ η ↦ b (x 0) (x 0-r) y η)
              (cutPhysicalMultiplierSlice β (χ j)
                (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
                hβ (hχ j) (hχcs j) (x 0-r)) (spatialPart x))) ∧
          Tendsto R atTop (𝓝 (elapsedGraph Ψ b χout χsource β r (graphTestToLp u)))) ∧
      ∃ Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        ‖Q‖ ≤ Δ * (C * M) ∧
        (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
        (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
        ∀ u : graphTestSpace (d + 1) q,
          ∃ R RAdj : ℕ → SpacetimeL2 d q,
            (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
              (cutRetardedPhysical Ψ b χout χsource β (χ j) hs hβ (hχ j) (hχcs j) a₀ u x)) ∧
            (∀ j, RAdj j =ᵐ[volume] fun y ↦ WithLp.toLp 2
              (cutReverseRetardedFourier Ψ b χout χsource β (χ j)
                (fun x ↦ (u.val x).ofLp) a₀ (a₀ + Δ) y)) ∧
            Tendsto R atTop (𝓝 (Q (graphTestToLp u))) ∧
            Tendsto RAdj atTop (𝓝 (Q.adjoint (graphTestToLp u))) := by
  classical
  obtain ⟨a, ha, b, hab, Cg, hCg, hf⟩ := exists_elapsedGraphFamily_of_primitive_phase
    (q := q) R ℓ Bmix Btime Bphase Δ hℓ hRcell hε
  obtain ⟨Ca, hCa, hbudget⟩ := exists_elapsed_fullLowReserve_constant
    (q := q) z δ hJ hU hJU χout χsource β ho hs hβ isClosed_univ
    (fun p hp ↦ hcover p ⟨hp.1, hp.2.1⟩) hβbound Δ hmap
  refine ⟨a, ha, b, hab, Cg * Ca, mul_pos hCg (lt_of_lt_of_le zero_lt_one hCa), ?_⟩
  intro Xouter Douter X Dnormal hXouter hDouter hcXouter hcDouter hX hDn hcX
    hXX hDD hXsub hFsub hR hcollar K hK htime hchart hmapK Ψ hΨ hnear hhom hmix
    hnormalized hphase o M b hb hbfinite hbM a₀ hout hzero
  obtain ⟨χ, hχ, hχcs, _hχzero, hχeq, hf⟩ := hf
    (tsupport χout) (tsupport χsource) (tsupport β) hocs hYbox (isClosed_tsupport _) hβzero
  have hf := hf Xouter Douter X Dnormal hXouter hDouter hcXouter hcDouter
    hX hDn hcX hXX hDD hXsub hFsub hR hcollar K J U hK hJ hU hJU htime hchart
    hmapK Ψ hΨ hnear hhom hmix hnormalized hphase
  have hl (r : ℝ) (hr : r ∈ Icc 0 Δ) := hf r hr
    (elapsedAmplitude b χout χsource β r)
    (elapsedAmplitude_forwardAdmissible b χout χsource β hb ho hs hβ r) (Ca * M)
    (hbudget o M b hb (fun _ _ _ _ h ↦ (h (mem_univ _)).elim) hbfinite hbM r hr)
  choose T ht hta htr hreal hrealAdj hlim hlimAdj htest hdist hdistAdj using hl
  let Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q :=
    fun j r ↦ if hr : r ∈ Icc 0 Δ then T r hr j else 0
  have hlow (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      ‖elapsedGraph Ψ b χout χsource β r‖ ≤ Cg * Ca * M := by
    simpa only [elapsedGraph, mul_assoc] using ht r hr
  have hreal' : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u := by
    intro j r hr u
    simpa only [Treg, dite_eq_left hr] using hreal r hr j u
  have hrealAdj' : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x y ξ ↦ (elapsedAmplitude b χout χsource β r x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y) := by
    intro j r hr u
    simpa only [Treg, dite_eq_left hr] using hrealAdj r hr j u
  have hsΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
    intro r hr x hx ξ hξ
    exact ((hΨ r hr x (hXX (subset_closure (hXsub hx))) _
      (hDD (subset_closure (hFsub hξ)))).comp ((x 0, x 0-r), (spatialPart x, spatialPart ξ))
      (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ ((p.1.1, p.1.2, p.2.1), p.2.2))
      ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd.fst)).prodMk
        contDiffAt_snd.snd)).continuousAt
  have hsb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
    intro r _ x _ ξ _
    exact (hb.comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous.continuousAt
  have hret := exists_retardedOperator_of_regularizations Ψ b χout χsource β Δ hΔ
    hsΨ hsb ho.continuous hs hβ hocs hscs χ hχ hχcs Treg hreal' hrealAdj'
    (C := Cg * Ca * M)
    (fun j r hr ↦ by simpa only [Treg, dite_eq_left hr, mul_assoc] using htr r hr j)
    (fun r hr u ↦ by simpa only [Treg, dite_eq_left hr, elapsedGraph] using hlim r hr u)
    (fun r hr u ↦ by simpa only [Treg, dite_eq_left hr, elapsedGraph] using hlimAdj r hr u)
    a₀ hout hzero
  refine ⟨hlow, hret.1, hret.2.1, χ, hχ, hχcs, hχeq, ?_, hret.2.2⟩
  exact elapsedGraph_strongLimit_spatialGraphs Ψ b χout χsource β Δ
    hsΨ hsb hs hβ χ hχ hχcs Treg hreal'
    (fun r hr u ↦ by simpa only [Treg, dite_eq_left hr, elapsedGraph] using hlim r hr u)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
