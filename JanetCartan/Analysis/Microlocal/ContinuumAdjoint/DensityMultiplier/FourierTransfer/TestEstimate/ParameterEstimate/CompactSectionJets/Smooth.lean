module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.CompactSectionJets.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily

/-!
# Differentiation of the actual compact carrier section

The compact-family derivative is transferred through bounded zero extension to
transverse L². This supplies the derivative identity and smoothness used by
`exists_carrierTestSlice_jet_bound` for `app:ch_background:eq:bg-density-adjoint`.
Only the carrier parameters are differentiated.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
open ResponseTransfer.ParameterRealization.L2Family
open CompactSectionJets
variable {n : ℕ}

private def transverseSupport (f : carrierInitialTestSpace n) : Set (Euclidean (n - 1)) :=
  Prod.snd '' tsupport f.val

private lemma transverseSupport_compact (f : carrierInitialTestSpace n) :
    IsCompact (transverseSupport f) := f.property.2.image continuous_snd

private lemma test_zero_off_transverseSupport (f : carrierInitialTestSpace n)
    {η : Euclidean (n - 1)} (hη : η ∉ transverseSupport f) (z : CarrierParameter) :
    f.val (z, η) = 0 := by
  by_contra h
  exact hη ⟨(z, η), subset_tsupport f.val h, rfl⟩

private lemma compactFamily_test_apply (f : carrierInitialTestSpace n)
    (z : CarrierParameter) (η : transverseSupport f) :
    compactFamily (K := transverseSupport f) (fun z η ↦ f.val (z, η)) z η =
      f.val (z, η) :=
  compactFamily_apply (U := univ) (by simpa only [univ_prod_univ, Function.uncurry_def] using f.property.1.contDiffOn (s := univ)) (mem_univ z) η

private lemma compactFamily_test_contDiffAt (f : carrierInitialTestSpace n)
    [CompactSpace (transverseSupport f)] (k : ℕ) (z : CarrierParameter) :
    ContDiffAt ℝ k (compactFamily (K := transverseSupport f) (fun z η ↦ f.val (z, η))) z :=
  compactFamily_contDiffAt k isOpen_univ
    (by simpa only [univ_prod_univ, Function.uncurry_def] using f.property.1.contDiffOn (s := univ)) (mem_univ z)

private lemma compactToL2_test_eq_slice (f : carrierInitialTestSpace n)
    [CompactSpace (transverseSupport f)] (z : CarrierParameter) :
    compactToL2 (transverseSupport_compact f)
      (compactFamily (K := transverseSupport f) (fun z η ↦ f.val (z, η)) z) =
        Fubini.slice f.val z := by
  apply Lp.ext
  change (extendZero_memLp (transverseSupport_compact f) _).toLp _ =ᵐ[volume] _
  filter_upwards [(extendZero_memLp (transverseSupport_compact f)
    (compactFamily (K := transverseSupport f) (fun z η ↦ f.val (z, η)) z)).coeFn_toLp,
    Fubini.slice_coeFn (carrier_memLp_slice_of_continuous_hasCompactSupport
      f.property.1.continuous f.property.2 z)] with η hη hslice
  rw [hη, hslice]
  by_cases h : η ∈ transverseSupport f
  · rw [extendZero_mem _ h]
    exact compactFamily_test_apply f z ⟨η, h⟩
  · rw [extendZero_notMem _ h, test_zero_off_transverseSupport f h z]

/-- Actual norm smoothness of the transverse L²-valued compact-test section,
consumed by `exists_carrierTestSlice_jet_bound` for
`app:ch_background:prop:bg-adjoint`. -/
theorem contDiff_carrierTestSlice (f : carrierInitialTestSpace n) :
    ContDiff ℝ ∞ (Fubini.slice f.val) := by
  let : CompactSpace (transverseSupport f) :=
    isCompact_iff_compactSpace.mp (transverseSupport_compact f)
  rw [contDiff_iff_contDiffAt]
  intro z
  apply contDiffAt_infty.mpr
  intro k
  have h := (compactToL2 (transverseSupport_compact f)).contDiff.contDiffAt.comp z
    (compactFamily_test_contDiffAt f k z)
  convert h using 1
  funext a
  exact (compactToL2_test_eq_slice f a).symm

/-- Every evaluated derivative of the L² section is represented by the
corresponding actual carrier derivative. This concrete identity is used in the
norm estimate of `app:ch_background:eq:bg-density-adjoint`. -/
theorem iteratedFDeriv_carrierTestSlice_coeFn (f : carrierInitialTestSpace n)
    (k : ℕ) (z : CarrierParameter) (v : Fin k → CarrierParameter) :
    iteratedFDeriv ℝ k (Fubini.slice f.val) z v =ᵐ[volume]
      fun η ↦ iteratedFDeriv ℝ k (fun a ↦ f.val (a, η)) z v := by
  let : CompactSpace (transverseSupport f) :=
    isCompact_iff_compactSpace.mp (transverseSupport_compact f)
  let g := compactFamily (K := transverseSupport f) (fun z η ↦ f.val (z, η))
  have he : (compactToL2 (transverseSupport_compact f)) ∘ g = Fubini.slice f.val := by
    funext a
    exact compactToL2_test_eq_slice f a
  have hd := (compactToL2 (transverseSupport_compact f)).iteratedFDeriv_comp_left
    (compactFamily_test_contDiffAt f k z) (le_refl (k : ℕ∞ω))
  rw [he] at hd
  rw [hd]
  change (compactToL2 (transverseSupport_compact f) (iteratedFDeriv ℝ k g z v)) =ᵐ[volume] _
  change (extendZero_memLp (transverseSupport_compact f) _).toLp _ =ᵐ[volume] _
  filter_upwards [(extendZero_memLp (transverseSupport_compact f)
    (iteratedFDeriv ℝ k g z v)).coeFn_toLp] with η hη
  rw [hη]
  by_cases h : η ∈ transverseSupport f
  · rw [extendZero_mem _ h]
    have hev := (ContinuousMap.evalCLM ℝ (⟨η, h⟩ : transverseSupport f) (M := ℂ)).iteratedFDeriv_comp_left
      (compactFamily_test_contDiffAt f k z) (le_refl (k : ℕ∞ω))
    have heval : (ContinuousMap.evalCLM ℝ (⟨η, h⟩ : transverseSupport f) (M := ℂ)) ∘ g =
        fun a ↦ f.val (a, η) := by
      funext a
      exact compactFamily_test_apply f a ⟨η, h⟩
    rw [heval] at hev
    exact (congrArg (fun m ↦ m v) hev).symm
  · rw [extendZero_notMem _ h]
    have hz : (fun a ↦ f.val (a, η)) = fun _ ↦ (0 : ℂ) :=
      funext (test_zero_off_transverseSupport f h)
    rw [hz]
    cases k with
    | zero => simp
    | succ k => simp

end JanetCartan.ContinuumAdjoint.DensityMultiplier
