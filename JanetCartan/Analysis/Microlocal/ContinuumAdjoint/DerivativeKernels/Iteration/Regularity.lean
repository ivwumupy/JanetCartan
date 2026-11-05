module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Expansion

/-!
# Regularity of the constructed adjoint amplitudes

The invariant used by the ordered derivative expansion in
`app:ch_background:prop:bg-adjoint` consists only of joint smoothness and common
measurement support. No derivative trade or integral identity is a field.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison
variable {n : ℕ}

/-- Analytic input for iterating `app:ch_background:eq:bg-derivative-trade`.
Frequency is a spectator; smoothness is joint in carrier and measurement. -/
structure SmoothSupportedAdjointAmplitude (S : Set (Euclidean n))
    (a : AdjointAmplitude n) : Prop where
  smooth : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ a p.1 p.2 η)
  zero_off : ∀ z x η, x ∉ S → a z x η = 0

/-- Common closed measurement support implies sectionwise topological support,
for the compact-integral consumer in `app:ch_background:prop:bg-adjoint`. -/
theorem SmoothSupportedAdjointAmplitude.tsupport_subset {S : Set (Euclidean n)}
    {a : AdjointAmplitude n} (ha : SmoothSupportedAdjointAmplitude S a)
    (hS : IsClosed S) (z : CarrierParameter) (η : Euclidean (n - 1)) :
    tsupport (fun x ↦ a z x η) ⊆ S := by
  apply closure_minimal _ hS
  intro x hx
  by_contra hn
  exact hx (ha.zero_off z x η hn)

private theorem smooth_measurement_partial
    {f : CarrierParameter × Euclidean n → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
      partialDeriv (fun y ↦ f (p.1, y)) p.2 j) := by
  exact (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv_apply
    contDiff_snd contDiff_const (by simp)

/-- The zero branch preserves joint smoothness and common measurement support
in `app:ch_background:prop:bg-adjoint`. In particular carrier derivatives do not
enlarge the measurement support. -/
theorem SmoothSupportedAdjointAmplitude.zeroBranch
    {S : Set (Euclidean n)} (hS : IsClosed S)
    {a : AdjointAmplitude n} (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (d : InitialCarrierDerivative n) :
    SmoothSupportedAdjointAmplitude S (zeroBranchAmplitude L V d a) := by
  have hs (η) (W : CarrierParameter → Euclidean n → Euclidean n)
      (hW : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ W p.1 p.2)) (j) :
      ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦
        partialDeriv (fun y ↦ W p.1 y j • a p.1 y η) p.2 j) :=
    smooth_measurement_partial
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp hW).smul
        (ha.smooth η)) j
  have hz (z x η) (hx : x ∉ S) (W : Euclidean n → Euclidean n) (j) :
      partialDeriv (fun y ↦ W y j • a z y η) x j = 0 := by
    have hn : x ∉ tsupport (fun y ↦ W y j • a z y η) :=
      fun hm ↦ hx (ha.tsupport_subset hS z η
        (tsupport_smul_subset_right _ _ hm))
    unfold partialDeriv
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
    rfl
  cases d with
  | initial h =>
    refine ⟨?_, ?_⟩
    · intro η
      exact ContDiff.sum (s := Finset.univ)
        (fun j _ ↦ hs η (fun z x ↦ L z x h) (hL h) j)
    intro z x η hx
    exact Finset.sum_eq_zero (s := Finset.univ)
      (fun j _ ↦ hz z x η hx (fun y ↦ L z y h) j)
  | carrier h =>
    refine ⟨?_, ?_⟩
    · intro η
      apply ContDiff.sub
      · exact ((ha.smooth η).comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv_apply
          contDiff_fst contDiff_const (by simp)
      · exact ContDiff.sum (fun j _ ↦ hs η (fun z x ↦ V z x h) (hV h) j)
    · intro z x η hx
      have he : (fun w ↦ a w x η) = fun _ ↦ (0 : ℂ) :=
        funext (fun w ↦ ha.zero_off w x η hx)
      simp only [zeroBranchAmplitude, carrierZeroAmplitude, transportCoefficient, he,
        fderiv_fun_const]
      rw [Finset.sum_eq_zero (fun j _ ↦ hz z x η hx (fun y ↦ V z y h) j)]
      simp

/-- The branch adding a datum derivative preserves the same analytic invariant
(`app:ch_background:prop:bg-adjoint`). -/
theorem SmoothSupportedAdjointAmplitude.firstBranch
    {S : Set (Euclidean n)} {a : AdjointAmplitude n}
    (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (d : InitialCarrierDerivative n) (j : Fin n) :
    SmoothSupportedAdjointAmplitude S (firstBranchAmplitude L V d a j) := by
  cases d with
  | initial h =>
    refine ⟨fun η ↦ ?_, ?_⟩
    · exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
        (hL h)).smul (ha.smooth η)
    · intro z x η hx
      simp [firstBranchAmplitude, initialFirstAmplitude, ha.zero_off z x η hx]
  | carrier h =>
    refine ⟨fun η ↦ ?_, ?_⟩
    · exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
        (hV h)).smul (ha.smooth η)).neg
    · intro z x η hx
      simp [firstBranchAmplitude, carrierFirstAmplitude, ha.zero_off z x η hx]

/-- Every amplitude in the concrete expansion has the original compact
measurement support and is jointly smooth (`app:ch_background:prop:bg-adjoint`). -/
theorem smoothSupported_adjointDerivativeExpansion
    {S : Set (Euclidean n)} (hS : IsClosed S)
    {a : AdjointAmplitude n} (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    SmoothSupportedAdjointAmplitude S t.amplitude := by
  induction ds generalizing t with
  | nil =>
    simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
    subst t
    exact ha
  | cons d ds ih =>
    obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
    simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at ht
    rcases ht with rfl | ⟨j, rfl⟩
    · exact (ih q hq).zeroBranch hS hL hV d
    · exact (ih q hq).firstBranch hL hV d j

/-- Smooth compact measurement amplitudes give a smooth carrier function after
integration; the required interchange follows from compact parameter integration
(`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_chartAdjoint_carrier
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {a : AdjointAmplitude n} (ha : SmoothSupportedAdjointAmplitude S a)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v) (η : Euclidean (n - 1)) :
    ContDiff ℝ ∞ (fun z ↦ chartAdjoint (fun x ↦ Φ z x η) (fun x ↦ a z x η) v) := by
  let F : CarrierParameter × Euclidean n → ℂ := fun p ↦
    oscillatoryFactor (-1) (Φ p.1 p.2 η) * (a p.1 p.2 η * v p.2)
  have hF : ContDiff ℝ ∞ F := (CompactTransport.contDiff_oscillatoryFactor (hΦ η) (-1)).mul
    ((ha.smooth η).mul (hv.comp contDiff_snd))
  have he (z) : chartAdjoint (fun x ↦ Φ z x η) (fun x ↦ a z x η) v =
      ∫ x in S, F (z, x) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      simp [F, ha.zero_off z x η hx]
  simp_rw [he]
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hS.measure_lt_top (μ := volume)⟩
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ
    hS (subset_univ _) hF.contDiffOn)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
