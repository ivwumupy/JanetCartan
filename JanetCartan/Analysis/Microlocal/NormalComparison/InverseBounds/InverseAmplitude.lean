module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Jets

/-!
# The smooth buffered inverse normal amplitude

The mask-free amplitude of `app:ch_osc:setup:osc-normal` and Step 1 of
`app:ch_osc:prop:osc-normal`, in native `(x,(y,v))` coordinates. Its actual
absolute Jacobian and both independent physical positions are retained.

The physical zero extension is globally spatially smooth, has a fixed compact
support, and has local ambient smooth extensions at both parameter endpoints.
Its full spatial Frobenius jets through `2(n+1)` are bounded by constants
chosen before the phase/amplitude family, from the original finite input jets.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ}

/-- Uniform full spatial Frobenius jets of the physical zero extension,
with all extra premises discharged (`app:ch_osc:prop:osc-normal`, Step 1).
Only the geometry and the finite original input bounds determine the constant. -/
theorem UniformNormalGeometry.exists_extendedInverseAmplitude_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ K > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ z : Euclidean n × (Euclidean n × Euclidean n), ∀ k ≤ 2 * (n + 1),
        ‖iteratedFDeriv ℝ k (F.extendedInverseAmplitude ε) z‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := G.exists_maskFreeInverseAmplitude_chart_jet_bound
    C (2 * (n + 1)) (by omega)
  refine ⟨K, hK, ?_⟩
  intro F ε hε z k hk
  by_cases hz : z ∈ G.X ×ˢ (G.X ×ˢ G.V)
  · have he : F.extendedInverseAmplitude ε =
        fun q ↦ F.maskFreeInverseAmplitude ε q.1 q.2.1 q.2.2 :=
      funext (F.extendedInverseAmplitude_eq_maskFree hε)
    rw [he]
    exact hbound F ε hε z hz k hk
  · have he := ((F.extendedInverseAmplitude_eventuallyEq_zero hε hz).iteratedFDeriv ℝ k).eq_of_nhds
    rw [he]
    simpa using hK.le

end JanetCartan.NormalComparison
