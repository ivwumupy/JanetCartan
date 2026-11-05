module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.PairedBounds

/-!
# Natural-order estimates on buffered supported conic charts

`SupportedSobolev.exists_graph_integer_sobolev_constant` and
`SupportedSobolev.exists_adjoint_integer_sobolev_constant` prove the integer
instances of `app:ch_regular_base:eq:fio-input` for orders zero and minus one.
The paired endpoint `exists_graph_adjoint_integer_sobolev_constant` uses the
same realization and its literal adjoint. All three retain output membership, input order `max(s-d,0)`, the original normalized
amplitude and phase seminorms, and the fixed reserve `μ = μ₀+2`.

The weak identities and all high-order branch estimates are derived. The only
operator inputs are the explicitly allowed fixed full-amplitude low L² reserve
and literal distributional realizations. The parent finite calculus must
instantiate those inputs and the original supported geometric hypotheses.
-/
