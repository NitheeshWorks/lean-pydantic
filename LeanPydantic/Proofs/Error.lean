import LeanPydantic.Specifications

/-!
# Proofs: an error's `type`, `ctx` and `msg` agree

pydantic-core renders a message from the template of the error's `type`,
filled from its `ctx`. `ErrorKind.message` writes each message out; this
theorem says each one is exactly that rendering, so a client that knows only
`type` and `ctx` (and the input mode) can reproduce `msg`.
-/

namespace LeanPydantic

/-- **Coherence of `type`, `ctx` and `msg`**: the message is the template of
the error's type, rendered from its context. -/
theorem error_type_ctx_coherent (e : ErrorDetails) :
    e.msg = render e.ctx (template e.mode e.type) := by
  obtain ⟨k, _, _, m⟩ := e
  simp only [ErrorDetails.msg, ErrorDetails.ctx, ErrorDetails.type]
  cases k <;> (try cases m) <;>
    simp [ErrorKind.message, ErrorKind.ctx, ErrorKind.type, template, render, ctxLookup,
      displayValue, String.append_assoc, ErrorKind.containerMessage, containerTemplate]

end LeanPydantic
