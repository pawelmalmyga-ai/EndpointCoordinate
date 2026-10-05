# Authorship, provenance, and verification

This document records how the research and the formalization in this
repository were produced. Its purpose is to distinguish the human research
contribution, AI-assisted work, and machine verification as clearly as
possible.

## Human contribution and responsibility

The underlying research problem and conceptual framework were developed and
directed by **Paweł Małmyga**. In particular, his contribution includes:

- the original research question concerning the position of the current
  observation relative to its exponentially weighted reference level;
- the interpretation of that displacement as an endpoint coordinate for a
  time series;
- the practical and financial interpretation of the construction;
- the decision to connect the endpoint coordinate to RSI, its bounded form,
  and its log-odds representation;
- the selection of the research direction, intended scope, assumptions, and
  claims considered relevant for publication;
- review and acceptance of the final mathematical statements included in the
  repository.

Paweł Małmyga is the human author and research director of the project. He is
responsible for the correspondence between the intended informal claims and
their formal statements, for empirical interpretation outside Lean, and for
all publication and citation decisions.

## AI contribution

AI systems contributed substantially as research, mathematical, programming,
and editorial tools. Their contribution included:

- proposing and developing candidate derivations and extensions;
- helping design proof strategies and the layered structure of the
  formalization;
- introducing or refining auxiliary definitions and lemmas needed by the
  formal proofs;
- translating mathematical statements and proofs into Lean 4;
- searching for suitable Mathlib results and constructing tactic proofs;
- diagnosing and repairing type, namespace, import, elaboration, and tactic
  errors;
- organizing modules, theorem names, and supporting documentation;
- drafting and revising explanatory text.

This assistance was substantive rather than merely typographical. The
repository should therefore not be described as an unaided human production
of every derivation, proof, or line of Lean code.

The work was iterative: Paweł Małmyga supplied the research direction,
interpretive framework, constraints, and final judgment, while AI systems
helped turn that program into detailed mathematical arguments and a checked
formal implementation. AI systems are not listed as authors because they
cannot review the final work independently, accept responsibility, or answer
for published claims.

AI-generated arguments and proof scripts were not treated as evidence of
correctness on their own.

## What Lean verification establishes

Every theorem in the verified source is accepted by the Lean kernel under the
assumptions stated in its type and in the imported foundations. At the time of
this disclosure, the project contains no `sorry`, `admit`, or project-defined
axioms.

This establishes that the formal conclusions follow from the formal
assumptions according to Lean's logic. The result does not depend on trusting
the natural-language explanation, an AI-generated derivation, or a tactic's
own claim that a proof succeeded: Lean checks the proof term produced by the
tactic.

## What Lean verification does not establish

Kernel acceptance does not by itself establish:

- that a formal definition is the only, or best, representation of the
  intended informal concept;
- that every assumption is empirically appropriate for financial time series;
- that market observations are independent or identically distributed;
- that a finite sample is accurately described by an asymptotic theorem;
- that software outside Lean implements the formal definitions correctly;
- that a theorem is novel or that its interpretation is economically useful;
- that any indicator, forecast, or trading strategy is profitable.

Those questions require human mathematical review, empirical investigation,
and, where appropriate, external peer review.

## Reproducibility

The repository pins its Lean toolchain and Mathlib dependencies. From the
repository root, obtain the dependency cache and build the complete project
with:

```bash
lake exe cache get
lake build
```

The authoritative verification target for a publication is the exact tagged
repository revision cited by that publication, rather than an unversioned
local working directory.

## Summary

- **Paweł Małmyga:** research origin, conceptual framework, interpretation,
  direction, selection of final claims, review, and responsibility.
- **AI systems:** substantial assistance with derivations, proof design, Lean
  implementation, debugging, organization, and documentation.
- **Lean kernel:** mechanical verification that the formal conclusions follow
  from the formal assumptions.

