# Public-release record

This document records the checks performed for the first public release and the
small number of external actions that cannot be completed inside the source
tree. It is not a claim of peer review.

## Verified for `v1.0.0`

- `lake build` completes successfully with the pinned Lean toolchain and
  Mathlib revision.
- GitHub Actions builds the project, checks Lean sources for proof
  placeholders, and runs the pinned symbolic audit.
- The Lean source contains no `sorry`, `admit`, or project-defined axioms.
- The theorem names cited in the manuscript and documentation are present in
  the stated modules.
- The documentation distinguishes kernel-checked declarations, conventional
  proofs, symbolic calculations, and numerical evidence.
- The main manuscript, heavy-tail technical note, numerical normality report,
  and price-path robustness report compile from their committed TeX sources
  without unresolved references.
- Internal Markdown links and YAML/CFF syntax have been checked.
- Generated build directories such as `.lake/` are excluded from version
  control.
- The current tree and all 15 pre-release commits were scanned for common
  high-confidence credential patterns; none were found.
- Authorship and AI assistance are disclosed in `PROVENANCE.md` and in the
  manuscripts.
- Software and research-content licenses are stated in `LICENSE`.

## Verification boundary

The Lean kernel checks the declarations in `EndpointCoordinate/*.lean` under
the assumptions visible in their types. In particular, it checks exact
finite-path identities, kernel geometry, conditional limit-transfer results,
benchmark-law layers, and the finite-variance CLT for normalized linear Wilder
rows.

The stationary nonlinear log-odds limit, Berry--Esseen argument, analytic
remainder estimates, and heavy-tail technical note remain conventional
mathematics. The SymPy audit checks finite symbolic coefficient calculations,
not analytic remainder bounds. The numerical normality audit is synthetic
evidence, not a proof and not a test on market data.

## Publication sequence

1. Commit the final release files and wait for a green CI run.
2. Run the manually triggered `Create Release` workflow with tag `v1.0.0`; it
   creates the immutable tag and release from the selected green commit.
3. Change repository visibility to public.
4. Cite the tag and commit rather than the moving `main` branch.

The repository includes a manually triggered release workflow. It does not
create releases merely because `lean-toolchain` changes.

## Post-publication metadata

The absence of an arXiv identifier or journal DOI is not a release blocker.
When either identifier becomes available:

1. add it to `CITATION.cff` and the manuscript;
2. create a small metadata-only patch release if desired;
3. connect the tagged GitHub release to Zenodo if a software archive DOI is
   useful.

## Suggested paper wording

> A specified subset of exact identities, kernel geometry, and auxiliary limit
> results was formalized in Lean 4 and checked by the Lean kernel. The
> stationary nonlinear limit, Berry--Esseen argument, and analytic remainder
> estimates remain conventional mathematical proofs. The versioned source,
> dependency manifest, and build instructions are available in the
> accompanying repository. Formal verification establishes derivability from
> the stated assumptions; it does not establish the empirical suitability of
> those assumptions for financial returns.
