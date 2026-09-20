# Palomar and Comparator requirements evidence

Checked against first-party sources on 30 August 2026. Exact repository HEADs
were obtained with `git ls-remote <official-url> HEAD`.

## Frozen authorities

| Authority | Observed immutable revision | Exact URL |
|---|---|---|
| Palomar policy | `d5a647db3757303b1d928cfae4d3d232eed3e79e` | <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md> |
| Palomar template | `128a6c5ce5f48622e69927ccd639cbff401022e8` | <https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8> |
| Palomar verifier repository | `e215b184d1b659e8e3e641162a7d63708678016f` | <https://github.com/PalomarRegistry/PalomarSubmission/tree/e215b184d1b659e8e3e641162a7d63708678016f> |
| Comparator documentation | observed HEAD `2312244ac716564a61cc0bf4e107d9abf1757a61` | <https://github.com/leanprover/comparator/blob/2312244ac716564a61cc0bf4e107d9abf1757a61/README.md> |

Recheck all four immediately before the final public commit because policy and
tooling can change.

## Binding and mechanical requirements

The policy's ordinary layout uses a toolchain file, exactly one Lakefile, a
committed manifest, `formalization.yaml`, distinct Challenge and Solution
modules, one Comparator configuration, and exactly one recognized root licence
file. Submission identifies a public GitHub repository, a full 40-character
commit SHA, and the repository-relative Comparator path; a branch or tag is not
a substitute. The checkout, excluding `.git` and symlinks, must be at most
500 MiB.

Evidence:

- <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md#2-prepare-an-ordinary-submission>
- <https://submit.palomar-registry.org/>

The Challenge must be the short auditable statement surface. Its transitive
imports may contain only Lean core, canonical verified Mathlib, Tau Ceti, or
CSLib sources. The Solution may use arbitrary public GitHub Git dependencies,
but every Git dependency in the manifest must use a credential-free GitHub URL
and a full lowercase commit SHA. No submitted or substantive Git submodules,
Git LFS pointers, or compiled artifacts outside `.lake` are accepted. The
Challenge hard limit is 100 KiB/1,000 lines, with warnings above 32 KiB/300
lines.

Evidence:

- <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md#22-challenge-and-solution-modules>
- <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md#24-dependencies>

`comparator.json` requires distinct `challenge_module` and `solution_module`, a
nonempty `theorem_names` array, and `permitted_axioms` drawn only from
`propext`, `Quot.sound`, and `Classical.choice`. The optional
`definition_names` and `enable_nanoda` keys are the only additional accepted
keys. Palomar ignores the submitted NanoDa switch and writes a protected config
that enables NanoDa.

Evidence:

- <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md#23-comparator-configuration>
- <https://github.com/PalomarRegistry/PalomarSubmission/blob/e215b184d1b659e8e3e641162a7d63708678016f/README.md#required-source-layout>

The verifier compiles the Challenge separately, protects it from project build
output, runs Comparator without network access or credentials, and requires
every exported proof to pass Lean's kernel and NanoDa. A green mechanical
report proves statement/proof agreement under those checks; it does not prove
mathematical significance, source fidelity, novelty, or peer review.

Evidence:

- <https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md#5-what-mechanical-verification-establishes>
- <https://github.com/leanprover/comparator/blob/2312244ac716564a61cc0bf4e107d9abf1757a61/README.md>

Current metadata uses `formalization.yaml` v0.4 and requires a nonempty project
identity, public description, authors, responsible maintainers, licence,
classification, sources with a coherent origin relationship, automation
methods, and review status. The root licence and `project.license` must agree on
one standard SPDX identifier.

Evidence:

- <https://github.com/PalomarRegistry/PalomarSubmission/blob/e215b184d1b659e8e3e641162a7d63708678016f/README.md#required-source-layout>
- <https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/128a6c5ce5f48622e69927ccd639cbff401022e8/formalization.yaml>

## Toolchain and verifier pins used here

Palomar's current minimum is `v4.28.0`:
<https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/e215b184d1b659e8e3e641162a7d63708678016f/toolchains.json>.
The verifier accepts released or RC toolchains at or above that minimum and
derives a matching lean4export release tag. This candidate instead follows the
official template's supported stable line:

- Lean `v4.32.0`:
  <https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/128a6c5ce5f48622e69927ccd639cbff401022e8/lean-toolchain>
- Mathlib manifest commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`:
  <https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/128a6c5ce5f48622e69927ccd639cbff401022e8/lake-manifest.json>
- Comparator `68a064109f01c08f47c8edc9f51d6a2bbffaa188`
- lean4export `4e7915201d3f9f04470d9eae002fa695f7cdc589`
- Landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
- NanoDa `68d5ca9db226849b41a6fff59d796ff19d0a8840`

Those four immutable revisions come directly from the official template script:
<https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/128a6c5ce5f48622e69927ccd639cbff401022e8/scripts/verify-comparator.sh>.
The pinned lean4export declares the same Lean toolchain:
<https://raw.githubusercontent.com/leanprover/lean4export/4e7915201d3f9f04470d9eae002fa695f7cdc589/lean-toolchain>.

The template's full local verifier requires Linux, Git, Go, Ruby, Rust/Cargo,
Python 3, and a working Landrun sandbox. `scripts/verify-linux.sh` preserves
that boundary and refuses macOS as authoritative evidence.

