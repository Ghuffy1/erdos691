# Source credit and rights

## Classical mathematics

H. Davenport and P. Erdős, *On sequences of positive integers*, Acta Arithmetica 2 (1936), 147–151, supplies the classical finite-approximation theorem used in the density transfer. The manuscript cites this result and proves the new criterion from it. [Original paper](https://renyi.hu/~p_erdos/1936-04.pdf)

P. Erdős, *Some unconventional problems in number theory*, Astérisque 61 (1979), 73–82, printed p. 77, supplies the original question. [Original paper](https://www.numdam.org/article/AST_1979__61__73_0.pdf)

## Adapted formal source

The initial classical Davenport–Erdős dependency in `Erdos691.lean` is adapted from **yuta0x89/ErdosProblems**, `Erdos691.lean`, commit **1aa94199fd3874e25b2126a0ff153e144e3e9c04**. Its original SHA256 is `0b01fd987b9f907eb695f573ba43d96108af669c0ccd00ea94d1e48579399b4e`. The adaptation selected the needed classical argument and repaired elaboration for the pinned environment. [Pinned source](https://github.com/yuta0x89/ErdosProblems/blob/1aa94199fd3874e25b2126a0ff153e144e3e9c04/Erdos691.lean)

The file contains an explicit Apache 2.0 notice at upstream lines 859–863, naming OpenAI ChatGPT. It is retained at lines 896–900 of the submitted file. The repository has no top-level LICENSE, so the earlier repository-metadata check missed this declaration. This package follows the file-level Apache 2.0 notice, includes the full license and a NOTICE, preserves attribution, and identifies the modifications. The notice occurs after the first analytic section and states no narrower scope. This is the licensing basis used for the private preparation. [Embedded notice](https://github.com/yuta0x89/ErdosProblems/blob/1aa94199fd3874e25b2126a0ff153e144e3e9c04/Erdos691.lean#L859)

The team's adaptive criterion, probability construction, finite pruning, recursive family construction, exact arithmetic fiber bridge, and statement bridge are the new formalization contribution in this repository. The mathematical and Lean credits for the classical input remain with the cited authors and source contributor.

## Libraries and process documents

Lean and Mathlib are external dependencies. Their source and license notices remain in their own repositories, at the revisions pinned by `lean-toolchain` and `lake-manifest.json`. Dependencies and compiled library artifacts are excluded from this repository.

The unmodified process documents in `submission/rules-snapshot/` are by The Justin Sun Prize contributors, from awards commit `f8801a856529dce27e738c6b305e46d76e7c387c`. Their documentation license, Creative Commons Attribution 4.0 International, is preserved in that directory. The snapshot identifies the rules used for this preparation. [Pinned rules repository](https://github.com/TheJustinSunPrize/awards/tree/f8801a856529dce27e738c6b305e46d76e7c387c)
