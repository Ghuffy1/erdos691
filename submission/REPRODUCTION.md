# Reproduction and trust

Use a fresh checkout of the selected full 40-character proof commit. Install official Elan and Python 3.9 or later. The `lean-toolchain` file selects Lean 4.34.0. The manifest fixes Mathlib and eight supporting packages by full Git commit.

```sh
lake exe cache get
python scripts/verify.py --fresh
```

The following are the individual proof checks used by the script.

```sh
lake build
lake build +Erdos691
lake build +Challenge
lake build +Audit
lake env lean Erdos691.lean
lake env lean Challenge.lean
lake env lean Audit.lean
lake env leanchecker -v Erdos691
lake env leanchecker -v Challenge
lake env leanchecker --fresh -v Challenge
```

`lake build` includes `Erdos691`, `Challenge`, and `Audit` through the library's roots. The script checks every dependency's actual Git revision before the build and after verification. It checks that source and configuration bytes stay unchanged and requires fifteen parsed axiom reports with only `propext`, `Classical.choice`, and `Quot.sound`.

The fresh replay includes the imported environment and the expanded statement bridge. This checker uses Lean's kernel. An independently implemented kernel checker and external human review require separate evidence.

Logs and a machine-readable result are written to `.audit/` by default and are excluded from version control. To select another new output directory, pass `--out PATH`. An existing result directory is rejected so earlier results cannot be overwritten. Each check records its actual exit code and duration. Failures return a nonzero process exit code and retain their logs.

For independent execution, use a restricted VM or container with only the source and output mounted, no credentials, and networking disabled after dependency preparation. A fresh source directory alone provides build separation. The environment used for each recorded audit is described in its report.
