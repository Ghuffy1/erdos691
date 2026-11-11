"""Reproduce the pinned proof and record actual verification results."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SOURCE_FILES = [
    "Erdos691.lean", "Challenge.lean", "Audit.lean",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_output(*args, cwd=ROOT):
    return subprocess.check_output(
        ["git", "--no-optional-locks", *args], cwd=cwd,
        text=True, encoding="utf-8", timeout=60,
    ).strip()


def dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    result = []
    for package in manifest["packages"]:
        location = ROOT / ".lake/packages" / package["name"]
        actual = git_output("rev-parse", "HEAD", cwd=location)
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch for {package['name']}")
        changes = git_output("status", "--porcelain", "--untracked-files=no", cwd=location)
        if changes:
            raise RuntimeError(f"Tracked dependency changes in {package['name']}")
        result.append({"name": package["name"], "commit": actual})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--fresh", action="store_true", help="Replay the imported environment too")
    parser.add_argument("--expect-commit", help="Require this exact repository commit")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = args.out or ROOT / ".audit" / stamp
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Install official Elan and prepare the pinned toolchain")
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    before = {name: digest(ROOT / name) for name in SOURCE_FILES}
    records = []
    result = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "commands": records,
        "source_before": before,
        "exit_code": 1,
    }

    def execute(label, command, timeout=2400):
        log = output / f"{label}.log"
        start = time.monotonic()
        with log.open("w", encoding="utf-8") as stream:
            try:
                code = subprocess.run(
                    command, cwd=ROOT, env=env, stdout=stream,
                    stderr=subprocess.STDOUT, timeout=timeout,
                ).returncode
            except subprocess.TimeoutExpired:
                code = 124
        records.append({
            "label": label, "command": command, "exit_code": code,
            "seconds": round(time.monotonic() - start, 3),
            "log": log.name, "log_sha256": digest(log),
        })
        print(f"{label}: exit {code}", flush=True)
        if code:
            raise RuntimeError(f"{label} failed with exit {code}; see {log.name}")
        return log.read_text(encoding="utf-8", errors="replace")

    try:
        result["repository_commit"] = git_output("rev-parse", "HEAD")
        if args.expect_commit and result["repository_commit"] != args.expect_commit:
            raise RuntimeError("The checkout does not match --expect-commit")
        result["dependencies_before"] = dependencies()
        version = execute("lean-version", [lake, "env", "lean", "--version"], 120)
        if not re.search(r"Lean \(version 4\.34\.0,", version):
            raise RuntimeError("The active Lean version does not match lean-toolchain")
        execute("lake-version", [lake, "--version"], 120)
        execute("default-build", [lake, "build"])
        for module in ["Erdos691", "Challenge", "Audit"]:
            execute(f"build-{module}", [lake, "build", f"+{module}"])
            execute(f"check-{module}", [lake, "env", "lean", f"{module}.lean"])
        audit = (output / "check-Audit.log").read_text(encoding="utf-8")
        expected = re.findall(r"^#print axioms ([\w.]+)$", (ROOT / "Audit.lean").read_text(encoding="utf-8"), re.M)
        observed = dict(re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", audit))
        if len(expected) != 15 or set(observed) != set(expected):
            raise RuntimeError("Missing or unexpected axiom audit declarations")
        axioms = {}
        for name in expected:
            names = set(filter(None, re.split(r"[,\s]+", observed[name])))
            if not names <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected axioms for {name}: {sorted(names)}")
            axioms[name] = sorted(names)
        result["axioms"] = axioms
        for module in ["Erdos691", "Challenge"]:
            execute(f"kernel-{module}", [lake, "env", "leanchecker", "-v", module])
        if args.fresh:
            execute("kernel-fresh-Challenge", [lake, "env", "leanchecker", "--fresh", "-v", "Challenge"])
        result["dependencies_after"] = dependencies()
        if result["dependencies_after"] != result["dependencies_before"]:
            raise RuntimeError("Dependency revisions changed during verification")
        result["exit_code"] = 0
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        result["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        result["source_after"] = {name: digest(ROOT / name) for name in SOURCE_FILES}
        result["sources_unchanged"] = result["source_after"] == before
        if not result["sources_unchanged"]:
            result["exit_code"] = 1
            result["error"] = "Source or configuration changed during verification"
        result["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (output / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
