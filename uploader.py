#!/usr/bin/env python3
"""
GitHub File Uploader  –  GUI edition  (v4)
==========================================
NEW IN v4:
  • 🗑️  Delete after upload  – successfully uploaded local files are moved to
        a Recycle folder (safe) or permanently deleted (with confirmation)
  • 📊  Stats dashboard  – live panel showing speed (files/min), bytes
        transferred, success rate, and a mini progress breakdown
  • 🌙  Dark / Light theme toggle
  • 🔔  Desktop notifications when upload finishes (cross-platform)
  • 💬  Discord webhook notifications  – sends a rich embed to any Discord
        channel when an upload session completes (or fails), with full stats,
        repo link, colour-coded by result, and optional @mention support
  • ⏸️  Pause / Resume  – freeze an in-progress upload and continue later
  • 🔍  Repo file browser  – list what's already in the target folder
  • 👁️  File preview  – click any queued file to see its content/metadata
  • 📁  Upload queue panel  – scrollable list of pending/done/failed files
        with per-file status icons updated in real time

CARRIED FROM v3:
  • ZERO git dependency  – GitHub REST API + token only
  • Per-file commits  (PUT /contents)  or  single commit  (Git Trees API)
  • Custom commit message with {filename} {filepath} {index} {total} vars
  • Dry-run mode
  • Token validation
  • fnmatch exclude patterns
  • Config save / load  (~/.github_uploader_config.json)
  • Live ETA
  • files.log committed to repo (created / appended each session)
  • Retry with exponential back-off on rate-limit / server errors

Requirements:
    pip install requests
    tkinter  (built into CPython on Windows/macOS;
              Linux: sudo apt install python3-tk)
"""

import base64
import fnmatch
import json
import os
import queue
import shutil
import sys
import threading
import time
import tkinter as tk
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from tkinter import filedialog, scrolledtext, ttk
from typing import Optional

try:
    import requests
except ImportError:
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "requests"])
    import requests

# ─────────────────────────────────────────────────────────────────────────────
# Constants
# ─────────────────────────────────────────────────────────────────────────────
API          = "https://api.github.com"
CONFIG_FILE  = Path.home() / ".github_uploader_config.json"
FILES_LOG    = "files.log"
RECYCLE_DIR  = Path.home() / ".github_uploader_recycle"

SKIP_NAMES: set      = {".DS_Store", "Thumbs.db", "desktop.ini", ".gitkeep"}
SKIP_EXTENSIONS: set = {".pyc", ".pyo", ".swp", ".swo", ".tmp"}

# Theme palettes
THEMES = {
    "dark": {
        "bg": "#1e1e2e", "fg": "#cdd6f4", "entry_bg": "#313244",
        "entry_fg": "#cdd6f4", "btn_bg": "#45475a", "btn_fg": "#cdd6f4",
        "accent": "#89b4fa", "ok": "#a6e3a1", "err": "#f38ba8",
        "warn": "#f9e2af", "log_bg": "#11111b", "log_fg": "#cdd6f4",
        "sep": "#45475a", "queue_bg": "#181825", "queue_sel": "#313244",
    },
    "light": {
        "bg": "#f5f5f5", "fg": "#1e1e2e", "entry_bg": "#ffffff",
        "entry_fg": "#1e1e2e", "btn_bg": "#e0e0e0", "btn_fg": "#1e1e2e",
        "accent": "#1a73e8", "ok": "#1e8a44", "err": "#c0392b",
        "warn": "#b7770d", "log_bg": "#ffffff", "log_fg": "#1e1e2e",
        "sep": "#cccccc", "queue_bg": "#f0f0f0", "queue_sel": "#dde8ff",
    },
}


# ─────────────────────────────────────────────────────────────────────────────
# Config
# ─────────────────────────────────────────────────────────────────────────────
def load_config() -> dict:
    try:
        if CONFIG_FILE.exists():
            return json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
    except Exception:
        pass
    return {}


def save_config(cfg: dict):
    try:
        safe = {k: v for k, v in cfg.items() if k != "token"}
        CONFIG_FILE.write_text(json.dumps(safe, indent=2), encoding="utf-8")
    except Exception:
        pass


# ─────────────────────────────────────────────────────────────────────────────
# Desktop notification (best-effort, never crashes the app)
# ─────────────────────────────────────────────────────────────────────────────
def _notify(title: str, message: str):
    try:
        if sys.platform == "win32":
            # Uses PowerShell toast on Windows 10+
            ps = (
                f'Add-Type -AssemblyName System.Windows.Forms;'
                f'$n=New-Object System.Windows.Forms.NotifyIcon;'
                f'$n.Icon=[System.Drawing.SystemIcons]::Information;'
                f'$n.Visible=$true;'
                f'$n.ShowBalloonTip(4000,"{title}","{message}",'
                f'[System.Windows.Forms.ToolTipIcon]::Info)'
            )
            import subprocess
            subprocess.Popen(
                ["powershell", "-WindowStyle", "Hidden", "-Command", ps],
                creationflags=0x08000000)
        elif sys.platform == "darwin":
            import subprocess
            subprocess.Popen(
                ["osascript", "-e",
                 f'display notification "{message}" with title "{title}"'])
        else:
            import subprocess
            subprocess.Popen(["notify-send", title, message],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:
        pass


# ─────────────────────────────────────────────────────────────────────────────
# Discord webhook notification
# ─────────────────────────────────────────────────────────────────────────────
def _discord_notify(webhook_url: str, owner: str, repo: str, branch: str,
                    done: int, failed: int, skipped: int, deleted: int,
                    elapsed_str: str, dry_run: bool, mention: str = ""):
    """
    POST a rich embed to a Discord webhook.
    Colour: green = all success, orange = partial failures, red = all failed.
    Never raises – silently logs failures.
    """
    if not webhook_url or not webhook_url.startswith("http"):
        return

    try:
        total   = done + failed + skipped
        success = failed == 0 and done > 0
        partial = failed > 0 and done > 0
        colour  = 0x57F287 if success else (0xFEE75C if partial else 0xED4245)

        repo_url = f"https://github.com/{owner}/{repo}/tree/{branch}"

        tag   = " *(dry run)*" if dry_run else ""
        title = f"{'🧪 Dry Run' if dry_run else ('✅ Upload Complete' if success else ('⚠️ Upload Finished with Errors' if partial else '❌ Upload Failed'))}{tag}"

        desc_lines = [
            f"**Repository:** [{owner}/{repo}]({repo_url}) `{branch}`",
            "",
            f"✅ **Committed:** {done}",
            f"❌ **Failed:** {failed}",
            f"⏭️ **Skipped:** {skipped}",
            f"🗑️ **Deleted locally:** {deleted}",
            f"⏱️ **Elapsed:** {elapsed_str}",
        ]
        if mention:
            desc_lines.insert(0, mention)
            desc_lines.insert(1, "")

        payload = {
            "embeds": [{
                "title":       title,
                "description": "\n".join(desc_lines),
                "color":       colour,
                "footer":      {"text": "GitHub File Uploader v4"},
                "timestamp":   datetime.now(timezone.utc).isoformat(),
            }]
        }

        resp = requests.post(webhook_url, json=payload, timeout=10)
        if resp.status_code not in (200, 204):
            print(f"[Discord] Webhook returned HTTP {resp.status_code}: {resp.text[:200]}")
    except Exception as e:
        print(f"[Discord] Notification error (non-fatal): {e}")


# ─────────────────────────────────────────────────────────────────────────────
# Delete / recycle helpers
# ─────────────────────────────────────────────────────────────────────────────
def _recycle_file(path: Path, log_fn) -> bool:
    """Move file to RECYCLE_DIR, preserving relative structure. Returns True on success."""
    try:
        RECYCLE_DIR.mkdir(parents=True, exist_ok=True)
        ts  = datetime.now().strftime("%Y%m%d_%H%M%S")
        dst = RECYCLE_DIR / f"{ts}_{path.name}"
        shutil.move(str(path), str(dst))
        log_fn(f"♻️  Recycled → {dst.name}")
        return True
    except Exception as e:
        log_fn(f"⚠️  Could not recycle {path.name}: {e}")
        return False


def _delete_file(path: Path, log_fn) -> bool:
    """Permanently delete a file. Returns True on success."""
    try:
        path.unlink()
        log_fn(f"🗑️  Deleted  → {path.name}")
        return True
    except Exception as e:
        log_fn(f"⚠️  Could not delete {path.name}: {e}")
        return False


# ─────────────────────────────────────────────────────────────────────────────
# GitHub API helpers
# ─────────────────────────────────────────────────────────────────────────────
def _headers(token: str) -> dict:
    return {
        "Authorization": f"token {token}",
        "Accept":        "application/vnd.github.v3+json",
        "User-Agent":    "GH-FileUploader-GUI/4.0",
    }


def validate_token(token: str) -> tuple:
    try:
        r = requests.get(f"{API}/user", headers=_headers(token), timeout=10)
        if r.status_code == 200:
            return True, r.json().get("login", "unknown")
        return False, f"HTTP {r.status_code}: {r.json().get('message', r.text[:100])}"
    except Exception as e:
        return False, str(e)


def list_repo_folder(token: str, owner: str, repo: str,
                     branch: str, path: str) -> tuple:
    """Returns (items_list, error_str). items are dicts with name/type/size."""
    try:
        url = f"{API}/repos/{owner}/{repo}/contents/{path}"
        r = requests.get(url, headers=_headers(token),
                         params={"ref": branch}, timeout=20)
        if r.status_code == 200:
            data = r.json()
            if isinstance(data, list):
                return sorted(data, key=lambda x: (x["type"] != "dir", x["name"])), ""
            return [], "Not a directory"
        return [], f"HTTP {r.status_code}: {r.json().get('message','')}"
    except Exception as e:
        return [], str(e)


def _get_file_sha(session, token, owner, repo, branch, path) -> Optional[str]:
    url = f"{API}/repos/{owner}/{repo}/contents/{path}"
    r = session.get(url, headers=_headers(token), params={"ref": branch}, timeout=30)
    if r.status_code == 200:
        return r.json().get("sha")
    return None


def _get_file_content_and_sha(session, token, owner, repo, branch, path):
    url = f"{API}/repos/{owner}/{repo}/contents/{path}"
    r = session.get(url, headers=_headers(token), params={"ref": branch}, timeout=30)
    if r.status_code == 200:
        d = r.json()
        return base64.b64decode(d.get("content", "")).decode("utf-8", errors="replace"), d.get("sha")
    return None, None


def _is_rate_limit(code, text, hdrs) -> bool:
    if code == 429:
        return True
    if code == 403:
        tl = text.lower()
        return ("rate limit" in tl or
                ("x-ratelimit-remaining" in {k.lower() for k in hdrs}
                 and hdrs.get("X-RateLimit-Remaining", "1") == "0"))
    return False


def _put_file(session, token, owner, repo, branch,
              path, b64, message, sha) -> tuple:
    url  = f"{API}/repos/{owner}/{repo}/contents/{path}"
    body = {"message": message, "content": b64, "branch": branch}
    if sha:
        body["sha"] = sha
    r = session.put(url, headers=_headers(token), json=body, timeout=60)
    if r.status_code in (200, 201):
        return True, False, ""
    rl = _is_rate_limit(r.status_code, r.text, dict(r.headers))
    return False, rl, f"HTTP {r.status_code}: {r.text[:300]}"


# ─────────────────────────────────────────────────────────────────────────────
# Git Trees API
# ─────────────────────────────────────────────────────────────────────────────
def _branch_sha(session, token, owner, repo, branch) -> Optional[str]:
    r = session.get(f"{API}/repos/{owner}/{repo}/git/ref/heads/{branch}",
                    headers=_headers(token), timeout=30)
    return r.json()["object"]["sha"] if r.status_code == 200 else None


def _tree_sha(session, token, owner, repo, commit_sha) -> Optional[str]:
    r = session.get(f"{API}/repos/{owner}/{repo}/git/commits/{commit_sha}",
                    headers=_headers(token), timeout=30)
    return r.json()["tree"]["sha"] if r.status_code == 200 else None


def _create_blob(session, token, owner, repo, b64) -> Optional[str]:
    r = session.post(f"{API}/repos/{owner}/{repo}/git/blobs",
                     headers=_headers(token),
                     json={"content": b64, "encoding": "base64"}, timeout=60)
    return r.json()["sha"] if r.status_code == 201 else None


def _create_tree(session, token, owner, repo, base_sha, items) -> Optional[str]:
    r = session.post(f"{API}/repos/{owner}/{repo}/git/trees",
                     headers=_headers(token),
                     json={"base_tree": base_sha, "tree": items}, timeout=120)
    return r.json()["sha"] if r.status_code == 201 else None


def _create_commit(session, token, owner, repo, msg, tree, parent) -> Optional[str]:
    r = session.post(f"{API}/repos/{owner}/{repo}/git/commits",
                     headers=_headers(token),
                     json={"message": msg, "tree": tree, "parents": [parent]}, timeout=60)
    return r.json()["sha"] if r.status_code == 201 else None


def _update_ref(session, token, owner, repo, branch, sha) -> bool:
    r = session.patch(f"{API}/repos/{owner}/{repo}/git/refs/heads/{branch}",
                      headers=_headers(token),
                      json={"sha": sha, "force": False}, timeout=30)
    return r.status_code == 200


# ─────────────────────────────────────────────────────────────────────────────
# File helpers
# ─────────────────────────────────────────────────────────────────────────────
def _build_patterns(raw: str) -> list:
    return [p.strip() for p in raw.replace(",", "\n").splitlines()
            if p.strip() and not p.strip().startswith("#")]


def _skip(p: Path, patterns: list) -> bool:
    if p.name in SKIP_NAMES or p.suffix.lower() in SKIP_EXTENSIONS:
        return True
    return any(fnmatch.fnmatch(p.name, pat) or fnmatch.fnmatch(str(p), pat)
               for pat in patterns)


def collect_files(root: Path, patterns: list) -> list:
    return sorted(p for p in root.rglob("*") if p.is_file() and not _skip(p, patterns))


def _human(n: int) -> str:
    for u in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n} {u}" if u == "B" else f"{n:.1f} {u}"
        n /= 1024
    return f"{n:.1f} TB"


def _elapsed(s: float) -> str:
    m, sc = divmod(int(s), 60)
    return f"{m}m {sc:02d}s" if m else f"{sc}s"


def _eta(done: int, total: int, elapsed: float) -> str:
    if done == 0 or elapsed < 0.1:
        return "ETA: —"
    rem = (total - done) / (done / elapsed)
    m, s = divmod(int(rem), 60)
    return f"ETA: {m}m {s:02d}s" if m else f"ETA: {s}s"


# ─────────────────────────────────────────────────────────────────────────────
# files.log helpers
# ─────────────────────────────────────────────────────────────────────────────
def _log_path(prefix: str) -> str:
    return f"{prefix}/{FILES_LOG}" if prefix else FILES_LOG


def _log_header(owner, repo, branch):
    return (f"# 📋 Upload Log — `{owner}/{repo}` (`{branch}`)\n\n"
            f"> Auto-generated by **GitHub File Uploader v4**. "
            f"Appended each session.\n\n")


def _session_block(entries, done, failed, skipped, elapsed_str, deleted, dry):
    ts  = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    tag = " *(dry run)*" if dry else ""
    lines = [
        f"---\n\n## 🚀 Session — {ts}{tag}\n\n",
        f"| Stat | Value |\n|------|-------|\n",
        f"| ✅ Committed | {done} |\n",
        f"| ❌ Failed | {failed} |\n",
        f"| ⏭️ Skipped | {skipped} |\n",
        f"| 🗑️ Deleted locally | {deleted} |\n",
        f"| ⏱️ Elapsed | {elapsed_str} |\n\n",
        f"### Files\n\n| Status | Path | Size |\n|--------|------|------|\n",
    ]
    for e in entries:
        lines.append(f"| {e['icon']} | `{e['path']}` | {e['size']} |\n")
    lines.append("\n")
    return "".join(lines)


def _push_log(session, token, owner, repo, branch,
              log_path, block, log_fn, delay):
    try:
        existing, sha = _get_file_content_and_sha(
            session, token, owner, repo, branch, log_path)
        full = (_log_header(owner, repo, branch) + block
                if existing is None else existing + block)
        encoded = base64.b64encode(full.encode()).decode()
        time.sleep(delay)
        ok, _, err = _put_file(session, token, owner, repo, branch,
                                log_path, encoded,
                                "chore: update files.log [skip ci]", sha)
        log_fn(f"📋 files.log updated → {log_path}" if ok
               else f"⚠️  files.log error: {err}")
    except Exception as e:
        log_fn(f"⚠️  files.log error (non-fatal): {e}")


# ─────────────────────────────────────────────────────────────────────────────
# Upload worker – per-file mode
# ─────────────────────────────────────────────────────────────────────────────
def worker_per_file(cfg: dict, log_q: queue.Queue,
                    cancel_ev: threading.Event, pause_ev: threading.Event):
    token      = cfg["token"]
    owner      = cfg["owner"]
    repo       = cfg["repo"]
    branch     = cfg["branch"]
    root       = Path(cfg["local_folder"])
    prefix     = cfg["repo_folder"].strip("/")
    delay      = float(cfg.get("delay", 1.0))
    tmpl       = cfg.get("commit_msg", "Upload {filename}") or "Upload {filename}"
    dry        = cfg.get("dry_run", False)
    patterns   = _build_patterns(cfg.get("exclude_patterns", ""))
    write_log  = cfg.get("write_files_log", True)
    del_mode   = cfg.get("delete_mode", "none")   # "none" | "recycle" | "permanent"
    discord_cfg = {
        "webhook_url": cfg.get("discord_webhook", ""),
        "mention":     cfg.get("discord_mention", ""),
        "on_success":  cfg.get("discord_on_success", True),
        "on_failure":  cfg.get("discord_on_failure", True),
        "owner": owner, "repo": repo, "branch": branch,
    }

    def log(m):     log_q.put(("log", m))
    def prog(d, t): log_q.put(("progress", d, t))
    def status(m):  log_q.put(("status", m))
    def qupdate(i, icon): log_q.put(("queue_update", i, icon))

    files = collect_files(root, patterns)
    total = len(files)
    if not total:
        log("⚠️  No files found."); log_q.put(("done", 0, 0, 0, 0)); return

    # Send full file list to queue panel
    log_q.put(("queue_init", [(str(f.relative_to(root)), _human(f.stat().st_size))
                               for f in files]))

    log(f"📂 {total} file(s) found")
    if dry: log("🧪 DRY-RUN – no API calls")
    log(f"📦 {owner}/{repo}  branch:{branch}  target:/{prefix or '(root)'}")
    log(f"📝 Commit: {tmpl}   delay:{delay}s   delete:{del_mode}")
    log("─" * 60)

    session  = requests.Session()
    done = failed = skipped = deleted = 0
    start    = time.monotonic()
    entries  = []
    bytes_up = 0

    for i, fpath in enumerate(files):
        # ── pause support ────────────────────────────────────────────────────
        while pause_ev.is_set() and not cancel_ev.is_set():
            status("⏸️  Paused — click Resume to continue")
            time.sleep(0.5)

        if cancel_ev.is_set():
            log("⏹️  Cancelled."); break

        rel       = PurePosixPath(fpath.relative_to(root))
        repo_path = f"{prefix}/{rel}" if prefix else str(rel)
        elapsed   = max(time.monotonic() - start, 0.01)

        status(f"[{i+1}/{total}] {fpath.name}  •  {_eta(i, total, elapsed)}  •  "
               f"{_human(bytes_up)} sent")
        qupdate(i, "⏳")

        try:
            size = fpath.stat().st_size
        except OSError:
            log(f"⚠️  Unreadable: {fpath.name}")
            entries.append({"icon":"⏭️","path":repo_path,"size":"?"})
            skipped += 1; qupdate(i,"⏭️"); prog(i+1,total); continue

        sstr = _human(size)

        if size > 99 * 1024 * 1024:
            log(f"⏭️  >99 MB skipped: {fpath.name}")
            entries.append({"icon":"⏭️","path":repo_path,"size":sstr})
            skipped += 1; qupdate(i,"⏭️"); prog(i+1,total); continue

        if dry:
            log(f"🧪 [{i+1}/{total}] Would upload → {repo_path}  ({sstr})")
            entries.append({"icon":"🧪","path":repo_path,"size":sstr})
            done += 1; qupdate(i,"🧪"); prog(i+1,total); continue

        try:
            raw = fpath.read_bytes()
        except OSError as e:
            log(f"❌ Read error: {fpath.name}: {e}")
            entries.append({"icon":"❌","path":repo_path,"size":sstr})
            failed += 1; qupdate(i,"❌"); prog(i+1,total); continue

        b64     = base64.b64encode(raw).decode()
        cmsg    = tmpl.format(filename=fpath.name, filepath=repo_path,
                              index=i+1, total=total)
        backoff = delay
        outcome = None

        for attempt in range(1, 8):
            if cancel_ev.is_set(): break
            while pause_ev.is_set() and not cancel_ev.is_set():
                time.sleep(0.3)

            time.sleep(delay)
            try:
                sha = _get_file_sha(session, token, owner, repo, branch, repo_path)
            except requests.exceptions.RequestException as e:
                log(f"⚠️  SHA fetch error (att {attempt}): {e}")
                time.sleep(backoff); backoff = min(backoff*2, 120); continue

            time.sleep(delay)
            try:
                ok, rl, err = _put_file(session, token, owner, repo, branch,
                                         repo_path, b64, cmsg, sha)
            except requests.exceptions.RequestException as e:
                log(f"⚠️  Upload error (att {attempt}): {e}")
                time.sleep(backoff); backoff = min(backoff*2, 120); continue

            if ok:
                now = time.monotonic() - start
                bytes_up += size
                speed = done / max(now, 0.01)
                log(f"✅ [{i+1}/{total}] {repo_path}  ({sstr})  •  "
                    f"{_eta(i+1,total,now)}  •  {speed*60:.1f} f/min")
                entries.append({"icon":"✅","path":repo_path,"size":sstr})
                done += 1; outcome = "ok"; qupdate(i,"✅")

                # ── delete / recycle ─────────────────────────────────────────
                if del_mode == "recycle":
                    if _recycle_file(fpath, log): deleted += 1
                elif del_mode == "permanent":
                    if _delete_file(fpath, log): deleted += 1
                break

            if rl:
                wait = backoff * 2
                log(f"⏳ Rate limited (att {attempt}) – wait {wait:.0f}s")
                time.sleep(wait); backoff = min(wait*2, 300); continue

            if "422" in err:
                log(f"⚠️  SHA conflict – retry (att {attempt})")
                time.sleep(delay); continue

            if any(c in err for c in ("500","502","503","504")):
                log(f"⚠️  Server error (att {attempt}) – retry")
                time.sleep(backoff); backoff = min(backoff*2, 120); continue

            log(f"❌ [{i+1}/{total}] {repo_path} → {err}")
            entries.append({"icon":"❌","path":repo_path,"size":sstr})
            failed += 1; outcome = "failed"; qupdate(i,"❌"); break

        if outcome is None and not cancel_ev.is_set():
            log(f"❌ Gave up: {repo_path}")
            entries.append({"icon":"❌","path":repo_path,"size":sstr})
            failed += 1; qupdate(i,"❌")

        prog(i+1, total)
        log_q.put(("stats", done, failed, skipped, bytes_up,
                   time.monotonic()-start))

    elapsed_str = _elapsed(time.monotonic() - start)

    if write_log and not dry and entries:
        log("─" * 60); log("📋 Updating files.log…")
        block = _session_block(entries, done, failed, skipped,
                                elapsed_str, deleted, dry)
        _push_log(session, token, owner, repo, branch,
                  _log_path(prefix), block, log, delay)

    _done(log_q, log, status, done, failed, skipped, deleted, elapsed_str, dry,
          discord_cfg)


# ─────────────────────────────────────────────────────────────────────────────
# Upload worker – single-commit mode
# ─────────────────────────────────────────────────────────────────────────────
def worker_single(cfg: dict, log_q: queue.Queue,
                  cancel_ev: threading.Event, pause_ev: threading.Event):
    token     = cfg["token"]
    owner     = cfg["owner"]
    repo      = cfg["repo"]
    branch    = cfg["branch"]
    root      = Path(cfg["local_folder"])
    prefix    = cfg["repo_folder"].strip("/")
    cmsg      = cfg.get("commit_msg","") or "Bulk upload via GitHub File Uploader"
    dry       = cfg.get("dry_run", False)
    patterns  = _build_patterns(cfg.get("exclude_patterns",""))
    write_log = cfg.get("write_files_log", True)
    del_mode  = cfg.get("delete_mode", "none")
    discord_cfg = {
        "webhook_url": cfg.get("discord_webhook", ""),
        "mention":     cfg.get("discord_mention", ""),
        "owner": owner, "repo": repo, "branch": branch,
    }

    def log(m):     log_q.put(("log", m))
    def prog(d, t): log_q.put(("progress", d, t))
    def status(m):  log_q.put(("status", m))
    def qupdate(i, icon): log_q.put(("queue_update", i, icon))

    files = collect_files(root, patterns)
    total = len(files)
    if not total:
        log("⚠️  No files found."); log_q.put(("done",0,0,0,0)); return

    log_q.put(("queue_init", [(str(f.relative_to(root)), _human(f.stat().st_size))
                               for f in files]))

    log(f"📂 {total} file(s) → single commit")
    if dry: log("🧪 DRY-RUN – no API calls")
    log(f"📦 {owner}/{repo}  branch:{branch}  target:/{prefix or '(root)'}")
    log(f"📝 \"{cmsg}\"   delete:{del_mode}")
    log("─" * 60)

    start     = time.monotonic()
    session   = requests.Session()
    done = failed = skipped = deleted = 0
    entries   = []
    file_data = []
    bytes_up  = 0

    for i, fpath in enumerate(files):
        while pause_ev.is_set() and not cancel_ev.is_set():
            status("⏸️  Paused"); time.sleep(0.5)
        if cancel_ev.is_set():
            log("⏹️  Cancelled."); log_q.put(("done",0,0,0,0)); return

        rel       = PurePosixPath(fpath.relative_to(root))
        repo_path = f"{prefix}/{rel}" if prefix else str(rel)
        qupdate(i, "⏳")
        try:
            size = fpath.stat().st_size
        except OSError:
            log(f"⚠️  Unreadable: {fpath.name}")
            entries.append({"icon":"⏭️","path":repo_path,"size":"?"})
            skipped += 1; qupdate(i,"⏭️"); continue
        sstr = _human(size)
        if size > 99*1024*1024:
            log(f"⏭️  >99 MB: {fpath.name}")
            entries.append({"icon":"⏭️","path":repo_path,"size":sstr})
            skipped += 1; qupdate(i,"⏭️"); continue
        try:
            raw = fpath.read_bytes()
        except OSError as e:
            log(f"❌ {fpath.name}: {e}")
            entries.append({"icon":"❌","path":repo_path,"size":sstr})
            failed += 1; qupdate(i,"❌"); continue

        file_data.append((repo_path, base64.b64encode(raw).decode(),
                          fpath.name, sstr, size, fpath))
        status(f"Reading {i+1}/{total}: {fpath.name}")
        prog(i+1, total)

    if dry:
        for rp,_,nm,ss,_,_ in file_data:
            log(f"🧪 Would include → {rp}  ({ss})")
            entries.append({"icon":"🧪","path":rp,"size":ss})
        _done(log_q, log, status, len(file_data), failed, skipped, 0,
              _elapsed(time.monotonic()-start), dry)
        return

    if not file_data:
        log("⚠️  Nothing to commit."); log_q.put(("done",0,0,0,0)); return

    # Branch / tree SHA
    status("Fetching branch…")
    c_sha = _branch_sha(session, token, owner, repo, branch)
    if not c_sha:
        log(f"❌ Branch '{branch}' not found."); log_q.put(("done",0,0,0,0)); return
    t_sha = _tree_sha(session, token, owner, repo, c_sha)
    if not t_sha:
        log("❌ Tree SHA failed."); log_q.put(("done",0,0,0,0)); return
    log(f"✅ Base commit:{c_sha[:12]}  tree:{t_sha[:12]}")
    log("─" * 60)

    tree_items = []
    up = len(file_data)
    for i, (rp, b64, nm, ss, sz, fpath) in enumerate(file_data):
        while pause_ev.is_set() and not cancel_ev.is_set():
            time.sleep(0.3)
        if cancel_ev.is_set():
            log("⏹️  Cancelled."); log_q.put(("done",0,0,0,0)); return

        el = max(time.monotonic()-start, 0.01)
        status(f"Blob {i+1}/{up}: {nm}  •  {_eta(i,up,el)}")
        blob = None
        for att in range(1,5):
            try:
                blob = _create_blob(session, token, owner, repo, b64)
                if blob: break
            except Exception as e:
                log(f"⚠️  Blob error att {att}: {e}"); time.sleep(2**att)

        if not blob:
            log(f"❌ Blob failed: {nm}")
            entries.append({"icon":"❌","path":rp,"size":ss})
            failed += 1; qupdate(i,"❌"); continue

        tree_items.append({"path":rp,"mode":"100644","type":"blob","sha":blob})
        bytes_up += sz; done += 1
        now = time.monotonic()-start
        log(f"  📎 [{i+1}/{up}] {rp}  •  {_eta(i+1,up,now)}")
        entries.append({"icon":"✅","path":rp,"size":ss})
        qupdate(i,"✅"); prog(i+1, up)
        log_q.put(("stats",done,failed,skipped,bytes_up,now))

    elapsed_str = _elapsed(time.monotonic()-start)

    # Append files.log blob
    lp = _log_path(prefix)
    if write_log:
        log("─"*60); log("📋 Building files.log blob…")
        existing, _ = _get_file_content_and_sha(session, token, owner, repo, branch, lp)
        block = _session_block(entries, done, failed, skipped, elapsed_str, 0, False)
        new_log = (_log_header(owner,repo,branch)+block
                   if existing is None else existing+block)
        lb64 = base64.b64encode(new_log.encode()).decode()
        lb = _create_blob(session, token, owner, repo, lb64)
        if lb:
            tree_items = [t for t in tree_items if t["path"] != lp]
            tree_items.append({"path":lp,"mode":"100644","type":"blob","sha":lb})
            log(f"✅ files.log blob → {lp}")

    if not tree_items:
        log("❌ No tree items."); log_q.put(("done",0,0,0,0)); return

    status("Creating tree…")
    nt = _create_tree(session, token, owner, repo, t_sha, tree_items)
    if not nt:
        log("❌ Tree creation failed."); log_q.put(("done",0,0,0,0)); return
    log(f"✅ Tree:{nt[:12]}")

    status("Creating commit…")
    log(f"💾 \"{cmsg}\"")
    nc = _create_commit(session, token, owner, repo, cmsg, nt, c_sha)
    if not nc:
        log("❌ Commit failed."); log_q.put(("done",0,0,0,0)); return
    log(f"✅ Commit:{nc[:12]}")

    status("Updating branch…")
    if not _update_ref(session, token, owner, repo, branch, nc):
        log("❌ Branch update failed."); log_q.put(("done",0,0,0,0)); return
    log(f"✅ Branch '{branch}' updated!")

    # Delete successfully uploaded files
    if del_mode != "none":
        log("─"*60)
        log(f"🗑️  {'Recycling' if del_mode=='recycle' else 'Deleting'} uploaded files…")
        for rp, _, nm, ss, sz, fpath in file_data:
            if any(e["path"]==rp and e["icon"]=="✅" for e in entries):
                if del_mode == "recycle":
                    if _recycle_file(fpath, log): deleted += 1
                else:
                    if _delete_file(fpath, log): deleted += 1

    _done(log_q, log, status, done, failed, skipped, deleted, elapsed_str, False,
          discord_cfg)


def _done(log_q, log, status, done, failed, skipped, deleted, elapsed_str, dry,
          discord_cfg: dict = None):
    pre = "🧪 DRY-RUN  " if dry else ""
    log("─"*60)
    log(f"{'🧪 ' if dry else ''}✅ Committed : {done}")
    log(f"❌ Failed    : {failed}")
    log(f"⏭️  Skipped   : {skipped}")
    log(f"🗑️  Deleted   : {deleted}")
    log(f"⏱️  Elapsed   : {elapsed_str}")
    status(f"{pre}Done — ✅{done} ❌{failed} ⏭️{skipped} 🗑️{deleted} ({elapsed_str})")

    # ── Discord notification ──────────────────────────────────────────────────
    if discord_cfg and discord_cfg.get("webhook_url"):
        is_success   = failed == 0 and done > 0
        is_failure   = failed > 0 or (done == 0 and not dry)
        want_success = discord_cfg.get("on_success", True)
        want_failure = discord_cfg.get("on_failure", True)
        should_send  = (is_success and want_success) or (is_failure and want_failure)
        if should_send:
            try:
                log("💬 Sending Discord notification…")
                _discord_notify(
                    webhook_url = discord_cfg["webhook_url"],
                    owner       = discord_cfg.get("owner", ""),
                    repo        = discord_cfg.get("repo", ""),
                    branch      = discord_cfg.get("branch", ""),
                    done        = done,
                    failed      = failed,
                    skipped     = skipped,
                    deleted     = deleted,
                    elapsed_str = elapsed_str,
                    dry_run     = dry,
                    mention     = discord_cfg.get("mention", ""),
                )
                log("✅ Discord notification sent!")
            except Exception as e:
                log(f"⚠️  Discord notification failed (non-fatal): {e}")
        else:
            log("💬 Discord notification skipped (filter settings)")

    log_q.put(("done", done, failed, skipped, deleted))


# ─────────────────────────────────────────────────────────────────────────────
# Custom dialogs
# ─────────────────────────────────────────────────────────────────────────────
class MsgDialog(tk.Toplevel):
    def __init__(self, parent, title, message, kind="error"):
        super().__init__(parent)
        self.title(title); self.resizable(False,False); self.grab_set()
        self.protocol("WM_DELETE_WINDOW", lambda: None)
        icons = {"error":("❌","#c0392b"),"warning":("⚠️","#e67e22"),
                 "info":("ℹ️","#2980b9"),"success":("✅","#27ae60")}
        ic, col = icons.get(kind, icons["error"])
        outer = tk.Frame(self,padx=20,pady=16); outer.pack(fill="both",expand=True)
        tk.Label(outer,text=ic,font=("Segoe UI",28)).grid(row=0,column=0,padx=(0,14),sticky="n")
        mf = tk.Frame(outer); mf.grid(row=0,column=1,sticky="nsew")
        tk.Label(mf,text=title,font=("Segoe UI",11,"bold"),fg=col,anchor="w").pack(fill="x")
        tk.Label(mf,text=message,font=("Segoe UI",10),justify="left",
                 anchor="w",wraplength=360).pack(fill="x",pady=(4,0))
        tk.Label(self,text="Press Enter to close",font=("Segoe UI",8),fg="gray").pack(pady=(0,4))
        btn = tk.Button(self,text="OK",font=("Segoe UI",10,"bold"),
                        width=10,default="active",command=self._close)
        btn.pack(pady=(0,14))
        self.bind("<Return>", lambda _:self._close())
        self.bind("<KP_Enter>", lambda _:self._close())
        self._center(parent); btn.focus_set(); self.wait_window()

    def _center(self,p):
        self.update_idletasks()
        pw=p.winfo_rootx()+p.winfo_width()//2
        ph=p.winfo_rooty()+p.winfo_height()//2
        w,h=self.winfo_width(),self.winfo_height()
        self.geometry(f"+{pw-w//2}+{ph-h//2}")

    def _close(self): self.grab_release(); self.destroy()


class ConfirmDialog(tk.Toplevel):
    def __init__(self, parent, title, message):
        super().__init__(parent)
        self.title(title); self.resizable(False,False); self.grab_set()
        self.result = False
        self.protocol("WM_DELETE_WINDOW", self._no)
        outer=tk.Frame(self,padx=20,pady=16); outer.pack(fill="both",expand=True)
        tk.Label(outer,text="⚠️",font=("Segoe UI",28)).grid(row=0,column=0,padx=(0,14),sticky="n")
        mf=tk.Frame(outer); mf.grid(row=0,column=1,sticky="nsew")
        tk.Label(mf,text=title,font=("Segoe UI",11,"bold"),fg="#e67e22",anchor="w").pack(fill="x")
        tk.Label(mf,text=message,font=("Segoe UI",10),justify="left",
                 anchor="w",wraplength=320).pack(fill="x",pady=(4,0))
        tk.Label(self,text="Enter = Yes    Escape = No",font=("Segoe UI",8),fg="gray").pack(pady=(0,4))
        br=tk.Frame(self); br.pack(pady=(0,14))
        by=tk.Button(br,text="Yes",font=("Segoe UI",10,"bold"),
                     bg="#c0392b",fg="white",padx=14,command=self._yes)
        by.pack(side="left",padx=6)
        tk.Button(br,text="No",font=("Segoe UI",10),padx=14,
                  command=self._no).pack(side="left",padx=6)
        self.bind("<Return>",lambda _:self._yes())
        self.bind("<KP_Enter>",lambda _:self._yes())
        self.bind("<Escape>",lambda _:self._no())
        self.update_idletasks()
        pw=parent.winfo_rootx()+parent.winfo_width()//2
        ph=parent.winfo_rooty()+parent.winfo_height()//2
        w,h=self.winfo_width(),self.winfo_height()
        self.geometry(f"+{pw-w//2}+{ph-h//2}")
        by.focus_set(); self.wait_window()

    def _yes(self): self.result=True;  self.grab_release(); self.destroy()
    def _no(self):  self.result=False; self.grab_release(); self.destroy()


# ─────────────────────────────────────────────────────────────────────────────
# Repo Browser window
# ─────────────────────────────────────────────────────────────────────────────
class RepoBrowser(tk.Toplevel):
    def __init__(self, parent, token, owner, repo, branch, start_path=""):
        super().__init__(parent)
        self.title(f"Repo Browser – {owner}/{repo}")
        self.geometry("600x480")
        self.resizable(True,True)
        self._token=token; self._owner=owner
        self._repo=repo; self._branch=branch
        self._path=start_path

        top=tk.Frame(self); top.pack(fill="x",padx=8,pady=4)
        self._path_var=tk.StringVar(value=f"/{start_path}")
        tk.Label(top,text="Path:",font=("Segoe UI",9)).pack(side="left")
        self._path_entry=tk.Entry(top,textvariable=self._path_var,
                                   font=("Segoe UI",9),width=40)
        self._path_entry.pack(side="left",padx=4,fill="x",expand=True)
        tk.Button(top,text="Go",command=self._go,
                  font=("Segoe UI",9)).pack(side="left",padx=2)
        tk.Button(top,text="⬆ Up",command=self._up,
                  font=("Segoe UI",9)).pack(side="left",padx=2)
        tk.Button(top,text="🔄 Refresh",command=self._refresh,
                  font=("Segoe UI",9)).pack(side="left",padx=2)

        cols=("Name","Type","Size")
        self._tree=ttk.Treeview(self,columns=cols,show="headings",
                                 selectmode="browse")
        for c,w in zip(cols,(340,60,100)):
            self._tree.heading(c,text=c)
            self._tree.column(c,width=w)
        sb=ttk.Scrollbar(self,orient="vertical",command=self._tree.yview)
        self._tree.configure(yscrollcommand=sb.set)
        self._tree.pack(side="left",fill="both",expand=True,padx=(8,0),pady=4)
        sb.pack(side="left",fill="y",pady=4,padx=(0,8))
        self._tree.bind("<Double-1>",self._on_double)

        self._status=tk.StringVar(value="")
        tk.Label(self,textvariable=self._status,font=("Segoe UI",8),
                 fg="gray",anchor="w").pack(fill="x",padx=8,pady=(0,4))

        self._refresh()

    def _refresh(self):
        p=self._path_var.get().strip("/")
        self._path=p
        self._status.set("Loading…"); self.update()
        items,err=list_repo_folder(self._token,self._owner,
                                    self._repo,self._branch,p)
        for row in self._tree.get_children():
            self._tree.delete(row)
        if err:
            self._status.set(f"Error: {err}"); return
        for it in items:
            sz = _human(it.get("size",0)) if it["type"]=="file" else "—"
            icon = "📁" if it["type"]=="dir" else "📄"
            self._tree.insert("","end",
                               values=(f"{icon} {it['name']}",it["type"],sz))
        self._status.set(f"/{p or '(root)'}  –  {len(items)} item(s)")

    def _go(self):
        self._refresh()

    def _up(self):
        cur=self._path_var.get().strip("/")
        parent="/".join(cur.split("/")[:-1])
        self._path_var.set(f"/{parent}")
        self._refresh()

    def _on_double(self, _):
        sel=self._tree.focus()
        if not sel: return
        vals=self._tree.item(sel,"values")
        name=vals[0].split(" ",1)[1]
        typ=vals[1]
        if typ=="dir":
            cur=self._path_var.get().strip("/")
            self._path_var.set(f"/{cur}/{name}" if cur else f"/{name}")
            self._refresh()


# ─────────────────────────────────────────────────────────────────────────────
# File Preview window
# ─────────────────────────────────────────────────────────────────────────────
class FilePreview(tk.Toplevel):
    def __init__(self, parent, fpath: Path):
        super().__init__(parent)
        self.title(f"Preview – {fpath.name}")
        self.geometry("640x480"); self.resizable(True,True)

        info_frame=tk.Frame(self); info_frame.pack(fill="x",padx=8,pady=4)
        try:
            stat=fpath.stat()
            mtime=datetime.fromtimestamp(stat.st_mtime).strftime("%Y-%m-%d %H:%M:%S")
            info=f"Path: {fpath}   |   Size: {_human(stat.st_size)}   |   Modified: {mtime}"
        except Exception:
            info=str(fpath)
        tk.Label(info_frame,text=info,font=("Segoe UI",8),fg="gray",
                 anchor="w",wraplength=620).pack(fill="x")

        txt=scrolledtext.ScrolledText(self,font=("Consolas",9),
                                       bg="#1e1e2e",fg="#cdd6f4",
                                       state="normal")
        txt.pack(fill="both",expand=True,padx=8,pady=(0,8))

        TEXT_EXTS={".txt",".md",".py",".js",".ts",".json",".yaml",".yml",
                   ".xml",".html",".css",".sh",".bat",".ini",".cfg",
                   ".toml",".rst",".log",".csv",".env"}
        try:
            if fpath.suffix.lower() in TEXT_EXTS:
                content=fpath.read_text(encoding="utf-8",errors="replace")
                lines=content.split("\n")
                preview="\n".join(lines[:500])
                if len(lines)>500:
                    preview+=f"\n\n… ({len(lines)-500} more lines)"
            else:
                raw=fpath.read_bytes()[:2048]
                preview=f"[Binary file – first 2048 bytes as hex]\n\n"
                preview+="\n".join(raw[i:i+16].hex(" ") for i in range(0,len(raw),16))
        except Exception as e:
            preview=f"Could not read file: {e}"

        txt.insert("1.0", preview)
        txt.config(state="disabled")


# ─────────────────────────────────────────────────────────────────────────────
# Main Application
# ─────────────────────────────────────────────────────────────────────────────
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("GitHub File Uploader  v4")
        self.resizable(True,True)
        self.minsize(820,700)

        self._cancel  = threading.Event()
        self._pause   = threading.Event()
        self._log_q   = queue.Queue()
        self._running = False
        self._theme   = "dark"

        # queue panel data
        self._queue_files: list = []   # (rel_path, size_str)

        self._build_ui()
        self._apply_theme()
        self._load_cfg()
        self.after(80, self._poll)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ─────────────────────────────────────────────────────────────────────────
    # UI BUILD
    # ─────────────────────────────────────────────────────────────────────────
    def _build_ui(self):
        # ── menu bar ──────────────────────────────────────────────────────────
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="💾 Save Config",  command=self._save_config)
        file_menu.add_command(label="📂 Load Config",  command=self._load_config_dialog)
        file_menu.add_separator()
        file_menu.add_command(label="🗑️  Open Recycle Folder", command=self._open_recycle)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_close)
        menubar.add_cascade(label="File", menu=file_menu)

        tools_menu = tk.Menu(menubar, tearoff=0)
        tools_menu.add_command(label="🔍 Browse Repo",   command=self._open_browser)
        tools_menu.add_command(label="🌙 Toggle Theme",  command=self._toggle_theme)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        self.config(menu=menubar)

        # ── header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(self); hdr.pack(fill="x",padx=12,pady=(10,2))
        tk.Label(hdr, text="GitHub File Uploader  v4",
                 font=("Segoe UI",15,"bold")).pack(side="left")
        self._theme_btn = tk.Button(hdr, text="🌙", font=("Segoe UI",12),
                                     relief="flat", command=self._toggle_theme)
        self._theme_btn.pack(side="right")
        tk.Label(self,
                 text="No git  •  token API  •  per-file / single commit  •  ETA  •  delete after upload  •  files.log",
                 font=("Segoe UI",9), fg="gray").pack()
        ttk.Separator(self, orient="horizontal").pack(fill="x", padx=10, pady=6)

        # ── main paned layout: left=form, right=queue panel ───────────────────
        paned = tk.PanedWindow(self, orient="horizontal", sashwidth=6,
                                sashrelief="flat")
        paned.pack(fill="both", expand=True, padx=8, pady=0)

        # ── LEFT: scrollable form ─────────────────────────────────────────────
        left_outer = tk.Frame(paned)
        paned.add(left_outer, minsize=460)
        canvas = tk.Canvas(left_outer, highlightthickness=0)
        vsb    = ttk.Scrollbar(left_outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        self._form = tk.Frame(canvas)
        self._fwin = canvas.create_window((0,0), window=self._form, anchor="nw")
        self._form.bind("<Configure>", lambda e: canvas.configure(
            scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(
            self._fwin, width=e.width))
        canvas.bind_all("<MouseWheel>",
            lambda e: canvas.yview_scroll(int(-1*(e.delta/120)), "units"))
        self._form.columnconfigure(1, weight=1)
        self._canvas_ref = canvas

        self._build_form()

        # ── RIGHT: queue panel ────────────────────────────────────────────────
        right = tk.Frame(paned)
        paned.add(right, minsize=220)
        q_hdr = tk.Frame(right); q_hdr.pack(fill="x", padx=4, pady=(4,0))
        tk.Label(q_hdr, text="Upload Queue", font=("Segoe UI",10,"bold")).pack(side="left")
        tk.Button(q_hdr, text="👁 Preview", font=("Segoe UI",8),
                  command=self._preview_selected).pack(side="right")
        self._queue_lb = tk.Listbox(right, font=("Consolas",8),
                                     selectmode="single", activestyle="none")
        qsb = ttk.Scrollbar(right, orient="vertical",
                             command=self._queue_lb.yview)
        self._queue_lb.configure(yscrollcommand=qsb.set)
        qsb.pack(side="right", fill="y")
        self._queue_lb.pack(side="left", fill="both", expand=True,
                             padx=(4,0), pady=4)

        # ── BOTTOM: stats + controls ──────────────────────────────────────────
        bottom = tk.Frame(self)
        bottom.pack(fill="x", padx=8, pady=(0,4))

        # stats row
        self._stats_frame = tk.Frame(bottom)
        self._stats_frame.pack(fill="x", pady=(0,4))
        self._stat_vars = {}
        for key, label in [("speed","⚡ Speed"),("bytes","📦 Sent"),
                             ("rate","✅ Rate"),("done","✅"),
                             ("failed","❌"),("skipped","⏭️")]:
            f = tk.Frame(self._stats_frame)
            f.pack(side="left", padx=8)
            tk.Label(f, text=label, font=("Segoe UI",8), fg="gray").pack()
            v = tk.StringVar(value="—")
            tk.Label(f, textvariable=v, font=("Segoe UI",10,"bold")).pack()
            self._stat_vars[key] = v

        # button row
        btn_row = tk.Frame(bottom); btn_row.pack(pady=2)
        self.btn_start = tk.Button(btn_row, text="🚀 Start Upload",
                                    font=("Segoe UI",11,"bold"),
                                    bg="#2ea043",fg="white",
                                    padx=14,pady=5,command=self._start)
        self.btn_start.pack(side="left",padx=4)

        self.btn_pause = tk.Button(btn_row, text="⏸ Pause",
                                    font=("Segoe UI",10),
                                    padx=10,pady=5,state="disabled",
                                    command=self._toggle_pause)
        self.btn_pause.pack(side="left",padx=4)

        self.btn_cancel = tk.Button(btn_row, text="⏹ Cancel",
                                     font=("Segoe UI",10),
                                     padx=10,pady=5,state="disabled",
                                     command=self._cancel_upload)
        self.btn_cancel.pack(side="left",padx=4)

        self.btn_browser = tk.Button(btn_row, text="🔍 Browse Repo",
                                      font=("Segoe UI",10),
                                      padx=10,pady=5,
                                      command=self._open_browser)
        self.btn_browser.pack(side="left",padx=4)

        self.btn_copy = tk.Button(btn_row, text="📋 Copy Log",
                                   font=("Segoe UI",10),
                                   padx=10,pady=5,command=self._copy_log)
        self.btn_copy.pack(side="left",padx=4)

        # status + progress
        self._status_var = tk.StringVar(value="Ready")
        tk.Label(self, textvariable=self._status_var,
                 font=("Segoe UI",9),fg="gray").pack()
        self._progress = ttk.Progressbar(self,length=600,mode="determinate")
        self._progress.pack(fill="x",padx=14,pady=(2,4))

        # log
        lh = tk.Frame(self); lh.pack(fill="x",padx=14,anchor="w")
        tk.Label(lh,text="Log:",font=("Segoe UI",9)).pack(side="left")
        self._log_box = scrolledtext.ScrolledText(
            self, height=9, font=("Consolas",9),
            state="disabled", bg="#11111b", fg="#cdd6f4",
            insertbackground="white")
        self._log_box.pack(fill="x",padx=14,pady=(2,8))
        self._log_box.tag_config("ok",   foreground="#a6e3a1")
        self._log_box.tag_config("err",  foreground="#f38ba8")
        self._log_box.tag_config("warn", foreground="#f9e2af")
        self._log_box.tag_config("info", foreground="#89b4fa")

    def _build_form(self):
        frm = self._form
        r   = [0]
        P   = {"padx":(10,8), "pady":3}

        def lbl(text, col=0, cs=1, bold=False, fg=None):
            f = ("Segoe UI",10,"bold") if bold else ("Segoe UI",10)
            kw = dict(text=text, anchor="w", font=f)
            if fg: kw["fg"] = fg
            tk.Label(frm,**kw).grid(row=r[0],column=col,columnspan=cs,
                                     sticky="w",padx=(10,8),pady=3)

        def erow(label, var):
            lbl(label)
            e=tk.Entry(frm,textvariable=var,font=("Segoe UI",10))
            e.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
            r[0]+=1; return e

        def sep():
            ttk.Separator(frm,orient="horizontal").grid(
                row=r[0],column=0,columnspan=2,sticky="ew",pady=6,padx=10)
            r[0]+=1

        # ── Token ─────────────────────────────────────────────────────────────
        self.v_token = tk.StringVar()
        lbl("GitHub Token:")
        tf = tk.Frame(frm); tf.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        tf.columnconfigure(0,weight=1)
        self.token_entry=tk.Entry(tf,textvariable=self.v_token,
                                   show="*",font=("Segoe UI",10))
        self.token_entry.grid(row=0,column=0,sticky="ew")
        self._tok_vis=False
        tk.Button(tf,text="👁",font=("Segoe UI",9),width=3,
                  command=self._toggle_tok).grid(row=0,column=1,padx=(4,0))
        tk.Button(tf,text="Validate",font=("Segoe UI",9),
                  command=self._validate_token).grid(row=0,column=2,padx=(4,0))
        r[0]+=1

        # ── Repo details ──────────────────────────────────────────────────────
        self.v_owner  = tk.StringVar()
        self.v_repo   = tk.StringVar()
        self.v_branch = tk.StringVar(value="main")
        erow("Owner / Org:", self.v_owner)
        erow("Repository:",  self.v_repo)
        erow("Branch:",      self.v_branch)

        # ── Local folder ──────────────────────────────────────────────────────
        lbl("Local Folder:")
        lf=tk.Frame(frm); lf.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        lf.columnconfigure(0,weight=1)
        self.v_local=tk.StringVar()
        tk.Entry(lf,textvariable=self.v_local,font=("Segoe UI",10)).grid(
            row=0,column=0,sticky="ew")
        tk.Button(lf,text="Browse…",command=self._browse_local).grid(
            row=0,column=1,padx=(6,0))
        r[0]+=1
        sep()

        # ── Target folder ─────────────────────────────────────────────────────
        lbl("Target folder in repo:", cs=2, bold=True)
        r[0]+=1
        self.v_repo_folder=tk.StringVar()
        rff=tk.Frame(frm); rff.grid(row=r[0],column=0,columnspan=2,
                                     sticky="ew",padx=10,pady=2)
        rff.columnconfigure(0,weight=1)
        tk.Entry(rff,textvariable=self.v_repo_folder,font=("Segoe UI",10)).grid(
            row=0,column=0,sticky="ew")
        tk.Label(rff,text="  (blank = root)",fg="gray",
                 font=("Segoe UI",9)).grid(row=0,column=1)
        r[0]+=1

        lbl("Build path:", cs=2, fg="gray"); r[0]+=1
        pf=tk.Frame(frm,bd=1,relief="sunken",bg="white")
        pf.grid(row=r[0],column=0,columnspan=2,sticky="ew",pady=2,padx=10)
        pf.columnconfigure(1,weight=1)
        tk.Label(pf,text="Folder:",bg="white",font=("Segoe UI",9)).grid(
            row=0,column=0,padx=6,pady=4)
        self.v_new_seg=tk.StringVar()
        se=tk.Entry(pf,textvariable=self.v_new_seg,font=("Segoe UI",9),width=18)
        se.grid(row=0,column=1,sticky="ew",padx=4,pady=4)
        se.bind("<Return>", lambda _:self._seg_add())
        tk.Button(pf,text="Add ▶",command=self._seg_add,font=("Segoe UI",9)).grid(row=0,column=2,padx=4,pady=4)
        tk.Button(pf,text="⬅ Back",command=self._seg_back,font=("Segoe UI",9)).grid(row=0,column=3,padx=4,pady=4)
        tk.Button(pf,text="Clear",command=self._seg_clear,font=("Segoe UI",9)).grid(row=0,column=4,padx=4,pady=4)
        self._path_lbl=tk.StringVar(value="📁  /  (root)")
        tk.Label(pf,textvariable=self._path_lbl,bg="white",fg="#0055aa",
                 font=("Segoe UI",9,"bold"),anchor="w").grid(
            row=1,column=0,columnspan=5,sticky="ew",padx=6,pady=(0,4))
        r[0]+=1
        sep()

        # ── Commit message ────────────────────────────────────────────────────
        lbl("Commit message:")
        cmf=tk.Frame(frm); cmf.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        cmf.columnconfigure(0,weight=1)
        self.v_commit=tk.StringVar(value="Upload {filename}")
        tk.Entry(cmf,textvariable=self.v_commit,font=("Segoe UI",10)).grid(
            row=0,column=0,sticky="ew")
        tk.Label(cmf,text=" {filename} {filepath} {index} {total}",
                 fg="gray",font=("Segoe UI",8)).grid(row=1,column=0,sticky="w")
        r[0]+=1

        # ── Commit mode ───────────────────────────────────────────────────────
        lbl("Commit mode:")
        mf=tk.Frame(frm); mf.grid(row=r[0],column=1,sticky="w",padx=(0,10),pady=3)
        self.v_mode=tk.StringVar(value="per_file")
        tk.Radiobutton(mf,text="Per file",variable=self.v_mode,
                       value="per_file",font=("Segoe UI",10),
                       command=self._mode_change).pack(side="left")
        tk.Radiobutton(mf,text="Single commit (Git Trees)",variable=self.v_mode,
                       value="single",font=("Segoe UI",10),
                       command=self._mode_change).pack(side="left",padx=(14,0))
        r[0]+=1

        # ── Exclude patterns ──────────────────────────────────────────────────
        lbl("Exclude patterns:")
        ef=tk.Frame(frm); ef.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        ef.columnconfigure(0,weight=1)
        self.v_exclude=tk.StringVar(value="*.tmp, __pycache__")
        tk.Entry(ef,textvariable=self.v_exclude,font=("Segoe UI",9)).grid(
            row=0,column=0,sticky="ew")
        tk.Label(ef,text=" fnmatch patterns, comma-separated",
                 fg="gray",font=("Segoe UI",8)).grid(row=1,column=0,sticky="w")
        r[0]+=1
        sep()

        # ── Delete after upload ───────────────────────────────────────────────
        lbl("After upload:", bold=True, cs=2); r[0]+=1
        del_f=tk.Frame(frm)
        del_f.grid(row=r[0],column=0,columnspan=2,sticky="w",padx=10,pady=3)
        self.v_delete=tk.StringVar(value="none")
        tk.Radiobutton(del_f,text="Keep files (no deletion)",
                       variable=self.v_delete,value="none",
                       font=("Segoe UI",10)).pack(side="left")
        tk.Radiobutton(del_f,text="♻️ Move to Recycle folder",
                       variable=self.v_delete,value="recycle",
                       font=("Segoe UI",10)).pack(side="left",padx=(14,0))
        tk.Radiobutton(del_f,text="🗑️ Permanently delete",
                       variable=self.v_delete,value="permanent",
                       font=("Segoe UI",10),fg="#c0392b").pack(side="left",padx=(14,0))
        r[0]+=1

        recycle_info=tk.Frame(frm)
        recycle_info.grid(row=r[0],column=0,columnspan=2,sticky="w",padx=10,pady=(0,4))
        tk.Label(recycle_info,
                 text=f"♻️ Recycle folder: {RECYCLE_DIR}",
                 fg="gray",font=("Segoe UI",8)).pack(side="left")
        r[0]+=1
        sep()

        # ── Options ───────────────────────────────────────────────────────────
        of=tk.Frame(frm)
        of.grid(row=r[0],column=0,columnspan=2,sticky="w",padx=10,pady=3)
        tk.Label(of,text="Delay (s/call):",font=("Segoe UI",10)).pack(side="left")
        self.v_delay=tk.DoubleVar(value=1.0)
        self._delay_spin=tk.Spinbox(of,from_=0.1,to=10.0,increment=0.5,
                                     textvariable=self.v_delay,width=5,
                                     font=("Segoe UI",10))
        self._delay_spin.pack(side="left",padx=(4,16))
        self.v_dry=tk.BooleanVar(value=False)
        tk.Checkbutton(of,text="🧪 Dry Run",variable=self.v_dry,
                       font=("Segoe UI",10)).pack(side="left",padx=(0,16))
        self.v_write_log=tk.BooleanVar(value=True)
        tk.Checkbutton(of,text="📋 Write files.log",variable=self.v_write_log,
                       font=("Segoe UI",10)).pack(side="left")
        r[0]+=1

        # ── Discord notifications ──────────────────────────────────────────────
        sep()
        lbl("💬 Discord Notifications", bold=True, cs=2); r[0]+=1

        lbl("Webhook URL:")
        dwf=tk.Frame(frm); dwf.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        dwf.columnconfigure(0,weight=1)
        self.v_discord_webhook=tk.StringVar()
        self._discord_entry=tk.Entry(dwf,textvariable=self.v_discord_webhook,
                                      show="*",font=("Segoe UI",10))
        self._discord_entry.grid(row=0,column=0,sticky="ew")
        self._disc_vis=False
        tk.Button(dwf,text="👁",font=("Segoe UI",9),width=3,
                  command=self._toggle_discord_vis).grid(row=0,column=1,padx=(4,0))
        tk.Button(dwf,text="Test",font=("Segoe UI",9),
                  command=self._test_discord).grid(row=0,column=2,padx=(4,0))
        tk.Label(dwf,
                 text="  Paste your Discord channel webhook URL",
                 fg="gray",font=("Segoe UI",8)).grid(row=1,column=0,columnspan=3,sticky="w")
        r[0]+=1

        lbl("Mention (optional):")
        mef=tk.Frame(frm); mef.grid(row=r[0],column=1,sticky="ew",padx=(0,10),pady=3)
        mef.columnconfigure(0,weight=1)
        self.v_discord_mention=tk.StringVar()
        tk.Entry(mef,textvariable=self.v_discord_mention,font=("Segoe UI",10)).grid(
            row=0,column=0,sticky="ew")
        tk.Label(mef,text="  e.g. @here  or  <@USER_ID>  or  <@&ROLE_ID>",
                 fg="gray",font=("Segoe UI",8)).grid(row=1,column=0,sticky="w")
        r[0]+=1

        # Notify-on options
        notify_f=tk.Frame(frm)
        notify_f.grid(row=r[0],column=0,columnspan=2,sticky="w",padx=10,pady=(0,4))
        self.v_discord_on_success=tk.BooleanVar(value=True)
        self.v_discord_on_failure=tk.BooleanVar(value=True)
        tk.Checkbutton(notify_f,text="Notify on success",
                       variable=self.v_discord_on_success,
                       font=("Segoe UI",10)).pack(side="left")
        tk.Checkbutton(notify_f,text="Notify on failure / partial",
                       variable=self.v_discord_on_failure,
                       font=("Segoe UI",10)).pack(side="left",padx=(14,0))
        r[0]+=1

        # ── Config buttons ────────────────────────────────────────────────────
        cf=tk.Frame(frm)
        cf.grid(row=r[0],column=0,columnspan=2,sticky="w",padx=10,pady=(2,10))
        tk.Button(cf,text="💾 Save Config",font=("Segoe UI",9),
                  command=self._save_config).pack(side="left",padx=(0,6))
        tk.Button(cf,text="📂 Load Config",font=("Segoe UI",9),
                  command=self._load_config_dialog).pack(side="left",padx=(0,6))
        self._cfg_lbl=tk.Label(cf,text="",fg="gray",font=("Segoe UI",8))
        self._cfg_lbl.pack(side="left")

    # ─────────────────────────────────────────────────────────────────────────
    # Theme
    # ─────────────────────────────────────────────────────────────────────────
    def _toggle_theme(self):
        self._theme = "light" if self._theme == "dark" else "dark"
        self._apply_theme()

    def _apply_theme(self):
        t = THEMES[self._theme]
        self.configure(bg=t["bg"])
        self._log_box.configure(bg=t["log_bg"], fg=t["log_fg"])
        self._log_box.tag_config("ok",   foreground=t["ok"])
        self._log_box.tag_config("err",  foreground=t["err"])
        self._log_box.tag_config("warn", foreground=t["warn"])
        self._log_box.tag_config("info", foreground=t["accent"])
        self._queue_lb.configure(bg=t["queue_bg"], fg=t["fg"],
                                  selectbackground=t["queue_sel"])
        icon = "☀️" if self._theme == "dark" else "🌙"
        self._theme_btn.configure(text=icon, bg=t["bg"], fg=t["fg"])

    # ─────────────────────────────────────────────────────────────────────────
    # Queue panel helpers
    # ─────────────────────────────────────────────────────────────────────────
    def _queue_init(self, files):
        self._queue_files = files
        self._queue_lb.delete(0, "end")
        for rel, sz in files:
            self._queue_lb.insert("end", f"⬜ {rel}  ({sz})")

    def _queue_update(self, idx, icon):
        if idx >= self._queue_lb.size():
            return
        rel, sz = self._queue_files[idx]
        self._queue_lb.delete(idx)
        self._queue_lb.insert(idx, f"{icon} {rel}  ({sz})")
        self._queue_lb.see(idx)

    def _preview_selected(self):
        sel = self._queue_lb.curselection()
        if not sel:
            return
        idx  = sel[0]
        if idx >= len(self._queue_files):
            return
        rel  = self._queue_files[idx][0]
        root = Path(self.v_local.get().strip())
        full = root / rel
        if full.exists():
            FilePreview(self, full)
        else:
            MsgDialog(self, "Not found", f"File not found:\n{full}", kind="warning")

    # ─────────────────────────────────────────────────────────────────────────
    # Stats update
    # ─────────────────────────────────────────────────────────────────────────
    def _update_stats(self, done, failed, skipped, bytes_up, elapsed):
        total = done + failed + skipped
        speed = (done / elapsed * 60) if elapsed > 0 else 0
        rate  = f"{done/(done+failed)*100:.0f}%" if (done+failed) > 0 else "—"
        self._stat_vars["speed"].set(f"{speed:.1f} f/min")
        self._stat_vars["bytes"].set(_human(int(bytes_up)))
        self._stat_vars["rate"].set(rate)
        self._stat_vars["done"].set(str(done))
        self._stat_vars["failed"].set(str(failed))
        self._stat_vars["skipped"].set(str(skipped))

    # ─────────────────────────────────────────────────────────────────────────
    # Config
    # ─────────────────────────────────────────────────────────────────────────
    def _collect_cfg(self) -> dict:
        return {
            "owner":                self.v_owner.get().strip(),
            "repo":                 self.v_repo.get().strip(),
            "branch":               self.v_branch.get().strip(),
            "local_folder":         self.v_local.get().strip(),
            "repo_folder":          self.v_repo_folder.get().strip("/"),
            "commit_msg":           self.v_commit.get().strip(),
            "mode":                 self.v_mode.get(),
            "exclude_patterns":     self.v_exclude.get().strip(),
            "delay":                self.v_delay.get(),
            "dry_run":              self.v_dry.get(),
            "write_files_log":      self.v_write_log.get(),
            "delete_mode":          self.v_delete.get(),
            "discord_webhook":      self.v_discord_webhook.get().strip(),
            "discord_mention":      self.v_discord_mention.get().strip(),
            "discord_on_success":   self.v_discord_on_success.get(),
            "discord_on_failure":   self.v_discord_on_failure.get(),
        }

    def _save_config(self):
        save_config(self._collect_cfg())
        self._cfg_lbl.config(text=f"✅ Saved")
        self.after(3000, lambda: self._cfg_lbl.config(text=""))

    def _load_cfg(self):
        cfg = load_config()
        if not cfg: return
        self.v_owner.set(cfg.get("owner",""))
        self.v_repo.set(cfg.get("repo",""))
        self.v_branch.set(cfg.get("branch","main"))
        self.v_local.set(cfg.get("local_folder",""))
        self.v_repo_folder.set(cfg.get("repo_folder",""))
        self.v_commit.set(cfg.get("commit_msg","Upload {filename}"))
        self.v_mode.set(cfg.get("mode","per_file"))
        self.v_exclude.set(cfg.get("exclude_patterns","*.tmp, __pycache__"))
        self.v_delay.set(cfg.get("delay",1.0))
        self.v_dry.set(cfg.get("dry_run",False))
        self.v_write_log.set(cfg.get("write_files_log",True))
        self.v_delete.set(cfg.get("delete_mode","none"))
        self.v_discord_webhook.set(cfg.get("discord_webhook",""))
        self.v_discord_mention.set(cfg.get("discord_mention",""))
        self.v_discord_on_success.set(cfg.get("discord_on_success",True))
        self.v_discord_on_failure.set(cfg.get("discord_on_failure",True))
        self._update_path_lbl()
        self._mode_change()

    def _load_config_dialog(self):
        p = filedialog.askopenfilename(
            title="Load config",
            filetypes=[("JSON","*.json"),("All","*.*")],
            initialdir=str(Path.home()))
        if not p: return
        try:
            cfg = json.loads(Path(p).read_text(encoding="utf-8"))
            CONFIG_FILE.write_text(json.dumps(cfg,indent=2),encoding="utf-8")
            self._load_cfg()
            self._cfg_lbl.config(text=f"✅ Loaded")
            self.after(3000, lambda: self._cfg_lbl.config(text=""))
        except Exception as e:
            MsgDialog(self,"Load error",str(e),kind="error")

    # ─────────────────────────────────────────────────────────────────────────
    # Misc UI helpers
    # ─────────────────────────────────────────────────────────────────────────
    def _mode_change(self):
        m = self.v_mode.get()
        self._delay_spin.config(state="normal" if m=="per_file" else "disabled")
        if m=="single" and ("{filename}" in self.v_commit.get()
                            or "{index}" in self.v_commit.get()):
            self.v_commit.set("Bulk upload via GitHub File Uploader")
        elif m=="per_file" and self.v_commit.get()=="Bulk upload via GitHub File Uploader":
            self.v_commit.set("Upload {filename}")

    def _toggle_tok(self):
        self._tok_vis = not self._tok_vis
        self.token_entry.config(show="" if self._tok_vis else "*")

    def _toggle_discord_vis(self):
        self._disc_vis = not self._disc_vis
        self._discord_entry.config(show="" if self._disc_vis else "*")

    def _test_discord(self):
        url = self.v_discord_webhook.get().strip()
        if not url:
            MsgDialog(self, "No Webhook", "Please enter a Discord webhook URL first.",
                      kind="warning")
            return
        owner  = self.v_owner.get().strip() or "owner"
        repo   = self.v_repo.get().strip()  or "repo"
        branch = self.v_branch.get().strip() or "main"

        def _do():
            try:
                _discord_notify(
                    webhook_url = url,
                    owner       = owner,
                    repo        = repo,
                    branch      = branch,
                    done        = 42,
                    failed      = 0,
                    skipped     = 1,
                    deleted     = 3,
                    elapsed_str = "1m 23s",
                    dry_run     = True,
                    mention     = self.v_discord_mention.get().strip(),
                )
                self._log_q.put(("discord_test_ok",))
            except Exception as e:
                self._log_q.put(("discord_test_fail", str(e)))

        self._status_var.set("Testing Discord webhook…")
        threading.Thread(target=_do, daemon=True).start()

    def _validate_token(self):
        tok = self.v_token.get().strip()
        if not tok:
            MsgDialog(self,"No Token","Please enter a GitHub token.",kind="warning"); return
        self._status_var.set("Validating…"); self.update()
        def _do():
            ok,r = validate_token(tok)
            self._log_q.put(("validate_ok",r) if ok else ("validate_fail",r))
        threading.Thread(target=_do,daemon=True).start()

    def _seg_add(self):
        s=self.v_new_seg.get().strip().strip("/")
        if not s: return
        c=self.v_repo_folder.get().strip("/")
        self.v_repo_folder.set(f"{c}/{s}" if c else s)
        self.v_new_seg.set(""); self._update_path_lbl()

    def _seg_back(self):
        c=self.v_repo_folder.get().strip("/")
        parts=c.rsplit("/",1)
        self.v_repo_folder.set(parts[0] if len(parts)>1 else "")
        self._update_path_lbl()

    def _seg_clear(self):
        self.v_repo_folder.set(""); self._update_path_lbl()

    def _update_path_lbl(self):
        p=self.v_repo_folder.get().strip("/")
        self._path_lbl.set(f"📁  /  {p}  /" if p else "📁  /  (root)")

    def _browse_local(self):
        d=filedialog.askdirectory(title="Select folder to upload")
        if d: self.v_local.set(d)

    def _open_browser(self):
        tok=self.v_token.get().strip()
        own=self.v_owner.get().strip()
        rep=self.v_repo.get().strip()
        br=self.v_branch.get().strip() or "main"
        if not tok or not own or not rep:
            MsgDialog(self,"Missing info","Please fill in token, owner, and repo first.",
                      kind="warning"); return
        RepoBrowser(self, tok, own, rep, br,
                    self.v_repo_folder.get().strip("/"))

    def _open_recycle(self):
        RECYCLE_DIR.mkdir(parents=True,exist_ok=True)
        try:
            if sys.platform=="win32":
                os.startfile(str(RECYCLE_DIR))
            elif sys.platform=="darwin":
                import subprocess; subprocess.Popen(["open",str(RECYCLE_DIR)])
            else:
                import subprocess; subprocess.Popen(["xdg-open",str(RECYCLE_DIR)])
        except Exception as e:
            MsgDialog(self,"Error",str(e),kind="error")

    # ─────────────────────────────────────────────────────────────────────────
    # Log
    # ─────────────────────────────────────────────────────────────────────────
    def _append_log(self, msg):
        self._log_box.config(state="normal")
        tag="info"
        if   msg.startswith("✅"): tag="ok"
        elif msg.startswith("❌"): tag="err"
        elif any(msg.startswith(p) for p in ("⚠️","⏳","⏭️","⏹️","🧪","♻️","🗑️")): tag="warn"
        self._log_box.insert("end", msg+"\n", tag)
        self._log_box.see("end")
        self._log_box.config(state="disabled")

    def _copy_log(self):
        self._log_box.config(state="normal")
        t=self._log_box.get("1.0","end")
        self._log_box.config(state="disabled")
        self.clipboard_clear(); self.clipboard_append(t)
        orig=self.btn_copy.cget("text")
        self.btn_copy.config(text="✅ Copied!")
        self.after(1500,lambda:self.btn_copy.config(text=orig))

    # ─────────────────────────────────────────────────────────────────────────
    # Queue poll
    # ─────────────────────────────────────────────────────────────────────────
    def _poll(self):
        try:
            while True:
                item = self._log_q.get_nowait()
                t = item[0]
                if   t=="log":          self._append_log(item[1])
                elif t=="status":       self._status_var.set(item[1])
                elif t=="progress":
                    self._progress["maximum"]=item[2]
                    self._progress["value"]=item[1]
                elif t=="queue_init":   self._queue_init(item[1])
                elif t=="queue_update": self._queue_update(item[1],item[2])
                elif t=="stats":
                    self._update_stats(item[1],item[2],item[3],item[4],item[5])
                elif t=="done":
                    done,failed,skipped,deleted = item[1],item[2],item[3],item[4]
                    self._running=False
                    self.btn_start.config(state="normal")
                    self.btn_pause.config(state="disabled",text="⏸ Pause")
                    self.btn_cancel.config(state="disabled")
                    self._pause.clear()
                    # desktop notification
                    _notify("Upload Complete",
                            f"✅{done} uploaded  ❌{failed} failed  🗑️{deleted} deleted")
                elif t=="validate_ok":
                    self._status_var.set(f"✅ Authenticated as: {item[1]}")
                    MsgDialog(self,"Token Valid",
                              f"Authenticated as: {item[1]}",kind="success")
                elif t=="validate_fail":
                    self._status_var.set("❌ Token invalid")
                    MsgDialog(self,"Token Invalid",
                              f"Could not authenticate:\n{item[1]}",kind="error")
                elif t=="discord_test_ok":
                    self._status_var.set("✅ Discord test message sent!")
                    MsgDialog(self,"Discord Test OK",
                              "Test embed sent successfully!\nCheck your Discord channel.",
                              kind="success")
                elif t=="discord_test_fail":
                    self._status_var.set("❌ Discord test failed")
                    MsgDialog(self,"Discord Test Failed",
                              f"Could not send test message:\n{item[1]}",kind="error")
        except queue.Empty:
            pass
        self.after(80, self._poll)

    # ─────────────────────────────────────────────────────────────────────────
    # Start / Pause / Cancel
    # ─────────────────────────────────────────────────────────────────────────
    def _start(self):
        tok   = self.v_token.get().strip()
        owner = self.v_owner.get().strip()
        repo  = self.v_repo.get().strip()
        branch= self.v_branch.get().strip() or "main"
        local = self.v_local.get().strip()
        rdir  = self.v_repo_folder.get().strip("/")
        dmode = self.v_delete.get()

        errors=[]
        if not tok:   errors.append("GitHub Token is required.")
        if not owner: errors.append("Owner / Org is required.")
        if not repo:  errors.append("Repository name is required.")
        if not local: errors.append("Local folder is required.")
        elif not Path(local).is_dir(): errors.append(f"Folder not found:\n{local}")
        if errors:
            MsgDialog(self,"Missing fields","\n".join(errors),kind="error"); return

        # Extra confirmation for permanent delete
        if dmode == "permanent" and not self.v_dry.get():
            msg = ("⚠️  PERMANENT DELETE is enabled.\n\n"
                   "Successfully uploaded files will be PERMANENTLY deleted "
                   "from your local disk with no recovery possible.\n\n"
                   "Are you absolutely sure?")
            if not ConfirmDialog(self, "Confirm Permanent Delete", msg).result:
                return

        save_config(self._collect_cfg())

        self._log_box.config(state="normal"); self._log_box.delete("1.0","end")
        self._log_box.config(state="disabled"); self._progress["value"]=0
        for v in self._stat_vars.values(): v.set("—")

        self._cancel.clear(); self._pause.clear()
        self._running=True
        self.btn_start.config(state="disabled")
        self.btn_pause.config(state="normal")
        self.btn_cancel.config(state="normal")
        self._status_var.set("Starting…")

        cfg = dict(
            token=tok, owner=owner, repo=repo, branch=branch,
            local_folder=local, repo_folder=rdir,
            delay=self.v_delay.get(),
            commit_msg=self.v_commit.get().strip(),
            dry_run=self.v_dry.get(),
            exclude_patterns=self.v_exclude.get().strip(),
            write_files_log=self.v_write_log.get(),
            delete_mode=dmode,
            discord_webhook=self.v_discord_webhook.get().strip(),
            discord_mention=self.v_discord_mention.get().strip(),
            discord_on_success=self.v_discord_on_success.get(),
            discord_on_failure=self.v_discord_on_failure.get(),
        )
        worker = (worker_single if self.v_mode.get()=="single"
                  else worker_per_file)
        threading.Thread(target=worker,
                          args=(cfg, self._log_q, self._cancel, self._pause),
                          daemon=True).start()

    def _toggle_pause(self):
        if self._pause.is_set():
            self._pause.clear()
            self.btn_pause.config(text="⏸ Pause")
            self._status_var.set("Resumed…")
        else:
            self._pause.set()
            self.btn_pause.config(text="▶ Resume")

    def _cancel_upload(self):
        self._cancel.set(); self._pause.clear()
        self._status_var.set("Cancelling…")
        self.btn_cancel.config(state="disabled")

    def _on_close(self):
        if self._running:
            if ConfirmDialog(self,"Upload running",
                             "An upload is running.\nCancel it and quit?").result:
                self._cancel.set(); self.destroy()
        else:
            self.destroy()


# ─────────────────────────────────────────────────────────────────────────────
def main():
    app = App()
    app.update_idletasks()
    w,h   = app.winfo_width(), app.winfo_height()
    sw,sh = app.winfo_screenwidth(), app.winfo_screenheight()
    app.geometry(f"+{(sw-w)//2}+{(sh-h)//2}")
    app.mainloop()


if __name__ == "__main__":
    main()
