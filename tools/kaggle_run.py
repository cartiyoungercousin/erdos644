"""Run a compute job on Kaggle (free CPU), as a PRIVATE script kernel.

usage:
  py -3.14 tools/kaggle_run.py push NAME SRC_DIR [--pip pkg1,pkg2] -- CMD ARGS...
  py -3.14 tools/kaggle_run.py status NAME
  py -3.14 tools/kaggle_run.py fetch NAME DEST_DIR

push:  zips SRC_DIR (skipping caches, logs, certificate dirs and files > 5 MB), embeds it in a
       script that unpacks it on Kaggle, runs CMD inside it, and leaves everything the command
       writes under /kaggle/working/job/ (plus run.log) as kernel output.
status / fetch: wrap `kaggle kernels status` / `kaggle kernels output`.
The Kaggle username is read from the local Kaggle config; nothing identifying is written here.
"""
import base64, io, json, os, subprocess, sys, tempfile, zipfile

SKIP_DIRS = {"__pycache__", ".git", "logs", ".lake"}
MAX_FILE = 5 * 1024 * 1024


def user():
    out = subprocess.run(["kaggle", "config", "view"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        if line.strip().startswith("- username:"):
            return line.split(":", 1)[1].strip()
    raise SystemExit("could not read the Kaggle username from `kaggle config view`")


def slug(name):
    return "erdos644-" + "".join(c if c.isalnum() else "-" for c in name.lower())


def pack(src):
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for root, dirs, files in os.walk(src):
            dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith("certs")]
            for f in files:
                p = os.path.join(root, f)
                if os.path.getsize(p) <= MAX_FILE and not f.endswith((".pyc", ".log")):
                    z.write(p, os.path.relpath(p, src))
    return base64.b64encode(buf.getvalue()).decode()


SCRIPT = r'''
import base64, io, os, subprocess, sys, zipfile
PIP = %(pip)r
CMD = %(cmd)r
if PIP:
    subprocess.run([sys.executable, "-m", "pip", "install", "-q"] + PIP)
os.makedirs("/kaggle/working/job", exist_ok=True)
zipfile.ZipFile(io.BytesIO(base64.b64decode(BLOB))).extractall("/kaggle/working/job")
os.chdir("/kaggle/working/job")
cmd = [sys.executable if c == "python" else c for c in CMD]
with open("/kaggle/working/run.log", "w") as log:
    print("nproc:", os.cpu_count(), file=log, flush=True)
    r = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
    print("exit:", r.returncode, file=log)
'''


def push(name, src, cmd, pip):
    d = tempfile.mkdtemp()
    code = "BLOB = %r\n" % pack(src) + SCRIPT % {"pip": pip, "cmd": cmd}
    open(os.path.join(d, "job.py"), "w").write(code)
    meta = {"id": f"{user()}/{slug(name)}", "title": slug(name), "code_file": "job.py",
            "language": "python", "kernel_type": "script", "is_private": True,
            "enable_gpu": False, "enable_tpu": False, "enable_internet": bool(pip),
            "dataset_sources": [], "competition_sources": [], "kernel_sources": []}
    json.dump(meta, open(os.path.join(d, "kernel-metadata.json"), "w"))
    subprocess.run(["kaggle", "kernels", "push", "-p", d], check=True)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == "push":
        cut = a.index("--")
        opts, cmd = a[1:cut], a[cut + 1:]
        pip = []
        if "--pip" in opts:
            i = opts.index("--pip"); pip = opts[i + 1].split(","); del opts[i:i + 2]
        push(opts[0], opts[1], cmd, pip)
    elif a[0] == "status":
        subprocess.run(["kaggle", "kernels", "status", f"{user()}/{slug(a[1])}"])
    elif a[0] == "fetch":
        os.makedirs(a[2], exist_ok=True)
        subprocess.run(["kaggle", "kernels", "output", f"{user()}/{slug(a[1])}", "-p", a[2]])
