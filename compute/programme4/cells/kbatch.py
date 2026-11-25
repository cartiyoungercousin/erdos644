r"""Batch for Kaggle (or local): run_cells.py for several (k, T, q, nmax) specs, then check_cert.py on each output.
usage: kbatch.py procs k:T:q:nmax [k:T:q:nmax ...]      outputs in certs/ ; summary on stdout"""
import subprocess, sys
procs = sys.argv[1]
for spec in sys.argv[2:]:
    k, T, q, nmax = spec.split(':')
    subprocess.run([sys.executable, '-u', 'run_cells.py', k, T, q, nmax, 'certs', procs, '3600'])
    subprocess.run([sys.executable, '-u', 'check_cert.py', f'certs/k{k}_T{T}_q{q}.jsonl'])
