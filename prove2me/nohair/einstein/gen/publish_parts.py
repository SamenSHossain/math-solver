"""Publish the Kerr–Newman Einstein definition parts in dependency order (resumable)."""
import json, subprocess, sys, time, os
REPO = '/home/user/math-solver'
W = '/root/prove2me_workspace/Definitions'
N = '/tmp/claude-0/-home-user-math-solver/ee9f98fb-9768-5748-b1b3-ebbf1e9b4bc0/scratchpad/nh_ein'
STATE = f'{N}/publish_state.json'
state = json.load(open(STATE)) if os.path.exists(STATE) else {}
meta = json.load(open(f'{N}/parts_meta.json'))
NP = len(meta)

def p2m(*args):
    for i in range(6):
        r = subprocess.run(['./scripts/p2m.py', *args], cwd=REPO, capture_output=True, text=True)
        try:
            return json.loads(r.stdout)
        except Exception:
            time.sleep(2 ** i)
    raise RuntimeError(r.stdout + r.stderr)

COMMON = ("This block belongs to a machine-checked proof that the Kerr–Newman metric $g=\\eta+f\\,k\\otimes k$ "
          "(Kerr–Schild form, $f=r^2(2mr-e^2)/(r^4+a^2z^2)$) and field $F=dA$, $A=\\frac{e r^3}{r^4+a^2z^2}k$, satisfy the "
          "Einstein equation $G_{\\mu\\nu}=2(F_{\\mu\\alpha}F_\\nu{}^\\alpha-\\tfrac14 g_{\\mu\\nu}F_{\\alpha\\beta}F^{\\alpha\\beta})$ at every "
          "point with $r>0$, using the definitions `NoHair_coordinates` and `NoHair_kerrNewman` "
          "(statement `NoHair.kerrNewman_einstein`). Everything is expressed through the atoms $r$, $k_1,k_2,k_3$ and "
          "$W=1/(r^2+a^2k_3^2)$, which satisfy $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$. The curvature computation "
          "becomes polynomial identities modulo these two relations; each identity is closed by `linear_combination` "
          "with cofactors precomputed by a Gröbner-basis division. The proof is split into "
          f"{NP} blocks only so that each compiles within the platform's time limit; they contain no `sorry` and use "
          "only the standard axioms.")

for p in meta:
    name = p['name']
    if state.get(name, {}).get('status') == 'PUBLISHED':
        print(name, 'already published', flush=True)
        continue
    src = open(f"{W}/Def_{name}.lean").read()
    payload = {
        'definition_name': name,
        'definition_title': f"Kerr–Newman solves the Einstein equation: {p['key']} (block {p['i']} of {NP})",
        'definition': src,
        'natural_language_statement': f"**{p['key']}.** {p['desc']}\n\n{COMMON}",
        'source': ("Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary "
                   "Kerr–Newman Black Holes*. Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, "
                   "https://doi.org/10.1063/1.1704351; Kerr–Schild form as in the platform definition `NoHair_kerrNewman`."),
        'tags': ['general-relativity', 'kerr-newman', 'einstein-maxwell'],
    }
    if len(sys.argv) > 1 and sys.argv[1] == 'dry':
        print(json.dumps({k: (v if k != 'definition' else v[:120]) for k, v in payload.items()}, indent=1, ensure_ascii=False))
        break
    for attempt in range(1, 7):
        if 'job' not in state.get(name, {}):
            pf = f'{N}/payload_{name}.json'
            json.dump(payload, open(pf, 'w', encoding='utf-8'), ensure_ascii=False)
            r = p2m('post', 'submit-definition', '@' + pf)
            job = r.get('job_id') or (r.get('jobs') or [{}])[0].get('job_id')
            if not job:
                print(name, 'SUBMIT FAILED', str(r)[:500], flush=True)
                sys.exit(1)
            state[name] = {'job': job}
            json.dump(state, open(STATE, 'w'), indent=1)
            print(name, 'attempt', attempt, 'job', job, flush=True)
        job = state[name]['job']
        st, r = None, {}
        for _ in range(400):
            time.sleep(8)
            r = p2m('get', f'publish-jobs/{job}')
            st = r.get('status')
            if st in ('PUBLISHED', 'FAILED', 'ERROR'):
                break
        err = (r.get('error_message') or '')
        print(name, st, err[:400], flush=True)
        if st == 'PUBLISHED':
            state[name].update(status=st, theorem_id=r.get('theorem_id'))
            json.dump(state, open(STATE, 'w'), indent=1)
            break
        if 'timed out' in err or 'Internal error' in err:
            state[f'{name}_try{attempt}'] = state.pop(name)
            json.dump(state, open(STATE, 'w'), indent=1)
            continue
        sys.exit(1)
    else:
        print(name, 'gave up after retries', flush=True)
        sys.exit(2)
print('ALL PUBLISHED', flush=True)
