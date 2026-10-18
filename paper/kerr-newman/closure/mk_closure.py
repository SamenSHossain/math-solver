"""Build a single-environment closure of the Kerr-Newman Einstein-Maxwell proof:
every platform theorem stub (Theorems.Thm_X, which contains `sorry`) is replaced by a module
that proves the theorem under its platform name using the accepted solution file."""
import re, os  # noqa
NH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'prove2me', 'nohair')
OUT = os.path.dirname(os.path.abspath(__file__)) + '/src/Closure'
os.makedirs(OUT, exist_ok=True)
KNE = ['christoffel', 'div_one', 'div_two', 'div_three', 'ricci_a', 'ricci_b', 'ricci_c', 'maxwell']
mods = []  # (module, source path, full theorem name)
for t in KNE:
    mods.append((f'KNE_thm_{t}', f'{NH}/einstein/Sol_NoHair_KNE_thm_{t}.lean', f'NoHair.KNE.thm_{t}'))
mods += [
    ('kerrNewman_flat_maxwell', f'{NH}/Sol_NoHair_kerrNewman_flat_maxwell.lean', 'NoHair.kerrNewman_flat_maxwell'),
    ('kerrNewman_field_closed', f'{NH}/Sol_NoHair_kerrNewman_field_closed.lean', 'NoHair.kerrNewman_field_closed'),
    ('kerrNewman_maxwell', f'{NH}/Sol_NoHair_kerrNewman_maxwell.lean', 'NoHair.kerrNewman_maxwell'),
    ('kerrNewman_einstein', f'{NH}/einstein/Sol_NoHair_kerrNewman_einstein.lean', 'NoHair.kerrNewman_einstein'),
    ('kerrNewman_einsteinMaxwell', f'{NH}/Sol_NoHair_kerrNewman_einsteinMaxwell.lean', 'NoHair.kerrNewman_einsteinMaxwell'),
]
# helper lemmas of the final Einstein file that clash with same-named lemmas in the definition blocks
CLASH = ['Gam_symm', 'dDivT_symm', 'RicA_symm', 'RicS_symm', 'fS', 'fU', 'fF', 'tS']
for mod, src, full in mods:
    s = open(src, encoding='utf-8').read()
    s = re.sub(r'^import Theorems\.Thm_NoHair_(\S+)$', lambda mm: f'import Closure.{mm.group(1)}', s, flags=re.M)
    n = len(re.findall(r'^theorem solution\b', s, flags=re.M))
    assert n == 1, (src, n)
    s = re.sub(r'^theorem solution\b', f'theorem {full}', s, flags=re.M)
    if mod == 'kerrNewman_einstein':
        for c in CLASH:
            s = re.sub(rf'(?<![\w.]){c}(?![\w\'])', f'{c}_fin', s)
    open(f'{OUT}/{mod}.lean', 'w', encoding='utf-8').write(s)
open(f'{OUT}/All.lean', 'w').write(
    'import Closure.kerrNewman_einsteinMaxwell\n\n'
    '#print axioms NoHair.kerrNewman_einsteinMaxwell\n'
    '#print axioms NoHair.kerrNewman_einstein\n'
    '#print axioms NoHair.kerrNewman_maxwell\n'
    '#print axioms NoHair.kerrNewman_field_closed\n')
order = [m for m, _, _ in mods] + ['All']
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'order.txt'), 'w').write('\n'.join(order) + '\n')
print('\n'.join(order))
