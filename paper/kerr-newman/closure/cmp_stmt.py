import re
import os, sys
NH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'prove2me', 'nohair')
TH = os.path.join(sys.argv[1] if len(sys.argv) > 1 else '/root/prove2me_workspace', 'Theorems')
pairs = [(f'{NH}/einstein/Sol_NoHair_KNE_thm_{t}.lean', f'{TH}/Thm_NoHair_KNE_thm_{t}.lean', f'thm_{t}') for t in
         ['christoffel', 'div_one', 'div_two', 'div_three', 'ricci_a', 'ricci_b', 'ricci_c', 'maxwell']]
pairs += [(f'{NH}/Sol_NoHair_kerrNewman_{t}.lean', f'{TH}/Thm_NoHair_kerrNewman_{t}.lean', f'kerrNewman_{t}') for t in
          ['flat_maxwell', 'field_closed', 'maxwell', 'einsteinMaxwell']]
pairs.append((f'{NH}/einstein/Sol_NoHair_kerrNewman_einstein.lean', f'{TH}/Thm_NoHair_kerrNewman_einstein.lean', 'kerrNewman_einstein'))
def stmt(text, name):
    i = re.search(rf'^theorem {name}\b', text, flags=re.M).end()
    j = text.index(':=', i)
    return ' '.join(text[i:j].split())
for sol, thm, name in pairs:
    a = stmt(open(sol).read(), 'solution'); b = stmt(open(thm).read(), name)
    print('SAME' if a == b else 'DIFF', name)
    if a != b: print('  sol:', a[:300]); print('  thm:', b[:300])
