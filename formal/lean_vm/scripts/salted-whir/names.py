"""The salted core IR's function names and indices: `index(name)`, read off `LeanVM/SaltedGuest/Data/Core*.lean`."""
import glob, os, re

ROOT = os.path.join(os.path.dirname(__file__), '..', '..')


def table(datadir):
    idx = {}
    for f in sorted(glob.glob(os.path.join(ROOT, datadir, 'Core*.lean'))):
        s = open(f).read()
        for m in re.finditer(r'noncomputable def core(\d+) : Core\.Fn where\n  name := "([^"]+)"', s):
            idx[m.group(2)] = int(m.group(1))
    return idx


SALTED = table('LeanVM/SaltedGuest/Data')
