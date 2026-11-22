"""Copy declarations of the deployed WHIR soundness chain to the salted guest: the program the salted
core IR, the runs at the keyed hash `keyedHash S` (`RunsWithH`), the queries over the salted
`level_queries` (`osQueries_soundK`), with the seed `S` of memory words 2 and 3 (`hS2`, `hS3`).

  python3 scripts/salted-whir/chaincopy.py OUT.lean HEADER.lean SRC:NAME[:NEWNAME] ...

Each `SRC:NAME` is a declaration of `LeanVM/Guest/B1/Whir/SRC.lean` (from its doc comment to the next
declaration's); the output is HEADER, then the copies in order, then the namespace's end.
"""
import os, re, sys

ROOT = os.path.join(os.path.dirname(__file__), '..', '..')
DECL = re.compile(r'^(?:/--|theorem |def |abbrev |structure |noncomputable def |set_option )', re.M)

RENAME = ['LvQCallees', 'LvQW', 'LvCallees', 'CalleesOk', 'QWOk', 'calleesOk_at', 'lvOs', 'bOs',
          'osQueries_sound', 'osLevelB_common', 'levelRest_run', 'osLevelB_sound',
          'osLevel_nonfinal_sound', 'osLevel_final_sound', 'osLevels_sound', 'OpenOutW',
          'lqOpenings', 'osLevelOs', 'open_stacked_osW', 'open_stacked_sound_w_Spec',
          'open_generic', 'open_stacked_sound_w', 'lvQW_of', 'qwOk_of', 'calleesOk_of',
          'lvCallees_of', 'lp_callee', 'lr_callee', 'rw_callee', 'osSoundW_of', 'OsSoundW', 'lvW',
          'FnIs', 'lqBody', 'lqCall', 'qwOk_at', 'ResIn', 'osResiduals_sound', 'osFinish_sound',
          'osHead_sound']
SUBST = [
    ("coreProgram.Rel", "SaltedGuest.coreProgram.Rel"),
    ("coreProgram.find?", "SaltedGuest.coreProgram.find?"),
    ("UnfoldsV rd C V", "SaltedGuest.End.UnfoldsV rd C V"),
    ("UnfoldsV L.read C V", "SaltedGuest.End.UnfoldsV L.read C V"),
    ("(V : FrameMap)", "(V : SaltedGuest.End.FrameMap)"),
    ("{V : FrameMap}", "{V : SaltedGuest.End.FrameMap}"),
    ("(Fr : FrameMap)", "(Fr : SaltedGuest.End.FrameMap)"),
    ("FrameMap →", "SaltedGuest.End.FrameMap →"),
    ("RunsWith.bind'", "RunsWithH.bind"),
    ("RunsWith.bind", "RunsWithH.bind"),
    ("RunsWith.of_eq", "RunsWithH.of_eq"),
    ("RunsTo.withRoots", "RunsTo.withRootsH"),
    ("runsWith_ret", "runsWithH_ret"),
    ("runsWith_queryP", "runsWithH_queryP"),
    ("runsWith_commitP", "runsWithH_commitP"),
    ("MeaningVerifyMerkleCap lv.capDepth", "MeaningCapK (2 ^ lv.capDepth)"),
]
HS = "{S : Digest} (hS2 : LoadHolds rd 1 2 (digestHalves S).1)\n    (hS3 : LoadHolds rd 1 3 (digestHalves S).2)"


def decl(src, name):
    s = open(os.path.join(ROOT, 'LeanVM/Guest/B1/Whir', src + '.lean')).read()
    m = re.search(r'^(?:theorem|def|abbrev|structure|noncomputable def) ' + re.escape(name) + r'\b', s, re.M)
    assert m, (src, name)
    i = m.start()
    # back up over the doc comment and set_option lines right above
    head = s[:i]
    k = head.rfind('/--')
    if k >= 0 and '-/' in head[k:] and head[head.index('-/', k) + 2:].strip() == '':
        i = k
    while True:
        pre = s[:i].rstrip('\n')
        line = pre[pre.rfind('\n') + 1:]
        if line.startswith('set_option'):
            i = pre.rfind('\n') + 1
        else:
            break
    rest = s[m.end():]
    n = DECL.search(rest)
    e = m.end() + (n.start() if n else len(rest))
    j = s.rfind('\nend', m.end(), e)
    body = s[i:e]
    lines = body.rstrip().split('\n')
    while lines and re.match(r'(end\b|section\b|variable\b|/-! |@\[expose\])', lines[-1]):
        lines.pop()
        while lines and not lines[-1].strip():
            lines.pop()
    return '\n'.join(lines) + '\n\n'


def convert(t):
    for a, b in SUBST:
        t = t.replace(a, b)
    t = re.sub(r'\bRunsWith \(', 'RunsWithH (keyedHash S) (', t)
    t = re.sub(r'\bRunsWith\n', 'RunsWithH (keyedHash S)\n', t)
    t = t.replace('keccak256', '(keyedHash S)')
    for n in RENAME:
        t = re.sub(r'\b' + n + r'\b(?!K)', n + 'K', t)
    t = t.replace('SaltedGuest.coreProgram.SaltedGuest.', 'SaltedGuest.')
    t = t.replace('(hU : SaltedGuest.End.UnfoldsV rd C V)', '(hU : SaltedGuest.End.UnfoldsV rd C V)\n    ' + HS)
    t = re.sub(r'\bhle hU\b(?! hS2)', 'hle hU hS2 hS3', t)
    t = re.sub(r'\bhU hcfg\b', 'hU hS2 hS3 hcfg', t)
    t = t.replace('hcal.cap W hQW', 'hcal.cap W hQW hS2 hS3')
    t = t.replace('osQueries_soundK hle hU hS2 hS3', 'osQueries_soundK hle hU')
    t = re.sub(r'exact hrun2\n', 'exact RunsWith.toH hrun2\n', t)
    t = t.replace('(opening_fold_holds rd _ _).mp (hle _ _ _ h)', 'opening_foldK (hle _ _ _ h)')
    t = re.sub(r'RunsTo\.withRootsH (?!\(H)', 'RunsTo.withRootsH (H := keyedHash S) ', t)
    t = re.sub(r'([ \[,])StmtOk([,\]])', r'\1Whir.StmtOk\2', t)
    return t


out, header, *items = sys.argv[1:]
txt = open(header).read()
for it in items:
    p = it.split(':')
    txt += convert(decl(p[0], p[1]))
txt += 'end\nend LeanVM.SaltedGuest.B1.Whir\n'
open(out, 'w').write(txt)
