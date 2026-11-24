#!/usr/bin/env python3
"""Extract Lewis Carroll's *Pillow-Problems* (PG #79080) into data/problems.json.

Reads the Project Gutenberg MathJax source (79080-src.htm) given as argv[1] and writes JSON with,
for each of the 72 problems: the question (Chapter I), the answer (Chapter II, where Carroll
gives one separately), the solution (Chapter III), Carroll's page cross-references, the date
he noted, and the subject(s) from his "Subjects classified" index. TeX is kept as \\( \\) / \\[ \\].
"""
import html, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def to_text(fragment: str, notes: dict) -> str:
    t = fragment
    t = re.sub(r'<span class="pagenum"[^>]*>.*?</span>', '', t, flags=re.S)
    t = re.sub(r'<a id="FNanchor_(\d+)"[^>]*>\[\d+\]</a>',
               lambda m: f" [Footnote: {notes.get(m.group(1), '')}]", t)
    t = re.sub(r'<figure.*?alt="(.*?)".*?</figure>',
               lambda m: '\n\n[Figure: ' + ' '.join(m.group(1).split()) + ']\n\n', t, flags=re.S)
    t = re.sub(r'<figure.*?</figure>', '\n\n[Figure]\n\n', t, flags=re.S)
    t = re.sub(r'</?(i|em)>', '*', t)
    t = re.sub(r'</?(b|strong)>', '**', t)
    t = re.sub(r'<br\s*/?>', '\n', t)
    t = re.sub(r'</(p|div|tr|li|table|h\d)>', '\n\n', t)
    t = re.sub(r'</t[dh]>', ' | ', t)
    t = re.sub(r'<hr[^>]*>', '\n\n', t)
    t = re.sub(r'<[^>]+>', '', t)
    t = html.unescape(t).replace(' ', ' ')
    paras = [' '.join(p.split()) for p in re.split(r'\n\s*\n', t)]
    return '\n\n'.join(p for p in paras if p)


def main() -> int:
    src = Path(sys.argv[1]).read_text(encoding='utf-8')
    # footnotes: <div class="footnote"> ... <a id="Footnote_N" ...>[N]</a> text
    notes = {}
    for m in re.finditer(r'<a id="Footnote_(\d+)"[^>]*>\[\d+\]</a>(.*?)</div>', src, flags=re.S):
        notes[m.group(1)] = to_text(m.group(2), {}).replace('\n\n', ' ')
    src_nofn = re.sub(r'<h3>FOOTNOTES:</h3>.*?(?=<hr class="chap|<h2)', '', src, flags=re.S)

    def chapter(cid: str, nxt: str) -> str:
        i = src_nofn.find('>', src_nofn.find(f'id="{cid}"')) + 1
        j = src_nofn.rfind('<', 0, src_nofn.find(f'id="{nxt}"', i))
        return src_nofn[i:j]

    # "<b>12.</b> (4, 20)" and, twice in Chapter III, "<b>12. (4, 20)</b>"
    marker = re.compile(r'<p class="nindc space-above2"><b>(?:<a id="\d+">)?(\d+)(?:</a>)?\.(?:</b>)?\s*'
                        r'\(([^)]*)\)(?:</b>)?(.*?)</p>', re.S)

    def split(chap: str) -> dict:
        ms = list(marker.finditer(chap))
        out = {}
        for k, m in enumerate(ms):
            end = ms[k + 1].start() if k + 1 < len(ms) else len(chap)
            body = chap[m.end():end]
            date = None
            dm = re.search(r'<p class="right">\s*\[([^<]*)</p>', body)
            if dm and not re.search(r'Q\.\s*E\.', dm.group(1)):
                date = dm.group(1).strip()
                body = body[:dm.start()] + body[dm.end():]
            # the only footnote on a problem-number line (No. 1) explains the page numbers in
            # parentheses; it belongs to the book, not to the problem
            extra = to_text(re.sub(r'<a id="FNanchor_\d+"[^>]*>\[\d+\]</a>', '', m.group(3)), notes)
            text = to_text(body, notes)
            out[int(m.group(1))] = dict(refs=m.group(2).strip(), text=(extra + '\n\n' + text).strip() if extra else text, date=date)
        return out

    qs = split(chapter('CHAPTER_I', 'CHAPTER_II'))
    ans = split(chapter('CHAPTER_II', 'CHAPTER_III'))
    sol = split(chapter('CHAPTER_III', 'WORKS_BY_C_L_DODGSON'))
    if 72 in sol:  # the book's closing words follow the last solution
        sol[72]['text'] = re.sub(r'\s*THE END\.?\s*$', '', sol[72]['text'])

    # subjects index
    i = src.find('id="SUBJECTS_CLASSIFIED"'); j = src.find('</ul>', i)
    subjects = {}
    head = None
    for li in re.findall(r'<li class="([^"]+)">(.*?)</li>', src[i:j], flags=re.S):
        cls, body = li
        label = re.sub(r'<[^>]+>', '', body.split('No')[0]).strip().strip(':').strip('.').strip()
        label = re.sub(r'[^\w ,]+$', '', html.unescape(label).replace(' ', ' ')).strip(' :.')
        nums = [int(x) for x in re.findall(r'href="#(\d+)"', body)]
        if cls in ('ifrst', 'indx'):
            head = label
            name = label
        elif cls.startswith('isub') and nums and re.search('[A-Za-z]', label):  # not a continuation line
            name = f'{head}: {label}' if head else label
        else:
            name = None
        if nums:
            key = name or last_name
            for n in nums:
                subjects.setdefault(n, [])
                if key not in subjects[n]:
                    subjects[n].append(key)
            last_name = key
        elif name:
            last_name = name

    def section(cid: str, nxt: str) -> str:
        return to_text(chapter(cid, nxt), notes)

    problems = []
    for n in range(1, 73):
        problems.append(dict(
            n=n, subjects=subjects.get(n, []), date=qs.get(n, {}).get('date'),
            question=qs.get(n, {}).get('text'), question_refs=qs.get(n, {}).get('refs'),
            answer=ans.get(n, {}).get('text'), solution=sol.get(n, {}).get('text'),
        ))
    out = dict(
        source='Project Gutenberg eBook #79080: Lewis Carroll (C. L. Dodgson), Curiosa Mathematica, '
               'Part II: Pillow-Problems thought out during wakeful hours, 4th edition, Macmillan 1895',
        preface_4th=section('PREFACE_TO_FOURTH_EDITION', 'PREFACE_TO_SECOND_EDITION'),
        preface_2nd=section('PREFACE_TO_SECOND_EDITION', 'INTRODUCTION'),
        introduction=section('INTRODUCTION', 'CONTENTS'),
        problems=problems,
    )
    missing = [p['n'] for p in problems if not p['question'] or not p['solution']]
    (ROOT / 'data' / 'problems.json').write_text(json.dumps(out, ensure_ascii=False, indent=1) + '\n', encoding='utf-8')
    print(f"{len(qs)} questions, {len(ans)} separate answers, {len(sol)} solutions; missing: {missing}")
    return 1 if missing else 0


if __name__ == '__main__':
    sys.exit(main())
