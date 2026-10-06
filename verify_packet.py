"""Verify published evidence and source integrity. Never executes Lean."""
import hashlib
import json
import re
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def read(name):
    return json.loads((ROOT / name).read_text())

def main():
    report = read('formal/verification-source-azure.json')
    review = read('review/source-model-review.json')
    require(sha((ROOT / review['formal_certificate']['path']).read_bytes()) == review['formal_certificate']['sha256'], 'certificate hash')
    for key in ['manuscript', 'archived_research_narrative']:
        item = review[key]
        require(sha((ROOT / item['path']).read_bytes()) == item['sha256'], key + ' hash')
    require((ROOT / 'docs/research-note.tex').read_bytes() == (ROOT / 'research-note.tex').read_bytes(), 'site manuscript differs')
    for filename, digest in report['source_sha256'].items():
        require(sha((ROOT / 'formal' / filename).read_bytes()) == digest, 'source hash: ' + filename)
    history = read('evidence/development-history.json')
    positive = next(x for x in history if x['seq'] == report['positive_request'])
    negative = next(x for x in history if x['seq'] == report['negative_control']['request'])
    require(positive['status'] == 'PASS' and positive['records'] == report['modules'], 'positive record')
    require(all(x['exit_code'] == 0 for x in positive['records']), 'positive exit codes')
    require(positive['source_sha256'] == report['source_sha256'], 'returned source map')
    control = next(x for x in negative['records'] if x['module'] == 'NegativeSource')
    require(negative['status'] == 'FAIL' and control['exit_code'] == 1 and control['log'].count('error:') == 1
            and control['log'].rstrip().endswith('⊢ False'), 'negative control')
    require(all(x['exit_code'] == 0 for x in negative['records'] if x is not control), 'unexpected negative-run failure')
    artifact = ROOT / 'evidence/proof-artifacts.tgz'
    require(sha(artifact.read_bytes()) == report['proof_artifacts_sha256'], 'artifact archive hash')
    with tarfile.open(artifact, 'r:gz') as archive:
        members = archive.getmembers()
        require(len({m.name for m in members}) == len(members), 'duplicate archive members')
        require(all(m.isfile() and Path(m.name).name == m.name and m.size <= 32*1024*1024 for m in members), 'unexpected archive entries')
        for filename, digest in report['source_sha256'].items():
            require(sha(archive.extractfile(filename).read()) == digest, 'archived source: ' + filename)
        for record in report['modules']:
            require(archive.getmember(record['module'] + '.olean').size > 0, 'missing compiled module')
    expected = []
    theorem_count = 0
    for module in report['modules']:
        if module['module'] == 'Audit':
            continue
        source = (ROOT / 'formal' / (module['module'] + '.lean')).read_text()
        expected += re.findall(r'^(?:theorem|def|abbrev|structure)\s+([\w.]+)', source, re.M)
        theorem_count += len(re.findall(r'^theorem\s+', source, re.M))
        require(not re.search(r'\b(?:sorry|admit|native_decide|ofReduceBool)\b|^(?:unsafe\s+|axiom\s+)', source, re.M), 'forbidden proof token')
    entries = re.findall(r"'MatchingCapacity\.([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", report['modules'][-1]['log'], re.S)
    require([n for n, _ in entries] == expected, 'incomplete declaration audit')
    axioms = {name: sorted(a.strip() for a in values.split(',') if a.strip()) for name, values in entries}
    require(axioms == report['axioms_by_declaration'], 'axiom report differs from log')
    require(all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms.values()), 'unexpected axioms')
    require(theorem_count == report['named_theorem_count'] == 714, 'theorem count')
    require(len(expected) == report['audited_declaration_count'] == 929, 'declaration count')
    require(read('evidence/pins.json') == report['pins'] == read('formal/pins.json'), 'version pins')
    require(read('evidence/remote-result.json')['exit_code'] == 0, 'worker failed')
    cleanup = read('evidence/cleanup-report.json')
    require(cleanup == report['cleanup'] and cleanup['all_deleted'] and not any(cleanup['group_exists'].values()) and not cleanup['resource_ids'], 'cleanup record')
    tex = (ROOT / 'research-note.tex').read_text()
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    require(len(labels) == len(set(labels)), 'duplicate manuscript labels')
    require(set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', tex)) <= set(labels), 'unresolved manuscript reference')
    require(set(re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', tex)) <= set(re.findall(r'\\bibitem\{([^}]+)\}', tex)), 'unresolved citation')
    for row in review['model_correspondence'] + review['proof_correspondence']:
        if 'manuscript_label' in row:
            require(row['manuscript_label'] in labels, 'review label')
        for decl in row['lean']:
            name = decl['name'].split('.')[-1]
            line = (ROOT / decl['file']).read_text().splitlines()[decl['line']-1]
            require(re.match(r'(?:def|theorem|lemma|abbrev) '+re.escape(name)+r'\b', line), 'declaration location')
            require(name in axioms, 'unaudited mapped declaration')
    print(json.dumps({'status':'PASS_PUBLIC_PACKET','theorems':theorem_count,'audited_declarations':len(axioms),
        'modules':len(report['modules']),'scope':'Recorded evidence and file integrity only; no Lean execution'},indent=2))

if __name__ == '__main__':
    main()
