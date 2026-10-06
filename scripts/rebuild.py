"""Rebuild on an already provisioned, bounded Azure Linux worker. No provisioning."""
import json, os, platform, re, shutil, subprocess, sys, time
from pathlib import Path

root = Path(__file__).resolve().parents[1]
if platform.system() != 'Linux':
    raise SystemExit('Run only on a bounded Azure Linux worker; see REPRODUCE.rst.')
if len(sys.argv) != 2:
    raise SystemExit('Usage: timeout 1800 python3 scripts/rebuild.py /path/to/pinned-mathlib')
work = Path(sys.argv[1]).resolve()
report = json.loads((root/'formal/verification-source-azure.json').read_text())
pins = report['pins']
def command(args, timeout=30, env=None):
    return subprocess.run(args,cwd=work,env=env,capture_output=True,text=True,timeout=timeout)
revision = command(['git','rev-parse','HEAD'])
if revision.returncode or revision.stdout.strip() != pins['mathlib']:
    raise SystemExit('Mathlib revision mismatch')
version = command(['lake','env','lean','--version'])
if version.returncode or not re.search(r'\b4\.34\.0\b',version.stdout):
    raise SystemExit('Lean version mismatch')
out = work/'matching-rebuild-output'
out.mkdir(exist_ok=False)
for path in (root/'formal').glob('*.lean'):
    shutil.copy2(path,out/path.name)
env = dict(os.environ,LEAN_PATH=str(out))
records=[]
for module in [x['module'] for x in report['modules']]+['NegativeSource']:
    start=time.monotonic()
    result=command(['lake','env','lean','-j1','-M6000','-DwarningAsError=true','-DElab.async=false',
                    '-o',str(out/(module+'.olean')),str(out/(module+'.lean'))],90,env)
    record={'module':module,'exit_code':result.returncode,'log':result.stdout+result.stderr,'seconds':time.monotonic()-start}
    records.append(record)
    (out/'rebuild-record.json').write_text(json.dumps(records,indent=2)+'\n')
    print(module,result.returncode,flush=True)
    if module=='NegativeSource':
        if result.returncode!=1 or record['log'].count('error:')!=1 or not record['log'].rstrip().endswith('⊢ False'):
            raise SystemExit('Negative control did not fail as expected')
    elif result.returncode:
        raise SystemExit('Positive module failed: '+module)
audit=next(x['log'] for x in records if x['module']=='Audit')
entries=re.findall(r"'MatchingCapacity\.([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",audit,re.S)
axioms={n:sorted(a.strip() for a in s.split(',') if a.strip()) for n,s in entries}
if axioms!=report['axioms_by_declaration']:
    raise SystemExit('Audit differs from published declaration map')
print('PASS: all positive modules, full axiom audit and expected negative rejection. Retrieve results and confirm Azure resource deletion.')
