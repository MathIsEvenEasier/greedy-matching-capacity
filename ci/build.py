#!/usr/bin/env python3
"""Fresh project proof build; intended only for an independently bounded Azure runner."""
import gzip,hashlib,json,os,pathlib,re,shutil,subprocess,time,urllib.request
root=pathlib.Path(__file__).resolve().parents[1]
out=root/'ci-output';out.mkdir(exist_ok=False)
pin='5ed2965256430c3649e86755f9576b54eca72435'
started=time.monotonic()
def run(cmd,cwd=None,timeout=900,env=None,capture=False):
    p=subprocess.run(cmd,cwd=cwd or root,env=env,timeout=timeout,
        text=True,stdout=subprocess.PIPE if capture else None,stderr=subprocess.STDOUT)
    if p.returncode: raise RuntimeError('Command failed: '+cmd[0]+' (exit '+str(p.returncode)+')')
    return p.stdout if capture else None
if not pathlib.Path('/run/mathiseasy-azure-verified').is_file():
    raise SystemExit('A verified Azure worker with independent deletion guard is required')
cgroup=next(x.split(':',2)[2] for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0:'))
cap=(pathlib.Path('/sys/fs/cgroup')/cgroup.lstrip('/')/'memory.max').read_text().strip()
if cap=='max' or int(cap)>24*1024**3: raise SystemExit('Whole-job memory limit must be at most 24 GiB')
commit=run(['git','rev-parse','HEAD'],capture=True).strip()
if commit!=os.environ['GITHUB_SHA']: raise SystemExit('Checkout does not match the workflow commit')
if run(['git','status','--porcelain'],capture=True).strip(): raise SystemExit('Checkout is not clean')
provenance={'repository':os.environ['GITHUB_REPOSITORY'],'commit':commit,
 'run_url':'https://github.com/'+os.environ['GITHUB_REPOSITORY']+'/actions/runs/'+os.environ['GITHUB_RUN_ID'],
 'mathlib':pin,'lean':'4.34.0','memory_limit_bytes':int(cap),'status':'IN_PROGRESS'}
(out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print(json.dumps(provenance,indent=2),flush=True)
release=json.loads((root/'ci/lean-release.json').read_text())
cache=pathlib.Path('/opt/proof-cache');archive=cache/'lean.tar.zst'
if not archive.is_file(): urllib.request.urlretrieve(release['browser_download_url'],archive)
if hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()!=release['digest'].split(':')[1]:
    raise SystemExit('Lean release hash mismatch')
if not (cache/'lean-4.34.0-linux').exists(): run(['tar','--zstd','-xf',str(archive),'-C',str(cache)])
os.environ['PATH']=str(cache/'lean-4.34.0-linux/bin')+':'+os.environ['PATH']
print('Lean release SHA-256 verified: '+release['digest'],flush=True)
work=pathlib.Path(os.environ['RUNNER_TEMP'])/'mathlib'
run(['git','init',str(work)])
run(['git','-C',str(work),'remote','add','origin','https://github.com/leanprover-community/mathlib4.git'])
run(['git','-C',str(work),'fetch','--depth','1','origin',pin])
run(['git','-C',str(work),'checkout','--detach','FETCH_HEAD'])
if run(['git','rev-parse','HEAD'],work,capture=True).strip()!=pin: raise SystemExit('Wrong mathlib commit')
version=run(['lean','--version'],work,capture=True).strip();print(version,flush=True)
if not version.startswith('Lean (version 4.34.0,'): raise SystemExit('Wrong Lean version')
run(['lake','exe','cache','get','Mathlib.lean'],work,timeout=900)
kind=os.environ['GITHUB_REPOSITORY'].split('/')[1]
finals={'minkowski14':('Final','Minkowski14.at_least_five_colours'),
 'dna-recovery-duality':('CodeResult','DNA.codeRecoveryBalanced_dual_iff'),
 'greedy-matching-capacity':('SourceModel','MatchingCapacity.source_matching_tail_comparison')}
if kind not in finals: raise SystemExit('Unsupported repository')
source=root/('lean' if kind=='dna-recovery-duality' else 'formal')
provenance['source_sha256']={str(p.relative_to(source)):hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*.lean')}
proof_dir=work
try:
    if kind=='minkowski14':
        # Sources and certificates only: never copy project compiled artifacts.
        for p in source.rglob('*'):
            if p.is_file() and (p.suffix in ('.lean','.py','.json','.cnf','.gz') or p.name=='lean-toolchain'):
                q=work/p.relative_to(source);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
        gz=work/'artifacts/minkowski14_final_4color.lrat.gz'
        with gzip.open(gz,'rb') as i,gz.with_suffix('').open('wb') as o: shutil.copyfileobj(i,o)
        manifest=json.loads((root/'evidence/proof-source-manifest.json').read_text())
        if hashlib.file_digest(gz.with_suffix('').open('rb'),'sha256').hexdigest()!=manifest['artifacts/minkowski14_final_4color.lrat']:
            raise RuntimeError('LRAT input hash mismatch')
        run(['python3','-u','rebuild.py'],work,timeout=6450)
        report=json.loads((work/'rebuild-report.json').read_text())
        if report['status']!='VERIFIED' or len(report['records'])!=165: raise RuntimeError('Incomplete build report')
    elif kind=='greedy-matching-capacity':
        proof_dir=work/'matching-rebuild-output'
        run(['python3','-u',str(root/'scripts/rebuild.py'),str(work)],work,timeout=2100)
    else:
        proof_dir=work/'dna-rebuild-output';proof_dir.mkdir()
        for p in source.glob('*.lean'): shutil.copy2(p,proof_dir/p.name)
        modules='Sampling Words Occupancy TailFormula Pairing MatroidDual Result Audit CodeLinear CodeGenerator CodeResult CodeProbability CodeAudit'.split()
        records=[]
        for module in modules+['NegativeControl','CodeNegativeControl']:
            begin=time.monotonic();negative=module not in modules
            p=subprocess.run(['lake','env','lean','-j1','-M6000','-DwarningAsError=true','-DElab.async=false',
                '-o',str(proof_dir/(module+'.olean')),str(proof_dir/(module+'.lean'))],
                cwd=work,env=dict(os.environ,LEAN_PATH=str(proof_dir)),capture_output=True,text=True,timeout=90)
            log=p.stdout+p.stderr
            records.append({'module':module,'exit_code':p.returncode,'log':log,
                'expected_failure':negative,'seconds':round(time.monotonic()-begin,3)})
            (out/'rebuild-record.json').write_text(json.dumps(records,indent=2)+'\n')
            print(module+': exit '+str(p.returncode),flush=True)
            if module in ('Audit','CodeAudit') or negative or p.returncode: print(log,flush=True)
            if negative:
                if p.returncode!=1 or 'True.intro' not in log or 'False' not in log or 'type mismatch' not in log.lower():
                    raise RuntimeError('Negative control did not fail for the expected type mismatch')
            elif p.returncode: raise RuntimeError('Positive module failed')
        for rec in records:
            if rec['module'] in ('Audit','CodeAudit'):
                entries=re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",rec['log'],re.S)
                if not entries: raise RuntimeError('Missing axiom audit')
                for _,axioms in entries:
                    if set(a.strip() for a in axioms.split(',') if a.strip())-{'propext','Classical.choice','Quot.sound'}:
                        raise RuntimeError('Unapproved axiom')
    module,theorem=finals[kind]
    query=proof_dir/'PublicFinalAudit.lean'
    query.write_text('import '+module+'\n#print axioms '+theorem+'\n#check '+theorem+'\n')
    output=run(['lake','env','lean','-j1','-M18000','-DElab.async=false',str(query)],work,timeout=600,
        env=dict(os.environ,LEAN_PATH=str(proof_dir)),capture=True)
    print('\nFINAL THEOREM AND AXIOMS\n'+output,flush=True)
    (out/'final-axioms.txt').write_text(output)
    m=re.search(re.escape("'"+theorem+"'")+r' depends on axioms: \[(.*?)\]',output,re.S)
    if not m: raise RuntimeError('Final axiom output missing')
    axioms=sorted(a.strip() for a in m[1].split(',') if a.strip())
    if set(axioms)-{'propext','Classical.choice','Quot.sound'}: raise RuntimeError('Unapproved final axiom')
    provenance.update(status='VERIFIED',final_theorem=theorem,axioms=axioms)
except BaseException:
    provenance['status']='FAILED'
    raise
finally:
    for name in ('rebuild-report.json','rebuild-record.json'):
        for folder in (work,proof_dir):
            if (folder/name).is_file(): shutil.copy2(folder/name,out/name)
    provenance['seconds']=round(time.monotonic()-started,3)
    (out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'],'a') as f:
            f.write('## Lean verification: '+provenance['status']+'\n\nCommit: `'+commit+'`\n\n')
            f.write('Lean 4.34.0; mathlib `'+pin+'`. All project modules rebuilt from source.\n\n')
            if provenance['status']=='VERIFIED': f.write('Final theorem: `'+theorem+'`\n\nAxioms: `'+', '.join(axioms)+'`.\n')
    print('Build status: '+provenance['status'],flush=True)
if provenance['status']!='VERIFIED': raise SystemExit(1)
