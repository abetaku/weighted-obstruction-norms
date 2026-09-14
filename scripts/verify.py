#!/usr/bin/env python3
"""Build the project and audit every named project theorem's kernel dependencies."""
from pathlib import Path
import os, re, subprocess, json, time, hashlib, datetime, sys
root=Path(__file__).resolve().parents[1]
os.chdir(root)
audit=root/'audit'; audit.mkdir(exist_ok=True)
files=sorted((root/'WeightedObstructionNorms').glob('*.lean'))
names=[]
for path in files:
    text=path.read_text()
    # The source files intentionally use no nested block comments.
    code=re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    code=re.sub(r'--[^\n]*','',code)
    forbidden=re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code)
    if forbidden:
        raise SystemExit(f'Forbidden proof escape in {path.name}: {forbidden.group()}')
    namespaces=[]
    for line in code.splitlines():
        if m:=re.match(r'namespace\s+(\w+)',line): namespaces.append(m[1])
        elif m:=re.match(r'end\s+(\w+)',line):
            if namespaces and namespaces[-1]==m[1]: namespaces.pop()
        elif m:=re.match(r'(?:@\[[^\]]*\]\s*)*(?:theorem|lemma)\s+([\w.]+)',line):
            names.append('.'.join(namespaces+[m[1]]))
coverage=json.loads((audit/'paper_coverage.json').read_text())
if coverage['status'] != 'complete' or len(coverage['statements']) != 14 or any(e['status'] != 'complete' or not e['declarations'] for e in coverage['statements']):
    raise SystemExit('The manuscript coverage table is incomplete.')
coverage_names={n for e in coverage['statements'] for n in e['declarations']}
extra_names=sorted(coverage_names-set(names))
audit_names=names+extra_names
checker=audit/'CheckAxioms.lean' 
checker.write_text('import WeightedObstructionNorms\n\n'+''.join(f'#print axioms {name}\n' for name in audit_names))
commands=[['lake','build'],['lake','env','lean','audit/CheckAxioms.lean']]
start=time.time();started=datetime.datetime.now(datetime.timezone.utc).isoformat()
records=[]
for cmd,logfile in zip(commands,['build.log','axioms.log']):
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (audit/logfile).write_text(p.stdout)
    records.append({'argv':cmd,'exit_status':p.returncode,'log':f'audit/{logfile}'})
    if p.returncode:
        print(p.stdout)
        raise SystemExit(p.returncode)
text=(audit/'axioms.log').read_text()
entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",text)
seen={n for n,_ in entries}|set(noaxioms)
if seen != set(audit_names):
    raise SystemExit('Axiom audit did not cover exactly the requested theorem list: '+str(set(audit_names)-seen))
allowed={'propext','Classical.choice','Quot.sound'}
for name,axioms in entries:
    used={s.strip() for s in axioms.split(',') if s.strip()}
    if not used<=allowed:
        raise SystemExit(f'Unexpected axioms for {name}: {used-allowed}')
version=subprocess.run(['lean','--version'],capture_output=True,text=True,check=True).stdout.strip()
result={
 'status':'kernel_checked_complete_mathematical_formalization',
 'entire_paper_formalized':True,
 'formalization_scope':coverage['scope'],
 'paper_statement_count':len(coverage['statements']),
 'additional_declarations_checked':extra_names,
 'paper_coverage_sha256':hashlib.sha256((audit/'paper_coverage.json').read_bytes()).hexdigest(),
 'started_at':started,'runtime_seconds':time.time()-start,
 'lean_version':version,
 'mathlib_commit':'c44e0c8ee63ca166450922a373c7409c5d26b00b',
 'commands':records,'named_theorems_checked':len(names),'theorems':names,
 'allowed_standard_axioms':sorted(allowed),
 'custom_axioms':0,'sorry_or_admit':0,
 'source_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
   for p in [root/'WeightedObstructionNorms.lean',*files,root/'paper/weighted_obstruction_norms_en.tex']}
}
(audit/'verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(f'PASS: {len(names)} named theorem/lemma declarations; no proof holes or nonstandard axioms.')
