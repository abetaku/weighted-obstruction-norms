#!/usr/bin/env python3
"""Package the current verified source snapshot; refuse stale verification."""
from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parents[1]
audit=root/'audit'
v=json.loads((audit/'verification.json').read_text())
if not v.get('entire_paper_formalized'):
 raise SystemExit('The final package requires a complete verification record.')
if hashlib.sha256((audit/'paper_coverage.json').read_bytes()).hexdigest()!=v['paper_coverage_sha256']:
 raise SystemExit('Coverage changed; run scripts/verify.py again.')
current_sources={str(p.relative_to(root)) for p in (root/'WeightedObstructionNorms').glob('*.lean')}
verified_sources={p for p in v['source_sha256'] if p.startswith('WeightedObstructionNorms/')}
if current_sources != verified_sources:
 raise SystemExit('Source file set changed; run scripts/verify.py first.')
for name,digest in v['source_sha256'].items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
  raise SystemExit('Stale verification for '+name+'; run scripts/verify.py first.')
files=[root/'WeightedObstructionNorms.lean',root/'lakefile.toml',root/'lake-manifest.json',root/'lean-toolchain',root/'docs/LEAN.md',root/'docs/FORMALIZATION_STATUS.md']
files+=sorted((root/'WeightedObstructionNorms').glob('*.lean'))
files+=sorted((root/'scripts').glob('*.py'))
files+=sorted((root/'paper').glob('*.tex'))
files += [audit/name for name in ['paper_coverage.json','CheckAxioms.lean','axioms.log','build.log','verification.json','environment.md','lean_proc_compat.c','mathlib-lake-manifest.json']]
files+=sorted((audit/'history').glob('*.json'))
files+=sorted((root/'docs/history/revisions').glob('REVISION_*.md'))
hashes=[{'path':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
m=json.loads((audit/'computation-manifest.json').read_text())
m['claim_id']='weighted-obstruction-norms-complete-lean-formalization'
m['residual_risks']=['The source-to-manuscript correspondence is documented in paper_coverage.json and docs/FORMALIZATION_STATUS.md; kernel checking validates the stated Lean propositions.','The documented runtime compatibility helper affects only executable-path discovery; ordinary-environment rechecking is available through the pinned toolchain.']
m['command']='python3 scripts/verify.py (runtime environment: audit/environment.md)'
m['run']={'started_at':v['started_at'],'runtime_seconds':v['runtime_seconds'],'exit_status':0}
m['mathematics']['assertion_tested']=f"All {v['named_theorems_checked']} named theorem/lemma declarations and {len(v['additional_declarations_checked'])} additional key definitions compile and use only permitted standard axioms. Coverage: all fourteen numbered mathematical results, including Appendix A.1 and actual binary examples."
m['mathematics']['bounds']['named_declarations']=v['named_theorems_checked']
m['mathematics']['inputs']=[p for p in hashes if p['path'].endswith(('.lean','.tex'))]
m['mathematics']['non_claims']=['Prose motivation, literature attribution, applications, and open future directions are not encoded as proved propositions.','The formalization uses the fixed Lean/mathlib versions recorded in verification.json and standard classical axioms; it does not claim an independently implemented foundational kernel or executable numerical optimizer.']
m['outputs']=hashes
m['checks']=['lake build succeeded',f"Axiom audit covers all {v['named_theorems_checked']} named theorem/lemma declarations",'No sorry, admit, custom axiom, unsafe, or native_decide in implementation','Transitive axiom dependencies restricted to propext, Classical.choice, Quot.sound','Packaged proof source hashes match the final verification record']
m['result']='Kernel-checked completed mathematical formalization of all fourteen numbered results, including Appendix A.1 and both actual binary Cech examples. The diagonal dimension and relative connecting kernel are now linked to the general frontend. See paper_coverage.json and verification.json for exact scope and evidence.'

(audit/'computation-manifest.json').write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n')
files.append(audit/'computation-manifest.json')
dst=root.parent/'weighted_obstruction_norms_lean.zip'
with zipfile.ZipFile(dst,'w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,Path(root.name)/p.relative_to(root))
print(f'{dst}: {dst.stat().st_size} bytes, {len(files)} files')
