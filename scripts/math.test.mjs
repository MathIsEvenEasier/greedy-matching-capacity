import test from 'node:test';
import assert from 'node:assert/strict';
import {matchingDistribution,tails,pairCoefficients,cappedLaw,waitingLaw,quantile,refinement,referenceHazard} from '../docs/math.mjs';
const close=(a,b)=>assert.ok(Math.abs(a-b)<1e-10,`${a} != ${b}`);
test('one job and no jobs have the expected matching laws',()=>{
 for(const alg of ['rv','rk']){assert.deepEqual(matchingDistribution(3,2,[],alg),[1]);assert.deepEqual(matchingDistribution(3,2,[0],alg),[1,0]);close(matchingDistribution(3,2,[2],alg)[1],1);}
});
test('degree-one jobs agree, and full neighborhoods fill all available slots',()=>{
 for(const C of [1,2,3]){
  const r=matchingDistribution(3,C,[1,1,1,1,1,1,1],'rv'),k=matchingDistribution(3,C,[1,1,1,1,1,1,1],'rk');r.forEach((p,i)=>close(p,k[i]));
  for(const alg of ['rv','rk'])close(matchingDistribution(3,C,Array(10).fill(3),alg)[3*C],1);
 }
});
test('displayed instances normalize and have ordered tails; capacity one gives equality',()=>{
 for(const [C,degrees] of [[1,[2,1,2,1]],[2,[2,2,2,1,2,1,2]],[3,[2,2,1,2,2,1,2,2,1,2]]]){
  const r=matchingDistribution(3,C,degrees,'rv'),k=matchingDistribution(3,C,degrees,'rk');close(r.reduce((a,b)=>a+b),1);close(k.reduce((a,b)=>a+b),1);
  tails(r).forEach((p,i)=>{assert.ok(p+1e-10>=tails(k)[i]);if(C===1)close(p,tails(k)[i]);});
 }
});
test('normalized pair coefficients agree with the identical unbiased row formula',()=>{
 pairCoefficients(0).g.forEach(x=>close(x,1/16));
 for(const a of [0,.4,1]){const p=pairCoefficients(a);assert.ok(p.delta.every(x=>x>=-1e-12));assert.ok(p.second.every(x=>x>=-1e-12));}
});
test('capped baseline masses are known factorial weights',()=>{
 const p=cappedLaw(0,3);close(p.capProbability,78/81);
 const groups=new Map(p.groups.map(g=>[g.x.join(','),g]));close(groups.get('3,1,0').mu,4/13);close(groups.get('2,2,0').mu,3/13);close(groups.get('2,1,1').mu,6/13);
 p.groups.forEach(g=>close(g.L,1));
 for(const q of [2,3])for(const a of [0,.5,.95]){const z=cappedLaw(a,q);close(z.groups.reduce((s,g)=>s+g.mu*g.L,0),1);assert.ok(z.meanOrdered+1e-10>=z.meanUniform);assert.ok(z.boundary[0]+1e-10>=z.boundary[1]&&z.boundary[1]+1e-10>=z.boundary[2]);}
});
test('the history fiber has exactly six compatible assignments',()=>{
 let count=0;for(const a of [1,2])for(const b of [1,2])for(const c of [1,2]){const r=refinement([a,b,c]);if(r.valid){count++;assert.ok(r.available.every(x=>x.length===3));}else assert.equal(r.available.at(-1).length,2);}
 assert.equal(count,6);
});
test('waiting quantiles order finite hits and correctly preserve a never-hit atom',()=>{
 const d=Array.from({length:12},(_,i)=>i%2?2:1),rv=waitingLaw(4,1,6,d);
 for(const a of [1,2]){const rk=waitingLaw(4,a,8,d);close(rk.reduce((s,e)=>s+e.p,0),1);for(const u of [0,.2,.58,.99,.9999])assert.ok(quantile(rv,u)<=quantile(rk,u));}
 const never=waitingLaw(3,2,0,[0,0]);close(never.at(-1).p,1);assert.equal(quantile(never,.5),Infinity);
 // Of the 24 capped assignments, 18 have shape (2,1,0); the next
 // uniform choice hits their unique boundary bin with probability 1/3.
 close(referenceHazard(3,2,3),(18/24)/3);
});
