// Small finite illustrations. The general theorem is proved in Lean.
export function choose(n,k){if(k<0||k>n)return 0;let v=1;for(let i=1;i<=k;i++)v=v*(n-i+1)/i;return v;}
export function subsets(m,d){return Array.from({length:1<<m},(_,mask)=>Array.from({length:m},(_,i)=>i).filter(i=>mask>>i&1)).filter(s=>s.length===d);}
export function matchingDistribution(m,C,degrees,algorithm){
  let states=new Map([[Array(m).fill(0).join(','),1]]);
  for(const d of degrees){const next=new Map(), neighborhoods=subsets(m,d);
    for(const [key,mass] of states){const load=key.split(',').map(Number);
      for(const set of neighborhoods){const available=set.filter(i=>load[i]<C);
        const outcomes=available.length?(algorithm==='rv'?available:[available[0]]):[-1];
        for(const bin of outcomes){const x=[...load];if(bin>=0)x[bin]++;const k=x.join(',');next.set(k,(next.get(k)||0)+mass/neighborhoods.length/outcomes.length);}
      }
    }states=next;
  }
  const result=Array(Math.min(m*C,degrees.length)+1).fill(0);
  for(const [key,mass] of states)result[key.split(',').map(Number).reduce((a,b)=>a+b,0)]+=mass;
  return result;
}
export const tails = dist => dist.map((_,i)=>dist.slice(i).reduce((a,b)=>a+b,0));
export function pairCoefficients(strength){
  const rows=Array.from({length:4},(_,j)=>{let u=.5+.45*strength*(j+1)/4;return [u,1-u];});
  let c=[1];for(const [u,v] of rows){let a=Array(c.length+1).fill(0);c.forEach((x,i)=>{a[i]+=x*v;a[i+1]+=x*u;});c=a;}
  let g=c.map((v,k)=>v/choose(4,k)), delta=g.slice(1).map((v,i)=>v-g[i]), second=delta.slice(1).map((v,i)=>v-delta[i]);
  return {rows,g,delta,second};
}
export function categoricalLoads(rows,b){let states=new Map([[Array(b).fill(0).join(','),1]]);
  for(const row of rows){let next=new Map();for(const [key,mass] of states){let x=key.split(',').map(Number);row.forEach((p,i)=>{let y=[...x];y[i]++;let k=y.join(',');next.set(k,(next.get(k)||0)+mass*p);});}states=next;}
  return [...states].map(([key,p])=>({x:key.split(',').map(Number),p}));
}
export function cappedLaw(strength,q=3){
  const rows=Array.from({length:4},(_,j)=>{let a=strength*(j+1)/4;return [(1+a)/3,1/3,(1-a)/3];});
  const condition=rows=>{let items=categoricalLoads(rows,3).filter(e=>Math.max(...e.x)<=q),z=items.reduce((a,e)=>a+e.p,0);return {z,items:items.map(e=>({...e,p:e.p/z}))};};
  const ordered=condition(rows),uniform=condition(Array.from({length:4},()=>[1/3,1/3,1/3]));
  const groups=new Map();for(const e of uniform.items){let k=[...e.x].sort((a,b)=>b-a).join(',');if(!groups.has(k))groups.set(k,{x:k.split(',').map(Number),mu:0,nu:0});groups.get(k).mu+=e.p;}
  for(const e of ordered.items)groups.get([...e.x].sort((a,b)=>b-a).join(',')).nu+=e.p;
  let grouped=[...groups.values()].sort((a,b)=>b.x[0]-a.x[0]||b.x[1]-a.x[1]).map(g=>({...g,L:g.nu/g.mu,F:g.x.reduce((a,x)=>a+x*x,0),B:g.x.filter(x=>x===q).length}));
  const boundary=law=>Array.from({length:3},(_,i)=>law.items.reduce((a,e)=>a+(e.x[i]===q?e.p:0),0));
  const expected=(law,F)=>law.items.reduce((a,e)=>a+e.p*F(e.x),0);
  return {rows,groups:grouped,boundary:boundary(ordered),uniformBoundary:boundary(uniform),capProbability:ordered.z,
    meanUniform:expected(uniform,x=>x.reduce((a,v)=>a+v*v,0)),meanOrdered:expected(ordered,x=>x.reduce((a,v)=>a+v*v,0))};
}
export function waitingLaw(m,a,start,degrees){let survival=1,atoms=[];for(let j=start;j<degrees.length;j++){const f=choose(a,degrees[j])/choose(m,degrees[j]);atoms.push({time:j+1,p:survival*(1-f)});survival*=f;}atoms.push({time:Infinity,p:survival});return atoms;}
export function quantile(atoms,u){let s=0;for(const atom of atoms){s+=atom.p;if(u<s-1e-12)return atom.time;}return atoms.at(-1).time;}
export function referenceHazard(b,q,r){const items=categoricalLoads(Array.from({length:r},()=>Array(b).fill(1/b)),b).filter(e=>Math.max(...e.x)<=q);let z=items.reduce((a,e)=>a+e.p,0);return items.reduce((a,e)=>a+e.p*e.x.filter(x=>x===q).length/b,0)/z;}
export function refinement(choices){const history=[choices[0],0,choices[1],0,choices[2],0],loads=[0,0,0],available=[];for(const x of history){available.push(loads.map((v,i)=>v<3?i:null).filter(v=>v!==null));loads[x]++;}return {history,loads,available,valid:loads[0]===3&&loads[1]<3&&loads[2]<3};}
