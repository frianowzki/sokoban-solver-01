import F from'fs';
const I=process.env.MAKEFUN_INPUT_DIR,O=process.env.MAKEFUN_OUTPUT_DIR;
let E,w,T,P;
const G=c=>T[c]>41&&T[c]<47;
for(let d of F.readdirSync(I)){
let b=F.readFileSync(I+'/'+d+'/level.txt');
w=b.indexOf(10);E=[-w,w,-1,1];T=b.filter(c=>c-10);P=T.findIndex(c=>c&64|c==43);
let H=P/w|0,u=P,m='';
for(let r of[H-1,H+1])for(let D=r*w;D<r*w+w;D++)if(T[D]-35){
let v=D+(H-r)*w;
let R=c=>c==v||T[c]-35&&((c/w|0)-H)*(r-H)>0&&(c%w/7|0)==(D%w/7|0);
let B=[...T.keys()].filter(j=>R(j)&&T[j]%6<1);
let x=(()=>{let V={[B+'|'+v]:0},Q=[[[B,v,'']]],c=0;
while(c<Q.length){for(let S of Q[c]){let[b,p,g]=S;
if(p==D&&b.every(G))return g;
for(let j=4;j--;){let t=p+E[j];
if(!R(t))continue;
let nb=b,nc=c;
if(b.includes(t)){let z=t+E[j];
if(!R(z)||b.includes(z))continue;
nb=b.map(x=>x==t?z:x).sort();nc++;
if(!G(z)&&!E.some(f=>R(z+f)&R(z-f)))continue;}
let k=nb+'|'+t;
if(V[k]<=nc)continue;
V[k]=nc;(Q[nc]??=[]).push([nb,t,g+'udlr'[j]]);}}
c++}})();
m+=(v>u?'r':'l').repeat(Math.abs(v-u));
m+=x+(D<v?'d':'u');u=v;}
F.mkdirSync(O+'/'+d,{recursive:true});F.writeFileSync(O+'/'+d+'/solution.txt',m)}
