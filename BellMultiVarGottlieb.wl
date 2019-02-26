BeginPackage["BellMultiVarGottlieb`"]

LagrangeSolve2D::usage = "LagrangeSolve2D[f,g,{x,y}] returns maximum and minimum values of f(x,y) on the constraint curve g(x,y)=0";
LagrangeSolve3D::usage = "LagrangeSolve3D[f,g,{x,y,z}] returns maximum and minimum values of f(x,y,z) on the constraint curve g(x,y,z)=0";
DiscrimFunc::usage="DiscrimFunc[f,a,b,{x,y}] returns the discriminant, D, from the second partial test of function f(x,y) at (a,b)";
CriticalPoints2D::usage="CricticalPoints2D[f,{x,y}] returns the critical points of f(x,y) with the discriminant, D, from the second partial test and fxx at each point";
DoubleIntegrate::usage="DoubleIntegrate[f,{a,aLower,aUpper},{b,bLower,bUpper}] returns the double integratl of f, 1st integrating over a from aLower to aUpper and then integrating over b from bLower to bUpper";
J::usage="J[{x,y},{u,v}] returns the Jacobian of x[u,v] and y[u,v]";
J2::usage="DEPRICATED J2[{u,v},{x,y}] returns the Jacobian of x[u,v] and y[u,v] when given u[x,y] and v[x,y]";
JU::usage="JU[{u,v},{x,y}] returns the Jacobian of x[u,v] and y[u,v] when given u[x,y] and v[x,y]";
J3::usage="J3[{x,y,z},{u,v,w}] returns the Jacobian of x[u,v,w], y[u,v,w], z[u,v,w]";
VFLineIntegrate2D::usage="VFLineIntegrate2D[{Fx,Fy},{rx,ry},{t,tlower,tupper}] returns the line integral of {Fx(t),Fy(t)} along {rx(t),ry(t)} with t going from tlower to tupper";
VFLineIntegrate3D::usage="VFLineIntegrate3D[{Fx,Fy,Fz},{rx,ry,rz},{t,tlower,tupper}] returns the line integral of {Fx(t),Fy(t),Fz(t)} along {rx(t),ry(t),rz(t)} with t going from tlower to tupper";
GreenInt::usage="GreenInt[{Fx, Fy},{xb, xlower ,xupper},{yb, ylower, yupper}, x, y] returns the closed path line integrat of {Fx,Fy}, taken over a region {x,xlower,xupper} (x here is the variable that will be integrated first) by {y,ylower,yupper} with the last two variables being x and y in order";
SurfaceIntegrate::usage="SurfaceIntegrate[F_,{rx_,ry_,rz_},{x_,y_,z_},{u_,ulower_,uupper_},{v_,vlower_,vupper_}] returns the surface integral of F(rx(u,v),ry(u,v),rz(u,v)) where F(x,y,z) and {rx(u,v),ry(u,v),rz(u,v)} which parametricies sigma with u bounds ulower to uupper and v bounds vlower to vupper";
SurfaceIntegrateCP::usage="SurfaceIntegrateCP[F_,cp_,{rx_,ry_,rz_},{x_,y_,z_},{u_,ulower_,uupper_},{v_,vlower_,vupper_}] returns the surface integral of F(rx(u,v),ry(u,v),rz(u,v)) where F(x,y,z), cp=Norm[Cross[drdu,drdv]], and {rx(u,v),ry(u,v),rz(u,v)} which parametricies sigma with u bounds ulower to uupper and v bounds vlower to vupper";

TripInt::usage="TripInt[f_, {a_, aLower_,aUpper_},{b_,bLower_,bUpper_},{c_,cLower_,cUpper_}] return the triple integrals of f with respect to a from aLower to aUpper, then b, then c"

Begin["`Private`"]

SetAttributes[LagrangeSolve2D, HoldAll];
LagrangeSolve2D[f_, g_, {x_, y_}] := 
 Module[{localF,localG,localX,localY,\[Lambda],s,n,p},
   localX=x;
   localY=y;
   localF=f;
  localG=g;
  s= NSolve[D[localF,localX]==\[Lambda]*D[localG,localX]&&D[localF,localY]==\[Lambda]*D[localG,localY]&&localG==0,{localX, localY,\[Lambda]}];
  n={localX,localY}/.s;
  p=(localF/.{localX->n[[#]][[1]],localY->n[[#]][[2]]})&/@Range[Length[n]];
  {Max[p],Min[p]}
  ]
  
SetAttributes[LagrangeSolve3D, HoldAll];
LagrangeSolve3D[f_, g_, {x_, y_,z_}] := 
 Module[{localF,localG,localX,localY,localZ,\[Lambda],s,n,p},
   localX=x;
   localY=y;
  localZ=z; 
   localF=f;
  localG=g;
  s= NSolve[D[localF,localX]==\[Lambda]*D[localG,localX]&&D[localF,localY]==\[Lambda]*D[localG,localY]&&D[localF,localZ]==\[Lambda]*D[localG,localZ]&&localG==0,{localX, localY,localZ,\[Lambda]}];
  n={localX,localY,localZ}/.s;
  p=(localF/.{localX->n[[#]][[1]],localY->n[[#]][[2]],localZ->n[[#]][[3]]})&/@Range[Length[n]];
  {Max[p],Min[p]}
  ]

SetAttributes[DiscrimFunc,HoldAll];
DiscrimFunc[f_,a_,b_,{x_,y_}]:=
Module[{localX,localY,localF, cp,s,n,ans,discrim,discrimFunction},
localX=x;
localY=y;
localF=f;
(D[localF,localX,localX]*D[localF,localY,localY]-(D[localF,localX,localY])^2)/.{localX->a,localY->b}
]

SetAttributes[CriticalPoints2D,HoldAll];
CriticalPoints2D[f_,{x_,y_}]:=
 Module[{localX,localY,localF, cp,s,n,ans,discrim,discrimFunction,fxx,point,a,b},
 localX=x;
 localY=y;
 localF=f;
 s=NSolve[D[localF,localX]==0&& D[localF,localY]==0,{localX,localY}];
 n={localX,localY}/.s;
 discrim=(DiscrimFunc[localF,a,b,{localX,localY}]/.{a->n[[#]][[1]],b->n[[#]][[2]]})&/@Range[Length[n]];
 fxx=(D[localF,localX,localX]/.{localX->n[[#]][[1]],localY->n[[#]][[2]]})&/@Range[Length[n]];
 ans=({{localX,localY},discrim,fxx}/.{localX->n[[#]][[1]],localY->n[[#]][[2]],discrim->discrim[[#]],fxx->fxx[[#]]})&/@Range[Length[n]]
 ]
 
SetAttributes[DoubleIntegrate, HoldAll];
DoubleIntegrate[f_, {a_, aLower_,aUpper_},{b_,bLower_,bUpper_}] := 
 Module[{localF,localA,localALower,localAUpper,localB,localBLower,localBUpper,int1,int2}, 
   localF=f;
  localA=a;
  localALower=aLower;
  localAUpper=aUpper;
  localB=b;
  localBLower=bLower;
  localBUpper=bUpper;
  int1=Integrate[localF,localA];
  int1=(int1/.localA->localAUpper)-(int1/.localA->localALower);
  int2=Integrate[int1,localB];
  (int2/.localB->localBUpper)-(int2/.localB->localBLower)
  ]

SetAttributes[J, HoldAll];
J[{x_,y_},{u_,v_}]:=
Module[{localX,localY,localU,localV},
localX=x;
localY=y;
localU=u;
localV=v;
Simplify[D[x,u]*D[y,v]-D[y,u]*D[x,v]]
]

SetAttributes[J2, HoldAll];
J2[{u1_,v1_},{x_,y_}]:=
Module[{localX,localY,localU,localV,solvedU,solvedV,s,n,u,v},
localX=x;
localY=y;
localU=u1;
localV=v1;
s=Solve[solvedU==localU&&solvedV==localV,{localX,localY}];
n={localX,localY}/.s;
D[n[[1]][[1]],solvedU]*D[n[[1]][[2]],solvedV]-D[n[[1]][[2]],solvedU]*D[n[[1]][[1]],solvedV]/.{solvedV->v,solvedU->u}
]

SetAttributes[JU, HoldAll];
JU[{u1_,v1_},{x_,y_}]:=
Module[{localX,localY,localU,localV,solvedU,solvedV,s,n,u,v},
localX=x;
localY=y;
localU=u1;
localV=v1;
s=Solve[solvedU==localU&&solvedV==localV,{localX,localY}];
n={localX,localY}/.s;
D[n[[1]][[1]],solvedU]*D[n[[1]][[2]],solvedV]-D[n[[1]][[2]],solvedU]*D[n[[1]][[1]],solvedV]/.{solvedV->v,solvedU->u}
]

SetAttributes[J3, HoldAll];
J3[{x_,y_,z_},{u_,v_,w_}]:=
Module[{localX,localY,localZ,localU,localV,localW},
localX=x;
localY=y;
localZ=z;
localU=u;
localV=v;
localW=w;
Simplify[Det[{{D[localX,localU],D[localX,localV],D[localX,localW]},{D[localY,localU],D[localY,localV],D[localY,localW]},{D[localZ,localU],D[localZ,localV],D[localZ,localW]}}]]
]

SetAttributes[VFLineIntegrate2D, HoldAll];
VFLineIntegrate2D[{Fx_,Fy_},{rx_,ry_},{t_,tlower_,tupper_}]:=
Module[{lFx,lFy,lrx,lry,lt,ltlower,ltupper,r,F,dr},
(*Create local copies, possibly*)
lFx=Fx;
lFy=Fy;
lrx=rx;
lry=ry;
lt=t;
ltlower=tlower;
ltupper=tupper;
(*Create vectors*)
F={lFx,lFy};
r={lrx,lry};
dr=D[r,lt];
(*Integrate*)
Integrate[Dot[F,dr],{lt,ltlower,ltupper}]
]

SetAttributes[VFLineIntegrate3D, HoldAll];
VFLineIntegrate3D[{Fx_,Fy_,Fz_},{rx_,ry_,rz_},{t_,tlower_,tupper_}]:=
Module[{lFx,lFy,lFz,lrx,lry,lrz,lt,ltlower,ltupper,r,F,dr},
(*Create local copies, possibly*)
lFx=Fx;
lFy=Fy;
lFz=Fz;
lrx=rx;
lry=ry;
lrz=rz;
lt=t;
ltlower=tlower;
ltupper=tupper;
(*Create vectors*)
F={lFx,lFy,lFz};
r={lrx,lry,lrz};
dr=D[r,lt];
(*Integrate*)
Integrate[Dot[F,dr],{lt,ltlower,ltupper}]
]

SetAttributes[GreenInt, HoldAll];
GreenInt[{Fx_,Fy_},{xb_,xlower_,xupper_},{yb_,ylower_,yupper_},x_,y_]:=
Module[{lFx,lFy,lxb,lxlower,lxupper,lyb,lylower,lyupper,integrand,lx,ly},
(*Create local copies*)
lFx=Fx;
lFy=Fy;
lxb=xb;
lxlower=xlower;
lxupper=xupper;
lyb=yb;
lylower=ylower;
lyupper=yupper;
lx=x;
ly=y;
(*Create integrand*)
integrand = D[lFy,lx]-D[lFx,ly];
(*Integrate*)
Integrate[Integrate[integrand,{lxb,lxlower,lxupper}],{lyb,lylower,lyupper}]
]

SetAttributes[SurfaceIntegrate, HoldAll];
SurfaceIntegrate[F_,{rx_,ry_,rz_},{x_,y_,z_},{u_,ulower_,uupper_},{v_,vlower_,vupper_}]:=
Module[{lF,lrx,lry,lrz,lx,ly,lz,lu,lulower,luupper,lv,lvlower,lvupper,r,drdu,drdv,newF},
(*Create local copies, possibly*)
lF=F;
lrx=rx;
lry=ry;
lrz=rz;
lx=x;
ly=y;
lz=z;
lu=u;
lulower=ulower;
luupper=uupper;
lv=v;
lvlower=vlower;
lvupper=vupper;
(*Create vectors*)
r={lrx,lry,lrz};
drdu=D[r,lu];
drdv=D[r,lv];
(*Create f(x(u,v),y(u,v),z(u,v))*)
newF=Simplify[lF/.{lx->lrx,ly->lry,lz->lrz},Element[{lrx,lry,lrz},Reals]];
(*Integrate*)
Simplify[Integrate[Integrate[Simplify[newF*Norm[Cross[drdu,drdv]],Element[{drdu,drdv,lu,lulower,luupper,lv,lvlower,lvupper},Reals]],{lu,lulower,luupper}],{lv,lvlower,lvupper}],Element[{drdu,drdv,lu,lulower,luupper,lv,lvlower,lvupper},Reals]]
]

SetAttributes[SurfaceIntegrateCP, HoldAll];
SurfaceIntegrateCP[F_,cp_,{rx_,ry_,rz_},{x_,y_,z_},{u_,ulower_,uupper_},{v_,vlower_,vupper_}]:=
Module[{lF,lcp,lrx,lry,lrz,lx,ly,lz,lu,lulower,luupper,lv,lvlower,lvupper,r,drdu,drdv,newF},
(*Create local copies, possibly*)
lF=F;
lcp=cp;
lrx=rx;
lry=ry;
lrz=rz;
lx=x;
ly=y;
lz=z;
lu=u;
lulower=ulower;
luupper=uupper;
lv=v;
lvlower=vlower;
lvupper=vupper;
(*Create f(x(u,v),y(u,v),z(u,v))*)
newF=Simplify[lF/.{lx->lrx,ly->lry,lz->lrz}];
(*Integrate*)
Integrate[Integrate[Simplify[newF*lcp],{lu,lulower,luupper}],{lv,lvlower,lvupper}]
]

SetAttributes[TripInt, HoldAll];
TripInt[f_, {a_, aLower_,aUpper_},{b_,bLower_,bUpper_},{c_,cLower_,cUpper_}] := 
 Module[{localF,localA,localALower,localAUpper,localB,localBLower,localBUpper,localC,localCLower,localCUpper, int1,int2}, 
 localF=f;
 localA=a;
 localALower=aLower;
 localAUpper=aUpper;
 localB=b;
 localBLower=bLower;
 localBUpper=bUpper;
 localC=c;
 localCLower=cLower;
 localCUpper=cUpper;
 Simplify[Integrate[Integrate[Integrate[Simplify[localF,Element[{localA,localB,localC},Reals]],{localA, localALower,localAUpper}],{localB, localBLower,localBUpper}],{localC, localCLower,localCUpper}],Element[{localA,localB,localC},Reals]]
]

End[]
EndPackage[]