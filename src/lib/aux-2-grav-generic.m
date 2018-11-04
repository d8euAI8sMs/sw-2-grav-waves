(* ::Package:: *)

(* ::Section::Closed:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Input::Initialization:: *)
If[$FrontEnd =!= Null, AppendTo[$Path, FileNameJoin[{NotebookDirectory[], "../../lib/mathematica"}]]];

(Once@Get[#] &) /@ { "Formal.m", "Features.m", "Ricci_grav.m" };


(* ::Input::Initialization:: *)
EnableFeature[{Formatter[DD],Formatter[Tensor]}];


(* ::Section:: *)
(*\:0412\:0441\:043f\:043e\:043c\:043e\:0433\:0430\:0442\:0435\:043b\:044c\:043d\:044b\:0435 \:0444\:0443\:043d\:043a\:0446\:0438\:0438*)


(* ::Subsection::Closed:: *)
(*\:0412\:0441\:043f\:043e\:043c\:043e\:0433\:0430\:0442\:0435\:043b\:044c\:043d\:044b\:0435 \:043e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


(* ::Input::Initialization:: *)
coords:=Array[x,4,{0,3}];

tm=Tensor[\[Gamma],0,2];
th=Tensor[h,0,2];
td=TensorDelta[];
tV=Tensor[V,0,1];
tE=Tensor[\[CapitalEpsilon],0,2];
tB=Tensor[\[CapitalBeta],1,1];
tq=Tensor[q,0,1];
tlc=TensorLeviCivita3[];
tmd=HoldForm[Evaluate[Sqrt[TensorSymbol[tm]]]];

\[Eth]t[e_]:=\[Eth][e,Cov[0]];
\[Eth][Tensor[TensorSymbol[tm],d__][a__],Cov[i_],___]:=0;
\[Eth][Tensor[TensorSymbol[td],d__][a__],__]:=0;

Val[tE[i_,j_]]:=\[Eth]t[th[i,j]]+\[Eth][tV[i],Cov[j]]+\[Eth][tV[j],Cov[i]];
Val[td[i_,j_]]:=TensorDeltaValue[i,j];
Val[tlc[i_,j_,k_]]:=TensorLeviCivita3Value[i,j,k];
Val[tq[i_]]:=USum[\[Eth][th[i,j],Cov[j]]-\[Eth][th[j,j],Cov[i]],j];
Val[tB[i_,j_]]:=sr[th][i,j];

Val[tm[i_,j_]]:=gg[i,j];
Val[TensorContr[tm][i_,j_]]:=hh[i,j];
Val[tmd]:= gd;

Sym[x:th[i_,j_]]:=th[j,i]/;i>j;
Sym[x:th[__]]:=x;
Sym[x:tE[i_,j_]]:=tE[j,i]/;i>j;
Sym[x:tE[__]]:=x;
Sym[x:\[Eth][a_,i_,j_]]:=\[Eth][a,j,i]/;TrueQ[i>j];
Sym[x:\[Eth][a_,__]]:=x;

br[x_][i_,j_]:=TensorBr[x][i,j]//.SSum2SumRules[{#,1,3}&]//.{z:tlc[__]:>Val[z]}//Simplify;
sr[x_][i_,j_]:=TensorSr[x][i,j]//.SSum2SumRules[{#,1,3}&]//.{z:tlc[__]:>Val[z]}//Simplify;
div[v_]:=USum[\[Eth][TensorContr[tm][i,j]v[j],Cov[i]],i,j];
lap[v_][k_]:=USum[TensorContr[tm][i,j]\[Eth][v[k],Cov[i],Cov[j]],i,j];


(* ::Subsection::Closed:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f, \:0437\:0430\:0432\:0438\:0441\:044f\:0449\:0438\:0435 \:043e\:0442 \:0441\:0438\:0441\:0442\:0435\:043c\:044b \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442*)


RecalculateGrav[]:=Module[{},
	lagr2s=USum[tmd TensorContr[tm][i,j]TensorContr[tm][k,l](tE[i,k]tE[j,l]-tE[i,j]tE[k,l]),i,j,k,l]/4-USum[tB[i,j]tB[j,i]/tmd,i,j]/4//Tensorify//TensorBeautify;
	lagr2n=lagr2s//.SSum2SumRules[{#,3}&]//.{x:TensorContr[tm][__]:>Val[x],x:tE[__]:>Sym[x]}//Simplify;
	lagr2n=lagr2n//.{x:tB[__]|tE[__]:>Val[x]}//.{y:th[a__]:>Sym[y]}//ExpandAll;

	Us=-1/8USum[TensorSr[th][i,j]TensorSr[th][j,i],i,j]//Tensorify//TensorBeautify;
	Un=-1/8Sum[sr[th][i,j]sr[th][j,i],{i,3},{j,3}]//.{y:th[a__]:>Sym[y]}//ExpandAll//Simplify//Expand;

	epss=\[Eth][lagr2s,tE[\[Alpha],\[Beta]]]//.{\[Eth][tB[a__]|tmd|1/tmd|TensorContr[tm][a__],b__]:>0,\[Eth][tE[i_,j_],tE[k_,l_]]:>td[i,k]td[j,l]}//Tensorify//TensorSimplify//Tensorify//TensorBeautify;
	epss=TensorMap[SSum[epss tE[\[Alpha],\[Beta]],\[Alpha],\[Beta]]-lagr2s//Tensorify,TensorTopoSortMapper]//Tensorify//TensorBeautify;
	epsn=epss//.SSum2SumRules[{#,1,3}&]//.{x:td[__]|tE[__]|tB[__]|TensorContr[tm][__]|tq[__]:>Val[x]}/.{tV[_]:>0}//.SSum2SumRules[{#,1,3}&]//.{y:th[a__]:>Sym[y]}//Simplify//ExpandAll;

	Uis=\[Eth][lagr2s,\[Eth][th[\[Alpha],\[Beta]],Cov[\[Iota]]]]//.{\[Eth][tE[a__]|tmd|1/tmd|TensorContr[tm][a__],b__]:>0,\[Eth][tB[i_,j_],\[Eth][th[k_,l_],Cov[m_]]]:>TensorLeviCivita3[][i,l,m]td[k,j]}//Tensorify//TensorSimplify//Tensorify//TensorBeautify;
	Uis=TensorMap[SSum[Uis tE[\[Alpha],\[Beta]],\[Alpha],\[Beta]]//Tensorify,TensorTopoSortMapper[{TensorTopoSortDDSymSource,(If[!MatchQ[#,TensorLeviCivita3[][__]],TensorTopoSortTensorSymSource[#],{}]&)}]]//Tensorify//TensorBeautify;

	Uin=Table[Uis//.SSum2SumRules[{#,1,3}&]//.{x:td[__]|tE[__]|tB[__]|TensorContr[tm][__]|tq[__]|tlc[ijk__]:>Val[x]}/.{tV[_]:>0}//.SSum2SumRules[{#,1,3}&]//.{y:th[a__]:>Sym[y]}//Simplify//ExpandAll,{\[Iota],3}]/.{tV[_]:>0}//ExpandAll;
	
	lagr2n=(lagr2n//CovExpand)//.SSum2SumRules[{#,0,3}&]//.{TensorChristoffel[][a__]:>cs2[a],tmd:>Val[tmd],tV[__]:>0};
	epsn=(epsn//CovExpand)//.SSum2SumRules[{#,0,3}&]//.{TensorChristoffel[][a__]:>cs2[a],tmd:>Val[tmd],tV[__]:>0};
	Uin=(Uin//CovExpand)//.SSum2SumRules[{#,0,3}&]//.{TensorChristoffel[][a__]:>cs2[a],tmd:>Val[tmd],tV[__]:>0};
	Un=(Un//CovExpand)//.SSum2SumRules[{#,0,3}&]//.{TensorChristoffel[][a__]:>cs2[a],tmd:>Val[tmd],tV[__]:>0};
	
	{lagr2s,Us,epss,Uis}
];


(* ::Subsection::Closed:: *)
(*\:0423\:0442\:0438\:043b\:0438\:0442\:044b*)


EvaluateAt[e_,r_]:=(e//.r)//.DD2DRules[coords];
EvaluateAt[r_]:=(EvaluateAt[#,r]&);
