(* ::Package:: *)

BeginPackage["ML`"]


(* These manage datasets *)


GetClass[sample[class_,vec_]]:=class


GetVec[sample[class_,vec_]]:=vec


MapVecs[f_,data_]:=
	(s\[Function]sample[GetClass[s],f[GetVec[s]]])/@data


ParallelMapVecs[f_,data_]:=
	ParallelMap[s\[Function]sample[GetClass[s],f[GetVec[s]]],data]


MapClasses[f_,data_]:=
	(s\[Function]sample[f[GetClass[s]],GetVec[s]])/@data


AllClasses[data_]:=
	DeleteDuplicates[GetClass/@data]


SelectClass[data_,class_]:=
	Select[data,s\[Function]GetClass[s]==class]


TallyClasses[data_]:=
	With[{cs=(i\[Function]GetClass[i[[1]]]->i[[2]])/@Tally[data,{x,y}\[Function]First[x]==First[y]]},
		Range[Max[First/@cs]]/.Append[cs,_Integer->{}]]


ClassMatrix[data_,class_]:=
	GetVec/@SelectClass[data,class]


FullMatrix[data_]:=GetVec/@data


GatherData[data_]:=
	With[{r=(s\[Function]GetClass[First[s]]->s)/@GatherBy[data,GetClass]},
	Range[Max[First/@r]]/.Append[r,_Integer->{}]]


ClassesFromGathered[gdata_]:=
	Range[Length[gdata]];


(* For clearing empty rows *)


RemoveZeros[data_]:=
	Module[{variances,d},
	variances=Variance[FullMatrix[data]];
	d=Length[variances];
	Select[
		(i\[Function]If[PossibleZeroQ[variances[[i]]],
				Null,
				PadRight[Normal[SparseArray[{i->1.0}]],d]])/@Range[d],
		VectorQ]]
	


(* A PCA Package *)


MakePCA[data_,n_]:=
	Module[{vals,vecs},
	{vals,vecs}=Eigensystem[data//FullMatrix//Covariance,n];
	{vecs,vals}]


(* An LDA Package *)


OuterDifference[l_,r_]:=
	With[{dif=l-r},
	Outer[Times,dif,dif]]


Scatter[classdata_,classmean_]:=
	Plus@@((x\[Function]OuterDifference[x,classmean])/@classdata)


MakeLDAMatrix[data_,n_]:=
	Module[{classdata,classcounts,classmeans,withinclass,full,fullmean,betweenclass},
	classdata=FullMatrix/@GatherData[data];
	classcounts=Length/@classdata;
	classmeans=Mean/@classdata;
	withinclass=Plus@@MapThread[Scatter,{classdata,classmeans}];
	full=FullMatrix[data];
	fullmean=Mean[full];
	betweenclass=Plus@@MapThread[{cm,cc}\[Function]cc*OuterDifference[cm,fullmean],
					{classmeans,classcounts}];
	Eigensystem[PseudoInverse[withinclass].betweenclass,n]]


MakeLDA[data_,n_]:=
	Module[{vals,matrix},
	{vals,matrix}=MakeLDAMatrix[data,n];
	{matrix,
	 vals}]


(* A Multivariate Normal Classifier *)


MultiVariateNormalClassifier[data_]:=
	Module[{n,gathered,classes,classdata,pcs,ms,ss,ssi,dss,wms,wvs,wss,fns},
	n=Length[data];
	gathered=GatherData[data];
	classes=ClassesFromGathered[gathered];
	classdata=FullMatrix/@gathered;
	pcs=N[(d\[Function]Length[d]/n)/@classdata];
	ms=Mean/@classdata;
	ss=Covariance/@classdata;
	ssi=PseudoInverse/@ss;
	dss=Det/@ss;
	wms=(si\[Function]-.5*si)/@ssi;
	wvs=MapThread[Dot,{ssi,ms}];
	wss=MapThread[{si,d,m,p}\[Function]-.5*m.si.m-.5*Log[d]+Log[p],{ssi,dss,ms,pcs}];
	fns=MapThread[{wm,wv,ws}\[Function]x\[Function]x.wm.x+wv.x+ws,{wms,wvs,wss}];
	x\[Function]Ordering[Through[fns[x]],-1][[1]]]


MultiVariateNormalClassifierSingleCovariance[data_]:=
	Module[{n,cov,icov,gathered,classes,pcs,ms,wvs,wss,fns},
	n=Length[data];
	cov=Covariance[FullMatrix[data]];
	icov=PseudoInverse[cov];
	gathered=GatherData[data];
	classes=ClassesFromGathered[gathered];
	classdata=FullMatrix/@gathered;
	pcs=N[(d\[Function]Length[d]/n)/@classdata];
	ms=Mean/@classdata;
	wvs=(m\[Function]icov.m)/@ms;
	wss=MapThread[{m,pc}\[Function]-.5*m.icov.m+Log[pc],{ms,pcs}];
	fns=MapThread[{wv,ws}\[Function]x\[Function]wv.x+ws,{wvs,wss}];
	x\[Function]Ordering[Through[fns[x]],-1][[1]]]


(* A Decision Tree Package *)


RunningEntropy[countswithzeros_]:=
	Module[{counts,total},
	counts=Select[countswithzeros,Positive];
	total=Plus@@counts;
	Plus@@(x\[Function]N[-(x/total)*Log2[x/total]])/@counts]


BestOfDimension[data_,dim_]:=
	Module[{best,less,more,countsr,countsl,num,shifter,lentropy,rentropy,impurity},
	best={dim,Null,\[Infinity],Null,\[Infinity],\[Infinity]};
	less={};
	more=Sort[data,(OrderedQ[{GetVec[#1][[dim]],GetVec[#2][[dim]]}])&];
	countsr=TallyClasses[more];
	countsl=Table[0,{Length[countsr]}];
	num=Length[more];
	While[Length[more]>1,
		shifter=First[more];
		more=Drop[more,1];
		AppendTo[less,shifter];
		countsr[[GetClass[shifter]]]-=1;
		countsl[[GetClass[shifter]]]+=1;
		If[GetVec[shifter][[dim]]==GetVec[First[more]][[dim]]
				\[Or] GetClass[shifter]==GetClass[First[more]],
			Null,
			lentropy=RunningEntropy[countsl];
			rentropy=RunningEntropy[countsr];
			impurity=(Length[less]/num)*lentropy+(Length[more]/num)*rentropy;
			If[impurity<best[[6]],
				best={dim,less,lentropy,more,rentropy,impurity},
				Null]]];
	best]


splitFactor=50;
BestSplit[data_]:=
	With[{n=Length[data],dims=First[data]//GetVec//Length},
		With[{map=If[n*dims<splitFactor,Map,ParallelMap]},
			Fold[{next,best}\[Function]If[next[[6]]<best[[6]],next,best],
				{Null,Null,\[Infinity],Null,\[Infinity],\[Infinity]},
				map[d\[Function]BestOfDimension[data,d],Range[dims]]]]]


LeafOrBranch[data_,entropy_,maxentropy_]:=
	With[{n=Length[data],dims=First[data]//GetVec//Length},
		If[entropy<=maxentropy,
			leaf[Ordering[TallyClasses[data],-1][[1]]],
			If[n*dims<splitfactor,
				MakeTree[data,maxentropy],
				ParallelEvaluate[{data,maxentropy},MakeTree[data,maxentropy]]]]]

MakeTree[data_,maxentropy_]:=
	Module[{dim,less,lentropy,more,mentropy,impurity,
			lbranch,rbranch,val},
	{dim,less,lentropy,more,mentropy,impurity}=BestSplit[data];
	If[dim===Null,
		(* No split, we're a leaf *)
		leaf[Ordering[TallyClasses[data],-1][[1]]],
		(* Split Here *)
		lbranch=LeafOrBranch[less,lentropy,maxentropy];
		rbranch=LeafOrBranch[more,mentropy,maxentropy];
		val=(GetVec[less[[-1]]][[dim]] + GetVec[more[[1]]][[dim]]) / 2.0;
		branch[dim,val,lbranch,rbranch]]]


DistributeDefinitions[MakeTree];


TreeClassify[branch[dim_,val_,leqtree_,gtree_],x_]:=
	If[x[[dim]]<=val,
		TreeClassify[leqtree,x],
		TreeClassify[gtree,x]]


TreeClassify[leaf[class_],_]:=class


DistributeDefinitions["ML`"]


EndPackage[];
