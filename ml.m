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
	Module[{bestval,bestless,bestmore,bestimpurity,
			less,more,countsr,countsl,num,
			shifter,impurity},
	bestval=Null;
	bestless=Null;
	bestmore=Null;
	bestimpurity=\[Infinity];
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
		impurity=(Length[less]/num)*RunningEntropy[countsl]
				+(Length[more]/num)*RunningEntropy[countsr];
		If[impurity<bestimpurity,
			bestval=N[(GetVec[Last[less]][[dim]]+GetVec[First[more]][[dim]])/2];
			bestless=less;
			bestmore=more;
			bestimpurity=impurity,
			Null]];
	{dim,bestval,bestless,bestmore,bestimpurity}]


BestSplit[data_]:=
	Fold[{next,best}\[Function]If[next[[5]]<best[[5]],next,best],
		{Null,Null,Null,Null,\[Infinity]},
		ParallelMap[d\[Function]BestOfDimension[data,d],
					Range[First[data]//GetVec//Length]]]


MakeTree[data_,maxentropy_]:=
	Module[{classes,dim,val,less,more,impurity},
	(*Print[{"Branch", Length[data]}];*)
	classes=Map[GetClass,data];
	If[Entropy[2,classes]<=maxentropy,
		(* Low entropy, make a leaf *)
		leaf[Tally[classes][[1,1]]],
		(* Or else split the tree *)
		{dim,val,less,more,impurity}=BestSplit[data];
		(*Print[{"Best",Length[less],Length[more]}];*)
		branch[dim,val,MakeTree[less,maxentropy],MakeTree[more,maxentropy]]]]


DistributeDefinitions[MakeTree];


TreeClassify[branch[dim_,val_,leqtree_,gtree_],x_]:=
	If[x[[dim]]<=val,
		TreeClassify[leqtree,x],
		TreeClassify[gtree,x]]


TreeClassify[leaf[class_],_]:=class


DistributeDefinitions["ML`"]


EndPackage[];
