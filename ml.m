(* ::Package:: *)

BeginPackage["ML`"]


(* These manage datasets *)


GetClass[sample[class_,vec_]]:=class


GetVec[sample[class_,vec_]]:=vec


MapVecs[f_,data_]:=
	(s\[Function]sample[GetClass[s],f[GetVec[s]]])/@data


ParallelMapVec[f_,data_]:=
	ParallelMap[s\[Function]sample[GetClass[s],f[GetVec[s]]],data]


MapClasses[f_,data_]:=
	(s\[Function]sample[f[GetClass[s]],GetVec[s]])/@data


AllClasses[data_]:=
	DeleteDuplicates[GetClass/@data]


SelectClass[data_,class_]:=
	Select[data,s\[Function]GetClass[c]==class]


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
	GetClass/@First/@gdata


(* For clearing empty rows *)


RemoveZeros[data_]:=
	Module[{variances,d,mat},
	variances=Variance[FullMatrix[data]];
	d=Length[variances];
	mat=Select[
	(i\[Function]If[PossibleZeroQ[variances[[i]]],
			Null,
			PadRight[Normal[SparseArray[{i->1.0}]],d]])/@Range[d],
		VectorQ];
	{MapVecs[v\[Function]mat.v,data],mat}]


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
	Print["Within"];
	withinclass=Plus@@MapThread[Scatter,{classdata,classmeans}];
	full=FullMatrix[data];
	fullmean=Mean[full];
	Print["Between"];
	betweenclass=Plus@@MapThread[{cm,cc}\[Function]cc*OuterDifference[cm,fullmean],
					{classmeans,classcounts}];
	Eigensystem[PseudoInverse[withinclass].betweenclass,n]]


MakeLDA[data_,n_]:=
	Module[{vals,matrix},
	{vals,matrix}=MakeLDAMatrix[data,n];
	{matrix,
	 vals}]


(* A Multivariate Normal Classifier *)


FindBest[data_]:=
	Module[{best=Null,bestval=-\[Infinity]},
	Scan[v\[Function]If[GetVec[v]>bestval,best=GetClass[v];bestval=GetVec[v],Null],
		data];
	best]


MultiVariateNormalClassifier[data_]:=
	Module[{n,subs,classes,pcs,ms,ss,ssi,dss,wms,wvs,wss,fns},
	n=Length[data];
	subs=GatherData[data];
	classes=ClassesFromGathered[subs];
	pcs=MapGathered[d\[Function]Length[d]/n,subs];
	ms=MapGathered[Mean,subs];
	ss=MapGathered[Covariance,subs];
	ssi=MapGathered[PseudoInverse,ss];
	dss=MapGathered[Det,ss];
	wms=(c\[Function]c->-(1/2)(c/.ssi))/@classes;
	wvs=(c\[Function]c->(c/.ssi).(c/.ms))/@classes;
	wss=(c\[Function]c->-(1/2)((c/.ms).(c/.ssi).(c/.ms))-(1/2)Log[c/.dss]+Log[c/.pcs])/@classes;
	fns=(c\[Function]x\[Function]sample[c,x.(c/.wms).x+(c/.wvs).x+(c/.wss)])/@classes;
	x\[Function]FindBest[(f\[Function]f[x])/@fns]]


MultiVariateNormalClassifierSingleCovariance[data_]:=
	Module[{n,cov,icov,subs,classes,pcs,ms,wvs,wss,fns},
	n=Length[data];
	cov=Covariance[FullMatrix[data]];
	icov=PseudoInverse[cov];
	subs=GatherData[data];
	classes=ClassesFromGathered[subs];
	pcs=MapGathered[d\[Function]Length[d]/n,subs];
	ms=MapGathered[Mean,subs];
	wvs=(c\[Function]c->icov.(c/.ms))/@classes;
	wss=(c\[Function]c->-(1/2)(c/.ms).icov.(c/.ms)+Log[c/.pcs])/@classes;
	fns=(c\[Function]x\[Function]sample[c,(c/.wvs).x+(c/.wss)])/@classes;
	x\[Function]FindBest[(f\[Function]f[x])/@fns]]


(* A Decision Tree Package *)


RunningEntropy[countsa_]:=
	Module[{counts,total},
	counts=Select[Map[x\[Function]x[[2]],ArrayRules[countsa]],Positive];
	total=Apply[Plus,counts];
	Apply[Plus,Map[x\[Function]N[-(x/total)*Log2[x/total]],counts]]]


BestOfDimension[data_,dim_]:=
	Module[{bestval,bestless,bestmore,bestimpurity,
			less,more,gathered,classes,countsr,countsl,num,
			shifter,impurity},
	bestval=Null;
	bestless=Null;
	bestmore=Null;
	bestimpurity=\[Infinity];
	less={};
	more=Sort[data,(OrderedQ[{GetVec[#1][[dim]],GetVec[#2][[dim]]}])&];
	gathered=MapGathered[Length,GatherData[more]];
	classes=ClassesFromGathered[gathered];
	countsr=SparseArray[gathered];
	countsl=SparseArray[(c\[Function]c->0)/@classes];
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
