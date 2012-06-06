(* ::Package:: *)

BeginPackage["ML`"]


(* These manage datasets *)


GetClass[sample[class_,vec_]]:=class


GetVec[sample[class_,vec_]]:=vec


MapVecs[f_,data_]:=
	sample[GetClass[#],f[GetVec[#]]]&/@data


AllClasses[data_]:=
	DeleteDuplicates[GetClass/@data]


SelectClass[data_,class_]:=
	Select[data,(GetClass[#]==class)&]


ClassMatrix[data_,class_]:=
	GetVec/@SelectClass[data,class]


FullMatrix[data_]:=GetVec/@data


GatherData[data_]:=
	(c\[Function]c-> ClassMatrix[data,c])/@AllClasses[data]


ClassesFromGathered[subs_]:=
	(r\[Function]r[[1]])/@subs


MapGathered[f_,subs_]:=
(c\[Function]c->f[c/.subs])/@ClassesFromGathered[subs]


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
	{MapVecs[x\[Function]vecs.x,data],
	 vecs,
	 vals}]


(* An LDA Package *)


OuterDifference[l_,r_]:=
	Module[{dif},
	dif=l-r;
	Outer[Times,dif,dif]]


MakeLDAMatrix[data_]:=
	Module[{subs,means,classes,withinclass,full,fullmean,betweenclass},
	subs=GatherData[data];
	means=MapGathered[Mean,subs];
	classes=ClassesFromGathered[subs];
	withinclass=
		Apply[Plus,
			(class\[Function]Apply[Plus,(s\[Function]OuterDifference[s,(class/.means)])/@(class/.subs)])
			/@classes];
	full=FullMatrix[data];
	fullmean=Mean[full];
	betweenclass=
		Apply[Plus,(c\[Function]Length[c/.subs]*OuterDifference[c/.means,fullmean])/@classes];
	Eigensystem[PseudoInverse[withinclass].betweenclass,Length[classes]-1]]


MakeLDA[data_]:=
	Module[{vals,matrix},
	{vals,matrix}=MakeLDAMatrix[data];
	{MapVecs[x\[Function]matrix.x,data],
	 matrix,
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


ComputeImpurity[dim_,less_,more_]:=
	Module[{len,lval,rval,impurity},
	len=Length[less]+Length[more];
	lval=GetVec[Last[less]][[dim]];
	rval=GetVec[First[more]][[dim]];
	If[lval==rval,
		\[Infinity],
		N[(Length[less]/len)*Entropy[2,Map[GetClass,less]]
			+(Length[more]/len)*Entropy[2,Map[GetClass,more]]]]]


BestOfDimension[data_,dim_]:=
	BestOfDimension[data,1,Length[data],dim]

BestOfDimension[data_,start_,end_,dim_]:=
	Module[{bestval,bestless,bestmore,bestimpurity,
			sorted,offset,sentinel,
			less,more,impurity},
	(*Print[{q,Length[data],start,end}];*)
	bestval=Null;
	bestless=Null;
	bestmore=Null;
	bestimpurity=\[Infinity];
	sorted=Sort[data,(OrderedQ[{GetVec[#1][[dim]],GetVec[#2][[dim]]}])&];
	offset=Quotient[end-start-1,20]+1;
	less=sorted[[;;start]];
	more=sorted[[start+1;;]];
	sentinel=(Length[data]-end)+offset;
	While[Length[more]>=sentinel,
		impurity=ComputeImpurity[dim,less,more];
		If[impurity<bestimpurity,
			bestval=N[(GetVec[Last[less]][[dim]]+GetVec[First[more]][[dim]])/2];
			bestless=less;
			bestmore=more;
			bestimpurity=impurity,
			Null];
		less=Join[less,Take[more,offset]];
		more=Drop[more,offset]];
	If[Length[bestless]==0,
		{Null,Null,Null,\[Infinity]},
		If[offset==1,
			{bestval,bestless,bestmore,bestimpurity},
			With[{center=Length[bestless],radius=Quotient[offset,2]},
				BestOfDimension[data,
								Max[center-radius,start],
								Min[center+radius,end],
								dim]]]]]


BestSplit[data_]:=
	Module[{bestdim,bestval,bestless,bestmore,bestimpurity,
			less,more,val,impurity},
	bestdim=Null;
	bestval=Null;
	bestless=Null;
	bestmore=Null;
	bestimpurity=\[Infinity];
	Scan[
	Function[dim,
		(*Print[{d,dim}];*)
		{val,less,more,impurity}=BestOfDimension[data,dim];
		If[impurity<bestimpurity,
			bestdim=dim;
			bestval=val;
			bestless=less;
			bestmore=more;
			bestimpurity=impurity,
			Null]],
	Range[First[data]//GetVec//Length]];
	{bestdim,bestval,bestless,bestmore}]


MakeTree[data_,maxentropy_]:=
	Module[{classes,dim,val,less,more},
	(*Print[{"Branch", Length[data]}];*)
	classes=Map[GetClass,data];
	If[Entropy[2,classes]<=maxentropy,
		(* Low entropy, make a leaf *)
		leaf[Tally[classes][[1,1]]],
		(* Or else split the tree *)
		{dim,val,less,more}=BestSplit[data];
		(*Print[{"Best",Length[less],Length[more]}];*)
		If[dim===Null,
			leaf[Tally[classes][[1,1]]],
			branch[dim,val,MakeTree[less,maxentropy],MakeTree[more,maxentropy]]]]]


TreeClassify[branch[dim_,val_,leqtree_,gtree_],x_]:=
	Module[{},
	Print[x];
	If[x[[dim]]<=val,
		TreeClassify[leqtree,x],
		TreeClassify[gtree,x]]]


TreeClassify[leaf[class_],_]:=class


EndPackage[];
