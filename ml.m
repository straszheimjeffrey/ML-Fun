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
	{MapVecs[(mat.#)&,data],mat}]


(* And LDA Package *)


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
			(class\[Function]Apply[Plus,
				(s\[Function]OuterDifference[s,(class/.means)])/@(class/.subs)])/@classes];
	full=FullMatrix[data];
	fullmean=Mean[full];
	betweenclass=
		Apply[Plus,(c\[Function]Length[c/.subs]*OuterDifference[c/.means,fullmean])/@classes];
	Eigensystem[PseudoInverse[withinclass].betweenclass,Length[classes]-1]]


MakeLDA[data_]:=
	Module[{vals,matrix,convert},
	{vals,matrix}=MakeLDAMatrix[data];
	convert=s\[Function]matrix.s;
	{MapVecs[convert,data],
	 matrix,
	 convert,
	 vals}]


(* A Multivariate Normal Classifier *)


FindBest[data_]:=
	Module[{best=Null,bestval=-\[Infinity]},
	Scan[v\[Function]If[GetVec[v]>bestval,best=GetClass[v];bestval=GetVec[v],Null],
		data];
	best]


MultiVariateNormClassifier[data_]:=
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


EndPackage[];
