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


multivarnorm[data_]:=
	Module[{},
	subs=gatherdata[data];
	classes=classesfromgathered[subs];
	]


EndPackage[];
