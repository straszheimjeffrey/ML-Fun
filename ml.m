(* ::Package:: *)

BeginPackage["ML`"]


(* These manage datasets *)


getclass[sample[class_,vec_]]:=class


getvec[sample[class_,vec_]]:=vec


mapvecs[f_,data_]:=
	sample[getclass[#],f[getvec[#]]]&/@data


allclasses[data_]:=
	DeleteDuplicates[getclass/@data]


selectclass[data_,class_]:=
	Select[data,(getclass[#]==class)&]


classmatrix[data_,class_]:=
	getvec/@selectclass[data,class]


fullmatrix[data_]:=getvec/@data


gatherdata[data_]:=
	(c\[Function]c-> classmatrix[data,c])/@allclasses[data]


classesfromgathered[subs_]:=
	(r\[Function]r[[1]])/@subs


mapgathered[f_,subs_]:=
(c\[Function]c->f[c/.subs])/@classesfromgathered[subs]


(* For clearing empty rows *)


removezeros[data_]:=
	Module[{variances,d,mat},
		variances=Variance[fullmatrix[data]];
		d=Length[variances];
		mat=Select[
		(i\[Function]If[PossibleZeroQ[variances[[i]]],
				Null,
				PadRight[Normal[SparseArray[{i->1.0}]],d]])/@Range[d],
		VectorQ];
	{mapvecs[(mat.#)&,data],mat}]


(* And LDA Package *)


outerdifference[l_,r_]:=
	Module[{dif},
	dif=l-r;
	Outer[Times,dif,dif]]


makeldamatrix[data_]:=
	Module[{subs,means,classes,withinclass,full,fullmean,betweenclass},
	subs=gatherdata[data];
	means=mapgathered[Mean,subs];
	classes=classesfromgathered[subs];
	withinclass=
		Apply[Plus,
			(class\[Function]Apply[Plus,
				(s\[Function]outerdifference[s,(class/.means)])/@(class/.subs)])/@classes];
	full=fullmatrix[data];
	fullmean=Mean[full];
	betweenclass=
		Apply[Plus,(c\[Function]Length[c/.subs]*outerdifference[c/.means,fullmean])/@classes];
	Eigensystem[PseudoInverse[withinclass].betweenclass,Length[classes]-1]]


makelda[data_]:=
	Module[{vals,matrix,convert},
	{vals,matrix}=makeldamatrix[data];
	convert=s\[Function]matrix.s;
	{mapvecs[convert,data],
	 matrix,
	 convert,
	 vals}]


EndPackage[];
