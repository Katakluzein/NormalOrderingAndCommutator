(* ::Package:: *)

(* ::Title:: *)
(*Normal Ordering and Commutator*)


BeginPackage["normalOrderingAndCommutator`"]


(* ::Chapter:: *)
(*\:5b9a\:4e49*)


(* ::Subsubsection:: *)
(*\:57fa\:672c\:5b9a\:4e49*)


(* ::Input::Initialization:: *)
a::usage="a\:662f\:6e6e\:706d(annihilation)\:7b97\:7b26\:ff0c\!\(\*SuperscriptBox[\(a\), \(\[Dagger]\)]\)\:662f\:4ea7\:751f\:7b97\:7b26\:ff0ca[k]\:662f\:7b2ck\:4e2a\:6a21\:5f0f\:7684\:6e6e\:706d\:7b97\:7b26";
a=op;
SuperDagger[a[x_]]=a[-x];


(* ::Input::Initialization:: *)
Power[x_op,n_]/;n>1^:=NonCommutativeMultiply@@Table[x,n](*\:5728\:8f93\:5165\:4e2d\:53ef\:4ee5\:4f7f\:7528\:7b97\:7b26\:7684\:5e42\:6b21*)
Unprotect[Power];
Power[x_,n_]/;(n>1&&MemberQ[{x},op,\[Infinity],Heads->True]):=NonCommutativeMultiply@@Table[x,n]
Protect[Power];
Unprotect[NonCommutativeMultiply];


(* ::Subsubsection:: *)
(*\:5bf9\:6613\:5b50*)


com::usage="\:5bf9\:6613\:5b50"


com[a[x_],a[y_]]/;OrderedQ[{x,y}]:=-KroneckerDelta[-x,y](*\:5b9a\:4e49\:6700\:57fa\:7840\:7684\:5bf9\:6613\:5173\:7cfb*)


com[x_,y_]/;(!MemberQ[x,op,\[Infinity],Heads->True])||(!MemberQ[y,op,\[Infinity],Heads->True]):=0(*\:5f53x\:6216\:8005y\:4e2d\:6709\:4e00\:4e2a\:6ca1\:6709op\:65f6\:ff0c\:5bf9\:6613\:5b50\:4e3a\:96f6*)
com[Plus[x_,y_],a_]:=com[x,a]+com[y,a]
com[a_,Plus[x_,y_]]:=com[a,x]+com[a,y]
com[s_,k_]:=com[Expand[s],Expand[k]]
com[a_,Times[b_op,y_]]:= y com[a,b]
com[Times[x_,a_op],b_]:=x  com[a,b]


com[a_**b_,c_]:=a**com[b,c]+com[a,c]**b
com[a:Except[_NonCommutativeMultiply],b:Except[_NonCommutativeMultiply]]/;!OrderedQ[{a,b}]:=-com[b,a](*\:8fd4\:56de\:7279\:5b9a\:987a\:5e8f\:7684\:5bf9\:6613\:5b50\:ff0c\:907f\:514d\:9677\:5165\:65e0\:9650\:5faa\:73af*)
com[NonCommutativeMultiply[a_,b_,r__],c_]:=a**com[NonCommutativeMultiply[b,r],c]+NonCommutativeMultiply[com[a,c],b,r]
com[a:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]:=-com[b,a]
com[Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply],z_]:=x com[y,z]
com[z_,Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply]]:=x com[z,y]


(* ::Input::Initialization:: *)
com[x_,y_]/;MatrixQ[x]&&MatrixQ[y]&&Dimensions[x]==Dimensions[y]:=Block[{d},d=Dimensions[x][[1]];Table[Sum[x[[i,j]]**y[[j,k]]-y[[i,j]]**x[[j,k]],{j,d}],{i,d},{k,d}]]


(* ::Subsubsection:: *)
(*\:975e\:4ea4\:6362\:4e58\:6cd5*)


NonCommutativeMultiply[a_Plus, b_] := Plus @@ (NonCommutativeMultiply[#, b] & /@ a)
NonCommutativeMultiply[a_, b_Plus] := Plus @@ (NonCommutativeMultiply[a, #] & /@ b)
NonCommutativeMultiply[a_Plus,b_]:=Plus@@(NonCommutativeMultiply[#,b]&/@a)
NonCommutativeMultiply[a_,b_Plus]:=Plus@@(NonCommutativeMultiply[a,#]&/@b)
NonCommutativeMultiply[a__,Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply],a__]:=c NonCommutativeMultiply[b,a]
NonCommutativeMultiply[a_,Times[c:Except[_op],b_op]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_op],b_op],a_]:=c NonCommutativeMultiply[b,a]

(*\:5f53x\:7684\:6df1\:5ea6\:8db3\:591f\:6d45\:ff0c(\:4e0d\:786e\:5b9a\:662f\:5426\:5fc5\:8981)\:4e14\:4e0d\:662f\:6240\:6709\:7684\:51fd\:6570\:5934\:90fd\:662fop\:65f6\:ff0c\:5c06\:51fd\:6570\:5934\:4e0d\:662fop\:7684\:5143\:7d20\:53d8\:4e3a\:666e\:901a\:4e58\:6cd5\:4e58\:8d77\:6765 *)
NonCommutativeMultiply[x_,y_]/;(!MemberQ[{x},op,Infinity,Heads->True]||!MemberQ[{y},op,Infinity,Heads->True]):=x y;
Protect[NonCommutativeMultiply];


(* ::Subsubsection:: *)
(*\:5316\:7b80\:4e0e\:5c55\:793a\:8868\:8fbe\:5f0f*)


sim[p_]:=p/.NonCommutativeMultiply[x_]:>x;(*\:7b2c\:4e8c\:4e2a\:89c4\:5219\:7684\:4f5c\:7528\:662f\:5c06\:591a\:4e2a\:7b97\:7b26\:7684\:4e58\:79ef\:5c55\:793a\:4e3a\:5e42\:6b21*)


dis[p_]:=p//.{op[x_]:>TraditionalForm[Subsuperscript["a",ToString[Abs[x]],ToString[If[x>0,"",\[Dagger]]]]],NonCommutativeMultiply[x__]:>Row[{x}]} ;(*\:5c06\:975e\:4ea4\:6362\:4e58\:6cd5\:91cc\:9762\:7684\:5143\:7d20\:4ee5\:884c\:7684\:5f62\:5f0f\:5c55\:793a\:ff0c\:5e76\:4e14\:5c06op\:66ff\:6362\:4e3a\:53ef\:8bfb\:6027\:597d\:7684\:5f62\:5f0f*)


(* ::Input::Initialization:: *)
col[p_]:=p//.HoldPattern[z___**x__op]/;SameQ@@((Part[#,1]&/@{x})):>z**Superscript[op[{x}[[1,1]]],If[Length[{x}]>1,Length[{x}]," "]]//.HoldPattern[x__op**y___]/;SameQ@@((Part[#,1]&/@{x})&&Length[{x}]>1):>Superscript[op[{x}[[1,1]]],Length[{x}]]**y//sim;


(* ::Subsubsection:: *)
(*ordering*)


order=HoldPattern[z___**op[x_]**op[y_]**w___]/;(x>0&&y<0):>z**op[y]**op[x]**w+z**com[op[x],op[y]]**w;(*\:5f53\:5339\:914d\:5230\:4e0d\:6ee1\:8db3\:6b63\:89c4\:6392\:5e8f\:7684\:65f6\:5019\:4ea4\:6362\:4e24\:8005\:7684\:987a\:5e8f\:ff0c\:5e76\:8865\:5145\:4e00\:4e2a\:5bf9\:6613\:5b50*)
ord[x_]:=(ReplaceRepeated[order][x])//sim;


(* ::Subsubsection:: *)
(*sorting after ordering*)


srt[x : Except[_NonCommutativeMultiply]] /; ! MemberQ[{x}, op[_], Infinity] := x;(*\:975e\:4ea4\:6362\:4e58\:6cd5\:4e0d\:4f5c\:4e3a\:51fd\:6570\:5934\:4e14\:4e0d\:542b\:6709op\:7684x\:4e0d\:9700\:8981\:88ab\:6392\:5e8f\:ff0c\:76f4\:63a5\:8fd4\:56de*)
srt[NonCommutativeMultiply[x___op, y___op]] /; (And @@ (# < 0 & /@ (#[[1]] & /@ ({x}))) || {x} == {}) && (And @@ (# > 0 & /@ (#[[1]] & /@ ({y}))) || {y} == {}) := NonCommutativeMultiply @@ Join[Reverse@Sort[{x}], Sort[{y}]]

srt[x_ + y_] := srt[x] + srt[y](*\:5bf9\:52a0\:6cd5\:900f\:660e*)
srt[Times[x_ , y_]] := srt[x] srt[y]
srt[x_op] := x(*\:5199\:4e00\:4e2a\:65b0\:7684\:51fd\:6570\:6765\:89e3\:51b3\:8f83\:4e3a\:7b80\:5355\:7684\:987a\:5e8f\:95ee\:9898\:ff0c\:4e0d\:5c06\:6240\:6709\:7684\:95ee\:9898\:90fd\:6253\:5305\:5728\:4e00\:4e2a\:51fd\:6570\:4e2d\:89e3\:51b3\:ff0c\:5206\:800c\:6cbb\:4e4b*)


(* ::Input:: *)
(*(*srtNcm[ordering[x_NonCommutativeMultiply]]:=srtNcm[x]*)*)


(* ::Input:: *)
(*(*\:8fd9\:4e2a\:53ef\:80fd\:662f\:6548\:7387\:5f88\:4f4e\:7684\:5199\:6cd5\:ff0c\:5316\:7b80\:65b9\:5411\:4e0d\:660e\:786e\:ff1f\:6709\:592a\:591a\:4e0d\:5fc5\:8981\:7684\:6b65\:9aa4\:ff1f*)*)


EndPackage[]
