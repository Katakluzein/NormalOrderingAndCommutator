(* ::Package:: *)

(* ::Title:: *)
(*Normal Ordering and Commutator*)


BeginPackage["normalOrderingAndCommutator`"]


(* ::Chapter:: *)
(*\:5b9a\:4e49*)


(* ::Subsubsection:: *)
(*\:57fa\:672c\:5b9a\:4e49*)


a::usage="a\:662f\:6e6e\:706d(annihilation)\:7b97\:7b26\:ff0c\!\(\*SuperscriptBox[\(a\), \(\[Dagger]\)]\)\:662f\:4ea7\:751f\:7b97\:7b26\:ff0ca[k]\:662f\:7b2ck\:4e2a\:6a21\:5f0f\:7684\:6e6e\:706d\:7b97\:7b26";
a=op;
SuperDagger[a[x_]]:=a[-x];


Power[x_op,n_]/;n>1^:=NonCommutativeMultiply@@Table[x,n](*\:5728\:8f93\:5165\:4e2d\:53ef\:4ee5\:4f7f\:7528\:7b97\:7b26\:7684\:5e42\:6b21*)
Unprotect[Power];
Power[x_,n_]/;(n>1&&MemberQ[{x},op,\[Infinity],Heads->True]):=NonCommutativeMultiply@@Table[x,n]
Protect[Power];
Unprotect[NonCommutativeMultiply];


(*op::usage="\:7b97\:7b26\:7684\:5185\:90e8\:5f62\:5f0f"*)
SuperDagger
com
acm
(*com::usage="\:5bf9\:6613\:5b50"*)
col::usage="\:5c06\:76f8\:540c\:7b97\:7b26\:7684\:8fde\:4e58\:53d8\:6210\:5e42\:6b21\:5f62\:5f0f"
sim::usage="\:5316\:7b80"
dis::usage="\:7f8e\:5316\:6700\:7ec8\:7684\:5c55\:793a\:7ed3\:679c\:ff0c\:53ea\:5728\:5f97\:5230\:6700\:7ec8\:8868\:8fbe\:5f0f\:540e\:4f7f\:7528"
ord::usage="\:5bf9\:7b97\:7b26\:8fdb\:884c\:6b63\:89c4\:6392\:5e8f"
srt::usage="\:4f7f\:5f97\:4e0d\:540c\:6a21\:5f0f\:7684\:7b97\:7b26\:4ece\:5c0f\:5230\:5927\:8fdb\:884c\:6392\:5e8f"
SuperDagger::usage="\:5171\:8f6d\:8f6c\:7f6e"
NonCommutativeMultiply::usage="\:5b9a\:5236\:4e86\:4e00\:4e9b\:975e\:4ea4\:6362\:4e58\:6cd5\:7684\:7ebf\:6027\:6027\:548c\:5206\:914d\:7387\:7b49\:989d\:5916\:6027\:8d28"


(* ::Subsubsection:: *)
(*\:5bf9\:6613\:5b50*)


Begin["`Private`"] (*\:4e3a\:4ec0\:4e48\:8981\:52a0\:8fd9\:4e2a\:554a*)


com[a[x__],a[y__]]/;OrderedQ[{{x}[[1]],{y}[[1]]}]:=-KroneckerDelta[-{x}[[1]],{y}[[1]]]
com[a[x_],a[y_]]/;OrderedQ[{x,y}]:=-KroneckerDelta[-x,y](*\:5b9a\:4e49\:6700\:57fa\:7840\:7684\:5bf9\:6613\:5173\:7cfb*)


com[x_,y_]/;(!MemberQ[x,op,{-1},Heads->True])||(!MemberQ[y,op,{-1},Heads->True]):=0(*\:5f53x\:6216\:8005y\:4e2d\:6709\:4e00\:4e2a\:6ca1\:6709op\:65f6\:ff0c\:5bf9\:6613\:5b50\:4e3a\:96f6*)(*\:4e00\:4e2a\:91cd\:8981\:7684\:6539\:8fdb\:ff0c\:628a\:68c0\:67e5\:6574\:4e2a\:51fd\:6570\:8868\:8fbe\:5f0f\:6539\:6210\:53ea\:7528\:68c0\:67e5\:5012\:6570\:51e0\:4e2alevel\:ff0c\:5f85\:529e*)
com[Plus[x_,y_],a_]:=com[x,a]+com[y,a]
com[a_,Plus[x_,y_]]:=com[a,x]+com[a,y]
(*com[s_,k_]:=com[Expand[s],Expand[k]]*)(*expand\:7684\:4f5c\:7528\:662f\:4ec0\:4e48\:ff1f\:4e3a\:4ec0\:4e48\:9677\:5165\:4e86\:5faa\:73af?*)
com[a_,Times[b_op,y_]]:= y com[a,b]
com[Times[x_,a_op],b_]:=x  com[a,b]


com[a_**b_,c_]:=a**com[b,c]+com[a,c]**b
com[a_,b_**c_]:=b**com[a,c]+com[a,b]**c
com[a:Except[__NonCommutativeMultiply],b:Except[__NonCommutativeMultiply]]/;!OrderedQ[{a[[1]],b[[1]]}]:=-com[b,a](*\:8fd4\:56de\:7279\:5b9a\:987a\:5e8f\:7684\:5bf9\:6613\:5b50\:ff0c\:907f\:514d\:9677\:5165\:65e0\:9650\:5faa\:73af*)(*\:6839\:636e\:7b2c\:4e00\:4e2a\:6570\:5b57\:5224\:65ad\:662f\:5426\:6709\:6b63\:786e\:7684\:987a\:5e8f*)
com[NonCommutativeMultiply[a_,b_,r__],c_]:=a**com[NonCommutativeMultiply[b,r],c]+NonCommutativeMultiply[com[a,c],b,r]
(*com[a:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]:=-com[b,a]*)
com[Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply],z_]:=x com[y,z]
com[z_,Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply]]:=x com[z,y]


com[x_,y_]/;MatrixQ[x]&&MatrixQ[y]&&Dimensions[x]==Dimensions[y]:=Block[{d},d=Dimensions[x][[1]];Table[Sum[x[[i,j]]**y[[j,k]]-y[[i,j]]**x[[j,k]],{j,d}],{i,d},{k,d}]]


(* ::Subsubsection:: *)
(*\:53cd\:5bf9\:6613\:5b50*)


(* ::Code:: *)
(*acm[a[x__],a[y__]]/;OrderedQ[{{x}[[1]],{y}[[1]]}]:=a[x]**a[y]+a[y]**a[x](*\:5b9a\:4e49\:6700\:57fa\:7840\:7684\:5bf9\:6613\:5173\:7cfb*)*)


(* ::Code:: *)
(*acm[x_,y_]/;(!MemberQ[x,op,{-1},Heads->True])||(!MemberQ[y,op,{-1},Heads->True]):=0(*\:5f53x\:6216\:8005y\:4e2d\:6709\:4e00\:4e2a\:6ca1\:6709op\:65f6\:ff0c\:5bf9\:6613\:5b50\:4e3a\:96f6*)(*\:4e00\:4e2a\:91cd\:8981\:7684\:6539\:8fdb\:ff0c\:628a\:68c0\:67e5\:6574\:4e2a\:51fd\:6570\:8868\:8fbe\:5f0f\:6539\:6210\:53ea\:7528\:68c0\:67e5\:5012\:6570\:51e0\:4e2alevel\:ff0c\:5f85\:529e*)*)
(*acm[Plus[x_,y_],a_]:=acm[x,a]+acm[y,a]*)
(*acm[a_,Plus[x_,y_]]:=acm[a,x]+acm[a,y]*)
(*(*acm[s_,k_]:=acm[Expand[s],Expand[k]]*)(*expand\:7684\:4f5c\:7528\:662f\:4ec0\:4e48\:ff1f\:4e3a\:4ec0\:4e48\:9677\:5165\:4e86\:5faa\:73af?*)(*Expand\:7684\:4f5c\:7528\:662f\:66b4\:9732\:51faop\:ff0c\:4f7f\:5f97\:5316\:7b80\:53ef\:4ee5\:987a\:5229\:8fdb\:884c*)*)
(*acm[a_,Times[b_op,y_]]:= y acm[a,b]*)
(*acm[Times[x_,a_op],b_]:=x  acm[a,b]*)


(* ::Code:: *)
(*acm[a_**b_,c_]:=a**acm[b,c]+acm[a,c]**b-2a**c**b*)
(*acm[a_,b_**c_]:=b**acm[a,c]+acm[a,b]**c-2a**c**b*)
(*acm[a:Except[__NonCommutativeMultiply],b:Except[__NonCommutativeMultiply]]/;!OrderedQ[{a[[1]],b[[1]]}]:=acm[b,a](*\:8fd4\:56de\:7279\:5b9a\:987a\:5e8f\:7684\:5bf9\:6613\:5b50\:ff0c\:907f\:514d\:9677\:5165\:65e0\:9650\:5faa\:73af*)(*\:6839\:636e\:7b2c\:4e00\:4e2a\:6570\:5b57\:5224\:65ad\:662f\:5426\:6709\:6b63\:786e\:7684\:987a\:5e8f*)*)
(*acm[NonCommutativeMultiply[a_,b_,r__],c_]:=a**acm[NonCommutativeMultiply[b,r],c]+NonCommutativeMultiply[acm[a,c],b,r]*)
(*(*acm[a:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]:=-acm[b,a]*)*)
(*acm[Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply],z_]:=x acm[y,z]*)
(*acm[z_,Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply]]:=x acm[z,y]*)


acm[x_,y_]/;MatrixQ[x]&&MatrixQ[y]&&Dimensions[x]==Dimensions[y]:=Block[{d},d=Dimensions[x][[1]];Table[Sum[x[[i,j]]**y[[j,k]]-y[[i,j]]**x[[j,k]],{j,d}],{i,d},{k,d}]]


(* ::Subsubsection:: *)
(*\:975e\:4ea4\:6362\:4e58\:6cd5*)


NonCommutativeMultiply[a_Plus,b_]:=Plus@@ (NonCommutativeMultiply[#, b] & /@ a)
NonCommutativeMultiply[a_, b_Plus] := Plus @@ (NonCommutativeMultiply[a, #] & /@ b)
NonCommutativeMultiply[a__,Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply],a__]:=c NonCommutativeMultiply[b,a]
NonCommutativeMultiply[a_,Times[c:Except[_op],b_op]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_op],b_op],a_]:=c NonCommutativeMultiply[b,a]
(*\:5f53x\:7684\:6df1\:5ea6\:8db3\:591f\:6d45\:ff0c(\:4e0d\:786e\:5b9a\:662f\:5426\:5fc5\:8981)\:4e14\:4e0d\:662f\:6240\:6709\:7684\:51fd\:6570\:5934\:90fd\:662fop\:65f6\:ff0c\:5c06\:51fd\:6570\:5934\:4e0d\:662fop\:7684\:5143\:7d20\:53d8\:4e3a\:666e\:901a\:4e58\:6cd5\:4e58\:8d77\:6765 *)
(*NonCommutativeMultiply[x_,y_]/;(!MemberQ[{x},op,{-1},Heads->True]||!MemberQ[{y},op,{-1},Heads->True]):=x y;*)(*\:8fd9\:662f\:6307\:6570\:589e\:957f\:7684\:590d\:6742\:5ea6*)
(*NonCommutativeMultiply[x__]/;Length[{x}]>1&&!MemberQ[{x},op,{-1},Heads->True]:=Times[x];*)
NonCommutativeMultiply[x__]/;Length[{x}]==2&&(!MemberQ[{x}[[1]],op,{-1},Heads->True]||!MemberQ[{x}[[2]],op,{-1},Heads->True]):=Times[x]
Protect[NonCommutativeMultiply];


(* ::Subsubsection:: *)
(*\:5171\:8f6d\:8f6c\:7f6e*)


SuperDagger[((f:(Times|Plus|NonCommutativeMultiply))[x__])]/;Not[f===op]:=SuperDagger[#]&/@f@@Reverse[{x}](*\:8ba9dagger\:7a7f\:900f\:6240\:6709\:7684\:51fd\:6570\:5934\:ff0c\:9664\:4e86op*)


SuperDagger[op[x__]]:=op@@Flatten[{-{x}[[1]],{x}[[2;;-1]]}]


(*((f_)[x__])^\[Dagger]/;Not[f===op]&&MemberQ[Attributes[f],Orderless]:=#^\[Dagger]&/@f[x](*\:52a0\:4e0a\:5224\:65ad\:ff0c\:5982\:679c\:6709orderless\:5c31\:4e0d\:7528\:6267\:884creverse*)
((f_)[x__])^\[Dagger]/;Not[f===op]&&Not[MemberQ[Attributes[f],Orderless]]:=#^\[Dagger]&/@f@@Reverse[{x}]*)


SuperDagger[x_]/;NumberQ[x]:=Conjugate@x


SuperDagger[SuperDagger[(x:Except[_op])]]/;Not[NumberQ[x]]:=x


(* ::Subsubsection:: *)
(*\:5316\:7b80\:4e0e\:5c55\:793a\:8868\:8fbe\:5f0f*)


sim[p_]:=p/.NonCommutativeMultiply[x_]:>x;(*\:7b2c\:4e8c\:4e2a\:89c4\:5219\:7684\:4f5c\:7528\:662f\:5c06\:591a\:4e2a\:7b97\:7b26\:7684\:4e58\:79ef\:5c55\:793a\:4e3a\:5e42\:6b21*)


dis[p_]:=p//.{op[x__]:>TraditionalForm[Subsuperscript["a",If[Length[{x}]>=2,ToString[Abs[{x}[[1]]]]<>","<>ToString@Row[{x}[[2;;-1]]],ToString[Abs[x]]],ToString[If[{x}[[1]]>0,"","\[Dagger]"]]]],NonCommutativeMultiply[x__]:>Row[{x}]} ;


(*dis[p_]:=p//.{op[x_]:>TraditionalForm[Subsuperscript["a",ToString[Abs[x]],ToString[If[x>0,"","\[Dagger]"]]]],NonCommutativeMultiply[x__]:>Row[{x}]} ;(*\:5c06\:975e\:4ea4\:6362\:4e58\:6cd5\:91cc\:9762\:7684\:5143\:7d20\:4ee5\:884c\:7684\:5f62\:5f0f\:5c55\:793a\:ff0c\:5e76\:4e14\:5c06op\:66ff\:6362\:4e3a\:53ef\:8bfb\:6027\:597d\:7684\:5f62\:5f0f*)*)


(*col[p_]:=p//.HoldPattern[z___**x__op]/;SameQ@@((Part[#,1]&/@{x})):>z**Superscript[op[{x}[[1,1]]],If[Length[{x}]>1,Length[{x}]," "]]//.HoldPattern[x__op**y___]/;SameQ@@((Part[#,1]&/@{x})&&Length[{x}]>1):>Superscript[op[{x}[[1,1]]],Length[{x}]]**y//sim;*)


col[p_]:=p//.HoldPattern[z___**x__op]/;Length[{x}]>1&&(SameQ@@((Part[#,1;;-1]&/@{x}))):>z**Superscript[op@@({x}[[1,1;;-1]]),Length[{x}]]//.HoldPattern[x__op**y___]/;SameQ@@((Part[#,1;;-1]&/@{x}))&&Length[{x}]>1:>Superscript[op@@({x}[[1,1;;-1]]),Length[{x}]]**y//sim;


(* ::Subsubsection:: *)
(*ordering*)


order=HoldPattern[z___**op[x_]**op[y_]**w___]/;(x>0&&y<0):>z**op[y]**op[x]**w+z**com[op[x],op[y]]**w;(*\:5f53\:5339\:914d\:5230\:4e0d\:6ee1\:8db3\:6b63\:89c4\:6392\:5e8f\:7684\:65f6\:5019\:4ea4\:6362\:4e24\:8005\:7684\:987a\:5e8f\:ff0c\:5e76\:8865\:5145\:4e00\:4e2a\:5bf9\:6613\:5b50*)
ord[x_]:=(ReplaceRepeated[order][x])//sim;


(*Sort\:548cordering\:6ca1\:6709\:6dfb\:52a0\:5bf9op[2,k]\:8fd9\:79cd\:5f62\:5f0f\:7684\:7b97\:7b26\:7684\:652f\:6301*)


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


Remove[x,n]


End[]; 


Protect @@ Names["normalOrderingAndCommutator`*"];


EndPackage[];
