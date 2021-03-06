Caml1999M025����          	   ?src/retrolixLivenessAnalysis.ml����  ,\  �    ߠ����1ocaml.ppx.context��&_none_@@ �A����������)tool_name���*ppx_driver@@@����,include_dirs����"[]@@@����)load_path!����
%@%@@����,open_modules*����.@.@@����+for_package3����$None8@8@@����%debug=����%falseB@B@@����+use_threadsG����
K@K@@����-use_vmthreadsP����T@T@@����/recursive_typesY����]@]@@����)principalb����%f@f@@����3transparent_modulesk����.o@o@@����-unboxed_typest����7x@x@@����-unsafe_string}����@�@�@@����'cookies�����o�@�@@@@�@@@�@�������*ocaml.text��������
  �

   Liveness Analysis
   =================

   Liveness analysis is a *data flow* analysis. This means that it
   overapproximates the set of possible values that can get involved
   at each program point. The notion of "set of possible values" here
   should be understood in a very broad set as it usually characterize
   an abstract semantic notion like "the definitions that are
   available", "the variables that are alive", ... etc.

   To do that, the analysis works on the control-flow graph (CFG) (i)
   by defining a *transfer function* for each node that
   overapproximates the effects of the node instruction on the values
   ; (ii) by refining the overapproximation iteratively until a
   fixpoint is reached.

   More precisely, a transfer function is defined by two functions
   _IN_ and _OUT_ such that for each program point ℓ, IN(ℓ) is the set
   of possible values entering ℓ and OUT(ℓ) is the set of possible
   values leaving ℓ. If the _domain_ of the transfer function is equiped
   with a partial order with no infinite descending chain and if
   _IN_ and _OUT_ are monotonic with respect to this partial order,
   then by Kleene-Knaster-Tarski's theorem, there exist a fixpoint.

   For liveness analysis, the transfer functions are defined as follows:

   1. The analysis abstract domain contains sets of alive variables.
      The partial order is ⊆. Given that there is only a finite number
      of variables, there is no infinite descending chain.

   2. x ∈ IN(ℓ)
      if x ∈ (OUT(ℓ) \ DEF(ℓ)) ∨ (∃ ℓ' -> ℓ, x ∈ OUT(ℓ')) ∨ x ∈ USE(ℓ)

      x ∈ OUT(ℓ)
      if ∃ ℓ', ℓ -> ℓ', x ∈ IN(ℓ')

      where:
      - USE(ℓ) is the set of variables possibly read at ℓ.
      - DEF(ℓ) is the set of variables possibly written at ℓ.

      or equivalently, removing the redundancy between IN and OUT:

      IN(ℓ)  = USE(ℓ) ∪ (OUT(ℓ) ∖ DEF(ℓ))
      OUT(ℓ) = ⋃_{s ∈ successors (ℓ)} IN(s)

   Notice that OUT(ℓ) only depends on the values IN(s) obtained from
   its successors. This is a characteristic of *backward data flow
   analysis*. We will consider *forward* analyses is a forthcoming
   optimization.

@��	(src/retrolix/retrolixLivenessAnalysis.mlAoo�u��@@@@@���������+RetrolixAST��w���w��@�@@A��w��@@�@��������-RetrolixUtils��x���x�	@�@@A��!x��@@�@���A�    �8liveness_analysis_result��+ @	x	}�, @	x	�@@@��Р'live_in��3 A	�	��4 A	�	�@@�����(LabelMap!t��= A	�	��> A	�	�@������$LSet!t��H A	�	��I A	�	�@@�@@@@�@@@��M A	�	�@@�Р(live_out��S B	�	��T B	�	�@@�����(LabelMap!t��] B	�	��^ B	�	�@������$LSet!t��h B	�	��i B	�	�@@�@@@@�@@@��m B	�	�@@@A@���)ocaml.doc�������	m

   The result of the liveness analysis is a mapping from program
   points to pairs of sets of variables.

@��{z		�|	u	w@@@@@@��~ @	x	x� C	�	�@@�@���@�����-empty_results��� E	�	��� E	�	�@�@@@������'live_in��� G	�	��� G	�
 @�����(LabelMap%empty��� G	�
�� G	�
@�@@@����(live_out��� H

�� H

 @�����(LabelMap%empty��� H

#�� H

1@�@@@@@��� F	�	��� I
3
6@@@@��� E	�	�@@�@���@�����1string_of_results��� K
8
<�� K
8
M@�@@@��@@���!r��� K
8
N�� K
8
O@�@@@�������&Printf'sprintf��� L
R
T�� L
R
b@�@@@��@���/IN:
%s
OUT:
%s
@��� M
c
g�� M
c
|@@@��@������.string_of_lmap��� N
}
��� N
}
�@�@@@��@������!r��  N
}
�� N
}
�@�@@@��'live_in�� N
}
�� N
}
�@�
@@@@�� N
}
�� N
}
�@��@@@��@������.string_of_lmap�� O
�
�� O
�
�@�@@@��@������!r��& O
�
��' O
�
�@�@@@��(live_out��- O
�
��. O
�
�@�
@@@@��1 O
�
��2 O
�
�@��@@@@�Y@@@�gA@@@��8 K
8
8@@�@���@�����#def��D R�E R	@�@@@��@@���!i��N R
�O R@�@@@������(failwith��Y S�Z S@�@@@��@���:Student! This is your job!@��c S�d S5@@@@�@@@�A@@�����������	? [def i] returns the variables defined by the instruction [i]. @��s Q
�
��t Q
�@@@@@@��v R@@�@���@�����#use��� Vim�� Vip@�@@@��@@���!i��� Viq�� Vir@�@@@������(failwith��� Wuw�� Wu@�@@@��@���:Student! This is your job!@��� Wu��� Wu�@@@@�@@@�A@@���7A�������	, [use i] returns the variables used by [i]. @��� U77�� U7h@@@@@L@��� Vii@@�@���@�����6instructions_of_labels��� \OS�� \Oi@�@@@��@@������@��� \Ol�� \Om@@@����"is��� \Oo�� \Oq@�@@@@��� \Ok�� \Or@��@@@����%block��� \Ou�� \Oz@@�@@@��� \Oj�� \O{@@@��@�����!m��� ]~��� ]~�@�@@@�  !�����(LabelMap��� ]~��� ]~�@�@@A@�������$List)fold_left��
 ]~�� ]~�@�@@@��@��@@���!m�� ]~�� ]~�@�@@@��@@������!l��# ]~��$ ]~�@�@@@����!i��, ]~��- ]~�@�@@@@��0 ]~��1 ]~�@��@@@������#add��< ]~��= ]~�@�@@@��@����!l��G ]~��H ]~�@�@@@��@����!i��R ]~��S ]~�@�@@@��@����!m��] ]~��^ ]~�@�@@@@�%@@@�2A@@��c ]~��d ]~�@���g ]~�
@@@��@����%empty��p ]~��q ]~�@�@@@��@����"is��{ ]~��| ]~�@�@@@@�u@@@���� ]~�@@@@��� ]~�@@��@@���!l��� ^���� ^��@�@@@���������(LabelMap$find��� ^���� ^��@�@@@��@����!l��� ^���� ^��@�@@@��@����!m��� ^���� ^��@�@@@@�@@@������)Not_found��� ^���� ^��@@�@@@@�  ����%false��� ^��� ^�	@@�@@@��� ^��@@@@��� ^��@@@��� ^��@@@�N	@@@��
A@@���cm�������	� [instructions_of_labels b] returns a function [instruction_of_label]
    such that [instruction_of_label l] returns the instruction labelled by
    [l] in the block [b]. @��� Y���� [2N@@@@@x@��� \OO@@�@���@�����1liveness_analysis��� r��� r�@�@@@��@@���!b��� r��� r�@�@@@�  ������(failwith�� s35� s3=@�@@@��@���:Student! This is your job!@�� s3>� s3Z@@@@�@@@����8liveness_analysis_result�� r�� r�0@@�@@@�� r�A@@�&A@@������������
  � [liveness_analysis b] returns the liveness analysis of block [b].

   There are many ways to implement this analysis, but some
   implementations will converge faster than others! Let us recall
   what we said during the course:

   1. A backward analysis converges faster by traversing the CFG
      from exit to entry.

   2. A fixpoint computation is better implemented using a *work list*
      that maintains the nodes whose analysis may need a refinement.

   Typically, in the case of the liveness analysis, when considering a
   node [n], we compute [IN(n)] and if it has changed we must update
   [OUT(p)] for all predecessors of [n] and consider these predecessors
   on more time. (This again suggests a backward traversal of the CFG.)

@��( `�) q��@@@@@�@��+ r��@@�@�����<ː������	 

   Some debugging functions.

@��; v]]�< z��@@@@@����@�����.debug_liveness��G |���H |��@�@@@��@@���!b��Q |���R |��@�@@@��@@���'results��[ |���\ |��@�@@@�  ���������'Options0get_verbose_mode��l }���m }��@�@@@��@����"()��w }���x }��@@�@@@@�@@@�  !�����5RetrolixPrettyPrinter��� }���� }��@�@@A@��@�����.get_decoration��� ~���� ~��@�@@@��@@���%space��� ~���� ~��@�@@@��@@���!m��� ~���� ~��@�@@@��@@���!l��� ~� �� ~�@�@@@��@�����!s��� �� @�@@@���������(LabelMap$find��� �� #@�@@@��@����!l��� $�� %@�@@@��@����!m��� &�� '@�@@@@�@@@������)Not_found��� -�� 6@@�@@@@�����$LSet%empty��� :�� D@�@@@@��� @@@@��� 
@@������!@�� ��� ��@�@@@��@����"::�� �HO� �H~A�����������&PPrint&string��  �H\@�@@@��@������!^��, �Hc�- �Hd@�@@@��@���"{ @��6 �H^�7 �Hb@@@��@������!^��B �Hv�C �Hw@�@@@��@������.string_of_lset��O �He�P �Hs@�@@@��@����!s��Z �Ht�[ �Hu@�@@@@�@@@��@���" }@��e �Hx�f �H|@@@@�@@@@��i �H]�j �H}@��7@@@@�^@@@�����"[]�dA@�eA@@@�gfA@@��x �HNh@@@��@������%space��� ���� ��@�@@@����|��� ���� ��A���������&PPrint%empty��� ��@�@@@�����-�A@�	A@@@�A@@��� ��@@@�����"[]��� ���� ��@@�@@@��� ���� ��@���� ��@@@@�>@@@��@@@�
A@@�A@@� 	A@@@��� ~��@@��@�����+decorations��� ����� ���@�@@@������#pre��� ����� ���@������.get_decoration��� ����� ���@�@@@��@������� ����� ���@@�@@@��@������'results��� ����� ���@�@@@��'live_in��� ����� ���@�
@@@@�"@@@����$post�� �	� �@������.get_decoration�� �� �@�@@@��@����$true�� �� �#@@�@@@��@������'results��$ �$�% �+@�@@@��(live_out��+ �,�, �4@�
@@@@�#@@@@@��0 ����1 �5:@@@@��3 ���@@��@�����!p��= �BJ�> �BK@�@@@�������)ExtPPrint)to_string��J �BN�K �Ba@�@@@��@������%block��W �Bc�X �Bh@�@@@��@����+decorations��b �Bi�c �Bt@�@@@@��f �Bb�g �Bu@��@@@��@����!b��r �Bv�s �Bw@�@@@@�,@@@@��w �BF@@�������&Printf'eprintf��� �{�� �{�@�@@@��@���-Liveness:
%s
@��� �{��� �{�@@@��@����!p��� �{��� �{�@�@@@@�@@@�$�� �{�@@@�j@@@��@@@��� ���@@@@��� }��@@@����'results��� ����� ���@�@@@�@@@�RA@@�]A@@@��� |��@@�@���@�����'process��� ����� ���@�@@@��@@���!b��� ����� ���@�@@@������"|>��� ����� ���@�@@@��@������1liveness_analysis��� ����� ���@�@@@��@����!b��� ����� ���@�@@@@�@@@��@������.debug_liveness��� ����� ���@�@@@��@����!b�� ���� ���@�@@@@�@@@@�)@@@�BA@@@�� ���@@�@@