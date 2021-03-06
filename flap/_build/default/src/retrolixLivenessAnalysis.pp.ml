Caml1999M025¦¾          	   ?src/retrolixLivenessAnalysis.ml¦¾  ,\  ©    ß  ° 1ocaml.ppx.context°À&_none_@@ ÿA   À«   )tool_nameÀ¢*ppx_driver@@@   ,include_dirsÀ© "[]@@@   )load_path!À© 
%@%@@   ,open_modules*À© .@.@@   +for_package3À© $None8@8@@   %debug=À© %falseB@B@@   +use_threadsGÀ© 
K@K@@   -use_vmthreadsPÀ© T@T@@   /recursive_typesYÀ© ]@]@@   )principalbÀ© %f@f@@   3transparent_moduleskÀ© .o@o@@   -unboxed_typestÀ© 7x@x@@   -unsafe_string}À© @@@@   'cookiesÀ© o@@@@@@@@@  ° *ocaml.text   À¢
  ª

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
   _IN_ and _OUT_ such that for each program point â, IN(â) is the set
   of possible values entering â and OUT(â) is the set of possible
   values leaving â. If the _domain_ of the transfer function is equiped
   with a partial order with no infinite descending chain and if
   _IN_ and _OUT_ are monotonic with respect to this partial order,
   then by Kleene-Knaster-Tarski's theorem, there exist a fixpoint.

   For liveness analysis, the transfer functions are defined as follows:

   1. The analysis abstract domain contains sets of alive variables.
      The partial order is â. Given that there is only a finite number
      of variables, there is no infinite descending chain.

   2. x â IN(â)
      if x â (OUT(â) \ DEF(â)) â¨ (â â' -> â, x â OUT(â')) â¨ x â USE(â)

      x â OUT(â)
      if â â', â -> â', x â IN(â')

      where:
      - USE(â) is the set of variables possibly read at â.
      - DEF(â) is the set of variables possibly written at â.

      or equivalently, removing the redundancy between IN and OUT:

      IN(â)  = USE(â) âª (OUT(â) â DEF(â))
      OUT(â) = â_{s â successors (â)} IN(s)

   Notice that OUT(â) only depends on the values IN(s) obtained from
   its successors. This is a characteristic of *backward data flow
   analysis*. We will consider *forward* analyses is a forthcoming
   optimization.

@°À	(src/retrolix/retrolixLivenessAnalysis.mlAooÀuÜÞ@@@@@  À° +RetrolixAST°ÀwàåÀwàð@°@@A°Àwàà@@°@  À° -RetrolixUtils°ÀxñöÀxñ	@°@@A°À!xññ@@°@  £A      8liveness_analysis_result°À+ @	x	}À, @	x	@@@ Ð 'live_in°À3 A		À4 A		£@@À£ ¡(LabelMap!t°À= A		®À> A		¸@ À£ ¡$LSet!t°ÀH A		§ÀI A		­@@°@@@@°@@@°ÀM A		¹@@ Ð (live_out°ÀS B	º	¼ÀT B	º	Ä@@À£ ¡(LabelMap!t°À] B	º	ÎÀ^ B	º	Ø@ À£ ¡$LSet!t°Àh B	º	ÇÀi B	º	Í@@°@@@@°@@@°Àm B	º	Ù@@@A@ ° )ocaml.doc   À¢	m

   The result of the liveness analysis is a mapping from program
   points to pairs of sets of variables.

@°À{z		À|	u	w@@@@@@°À~ @	x	xÀ C	Ú	Û@@°@  ¡@ ÀÀ -empty_results°À E	Ý	áÀ E	Ý	î@°@@@À«   'live_in°À G	õ	ùÀ G	õ
 @À ¡(LabelMap%empty°À  G	õ
À¡ G	õ
@°@@@   (live_out°À© H

Àª H

 @À ¡(LabelMap%empty°À³ H

#À´ H

1@°@@@@@°À· F	ñ	óÀ¸ I
3
6@@@@°Àº E	Ý	Ý@@°@  ¡@ ÀÀ 1string_of_results°ÀÆ K
8
<ÀÇ K
8
M@°@@@ÀÄ@@À !r°ÀÐ K
8
NÀÑ K
8
O@°@@@À¥À ¡&Printf'sprintf°ÀÝ L
R
TÀÞ L
R
b@°@@@  @À¢/IN:
%s
OUT:
%s
@°Àç M
c
gÀè M
c
|@@@  @À¥À .string_of_lmap°Àó N
}
Àô N
}
@°@@@  @À¬À !r°À  N
}
À N
}
@°@@@ 'live_in°À N
}
À N
}
@°
@@@@°À N
}
À N
}
@ °@@@  @À¥À .string_of_lmap°À O

¡À O

¯@°@@@  @À¬À !r°À& O

°À' O

±@°@@@ (live_out°À- O

²À. O

º@°
@@@@°À1 O

 À2 O

»@ °@@@@°Y@@@°gA@@@°À8 K
8
8@@°@  ¡@ ÀÀ #def°ÀD RÀE R	@°@@@ÀÄ@@À !i°ÀN R
ÀO R@°@@@À¥À (failwith°ÀY SÀZ S@°@@@  @À¢:Student! This is your job!@°Àc SÀd S5@@@@°@@@°A@@ ° ù   À¢	? [def i] returns the variables defined by the instruction [i]. @°Às Q
½
½Àt Q
½@@@@@@°Àv R@@°@  ¡@ ÀÀ #use°À VimÀ Vip@°@@@ÀÄ@@À !i°À ViqÀ Vir@°@@@À¥À (failwith°À WuwÀ Wu@°@@@  @À¢:Student! This is your job!@°À¡ WuÀ¢ Wu@@@@°@@@°A@@ ° 7A   À¢	, [use i] returns the variables used by [i]. @°À± U77À² U7h@@@@@L@°À´ Vii@@°@  ¡@ ÀÀ 6instructions_of_labels°ÀÀ \OSÀÁ \Oi@°@@@ÀÄ@@ÀªÀ À@°ÀÌ \OlÀÍ \Om@@@ À "is°ÀÔ \OoÀÕ \Oq@°@@@@°ÀØ \OkÀÙ \Or@ °@@@À£ %block°Àâ \OuÀã \Oz@@°@@@°Àæ \OjÀç \O{@@@À²@ ÀÀ !m°Àñ ]~Àò ]~@°@@@À  !À° (LabelMap°Àý ]~Àþ ]~@°@@A@À¥À ¡$List)fold_left°À
 ]~À ]~ @°@@@  @ÀÄ@@À !m°À ]~¦À ]~§@°@@@ÀÄ@@À À !l°À# ]~©À$ ]~ª@°@@@ À !i°À, ]~¬À- ]~­@°@@@@°À0 ]~¨À1 ]~®@ °@@@À¥À #add°À< ]~²À= ]~µ@°@@@  @À !l°ÀG ]~¶ÀH ]~·@°@@@  @À !i°ÀR ]~¸ÀS ]~¹@°@@@  @À !m°À] ]~ºÀ^ ]~»@°@@@@°%@@@°2A@@°Àc ]~¡Àd ]~¼@ °Àg ]~¢
@@@  @À %empty°Àp ]~½Àq ]~Â@°@@@  @À "is°À{ ]~ÃÀ| ]~Å@°@@@@°u@@@°À ]~Æ@@@@°À ]~@@ÀÄ@@À !l°À ^ÊÐÀ ^ÊÑ@°@@@À§À¥À ¡(LabelMap$find°À ^ÊÙÀ ^Êæ@°@@@  @À !l°À¤ ^ÊçÀ¥ ^Êè@°@@@  @À !m°À¯ ^ÊéÀ° ^Êê@°@@@@°@@@ °À¥ )Not_found°À» ^ÊðÀ¼ ^Êù@@°@@@@À  À© %false°ÀÆ ^ÊÀÇ ^Ê	@@°@@@°ÀÊ ^Êý@@@@°ÀÌ ^ÊÕ@@@°ÀÎ ^ÊÌ@@@°N	@@@°ë
A@@ ° cm   À¢	« [instructions_of_labels b] returns a function [instruction_of_label]
    such that [instruction_of_label l] returns the instruction labelled by
    [l] in the block [b]. @°ÀÝ YÀÞ [2N@@@@@x@°Àà \OO@@°@  ¡@ ÀÀ 1liveness_analysis°Àì rþÀí rþ@°@@@ÀÄ@@À !b°Àö rþÀ÷ rþ@°@@@À  À¥À (failwith°À s35À s3=@°@@@  @À¢:Student! This is your job!@°À s3>À s3Z@@@@°@@@À£ 8liveness_analysis_result°À rþÀ rþ0@@°@@@°À rþA@@°&A@@ ° ®¸   À¢
  í [liveness_analysis b] returns the liveness analysis of block [b].

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

@°À( `À) qûý@@@@@Ã@°À+ rþþ@@°@  ° <Ë   À¢	 

   Some debugging functions.

@°À; v]]À< z@@@@@Ö  ¡@ ÀÀ .debug_liveness°ÀG |ÀH |@°@@@ÀÄ@@À !b°ÀQ |ÀR |@°@@@ÀÄ@@À 'results°À[ |À\ | @°@@@À  À¿À¥À ¡'Options0get_verbose_mode°Àl }£¨Àm }£À@°@@@  @À© "()°Àw }£ÁÀx }£Ã@@°@@@@°@@@À  !À° 5RetrolixPrettyPrinter°À }£ÉÀ }£Þ@°@@A@À²@ ÀÀ .get_decoration°À ~áéÀ ~á÷@°@@@ÀÄ@@À %space°À ~áøÀ ~áý@°@@@ÀÄ@@À !m°À¤ ~áþÀ¥ ~áÿ@°@@@ÀÄ@@À !l°À® ~á À¯ ~á@°@@@À²@ ÀÀ !s°Àº À» @°@@@À§À¥À ¡(LabelMap$find°ÀÉ ÀÊ #@°@@@  @À !l°ÀÔ $ÀÕ %@°@@@  @À !m°Àß &Àà '@°@@@@°@@@ °À¥ )Not_found°Àë -Àì 6@@°@@@@À ¡$LSet%empty°Àö :À÷ D@°@@@@°Àú @@@@°Àü 
@@À¥À !@°À À @°@@@  @À© "::°À HOÀ H~AÀ À¥À ¡&PPrint&string°À  H\@°@@@  @À¥À !^°À, HcÀ- Hd@°@@@  @À¢"{ @°À6 H^À7 Hb@@@  @À¥À !^°ÀB HvÀC Hw@°@@@  @À¥À .string_of_lset°ÀO HeÀP Hs@°@@@  @À !s°ÀZ HtÀ[ Hu@°@@@@°@@@  @À¢" }@°Àe HxÀf H|@@@@°@@@@°Ài H]Àj H}@ °7@@@@°^@@@ À© "[]°dA@°eA@@@°gfA@@°Àx HNh@@@  @À¿À %space°À À @°@@@À© |°À À ¤AÀ À ¡&PPrint%empty°À £@°@@@ À© -°A@°	A@@@°A@@°À¤ @@@À© "[]°À¬ ªÀ­ ¬@@°@@@°À° À± ­@ °À´ @@@@°>@@@°»@@@°
A@@°A@@° 	A@@@°À» ~áå@@À²@ ÀÀ +decorations°ÀÅ µ½ÀÆ µÈ@°@@@À«   #pre°ÀÐ ÍÕÀÑ ÍØ@À¥À .get_decoration°ÀÚ ÍÛÀÛ Íé@°@@@  @À© °Àä ÍêÀå Íï@@°@@@  @À¬À 'results°Àñ ÍðÀò Í÷@°@@@ 'live_in°Àø ÍøÀù Íÿ@°
@@@@°"@@@   $post°À 	À @À¥À .get_decoration°À À @°@@@  @À© $true°À À #@@°@@@  @À¬À 'results°À$ $À% +@°@@@ (live_out°À+ ,À, 4@°
@@@@°#@@@@@°À0 µËÀ1 5:@@@@°À3 µ¹@@À²@ ÀÀ !p°À= BJÀ> BK@°@@@À¥À ¡)ExtPPrint)to_string°ÀJ BNÀK Ba@°@@@  @À¥À %block°ÀW BcÀX Bh@°@@@  @À +decorations°Àb BiÀc Bt@°@@@@°Àf BbÀg Bu@ °@@@  @À !b°Àr BvÀs Bw@°@@@@°,@@@@°Àw BF@@À¥À ¡&Printf'eprintf°À {À {@°@@@  @À¢-Liveness:
%s
@°À {À {@@@  @À !p°À { À {¡@°@@@@°@@@°$À {¢@@@°j@@@°ã@@@°À £¦@@@@°À¡ }£¥@@@À 'results°À¨ ¨ªÀ© ¨±@°@@@°@@@°RA@@°]A@@@°À¯ |@@°@  ¡@ ÀÀ 'process°À» ³·À¼ ³¾@°@@@ÀÄ@@À !b°ÀÅ ³¿ÀÆ ³À@°@@@À¥À "|>°ÀÐ ÃÙÀÑ ÃÛ@°@@@  @À¥À 1liveness_analysis°ÀÝ ÃÅÀÞ ÃÖ@°@@@  @À !b°Àè Ã×Àé ÃØ@°@@@@°@@@  @À¥À .debug_liveness°Àö ÃÜÀ÷ Ãê@°@@@  @À !b°À ÃëÀ Ãì@°@@@@°@@@@°)@@@°BA@@@°À ³³@@°@@