Caml1999M025????            +src/flap.ml????  f?  -  Ml  J󠠝??1ocaml.ppx.context??&_none_@@ ?A??????????)tool_name???*ppx_driver@@@????,include_dirs????"[]@@@????)load_path!????
%@%@@????,open_modules*????.@.@@????+for_package3????$None8@8@@????%debug=????%falseB@B@@????+use_threadsG????
K@K@@????-use_vmthreadsP????T@T@@????/recursive_typesY????]@]@@????)principalb????%f@f@@????3transparent_modulesk????.o@o@@????-unboxed_typest????7x@x@@????-unsafe_string}????@?@?@@????'cookies?????o?@?@@@@?@@@?@???????*ocaml.text????????
  ? The main driver module.

    The role of this module is to have [flap] behave as the command
    line options say. In particular, these options determine:

    - if the compiler is run in interactive or batch mode.
    - what is the source language of the compiler.
    - what is the target language of the compiler.

@??+src/flap.mlA@@?JBD@@@@@?????????'Options??P???P??@?@@A??P??@@?@???A?????*initialize??R???R??@?@@@??@@????"()??(R???)R??@@?@@@?  ??????4initialize_languages??5S???6S??@?@@@??@???????S???@S??@@?@@@@?@@@?  ??????2initialize_options??MT???NT??@?@@@??@????0??WT? ?XT?@@?@@@@?@@@??????1initialize_prompt??cU?dU@?@@@??@????F??mU?nU@@?@@@@?@@@?%@@@?>@@@?LA@@@??uR??@?????1initialize_prompt??}W ?~W1@?@@@??@@????`???W2??W4@@?@@@???????)UserInput*set_prompt???X79??X7M@?@@@??@???&flap> @???X7N??X7V@@@@?@@@?A@@@???W@?????2initialize_options???ZX\??ZXn@?@@@??@@????????ZXo??ZXq@@?@@@?  ???????2CommandLineOptions*initialize???[tv??[t?@?@@@??@????????[t???[t?@@?@@@@?@@@????????#not???\????\??@?@@@??@??????!!???\????\??@?@@@??@?????#Sys+interactive???\??@?@@@@???\????\??@??@@@@?"@@@???????2CommandLineOptions%parse??\???	\??@?@@@??@???????\???\??@@?@@@@?@@@@??\??@@@?U@@@?eA@@@??ZXX	@?????4initialize_languages??#^???$^??@?@@@??@@??????-^???.^??@@?@@@?  ???????3HopixInitialization*initialize??<_???=_?@?@@@??@??????F_??G_?@@?@@@@?@@@?  ???????1ElfInitialization*initialize??V`?W`7@?@@@??@????9??``8?a`:@@?@@@@?@@@?  ???????5X86_64_Initialization*initialize??pa<>?qa<^@?@@@??@????S??za<_?{a<a@@?@@@@?@@@?  ???????6RetrolixInitialization*initialize???bce??bc?@?@@@??@????m???bc???bc?@@?@@@@?@@@?  ???????3FopixInitialization*initialize???c????c??@?@@@??@????????c????c??@@?@@@@?@@@???????3HobixInitialization*initialize???d????d??@?@@@??@????????d????d??@@?@@@@?@@@?'@@@?B@@@?]@@@?x@@@??@@@??	A@@@???^??@@?^@???@?????5infer_source_language???hDH??hD]@?@@@??@@????????hD^??hD`@@?@@@?????????'Options5is_input_filename_set???ich??ic?@?@@@??@????ٰ? ic??ic?@@?@@@@?@@@??????"@@??k???k??@?@@@??@?????)Languages2get_from_extension??j???j??@?@@@??@???????(Filename)extension??(k???)k??@?@@@??@???????'Options2get_input_filename??7k???8k??@?@@@??@??????Ak???Bk??@@?@@@@??Ek???Fk??@??@@@@?"@@@@?2@@@????????)Languages#get??Vm???Wm?@?@@@??@??????3get_source_language??cm??dm?@?@@@??@????F??mm??nm?@@?@@@@??qm??rm?@??@@@@? @@@??wice@@@??A@@???)ocaml.doc???????	i Infer source language from the extension of the input file or from the
    related command line option. @???f????g C@@@@@!@???hDD@@?@???@?????,get_compiler???q????q??@?@@@??@@????x???q????q??@@?@@@?  ??@?????/source_language???r????r??@?@@@??????5infer_source_language???s????s??@?@@@??@????????s????s??@@?@@@@?@@@@???r??@@??@?????/target_language???u???u?@?@@@????????6is_target_language_set???v??v2@?@@@??@????????v3??v5@@?@@@@?@@@???????)Languages#get???w;A??w;N@?@@@??@??????3get_target_language??w;P?w;c@?@@@??@???????w;d?w;f@@?@@@@??w;O?w;g@??@@@@? @@@?????/source_language??yqw?yq?@?@@@??!v@@@@??#u??@@??@?????%using??-{???.{??@?@@@???????$List#map??:{???;{??@?@@@??@?????)Languages#get??G{???H{??@?@@@??@???????'Options)get_using??V{???W{??@?@@@??@????9??`{???a{??@@?@@@@??d{???e{??@??@@@@?/@@@@??j{??@@???????)Compilers#get??u|???v|??@?@@@???%using???????|????|??@?@@@??@????/source_language???|????|??@?@@@??@????/target_language???|????|?@?@@@@?&@@@?2@@@?z@@@??@@@??????)Compilers(Compiler???q????q??@@???q????q??@??@@@???q??A@@?A@@???8M???????	m Given the source language and the target language returns
    the right compiler (as a first-class module). @???o??pZ?@@@@@X@???q??)@@?*@???@?????$eval??? A???? A??@?@@@??@@???'runtime??? A???? A??@?@@@??@@???$eval??? A???? A??@?@@@??@@???%print??? A???? A??@?@@@??@?????#now??? B???? B??@?@@@???????$Unix,gettimeofday?? B??? B??@?@@@??@??????? B??? B??@@?@@@@?@@@@?? B??@@??@????????'runtime?? C???  C?@?@@@????+observation??( C??) C?@?@@@@?@@@??????$eval??4 C??5 C?@?@@@??@????'runtime??? C??@ C?@?@@@@?@@@@??D C??@@??@?????,elapsed_time??N D!'?O D!3@?@@@??????"-.??Y D!K?Z D!M@?@@@??@???????$Unix,gettimeofday??h D!6?i D!G@?@@@??@????K??r D!H?s D!J@@?@@@@?@@@??@????#now??~ D!N? D!Q@?@@@@?@@@@??? D!#@@?  ?????????'Options-get_benchmark??? EUZ?? EUo@?@@@??@????u??? EUp?? EUr@@?@@@@?@@@???????&Printf'eprintf??? Fx|?? Fx?@?@@@??@???&[%fs]
@??? Fx??? Fx?@@@??@????,elapsed_time??? Fx??? Fx?@?@@@@?@@@@??? EUW@@@?  ?????????'Options0get_verbose_eval??? G???? G??@?@@@??@???????? G???? G??@@?@@@@?@@@??????-print_endline??? H???? H??@?@@@??@??????%print??? H???? H??@?@@@??@????'runtime??  H??? H??@?@@@??@????+observation?? H??? H??@?@@@@?? H??? H??@??@@@@?,@@@@?? G??@@@????'runtime?? I??? I?	@?@@@?@@@?^@@@??@@@??@@@?@@@?;A@@?F	A@@?Q
A@@????Ð??????	? The evaluation function evaluates some code and prints the results
    into the standard output. It also benchmarks the time taken to
    evaluates the code, if asked. @??3~?4 @??@@@@@?@??6 A??@@?@???@?????0interactive_loop??B S	?	??C S	?	?@?@@@??@@????%??L S	?	??M S	?	?@@?@@@?  ???????&Printf&printf??[ U	?	??\ U	?	?@?@@@??@???;        Flap version %s

%!@??e U	?	??f U	?	?@@@??@?????'Version&number??q U	?	??r U	?	?@?@@@@?@@@?  ?(Compiler??z W	?

?{ W	?
@???  ??????,get_compiler??? W	?
?? W	?
&@?@@@??@????k??? W	?
'?? W	?
)@@?@@@@?@@@??????)Compilers(Compiler??? W	?
,?? W	?
>@@?@@@?A@@??? W	?
?? W	?
?@@?  !?????(Compiler??? X
C
N?? X
C
V@?@@A??? X
C
I@@??@?????$read??? Z
[
a?? Z
[
e@?@@@??@@???????? Z
[
f?? Z
[
h@@?@@@?  ??????1initialize_prompt??? [
k
o?? [
k
?@?@@@??@???????? [
k
??? [
k
?@@?@@@@?@@@??@?????!b??? \
?
??? \
?
?@?@@@???????&Buffer&create??? \
?
??? \
?
?@?@@@??@???"13@?? \
?
?? \
?
?@@@@?@@@@?? \
?
?@@??A?????$read?? ]
?
?? ]
?
?@?@@@??@@???$prev?? ]
?
?? ]
?
?@?@@@??@?????!c??& ^
?
??' ^
?
?@?@@@???????)UserInput*input_char??3 ^
?
??4 ^
?
?@?@@@??@????%stdin??> ^
?
??? ^
?
?@?@@@@?@@@@??C ^
?
?@@????????!=??N _
?
??O _
?
?@?@@@??@????!c??Y _
?
??Z _
?
?@?@@@??@???!
@??c _
?
??d _
?
?@@@@?@@@????????"<>??p ` ?q ` @?@@@??@????$prev??{ ` ?| ` @?@@@??@???!\@??? ` ?? ` @@@@?@@@?  ???????&Buffer*add_string??? a)?? a:@?@@@??@????!b??? a;?? a<@?@@@??@????$prev??? a=?? aA@?@@@@?@@@???????&Buffer(contents??? bCM?? bC\@?@@@??@????!b??? bC]?? bC^@?@@@@?@@@??? ` ?? c_h@??8@@@??  ???????)UserInput*set_prompt??? dpz?? dp?@?@@@??@???&....> @??? dp??? dp?@@@@?@@@??????$read??? e???? e??@?@@@??@????!c??? e???? e??@?@@@@?@@@??? c_n?? f??@??)@@@?? ` @@@??  ???????&Buffer*add_string?? h??? h??@?@@@??@????!b?? h??? h??@?@@@??@????$prev??' h???( h??@?@@@@?@@@??????$read??3 i???4 i??@?@@@??@????!c??> i???? i??@?@@@@?@@@??C g???D j??@??6@@@??H _
?
?@@@?@@@?1A@@@??L ]
?
?	@@??????$read??U l?V l	@?@@@??@??? @??_ l
?` l@@@@?@@@?@@@?^@@@??@@@??A@@@??g Z
[
]@@??A???????$step??s o?t o!@?@@@??@??@?????&Target'runtime??? p"(?? p"6@@?@@@??@?????(Compiler+environment??? p":?? p"N@@?@@@??@?????&Source2typing_environment??? p"R?? p"k@@?@@@????????&Target'runtime??? qls?? ql?@@?@@@??????(Compiler+environment??? ql??? ql?@@?@@@??????&Source2typing_environment??? ql??? ql?@@?@@@@?@@@?+@@@?9@@@?G@@@?HA@@?XA@@?  ??@@???'runtime??? r???? r??@?@@@??@@???,cenvironment??? r???? r??@?@@@??@@???,tenvironment??? r???? r??@?@@@??????????$read??? t???? t? @?@@@??@????ڰ? t?? t?@@?@@@@?@@@?????&+debug@?? u	? u	@@@@?  ???????'Options0set_verbose_mode?? v!-? v!E@?@@@??@????$true??% v!F?& v!J@@?@@@@?@@@??????$step??1 wLX?2 wL\@?@@@??@????'runtime??< wL]?= wLd@?@@@??@????,cenvironment??G wLe?H wLq@?@@@??@????,tenvironment??R wLr?S wL~@?@@@@?%@@@?=@@@?????&-debug@??^ y???_ y??@@@@?  ???????'Options0set_verbose_mode??l z???m z??@?@@@??@????%false??w z???x z??@@?@@@@?@@@??????$step??? {???? {??@?@@@??@????'runtime??? {???? {??@?@@@??@????,cenvironment??? {???? {??@?@@@??@????,tenvironment??? {???? {??@?@@@@?%@@@?=@@@?????%input??? }??? }?	@?@@@@??@?????#ast??? ~?? ~ @?@@@????????(Compiler&Source,parse_string??? ~#?? ~?@?@@@??@????%input??? ~@?? ~E@?@@@@?@@@@??? ~@@??@?????,tenvironment??? IY?? Ie@?@@@?????????'Options*get_unsafe??? ?hy?? ?h?@?@@@??@????װ?? ?h??? ?h?@@?@@@@?@@@????,tenvironment??	 ????		 ???@?@@@?????????(Compiler&Source)typecheck??	 ????	 ???@?@@@??@????,tenvironment??	# ????	$ ???@?@@@??@????#ast??	. ????	/ ???@?@@@@?@@@??	3 ?hv@@@@??	5 IU@@??@????????$cast??	B ??	C ?"@?@@@????,cenvironment??	K ?$?	L ?0@?@@@@?@@@???????(Compiler)translate??	Y ?3?	Z ?E@?@@@??@????#ast??	d ?F?	e ?I@?@@@??@????,cenvironment??	o ?J?	p ?V@?@@@@?@@@@??	t ?@@?  ?????????'Options0get_verbose_mode??	? ?Zi?	? ?Z?@?@@@??@????	f??	? ?Z??	? ?Z?@@?@@@@?@@@??????-print_endline??	? ????	? ???@?@@@??@???????&Target)print_ast??	? ????	? ???@?@@@??@????$cast??	? ????	? ???@?@@@@??	? ????	? ???@??@@@@?#@@@@??	? ?Zf@@@??@?????'runtime??	? ????	? ???@?@@@?  !??????(Compiler&Target??	? ????	? ???@?@@A@??????$eval??	? ????	? ???@?@@@??@????'runtime??	? ????	? ??@?@@@??@??@@???!r??	? ???	? ??@?@@@??????(evaluate??
 ???
 ??@?@@@??@????!r??
 ???
 ??@?@@@??@????$cast??
 ???
 ??@?@@@@?@@@??
 ???
 ?? @???
! ??	@@@??@????0print_observable??
* ??!?
+ ??1@?@@@@?N@@@?Z?
/ ?2?@@@@??
1 ???@@??????$step??
: ?O[?
; ?O_@?@@@??@????'runtime??
E ?O`?
F ?Og@?@@@??@????,cenvironment??
P ?Oh?
Q ?Ot@?@@@??@????,tenvironment??
[ ?Ou?
\ ?O?@?@@@@?%@@@?/@@@??@@@??@@@?.@@@??@@@@??
e t??
@@@?????!e??
m ????
n ???@?@@@???????	???
x ????
y ???@?@@@??@?????#Sys+interactive??
? ???@?@@@@?@@@??????%raise??
? ????
? ???@?@@@??@????!e??
? ????
? ???@?@@@@?@@@???????%Error%Error??
? ????
? ???@???????)positions??
? ????
? ???@?@@@????#msg??
? ?? ?
? ??@?@@@@??
? ????
? ??@??@@@?@@@@?  ??????-output_string??
? ??
? ?@?@@@??@????&stdout??
? ? ?
? ?&@?@@@??@???????%Error+print_error??
? ?(?
? ?9@?@@@??@????)positions??
? ?:?
? ?C@?@@@??@????#msg??  ?D? ?G@?@@@@?? ?'? ?H@??@@@@?9@@@??????$step?? ?JT? ?JX@?@@@??@????'runtime?? ?JY? ?J`@?@@@??@????,cenvironment??' ?Ja?( ?Jm@?@@@??@????,tenvironment??2 ?Jn?3 ?Jz@?@@@@?%@@@?g@@@??????+End_of_file??? ?{??@ ?{?@@?@@@@???????'runtime??K ????L ???@?@@@?????,cenvironment??U ????V ???@?@@@?????,tenvironment??_ ????` ???@?@@@@??c ????d ???@??@@@?????!e??n ????o ???@?@@@@?  ??????-print_endline??{ ????| ???@?@@@??@???????(Printexc-get_backtrace??? ????? ??@?@@@??@????m??? ???? ??@@?@@@@??? ????? ??@??@@@@?"@@@?  ??????-print_endline??? ??? ?@?@@@??@???????(Printexc)to_string??? ?!?? ?3@?@@@??@????!e??? ?4?? ?5@?@@@@??? ? ?? ?6@??@@@@?#@@@??????$step??? ?8B?? ?8F@?@@@??@????'runtime??? ?8G?? ?8N@?@@@??@????,cenvironment??? ?8O?? ?8[@?@@@??@????,tenvironment??? ?8\?? ?8h@?@@@@?%@@@?Q@@@?~@@@@??? s??@@@?A@@?	A@@??? r??@@@??@????????@?@@??@???????@|@@??@?????{zy@v@@????????uts@p@@??????onm@j@@??????ihg@d@@@c@@b@@a@@`@@??5A@@@??* o7@@?  ???????%Error/resume_on_error??7 ?np?8 ?n?@?@@@??@??????A ?n??B ?n?@@?@@@@?@@@??????&ignore??M ????N ???@?@@@??@??????$step??Z ????[ ???@?@@@??@???????&Target/initial_runtime??i ????j ???@?@@@??@????L??s ????t ???@@?@@@@??w ????x ???@??@@@??@???????(Compiler3initial_environment??? ????? ???@?@@@??@????j??? ????? ???@@?@@@@??? ????? ???@??@@@??@???????&Source:initial_typing_environment??? ????? ??@?@@@??@???????? ???? ?? @@?@@@@??? ????? ??!@??@@@@??? ????? ?"%@??b@@@@?p@@@??@@@??@@@?Y@@@??? X
C
E	@@@??? W	?	?@@@?j@@@?zA@@???
Mb???????	D

   The interactive mode is a basic read-compile-eval-print loop.

@??? N	W	W?? R	?	?@@@@@m@??? S	?	?@@?@???@?????1batch_compilation??? ????? ???@?@@@??@@????İ?? ????? ???@@?@@@?  ???????%Error-exit_on_error??? ????? ??@?@@@??@????ݰ? ??? ??@@?@@@@?@@@?  ?(Compiler?? ? ? ?(@???  ??????,get_compiler?? ?0? ?<@?@@@??@???????% ?=?& ??@@?@@@@?@@@??????)Compilers(Compiler??2 ?B?3 ?T@@?@@@?A@@??7 ?+?8 ?U@@?  !?????(Compiler??B ?Yd?C ?Yl@?@@A??F ?Y_@@??@?????.input_filename??P ?pv?Q ?p?@?@@@???????'Options2get_input_filename??] ?p??^ ?p?@?@@@??@????@??g ?p??h ?p?@@?@@@@?@@@@??l ?pr@@??@?????+module_name??v ????w ???@?@@@???????(Filename.chop_extension??? ????? ???@?@@@??@????.input_filename??? ????? ???@?@@@@?@@@@??? ???@@??@?????#ast??? ????? ???@?@@@???????&Source.parse_filename??? ????? ??@?@@@??@????.input_filename??? ???? ??@?@@@@?@@@@??? ???@@?  ????????#not??? ??? ?"@?@@@??@???????'Options*get_unsafe??? ?$?? ?6@?@@@??@???????? ?7?? ?9@@?@@@@??? ?#?? ?:@??@@@@?"@@@?  !??????(Compiler&Source??? ?@D?? ?@S@?@@A@??@?????$tenv??  ?V`? ?Vd@?@@@??????)typecheck?? ?Vg? ?Vp@?@@@??@??????:initial_typing_environment?? ?Vr? ?V?@?@@@??@???????" ?V??# ?V?@@?@@@@??& ?Vq?' ?V?@??@@@??@????#ast??2 ?V??3 ?V?@?@@@@?+@@@@??7 ?V\@@?????????'Options.get_show_types??D ????E ???@?@@@??@????'??N ????O ???@@?@@@@?@@@??????-print_endline??Z ????[ ???@?@@@??@??????8print_typing_environment??g ????h ???@?@@@??@????$tenv??r ????s ???@?@@@@??v ????w ???@??@@@@??{ ????| ???@??%@@@@??? ???@@@?K@@@???? ? @@@@??? ?@@@??@????????$cast??? ??? ?@?@@@??@??? ??? ?@@@@?	@@@?  !?????(Compiler??? ??? ?@?@@A@??????)translate??? ?!?? ?*@?@@@??@????#ast??? ?+?? ?.@?@@@??@??????3initial_environment??? ?0?? ?C@?@@@??@???????? ?D?? ?F@@?@@@@??? ?/?? ?G@??@@@@?+@@@?7?? ?H@@@@??? ?	@@??@?????/output_filename??? ?LR?? ?La@?@@@???????????? ?d??? ?d?@?@@@??@???????'Options/get_output_file?? ?dk? ?d?@?@@@??@??????? ?d?? ?d?@@?@@@@?@@@??@??? @?? ?d?? ?d?@@@@?@@@??@?????/output_filename??# ????$ ???@?@@@??????!^??. ????/ ???@?@@@??@????+module_name??9 ????: ???@?@@@??@?????&Target)extension??F ????G ???@?@@@@?@@@@??K ???@@????????	??U ????V ???@?@@@??@????/output_filename??` ????a ???@?@@@??@????.input_filename??k ????l ???@?@@@@?@@@??????!^??w ???x ??@?@@@??@????+module_name??? ???? ??@?@@@??@??????!^??? ??$?? ??%@?@@@??@?????&Target)extension??? ???? ??#@?@@@??@???*-optimized@??? ??&?? ??2@@@@?@@@@?(@@@?????/output_filename??? ?>F?? ?>U@?@@@??? ???@@@?l@@@????????'Options/get_output_file??? ?_e?? ?_|@?@@@??@???????? ?_}?? ?_@@?@@@@?@@@??? ?dh@@@@??? ?LN@@?  ?????????'Options0get_verbose_mode??? ????? ???@?@@@??@????Ű?? ????? ???@@?@@@@?@@@??????-output_string??? ????? ???@?@@@??@????&stdout?? ???? ???@?@@@??@??????!^?? ???? ???@?@@@??@???????&Target)print_ast?? ????  ???@?@@@??@????$cast??* ????+ ???@?@@@@?@@@??@???!
@??5 ????6 ???@@@@??8 ????9 ???@??@@@@?E@@@@??> ???@@@?  ????????#not??K ????L ???@?@@@??@??????"||??X ???Y ??@?@@@??@???????'Options,get_dry_mode??g ????h ??@?@@@??@????J??q ???r ??@@?@@@@?@@@??@??????
1??~ ??? ??@?@@@??@????/output_filename??? ??	?? ??@?@@@??@????.input_filename??? ???? ??)@?@@@@?@@@@??? ????? ??*@??6@@@@?S@@@??@?????$cout??? ?2:?? ?2>@?@@@??????(open_out??? ?2A?? ?2I@?@@@??@????/output_filename??? ?2J?? ?2Y@?@@@@?@@@@??? ?26@@?  ??????-output_string??? ?]a?? ?]n@?@@@??@????$cout??? ?]o?? ?]s@?@@@??@???????&Target)print_ast??? ?]u?? ?]?@?@@@??@????$cast??? ?]??? ?]?@?@@@@??? ?]t?? ?]?@??@@@@?.@@@?  ??????)close_out?? ???? ???@?@@@??@????$cout?? ???? ???@?@@@@?@@@???????&Target1executable_format?? ???? ???@?@@@????????&ExtStd$Unix-add_exec_bits??- ????. ???@?@@@??@????/output_filename??8 ????9 ???@?@@@@?@@@@??= ???@@@?:?? ???@@@?t@@@??B ??0?C ???@???@@@@??G ???@@@?????????'Options0get_running_mode??T ????U ??@?@@@??@????7??^ ???_ ??@@?@@@@?@@@?  !??????(Compiler&Target??m ???n ??+@?@@A@??????&ignore??x ?.2?y ?.8@?@@@??@????@?????%print??? ?EQ?? ?EV@?@@@?????????'Options0get_verbose_eval??? ?Yf?? ?Y~@?@@@??@????z??? ?Y?? ?Y?@@?@@@@?@@@????0print_observable??? ????? ???@?@@@???@@?@??? ????? ???@@@??@@?@??? ????? ???@@@??? @??? ????? ???@@@?
A@@??? ???@@@??? ?Yc@@@@??? ?EM@@??????$eval??? ????? ???@?@@@??@??????/initial_runtime??? ????? ???@?@@@??@???????? ????? ???@@?@@@@??? ????? ???@??@@@??@??@@???!r??? ????? ?? @?@@@??????(evaluate?? ??? ??@?@@@??@????!r?? ??? ??@?@@@??@????$cast?? ??? ??@?@@@@?@@@?? ????  ??@???# ???	@@@??@????%print??, ???- ??@?@@@@?_@@@?i@@@?????!e??8 ?&0?9 ?&1@?@@@@?  ??????-print_endline??E ?5??F ?5L@?@@@??@???????(Printexc-get_backtrace??T ?5N?U ?5d@?@@@??@????7??^ ?5e?_ ?5g@@?@@@@??b ?5M?c ?5h@??@@@@?"@@@?  ??????-print_endline??q ?jt?r ?j?@?@@@??@???????(Printexc)to_string??? ?j??? ?j?@?@@@??@????!e??? ?j??? ?j?@?@@@@??? ?j??? ?j?@??@@@@?#@@@??????$exit??? ????? ???@?@@@??@???!1@??? ????? ???@@@@?@@@?9@@@?f@@@@??? ?.9?? ???@???? ?;A
@@@@?:@@@?F?? ???@@@@??? ???@@@?p@@@?z@@@??@@@??@@@?6@@@?	@@@?*
@@@?R@@@??? ?Y[@@@??? ?@@@??@@@??A@@???K`???????
  r

   In batch mode, the compiler loads a file written in the source
   language and produces a file written in the target language.

   The filename of the output file is determined by the basename
   of the input filename concatenated with the extension of the
   target language.

   If the running mode is set, the compiler will also interpret
   the compiled code.

@??? ?ff?? ???@@@@@k@??? ???!@@?"@???@?????$main??? ????? ??@?@@@?  ??????*initialize??? ??? ?@?@@@??@????ϰ?? ??? ?@@?@@@@?@@@????????(get_mode?? ?? ?'@?@@@??@??????? ?(? ?*@@?@@@@?@@@???@?? ?06? ?07@@@???????8??  ?0=?! ?0>@?@@@??@?????#Sys+interactive??- ?0M@?@@@@?@@@??????5 ?0Q?6 ?0S@@?@@@??????+Interactive??@ ?TZ?A ?Te@@?@@@@??????0interactive_loop??K ?Ti?L ?Ty@?@@@??@????.??U ?Tz?V ?T|@@?@@@@?@@@??????%Batch??a ?}??b ?}?@@?@@@@??????1batch_compilation??l ?}??m ?}?@?@@@??@????O??v ?}??w ?}?@@?@@@@?@@@@??{ ?@@@??@@@??????????1 -------------- *@??? ????? ???@@@@@$@??? ???@@?@@