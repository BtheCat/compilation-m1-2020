Caml1999N025¦¾            1src/listMonad.mli¦¾  g    	ó  h  ° 1ocaml.ppx.context°À&_none_@@ ÿA   À«   )tool_nameÀ¢*ppx_driver@@@   ,include_dirsÀ© "[]@@@   )load_path!À© 
%@%@@   ,open_modules*À© .@.@@   +for_package3À© $None8@8@@   %debug=À© %falseB@B@@   +use_threadsGÀ© 
K@K@@   -use_vmthreadsPÀ© T@T@@   /recursive_typesYÀ© ]@]@@   )principalbÀ© %f@f@@   3transparent_moduleskÀ© .o@o@@   -unboxed_typestÀ© 7x@x@@   -unsafe_string}À© @@@@   'cookiesÀ© o@@@@@@@@@  ¡A      !t°À;src/utilities/listMonad.mlii	Ài
@  À!a°À	iÀ
i@@@B@@@A@ ° )ocaml.doc¡   À¢
  Ù

    The list monad
    or "non deterministic computations in OCaml"
    or "list comprehension in OCaml"

    As any monad, the purpose of the list monad is to represent in
    OCaml computations that are not directly expressible in OCaml.

    OCaml is a deterministic language: there is at most one value for
    each expression, i.e. at most one result for each computation.

    What if we want to represent computations that have zero, one
    or many results? For instance, imagine the following algorithm:

    pick x in {1..10}
    pick y in {1..10}
    return (x + y)

    This algorithm is non deterministic because "pick" takes one of
    the integers in the set {1..10}. Imagine that we want to know
    all possible executions of this program. How to do that?

    Before answering that question, you may wonder why it would be
    useful to write such a program and then ask for all its execution.
    The answer is: because that is exactly the syntax of sequences
    defined by comprehension! So, it is a concise and declarative way
    to represent a set of values defined by means of generators,
    combinaisons and filters. In other words, the previous program
    represents what a mathematician would write:

    { x + y | x â [1..10], y â [1.10] }

    Nice, isn't it?

    Now, let us come back to monads. In OCaml, there is no "pick"
    but we can program it. More generally, we can *represent*
    computations that are non deterministic as terms of type ['a t].

@°ÀAbbÀhþ @@@@@¬ ° ¯   À¢	{

   A value of type ['a t] is a computation that may produce nothing or
   a value of type 'a or many values of type 'a.

@°À&jÀ'o@@@@@º@°À)i(@@°)@  Ð $pick°À2sÀ3s@À±@À£ $list°À<sÀ=s@ À!a°ÀCsÀDs@@@@°	@@@À£ !t°ÀLsÀMs@ À!a°ÀSsÀTs@@@@°	@@@°
@@@@ ° Lì   À¢	p [pick s] is a non deterministic operation that takes one of the
    element of [s]. You do not know which one. @°ÀcqÀdrÑ@@@@@÷@°Àfs@°@  Ð &return°ÀowquÀpwq{@À±@À!a°Àwwq~Àxwq@@@À£ !t°ÀwqÀwq@ À!a°ÀwqÀwq@@@@°	@@@°
@@@@ °    À¢	L [return x] is a non deterministic computation that evaluates
    into [x]. @°ÀuÀv`p@@@@@*@°Àwqq@°@  Ð $fail°À¢zËÏÀ£zËÓ@À£ !t°ÀªzËÙÀ«zËÚ@ À!a°À±zËÖÀ²zËØ@@@@°	@@@@ ° ©I   À¢	; [fail] is a non deterministic computation with no result. @°ÀÀyÀÁyÊ@@@@@T@°ÀÃzËË@°@  Ð #>>=°ÀÌ AÆÊÀÍ AÆÑ@À±@À£ !t°ÀÖ AÆ×À× AÆØ@ À!a°ÀÝ AÆÔÀÞ AÆÖ@@@@°	@@@À±@À±@À!a°Àè AÆÝÀé AÆß@@@À£ !t°Àð AÆæÀñ AÆç@ À!b°À÷ AÆãÀø AÆå@@@@°	@@@°
@@@À£ !t°À AÆïÀ AÆð@ À!b°À AÆìÀ	 AÆî@@@@°	@@@°À AÆÜ@@@°1@@@@ ° £   À¢	ä [m >>= (fun x -> e)] is a computation that first executes
    [m], name its result [x] and then executes [e]. [x] may
    correspond to zero, one or many values of type ['a] but
    you consider it as a single potential value.
@°À|ÜÜÀ @ÃÅ@@@@@®@°À AÆÆ@°@  Ð #run°À& Q
Y
]À' Q
Y
`@À±@À£ !t°À0 Q
Y
fÀ1 Q
Y
g@ À!a°À7 Q
Y
cÀ8 Q
Y
e@@@@°	@@@À£ $list°À@ Q
Y
nÀA Q
Y
r@ À!a°ÀG Q
Y
kÀH Q
Y
m@@@@°	@@@°
@@@@ ° @à   À¢
  a Now, here is how to write the previous program using these
    functions:

    let allsums =
      pick (range 0 10) >>= (fun x ->
      pick (range 0 10) >>= (fun y ->
        return (x + y)
      )

    (assuming [range start stop] is the list of integers between
    [start] and [stop]).

    Finally, how to get all these integers? Just use [run]:
@°ÀW CòòÀX P
V
X@@@@@ë@°ÀZ Q
Y
Y@°@  ° *ocaml.textô   À¢
  ¡

    For instance, [run allsums] evaluates into:

   [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 2; 3; 4; 5;
    6; 7; 8; 9; 10; 11; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 4; 5; 6; 7; 8; 9; 10;
    11; 12; 13; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 6; 7; 8; 9; 10; 11; 12; 13;
    14; 15; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 8; 9; 10; 11; 12; 13; 14; 15;
    16; 17; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]

@°Àk S
t
tÀl ]@@@@@ÿ@