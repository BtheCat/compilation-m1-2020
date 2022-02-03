(** This module implements a compiler from Hobix to Fopix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Hobix
module S = Source.AST
module Target = Fopix
module T = Target.AST

(**

   The translation from Hobix to Fopix turns anonymous
   lambda-abstractions into toplevel functions and applications into
   function calls. In other words, it translates a high-level language
   (like OCaml) into a first order language (like C).

   To do so, we follow the closure conversion technique.

   The idea is to make explicit the construction of closures, which
   represent functions as first-class objects. A closure is a block
   that contains a code pointer to a toplevel function [f] followed by all
   the values needed to execute the body of [f]. For instance, consider
   the following OCaml code:

   let f =
     let x = 6 * 7 in
     let z = x + 1 in
     fun y -> x + y * z

   The values needed to execute the function "fun y -> x + y * z" are
   its free variables "x" and "z". The same program with explicit usage
   of closure can be written like this:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]

   (in an imaginary OCaml in which arrays are untyped.)

   Once closures are explicited, there are no more anonymous functions!

   But, wait, how to we call such a function? Let us see that on an
   example:

   let f = ... (* As in the previous example *)
   let u = f 0

   The application "f 0" must be turned into an expression in which
   "f" is a closure and the call to "f" is replaced to a call to "g"
   with the proper arguments. The argument "y" of "g" is known from
   the application: it is "0". Now, where is "env"? Easy! It is the
   closure itself! We get:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]
   let u = f[0] 0 f

   (Remark: Did you notice that this form of "auto-application" is
   very similar to the way "this" is defined in object-oriented
   programming languages?)

*)

(**
   Helpers functions.
*)

let error pos msg =
  Error.error "compilation" pos msg

let make_fresh_variable =
  let r = ref 0 in
  fun () -> incr r; T.Id (Printf.sprintf "_%d" !r)


let make_fresh_function_identifier =
  let r = ref 0 in
  fun () -> incr r; T.FunId (Printf.sprintf "_%d" !r)

let define e f =
  let x = make_fresh_variable () in
  T.Define (x, e, f x)

let rec defines ds e =
  match ds with
    | [] ->
      e
    | (x, d) :: ds ->
      T.Define (x, d, defines ds e)

let seq a b =
  define a (fun _ -> b)

let rec seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq x (seqs xs)

let allocate_block e =
  T.(FunCall (FunId "allocate_block", [e]))

let write_block e i v =
  T.(FunCall (FunId "write_block", [e; i; v]))

let read_block e i =
  T.(FunCall (FunId "read_block", [e; i]))

let lint i =
  T.(Literal (LInt (Int64.of_int i)))

let fill_block b es r =
  seqs (List.mapi (fun i e -> write_block (T.Variable b) (lint i) e) es @ [r])

let make_block es =
  define (allocate_block (lint (List.length es)))
    (fun b -> fill_block b es (T.Variable b))

(** [free_variables e] returns the list of free variables that
     occur in [e].*)
let free_variables =
  let module M =
    Set.Make (struct type t = S.identifier let compare = compare end)
  in
  let rec unions f = function
    | [] -> M.empty
    | [s] -> f s
    | s :: xs -> M.union (f s) (unions f xs)
  in
  let rec fvs = function
    | S.Literal _ ->
       M.empty
    | S.Variable x ->
       M.singleton x
    | S.While (cond, e) ->
       unions fvs [cond; e]
    | S.Define (S.SimpleValue (x, e), a) ->
       M.union (fvs e) (M.remove x (fvs a))
    | S.Define (S.RecFunctions fs, a) ->
       M.diff (unions fvs (a :: List.map snd fs)) (M.of_list (List.map fst fs))
    | S.ReadBlock (a, b) ->
       unions fvs [a; b]
    | S.Apply (a, b) ->
       unions fvs (a :: b)
    | S.WriteBlock (a, b, c) | S.IfThenElse (a, b, c) ->
       unions fvs [a; b; c]
    | S.AllocateBlock a ->
       fvs a
    | S.Fun (xs, e) ->
       M.diff (fvs e) (M.of_list xs)
    | S.Switch (a, b, c) ->
       let c = match c with None -> [] | Some c -> [c] in
       unions fvs (a :: ExtStd.Array.present_to_list b @ c)
  in
  fun e -> M.elements (fvs e)

(**

    A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
type environment = {
    vars : (HobixAST.identifier, FopixAST.expression) Dict.t;
    externals : (HobixAST.identifier, int) Dict.t;
}

let initial_environment () =
  { vars = Dict.empty; externals = Dict.empty }

let bind_external id n env =
  { env with externals = Dict.insert id n env.externals }

let is_external id env =
  Dict.lookup id env.externals <> None

let reset_vars env =
   { env with vars = Dict.empty }

(** Precondition: [is_external id env = true]. *)
let arity_of_external id env =
  match Dict.lookup id env.externals with
    | Some n -> n
    | None -> assert false (* By is_external. *)

let hobix_primitives =
  List.map (fun x -> (S.Id x, 1)) ["print_int"; "print_string"] @
  List.map (fun x -> (S.Id x, 2)) [
    "`+`"; "`-`"; "`*`"; "`/`";
    "`=?`"; "`<?`"; "`>?`"; "`>=?`"; "`<=?`";
    "`||`"; "`&&`"
  ]

let is_external_or_primitive id env =
  is_external id env || List.mem id (List.map fst hobix_primitives)

(** [translate p env] turns an Hobix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =
  let rec program env defs =
    let primdefs = List.map closure_of_primitive hobix_primitives in
    let env, defs = ExtStd.List.foldmap definition env defs in
    (List.flatten (primdefs @ defs), env)
  and closure_of_primitive (id, n) =
    let vars = ExtStd.List.repeatf n make_fresh_variable in
    let c = make_fresh_variable () in
    let f = make_fresh_function_identifier () in
    let fid = function_identifier id in
    let fdef = T.DefineFunction (f, vars @ [c],
      T.FunCall (fid, List.map (fun v -> T.Variable v) vars)) in
    let cdef = T.DefineValue (identifier id,
     make_block [T.Literal (T.LFun f)]) in
    [fdef; cdef]
  and definition env = function
    | S.DeclareExtern (id, n) ->
       let env = bind_external id n env in
       let edef = T.ExternalFunction (function_identifier id, n) in
       (env, edef :: closure_of_primitive (id, n))
    | S.DefineValue vd ->
       (env, value_definition env vd)
  and value_definition env = function
    | S.SimpleValue (x, e) ->
       let fs, e = expression (reset_vars env) e in
       fs @ [T.DefineValue (identifier x, e)]
    | S.RecFunctions fdefs ->
       let fs, defs = define_recursive_functions fdefs in
       fs @ List.map (fun (x, e) -> T.DefineValue (x, e)) defs

  and define_recursive_functions rdefs =

    let process_fun f =
      let function_name = make_fresh_function_identifier () in
      let closure_name = make_fresh_variable () in
      let fv = free_variables f in
      let (x, e) = match f with S.Fun (x, e) -> (x, e) | _ -> assert false in
      let vars = List.mapi (fun i v ->
        (v, read_block (T.Variable closure_name) (lint (i + 1)))) fv in
      let nenv = { env with vars = Dict.of_list vars } in
      let efs, e = expression nenv e in
      let fdef = T.DefineFunction
        (function_name, List.map identifier x @ [closure_name], e) in
      fdef :: efs, (function_name, fv)
    in

    let processed = List.map (fun (x, e) ->
      let r = process_fun e in (fst r, (identifier x, snd r))) rdefs in
    let fs = List.flatten (List.map fst processed) in
    let p = List.map snd processed in
    let defs = List.map (fun (x, (_, fv)) ->
        (x, allocate_block (lint (1 + List.length fv)))) p in
    let defs1, (x, b) = match List.rev defs with
      | x :: l -> List.rev l, x
      | _ -> assert false
    in
    let fill = List.fold_right (fun (y, (name, fv)) r ->
      fill_block y (T.Literal (T.LFun name) :: List.map (get_variable env) fv) r
    ) p (T.Variable x) in
    fs, defs1 @ [(x, T.Define (x, b, fill))]

  and get_variable env x =
    match Dict.lookup x env.vars with
    | None -> T.Variable (identifier x)
    | Some e -> e

  and expression env = function
    | S.Literal l ->
      [], T.Literal (literal l)
    | S.While (cond, e) ->
       let cfs, cond = expression env cond in
       let efs, e = expression env e in
       cfs @ efs, T.While (cond, e)
    | S.Variable x ->
      ([], get_variable env x)
    | S.Define (S.SimpleValue (x, e), a) ->
      let efs, e = expression env e in
      let afs, a = expression env a in
      efs @ afs, T.Define (identifier x, e, a)
    | S.Define (S.RecFunctions fdefs, a) ->
      let fs, defs = define_recursive_functions fdefs in
      let afs, a = expression env a in
      fs @ afs, defines defs a
    | S.Apply (S.Variable x, bs) when is_external_or_primitive x env ->
      (* Note: this relies on the assumption that names of external functions
         or primitives are not shadowed by other functions or local variables.
         However, it is needed to correctly compile `||` and `&&`. *)
      let bfs, bs = expressions env bs in
      bfs, T.FunCall (function_identifier x, bs)
    | S.Apply (a, bs) ->
      let afs, a = expression env a in
      let bfs, bs = expressions env bs in
      let e = define a (fun b ->
        let bv = T.Variable b in
        T.UnknownFunCall (read_block bv (lint 0), bs @ [bv])) in
      afs @ bfs, e
    | S.IfThenElse (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs, T.IfThenElse (a, b, c)

    | S.Fun (x, e) ->
      let function_name = make_fresh_function_identifier () in
      let closure_name = make_fresh_variable () in
      let fv = free_variables (S.Fun (x, e)) in
      let vars = List.mapi (fun i v ->
        (v, read_block (T.Variable closure_name) (lint (i + 1)))) fv in
      let nenv = { env with vars = Dict.of_list vars } in
      let efs, e = expression nenv e in
      let fdef = T.DefineFunction
        (function_name, List.map identifier x @ [closure_name], e) in
      let efv = List.map (get_variable env) fv in
      fdef :: efs, make_block (T.Literal (T.LFun function_name) :: efv)
    | S.AllocateBlock a ->
      let afs, a = expression env a in
      (afs, allocate_block a)
    | S.WriteBlock (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs,
      T.FunCall (T.FunId "write_block", [a; b; c])
    | S.ReadBlock (a, b) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      afs @ bfs,
      T.FunCall (T.FunId "read_block", [a; b])
    | S.Switch (a, bs, default) ->
      let afs, a = expression env a in
      let bsfs, bs =
        ExtStd.List.foldmap (fun bs t ->
                    match ExtStd.Option.map (expression env) t with
                    | None -> (bs, None)
                    | Some (bs', t') -> (bs @ bs', Some t')
                  ) [] (Array.to_list bs)
      in
      let dfs, default = match default with
        | None -> [], None
        | Some e -> let bs, e = expression env e in bs, Some e
      in
      afs @ bsfs @ dfs,
      T.Switch (a, Array.of_list bs, default)


  and expressions env = function
    | [] ->
       [], []
    | e :: es ->
       let efs, es = expressions env es in
       let fs, e = expression env e in
       fs @ efs, e :: es

  and literal = function
    | S.LInt x -> T.LInt x
    | S.LString s -> T.LString s
    | S.LChar c -> T.LChar c

  and identifier (S.Id x) = T.Id x

  and function_identifier (S.Id x) = T.FunId x

  in
  program env p
