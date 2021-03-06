open Position
open HopixAST

(** [fresh_identifier ()] returns a new fresh identifier each time it
    is called. *)
val fresh_identifier : unit -> identifier

(** [make_multi_assignments [e1; ...; eN] [f1; ...; fN]] returns
    an expression of the form:
    [
    let x_1 = f1 in
    ...
    let x_N = fN in
    e1 := x1;
    ...
    eN := xN
    ] *)
val make_multi_assignments
  : expression located list -> expression located list -> expression

(** [make_delayed_computation e] returns an expression of the form:

    [ \() => e ]

*)
val make_delayed_computation : expression located -> expression
