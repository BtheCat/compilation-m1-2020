
(* The type of tokens. *)

type token = 
  | WHILE
  | UNDERSCORE
  | TYPE
  | TO
  | SWITCH
  | STRING of (string)
  | STAR
  | SEMICOLON
  | RPAREN
  | REF
  | READ
  | RBRACKET
  | RBRACE
  | PLUS
  | OROP
  | MINUS
  | LT
  | LPAREN
  | LET
  | LBRACKET
  | LBRACE
  | ISLT
  | ISLEQ
  | ISGT
  | ISGEQ
  | ISEQUAL
  | INT of (string)
  | IN
  | IF
  | IDUP of (string)
  | IDQUOTE of (string)
  | IDLOW of (string)
  | GT
  | FUN
  | FOR
  | EXTERN
  | EQUAL
  | EOF
  | ELSE
  | DOT
  | DO
  | DIVIDE
  | COMMA
  | COLON
  | CHAR of (char)
  | BAR
  | BACKSLASH
  | ASSIGN
  | ARROW
  | ANDOP
  | AND
  | AMPERSAND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (HopixAST.t)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val program: Lexing.position -> (HopixAST.t) MenhirInterpreter.checkpoint
  
end
