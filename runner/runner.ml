open Solver
open Lit.Definitions
open PA.Definitions

exception ParseError of string

let lit_of_int (n: int): coq_Lit =
  match n with
  | 0 -> invalid_arg "DIMACS CNF has no literals with atom 0"
  | n when n > 0 -> Pos n
  | n -> Neg (-n)

let parse_stdin (): coq_Lit list list =
  let ic = stdin in

  let rec skip_comments () =
    match input_line ic with
    | line when line = "" -> skip_comments ()
    | line when line.[0] = 'c' -> skip_comments ()
    | line -> line
  in

  let parse_header line =
    try
      Scanf.sscanf line "p cnf %d %d"
        (fun _vars _clauses -> ())
    with _ ->
      raise (ParseError ("Invalid problem line: " ^ line))
  in

  (* Only the read is guarded by the exception handler, so that the recursive calls are tail calls and long
     files do not overflow the stack. *)
  let rec read_clauses acc current =
    match input_line ic with
    | exception End_of_file ->
      if current <> [] then
        raise(ParseError "Clause not terminated by 0");
      List.rev acc
    | line when line = "" || line.[0] = 'c' ->
      read_clauses acc current
    | line ->
      let ints =
        line
        |> String.map (fun ch -> if ch = '\t' || ch = '\r' then ' ' else ch)
        |> String.split_on_char ' '
        |> List.filter (fun s -> s <> "")
        |> List.map int_of_string
      in
      let rec consume ints acc current =
        match ints with
        | [] ->
            read_clauses acc current
        | 0 :: rest ->
            consume rest (List.rev current :: acc) []
        | x :: rest ->
            consume rest acc (lit_of_int x :: current)
      in
      consume ints acc current
  in

  let header = skip_comments () in
  parse_header header;
  read_clauses [] []

let string_of_lit (l: coq_Lit): string =
  match l with
  | Pos n -> string_of_int n
  | Neg n -> "-" ^ string_of_int n

let int_of_lit (l: coq_Lit): int =
  match l with
  | Pos n -> n
  | Neg n -> n

(* The formula as a set of clauses, each a set of literals. *)
let cnf_of_lists (f: coq_Lit list list): CNF.t =
  List.fold_left
    (fun f c -> CNF.add (List.fold_left (fun c l -> Clause.add l c) Clause.empty c) f)
    CNF.empty f

(* The literals of a trail, most recent first. *)
let rec lits_of_pa (m: coq_PA): coq_Lit list =
  match m with
  | Coq_empty -> []
  | Coq_propagate (m, l) | Coq_decide (m, l) -> l :: lits_of_pa m

(* A large minor heap (16M words) and a lazier major GC: the solver allocates many short-lived values, which
   then die young instead of being promoted. *)
let () = Gc.set { (Gc.get ()) with Gc.minor_heap_size = 16 * 1024 * 1024; Gc.space_overhead = 200 }

(* The C solver (c/), verified against the table-only step of verification/refinement/CStep.v. *)
external run_c: unit -> int = "rocqsat_run_c"

(* With --c, run the C solver instead, which reads the problem itself. *)
let () = if Array.mem "--c" Sys.argv then exit (run_c ())

let (): unit =
  match run (cnf_of_lists (parse_stdin ())) with
  | Fail ->
    print_endline "UNSAT"
  | State (m, _) ->
    Printf.printf "SAT %s\n"
      (m
        |> lits_of_pa
        |> List.sort (fun l1 l2 -> compare (int_of_lit l1) (int_of_lit l2))
        |> List.map string_of_lit
        |> String.concat " ")
