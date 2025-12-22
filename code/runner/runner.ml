open Solver

exception ParseError of string

let lit_of_int (n: int): Lit.coq_Lit =
  match n with
  | 0 -> invalid_arg "DIMACS CNF has no literals with atom 0"
  | n when n > 0 -> Lit.Pos n
  | n -> Lit.Neg (-n)

let parse_stdin (): Lit.coq_Lit list list =
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

  let rec read_clauses acc current =
    try
      let line = input_line ic in
      if line = "" || line.[0] = 'c' then
        read_clauses acc current
      else
        let ints =
          line
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
    with End_of_file ->
      if current <> [] then
        raise(ParseError "Clause not terminated by 0");
      List.rev acc
  in

  let header = skip_comments () in
  parse_header header;
  read_clauses [] []

let string_of_lit (l: Lit.coq_Lit): string =
  match l with
  | Lit.Pos n -> string_of_int n
  | Lit.Neg n -> "-" ^ string_of_int n

let int_of_lit (l: Lit.coq_Lit): int =
  match l with
  | Lit.Pos n -> n
  | Lit.Neg n -> n

let (): unit =
  match solve (parse_stdin ()) with
  | Trans.Coq_fail -> 
    print_endline "UNSAT"
  | Trans.Coq_state (m, _) ->
    Printf.printf "SAT %s\n"
      (m
        |> List.map fst
        |> List.sort (fun l1 l2 -> compare (int_of_lit l1) (int_of_lit l2))
        |> List.map string_of_lit
        |> String.concat " ")
