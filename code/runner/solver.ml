
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n
 end

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

module Atom =
 struct
  type coq_Atom = int

  (** val eqb : int -> int -> bool **)

  let eqb =
    Nat.eqb
 end

module Lit =
 struct
  type coq_Lit =
  | Pos of Atom.coq_Atom
  | Neg of Atom.coq_Atom

  (** val eqb : coq_Lit -> coq_Lit -> bool **)

  let eqb l1 l2 =
    match l1 with
    | Pos p -> (match l2 with
                | Pos p0 -> Atom.eqb p p0
                | Neg _ -> false)
    | Neg p -> (match l2 with
                | Pos _ -> false
                | Neg p0 -> Atom.eqb p p0)
 end

module Neg =
 struct
  (** val neg : Lit.coq_Lit -> Lit.coq_Lit **)

  let neg = function
  | Lit.Pos p -> Lit.Neg p
  | Lit.Neg p -> Lit.Pos p
 end

module Clause =
 struct
  type coq_Clause = Lit.coq_Lit list

  (** val l_remove : coq_Clause -> Lit.coq_Lit -> coq_Clause **)

  let l_remove c l =
    filter (fun l' -> negb (Lit.eqb l l')) c
 end

module CNF =
 struct
  type coq_CNF = Clause.coq_Clause list
 end

module Evaluation =
 struct
  type coq_Ann =
  | Coq_dec
  | Coq_prop

  type coq_PA = (Lit.coq_Lit * coq_Ann) list

  (** val l_eval_clause_2_clause_1 :
      (coq_PA -> Lit.coq_Lit -> bool option) -> Lit.coq_Lit -> coq_Ann ->
      (Lit.coq_Lit * coq_Ann) list -> Lit.coq_Lit -> bool -> bool -> bool
      option **)

  let l_eval_clause_2_clause_1 l_eval0 _ _ m l refine0 = function
  | true -> Some true
  | false -> if refine0 then Some false else l_eval0 m l

  (** val l_eval_clause_2 :
      (coq_PA -> Lit.coq_Lit -> bool option) -> Lit.coq_Lit -> coq_Ann ->
      (Lit.coq_Lit * coq_Ann) list -> Lit.coq_Lit -> bool -> bool option **)

  let l_eval_clause_2 l_eval0 l' _ m l = function
  | true -> Some true
  | false -> if Lit.eqb l (Neg.neg l') then Some false else l_eval0 m l

  (** val l_eval : coq_PA -> Lit.coq_Lit -> bool option **)

  let rec l_eval m l =
    match m with
    | [] -> None
    | p::l0 ->
      let (l1, _) = p in
      if Lit.eqb l l1
      then Some true
      else if Lit.eqb l (Neg.neg l1) then Some false else l_eval l0 l

  (** val c_eval_clause_2_clause_1 :
      (coq_PA -> Clause.coq_Clause -> bool option) -> coq_PA -> Lit.coq_Lit
      -> bool option -> Lit.coq_Lit list -> bool option -> bool option **)

  let c_eval_clause_2_clause_1 _ _ _ refine _ refine0 =
    match refine with
    | Some b -> if b then Some true else refine0
    | None ->
      (match refine0 with
       | Some b -> if b then Some true else None
       | None -> None)

  (** val c_eval_clause_2 :
      (coq_PA -> Clause.coq_Clause -> bool option) -> coq_PA -> Lit.coq_Lit
      -> bool option -> Lit.coq_Lit list -> bool option **)

  let c_eval_clause_2 c_eval0 m _ refine c =
    match refine with
    | Some b -> if b then Some true else c_eval0 m c
    | None ->
      (match c_eval0 m c with
       | Some b -> if b then Some true else None
       | None -> None)

  (** val c_eval : coq_PA -> Clause.coq_Clause -> bool option **)

  let rec c_eval m = function
  | [] -> Some false
  | l::l0 ->
    (match l_eval m l with
     | Some b -> if b then Some true else c_eval m l0
     | None ->
       (match c_eval m l0 with
        | Some b -> if b then Some true else None
        | None -> None))
 end

module Trans =
 struct
  type coq_State =
  | Coq_fail
  | Coq_state of Evaluation.coq_PA * CNF.coq_CNF
 end

(** val split_last_decision :
    Evaluation.coq_PA -> (Evaluation.coq_PA * Lit.coq_Lit) option **)

let rec split_last_decision = function
| [] -> None
| p::l ->
  let (l0, a) = p in
  (match a with
   | Evaluation.Coq_dec -> Some (l, l0)
   | Evaluation.Coq_prop -> split_last_decision l)

(** val is_conflict : Evaluation.coq_PA -> Clause.coq_Clause -> bool **)

let is_conflict m c =
  match Evaluation.c_eval m c with
  | Some b -> if b then false else true
  | None -> false

(** val find_conflict :
    Evaluation.coq_PA -> CNF.coq_CNF -> Clause.coq_Clause option **)

let find_conflict m f =
  find (is_conflict m) f

(** val find_unit_l :
    Evaluation.coq_PA -> Clause.coq_Clause -> Lit.coq_Lit option **)

let find_unit_l m c =
  find (fun l -> is_conflict m (Clause.l_remove c l)) c

(** val find_unit :
    Evaluation.coq_PA -> CNF.coq_CNF -> (Clause.coq_Clause * Lit.coq_Lit)
    option **)

let rec find_unit m = function
| [] -> None
| c::l ->
  (match find_unit_l m c with
   | Some l0 ->
     (match Evaluation.c_eval m c with
      | Some _ -> find_unit m l
      | None -> Some (c, l0))
   | None -> find_unit m l)

(** val is_undefined_l : Evaluation.coq_PA -> Lit.coq_Lit -> bool **)

let is_undefined_l m l =
  match Evaluation.l_eval m l with
  | Some _ -> false
  | None -> true

(** val find_undef_l :
    Evaluation.coq_PA -> Clause.coq_Clause -> Lit.coq_Lit option **)

let find_undef_l m c =
  find (is_undefined_l m) c

(** val find_decision :
    Evaluation.coq_PA -> CNF.coq_CNF -> Lit.coq_Lit option **)

let rec find_decision m = function
| [] -> None
| c::l ->
  (match find_undef_l m c with
   | Some l0 -> Some l0
   | None -> find_decision m l)

(** val inspect : 'a1 -> 'a1 **)

let inspect a =
  a

(** val next_state : Trans.coq_State -> Trans.coq_State option **)

let next_state = function
| Trans.Coq_fail -> None
| Trans.Coq_state (m, f) ->
  (match find_conflict m f with
   | Some _ ->
     (match inspect (split_last_decision m) with
      | Some p ->
        let (m', l) = p in
        Some (Trans.Coq_state ((((Neg.neg l), Evaluation.Coq_prop)::m'), f))
      | None -> Some Trans.Coq_fail)
   | None ->
     (match inspect (find_unit m f) with
      | Some p ->
        let (_, l) = p in
        Some (Trans.Coq_state (((l, Evaluation.Coq_prop)::m), f))
      | None ->
        (match inspect (find_decision m f) with
         | Some l -> Some (Trans.Coq_state (((l, Evaluation.Coq_dec)::m), f))
         | None -> None)))

(** val solve_aux : CNF.coq_CNF -> Trans.coq_State -> Trans.coq_State **)

let solve_aux _ a =
  let rec fix_F x =
    let s = let pr1,_ = x in pr1 in
    (match inspect (next_state s) with
     | Some s0 -> let y = s0,__ in fix_F y
     | None -> s)
  in fix_F (a,__)

(** val solve : CNF.coq_CNF -> Trans.coq_State **)

let solve f =
  solve_aux f (Trans.Coq_state ([], f))
