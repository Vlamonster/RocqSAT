
val negb : bool -> bool



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Nat :
 sig
  val eqb : int -> int -> bool
 end

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

module Atom :
 sig
  type coq_Atom = int

  val eqb : int -> int -> bool
 end

module Lit :
 sig
  type coq_Lit =
  | Pos of Atom.coq_Atom
  | Neg of Atom.coq_Atom

  val eqb : coq_Lit -> coq_Lit -> bool
 end

module Neg :
 sig
  val neg : Lit.coq_Lit -> Lit.coq_Lit
 end

module Clause :
 sig
  type coq_Clause = Lit.coq_Lit list

  val l_remove : coq_Clause -> Lit.coq_Lit -> coq_Clause
 end

module CNF :
 sig
  type coq_CNF = Clause.coq_Clause list
 end

module Evaluation :
 sig
  type coq_Ann =
  | Coq_dec
  | Coq_prop

  type coq_PA = (Lit.coq_Lit * coq_Ann) list

  val l_eval_clause_2_clause_1 :
    (coq_PA -> Lit.coq_Lit -> bool option) -> Lit.coq_Lit -> coq_Ann ->
    (Lit.coq_Lit * coq_Ann) list -> Lit.coq_Lit -> bool -> bool -> bool option

  val l_eval_clause_2 :
    (coq_PA -> Lit.coq_Lit -> bool option) -> Lit.coq_Lit -> coq_Ann ->
    (Lit.coq_Lit * coq_Ann) list -> Lit.coq_Lit -> bool -> bool option

  val l_eval : coq_PA -> Lit.coq_Lit -> bool option

  val c_eval_clause_2_clause_1 :
    (coq_PA -> Clause.coq_Clause -> bool option) -> coq_PA -> Lit.coq_Lit ->
    bool option -> Lit.coq_Lit list -> bool option -> bool option

  val c_eval_clause_2 :
    (coq_PA -> Clause.coq_Clause -> bool option) -> coq_PA -> Lit.coq_Lit ->
    bool option -> Lit.coq_Lit list -> bool option

  val c_eval : coq_PA -> Clause.coq_Clause -> bool option
 end

module Trans :
 sig
  type coq_State =
  | Coq_fail
  | Coq_state of Evaluation.coq_PA * CNF.coq_CNF
 end

val split_last_decision :
  Evaluation.coq_PA -> (Evaluation.coq_PA * Lit.coq_Lit) option

val is_conflict : Evaluation.coq_PA -> Clause.coq_Clause -> bool

val find_conflict :
  Evaluation.coq_PA -> CNF.coq_CNF -> Clause.coq_Clause option

val find_unit_l : Evaluation.coq_PA -> Clause.coq_Clause -> Lit.coq_Lit option

val find_unit :
  Evaluation.coq_PA -> CNF.coq_CNF -> (Clause.coq_Clause * Lit.coq_Lit) option

val is_undefined_l : Evaluation.coq_PA -> Lit.coq_Lit -> bool

val find_undef_l :
  Evaluation.coq_PA -> Clause.coq_Clause -> Lit.coq_Lit option

val find_decision : Evaluation.coq_PA -> CNF.coq_CNF -> Lit.coq_Lit option

val inspect : 'a1 -> 'a1

val next_state : Trans.coq_State -> Trans.coq_State option

val solve_aux : CNF.coq_CNF -> Trans.coq_State -> Trans.coq_State

val solve : CNF.coq_CNF -> Trans.coq_State
