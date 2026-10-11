(* The tables of the extracted solver's store, realizing Table of verification/refinement/Table.v: a mutable
   array that grows on demand, with a default for every entry past its end. Reading and writing an entry within
   the array are written out in the realizers of runner/Extract.v. *)

type 'a table = { mutable data : 'a array; default : 'a }

let make (d : 'a) : 'a table = { data = Array.make 16 d; default = d }

(* Set key k past the end of t: grow the array to hold it, filling the new entries with the default. *)
let grow_set (t : 'a table) (k : int) (a : 'a) : unit =
  let n = Array.length t.data in
  let data = Array.make (max (k + 1) (2 * n)) t.default in
  Array.blit t.data 0 data 0 n;
  t.data <- data;
  Array.unsafe_set t.data k a
