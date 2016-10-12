(*
 * This solver is based on:
 * JÖRG HUDELMAIER,
 * An O(n log n)-Space Decision Procedure
 * for Intuitionistic Propositional Logic.
 * J Logic Computation (1993) 3 (1): 63-75.
 * DOI: http://dx.doi.org/10.1093/logcom/3.1.63
 *)
(* author: Masaki Hara *)

open Term
open Lf_proof

val solve : int -> pterm -> lf_proof option
