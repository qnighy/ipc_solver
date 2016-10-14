open Term
open Lf_proof

type nj_proof =
  | NJ_var of pterm * int
  | NJ_app of pterm * nj_proof * nj_proof
  | NJ_abs of pterm * pterm * nj_proof
  | NJ_tt (* True *)
  | NJ_ab of pterm * nj_proof (* False -> A *)
  | NJ_conj of pterm * nj_proof * nj_proof (* A -> B -> A /\ B *)
  | NJ_fst of pterm * nj_proof (* A /\ B -> A *)
  | NJ_snd of pterm * nj_proof(* A /\ B -> B *)
  | NJ_left of pterm * nj_proof (* A -> A \/ B *)
  | NJ_right of pterm * nj_proof (* B -> A \/ B *)
  | NJ_disj of pterm * nj_proof * nj_proof * nj_proof (* A \/B -> (A -> C) -> (B -> C) -> C *)

val nj_type : nj_proof -> pterm
val pp_print_lambda : name_env -> Format.formatter -> nj_proof -> unit
val nj_check_type : pterm list -> nj_proof -> pterm
val convert_lf : pterm -> lf_proof -> nj_proof
val postproc_proof : nj_proof -> nj_proof


type proof_tree =
  | PTassumption of string
  | PTaxiom of string * string
  | PTunary of string * string * proof_tree
  | PTbinary of string * string * proof_tree * proof_tree
  | PTtrinary of string * string * proof_tree * proof_tree * proof_tree

val print_nj_latex : name_env -> Format.formatter -> nj_proof -> unit
