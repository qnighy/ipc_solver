open Term

(*
 * R = succedent
 * L = antecedent
 * T = top
 * B = bottom
 * C = conjunction
 * D = disjunction
 * I = implication
 * P = atomic proposition
 *)
type lf_proof =
  | LF_ax of int
  | LF_RT
  | LF_RC of lf_proof * lf_proof
  | LF_RDL of lf_proof
  | LF_RDR of lf_proof
  | LF_RI of lf_proof
  | LF_LT of int * lf_proof
  | LF_LB of int
  | LF_LC of int * lf_proof
  | LF_LD of int * lf_proof * lf_proof
  | LF_LIT of int * lf_proof
  | LF_LIB of int * lf_proof
  | LF_LIP of int * int * lf_proof
  | LF_LIC of int * lf_proof
  | LF_LID of int * lf_proof
  | LF_LII of int * lf_proof * lf_proof

val pp_print_proofitem : Format.formatter -> lf_proof -> unit
val pp_print_proof_internal :
  name_env -> int -> int -> (pterm * int) list ->
  pterm option -> pterm -> Format.formatter -> lf_proof -> unit
val pp_print_proof :
  name_env -> int -> pterm -> Format.formatter -> lf_proof -> unit
