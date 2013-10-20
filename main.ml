open Parser
open Lexer
open Term
open Format

let () =
  let lexbuf = Lexing.from_channel stdin in
  let tn = Parser.main Lexer.token lexbuf in
  printf "Term is %a@." (pp_print_pnterm 5) tn;
  let (t,env,num) = convert_name tn in
  printf "Term is %a@." (pp_print_pterm env 5) t;
  begin match Solver.solve num t with
  | Some pr ->
      printf "solved: true@.";
      printf "proof: %a@."
        Lf_proof.pp_print_proofitem pr;
      printf "proof:@,%a@."
        (Lf_proof.pp_print_proof env num t) pr
  | None -> printf "solved: false@."
  end

