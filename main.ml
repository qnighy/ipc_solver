open Parser
open Lexer
open Term
open Format

let () =
  let lexbuf = Lexing.from_channel stdin in
  let tn = Parser.main Lexer.token lexbuf in
  eprintf "Term is %a@." (pp_print_pnterm 5) tn;
  let (t,env,num) = convert_name tn in
  eprintf "Term is %a@." (pp_print_pterm env 5) t;
  begin match Solver.solve num t with
  | Some pr ->
      eprintf "solved: true@.";
      eprintf "proof(LF, plain): %a@."
        Lf_proof.pp_print_proofitem pr;
      eprintf "proof(LF):@,%a@."
        (Lf_proof.pp_print_proof env num t) pr;
      let npr = Nj_proof.convert_lf num t pr in
      eprintf "proof(NJ):@,%a@."
        Nj_proof.pp_print_lambda npr;
      let nd = Nj_proof.make_diagram npr in

      printf "%s@." "\\documentclass[preview]{standalone}";
      printf "%s@." "\\usepackage{bussproofs}";
      printf "%s@." "\\begin{document}";
      printf "%s@." "\\begin{prooftree}";
      printf "%a@."
        (Nj_proof.print_nj_diagram_latex env) nd;
      printf "%s@." "\\end{prooftree}";
      printf "%s@." "\\end{document}"
  | None -> eprintf "solved: false@."
  end

