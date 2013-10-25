open Parser
open Lexer
open Term
open Format

let () =
  let lexbuf = Lexing.from_channel stdin in
  begin try
    let tn = Parser.main Lexer.token lexbuf in
    eprintf "Term is %a@." (pp_print_pnterm 5) tn;
    let (t,env,num) = convert_name tn in
    eprintf "Term is %a@." (pp_print_pterm env 5) t;
    begin match Solver.solve num t with
    | Some pr ->
        eprintf "solved. provable@.";
        eprintf "proof(LF, plain): %a@."
          Lf_proof.pp_print_proofitem pr;
        eprintf "proof(LF):@,%a@."
          (Lf_proof.pp_print_proof env num t) pr;
        let npr = Nj_proof.convert_lf t pr in
        eprintf "proof(NJ):@,%a@."
          (Nj_proof.pp_print_lambda env) npr;
        Nj_proof.nj_check_type [] npr;
        let npr = Nj_proof.postproc_proof npr in
        Nj_proof.nj_check_type [] npr;

        (* printf "%s@." "\\documentclass[preview]{standalone}"; *)
        printf "%s@." "%provable";
        printf "%s@." "\\documentclass[preview,varwidth=10000px]{standalone}";
        printf "%s@." "\\usepackage{bussproofs}";
        printf "%s@." "\\usepackage{color}";
        printf "%s@." "\\begin{document}";
        printf "%a@."
          (Nj_proof.print_nj_diagram_latex env) npr;
        printf "%s@." "\\end{document}"
    | None ->
        eprintf "solved. unprovable@.";
        printf "%s@." "%unprovable";
        printf "%s@." "\\documentclass[preview,varwidth=4000px]{standalone}";
        printf "%s@." "\\begin{document}";
        printf "%s@." "unprovable";
        printf "%s@." "\\end{document}"
    end
  with
  | Parsing.Parse_error ->
      eprintf "Parse Error@.";
      printf "%s@." "%parse_error";
      printf "%s@." "\\documentclass[preview,varwidth=4000px]{standalone}";
      printf "%s@." "\\begin{document}";
      printf "%s@." "Parse Error";
      printf "%s@." "\\end{document}"
  end

