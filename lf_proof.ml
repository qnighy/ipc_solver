open Term
open Format

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

let rec pp_print_proofitem ppf = function
  | LF_ax x ->
      fprintf ppf "@[<1>(ax@ %d)@]" x
  | LF_RT ->
      fprintf ppf "@[<1>(TR)@]"
  | LF_RC (pr1,pr2) ->
      fprintf ppf "@[<1>(/\\R@ %a@ %a)@]"
        pp_print_proofitem pr1
        pp_print_proofitem pr2
  | LF_RDL pr ->
      fprintf ppf "@[<1>(\\/R1L@ %a)@]"
        pp_print_proofitem pr
  | LF_RDR pr ->
      fprintf ppf "@[<1>(\\/R1R@ %a)@]"
        pp_print_proofitem pr
  | LF_RI pr ->
      fprintf ppf "@[<1>(->R@ %a)@]"
        pp_print_proofitem pr
  | LF_LT (x,pr) ->
      fprintf ppf "@[<1>(TL@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LB x ->
      fprintf ppf "@[<1>(LB@ %d)@]" x
  | LF_LC (x,pr) ->
      fprintf ppf "@[<1>(/\\L@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LD (x,pr1,pr2) ->
      fprintf ppf "@[<1>(\\/L@ %d@ %a@ %a)@]" x
        pp_print_proofitem pr1
        pp_print_proofitem pr2
  | LF_LIT (x,pr) ->
      fprintf ppf "@[<1>(->TL@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LIB (x,pr) ->
      fprintf ppf "@[<1>(->BL@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LIP (x,y,pr) ->
      fprintf ppf "@[<1>(->pL@ %d@ %d@ %a)@]" x y
        pp_print_proofitem pr
  | LF_LIC (x,pr) ->
      fprintf ppf "@[<1>(->/\\L@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LID (x,pr) ->
      fprintf ppf "@[<1>(->\\/L@ %d@ %a)@]" x
        pp_print_proofitem pr
  | LF_LII (x,pr1,pr2) ->
      fprintf ppf "@[<1>(->->L@ %d@ %a@ %a)@]" x
        pp_print_proofitem pr1
        pp_print_proofitem pr2

let rec cutAnt ant id =
  begin match ant with
  | [] -> raise (Invalid_argument "cannot find desired proposition in antecedent")
  | (t,ti)::antt when ti = id ->
      ([],t,antt)
  | anth::antt ->
      let (c0,c1,c2) = cutAnt antt id in
      (anth::c0,c1,c2)
  end

let rec pp_print_proof_internal env anum pnum ant sucL sucR ppf pr =
  fprintf ppf "@[<1>{";
  List.iter (fun (x,_) ->
    fprintf ppf "%a,@ "
      (pp_print_pterm env 0) x
  ) ant;
  begin match sucL with
  | None ->
      fprintf ppf "|-@ %a@ "
        (pp_print_pterm env 0) sucR
  | Some sucLS ->
      fprintf ppf "[%a -> %a],@ |-@ %a@ "
        (pp_print_pterm env 0) sucR
        (pp_print_pterm env 0) sucLS
        (pp_print_pterm env 0) sucR
  end;
  begin match pr with
  | LF_ax x ->
      fprintf ppf "[ax:%d]@," x
  | LF_RT ->
      fprintf ppf "[TR]@,"
  | LF_RC (pr1,pr2) ->
      begin match sucR with
      | PAnd (t1,t2) ->
          fprintf ppf "[/\\R]:@,%a@,%a@,"
            (pp_print_proof_internal env anum pnum ant sucL t1) pr1
            (pp_print_proof_internal env anum pnum ant sucL t2) pr2
      | _ -> raise (Invalid_argument "LF_RC given, but not PAnd")
      end
  | LF_RDL pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              fprintf ppf "[\\/R1L]:@,%a@,"
                (pp_print_proof_internal env anum pnum ant sucL t1) pr
          | Some sucLS ->
              let p = PVar pnum in
              fprintf ppf "[\\/R2L]:@,%a@,"
                (pp_print_proof_internal env (anum+2) (pnum+1)
                  ((PArrow (t2,p),anum)::(PArrow (p,sucLS),anum+1)::ant)
                  (Some p) t1) pr
          end
      | _ -> raise (Invalid_argument "LF_RDL given, but not POr")
      end
  | LF_RDR pr ->
      begin match sucR with
      | POr (t1,t2) ->
          begin match sucL with
          | None ->
              fprintf ppf "[\\/R1R]:@,%a@,"
                (pp_print_proof_internal env anum pnum ant sucL t2) pr
          | Some sucLS ->
              let p = PVar pnum in
              fprintf ppf "[\\/R2R]:@,%a@,"
                (pp_print_proof_internal env (anum+2) (pnum+1)
                  ((PArrow (t1,p),anum)::(PArrow (p,sucLS),anum+1)::ant)
                  (Some p) t2) pr
          end
      | _ -> raise (Invalid_argument "LF_RDR given, but not POr")
      end
  | LF_RI pr ->
      begin match sucR with
      | PArrow (t1,t2) ->
          fprintf ppf "[->R]:@,%a@,"
            (pp_print_proof_internal env (anum+1) pnum (ant@[(t1,anum)])
              sucL t2) pr
      | _ -> raise (Invalid_argument "LF_RI given, but not PArrow")
      end
  | LF_LT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      fprintf ppf "[TL]:@,%a@,"
        (pp_print_proof_internal env anum pnum (ant0@ant1) sucL sucR) pr
  | LF_LB x ->
      fprintf ppf "[BL]@,"
  | LF_LC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PAnd (t1,t2) ->
          fprintf ppf "[/\\L]:@,%a@,"
            (pp_print_proof_internal env (anum+2) pnum
              (ant0@(t1,anum)::(t2,anum+1)::ant1) sucL sucR) pr
      | _ -> raise (Invalid_argument "LF_LC given, but not PAnd")
      end
  | LF_LD (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | POr (t1,t2) ->
          fprintf ppf "[\\/L]:@,%a@,%a@,"
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(t1,anum)::ant1) sucL sucR) pr1
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(t2,anum)::ant1) sucL sucR) pr2
      | _ -> raise (Invalid_argument "LF_LD given, but not POr")
      end
  | LF_LIT (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (_,t2) ->
          fprintf ppf "[->TL]:@,%a@,"
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(t2,anum)::ant1) sucL sucR) pr
      | _ -> raise (Invalid_argument "LF_LIT given, but not PArrow")
      end
  | LF_LIB (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      fprintf ppf "[->BL]:@,%a@,"
        (pp_print_proof_internal env anum pnum
          (ant0@ant1) sucL sucR) pr
  | LF_LIP (x,y,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (_,t2) ->
          fprintf ppf "[->pL]:@,%a@,"
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(t2,anum)::ant1) sucL sucR) pr
      | _ -> raise (Invalid_argument "LF_LIP given, but not PArrow")
      end
  | LF_LIC (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      begin match t with
      | PArrow (PAnd (t1,t2),t3) ->
          fprintf ppf "[->/\\L]:@,%a@,"
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(PArrow (t1,PArrow (t2,t3)),anum)::ant1) sucL sucR) pr
      | _ -> raise (Invalid_argument "LF_LIC given, but not PAnd")
      end
  | LF_LID (x,pr) ->
      let (ant0,t,ant1) = cutAnt ant x in
      let p = PVar pnum in
      begin match t with
      | PArrow (POr (t1,t2),t3) ->
          fprintf ppf "[->\\/L]:@,%a@,"
            (pp_print_proof_internal env (anum+3) (pnum+1) (ant0@
              (PArrow (t1,p),anum)::
              (PArrow (t2,p),anum+1)::
              (PArrow (p,t3),anum+2)::
            ant1) sucL sucR) pr
      | _ -> raise (Invalid_argument "LF_LID given, but not PArrow-POr")
      end
  | LF_LII (x,pr1,pr2) ->
      let (ant0,t,ant1) = cutAnt ant x in
      let p = PVar pnum in
      begin match t with
      | PArrow (PArrow (t1,t2),t3) ->
          fprintf ppf "[->->L]:@,%a@,%a@,"
            begin match sucL with
            | None ->
                pp_print_proof_internal env (anum+1) pnum
                  (ant0@(t1,anum)::ant1) (Some t3) t2
            | Some sucLS ->
                pp_print_proof_internal env (anum+2) pnum
                  (ant0@(PArrow (sucR,sucLS),anum)::(t1,anum+1)::ant1)
                  (Some t3) t2
            end pr1
            (pp_print_proof_internal env (anum+1) pnum
              (ant0@(t3,anum)::ant1) sucL sucR) pr2
      | _ -> raise (Invalid_argument "LF_LII given, but not PArrow-PArrow")
      end
  end;
  fprintf ppf "@,}@]@,"

let pp_print_proof env pnum suc ppf pr =
  pp_print_proof_internal env 0 pnum [] None suc ppf pr
