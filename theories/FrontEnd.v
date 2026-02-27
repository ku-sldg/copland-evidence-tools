From CLITools Require Import CLI_Tools.
From EasyBakeCakeML Require Import
  EasyBakeCakeML
  ExtrCakeMLNativeString
  ExtrCakeMLNat
  CakeML_Stdlib.All.
From CoplandSpec Require Import Term_Defs Attestation_Session Interface Appraisal TypeSys.
From RocqCandy Require Import All.
From CoplandEvidenceTools Require Import Interface.

Local Open Scope string_scope.

(*
Here is the usage we are aiming for:

`copland_evidence_tools <request_json_value>`
*)

Definition request_arg_spec : arg_spec := {|
  arg_name := "req";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The request JSON value.";
  arg_default := None
|}.

Definition unwrap_opt {A B} (opt: option A) (alt : B) : Result A B :=
  match opt with
  | Some v => res v
  | None => err alt
  end.

Local Open Scope map_scope.

Definition handle_appr_summary 
    '(mkAppSummReq sess (evc rwv evt))
    : Result AppraisalSummaryResponse string :=
  match do_appraisal_summary (ats_context sess) rwv (Session_Plc sess) evt with
  | inleft (inleft (exist _ appr_summ appsum_correct_prf)) => res (mkAppSummResp true appr_summ)
  | inleft (inright tc_failure_prf) => 
      err ("Type checking failed during appraisal summary generation")
  | inright evt_failure_prf => 
      err ("Evidence Stack Denotation failure: the stack size determined by evidence type does not match that of the provided raw evidence")
  end.

Definition handle_typecheck 
    '(mkTypeCheckReq sess req_term (evc rwv evt))
    : Result TypeCheckResponse string :=
  match typeof_fix (ats_context sess) (Session_Plc sess) req_term evt with
  | inleft (existT _ typecheck_summ typecheck_correct_prf) => res (mkTypeCheckResp true (Some typecheck_summ))
  | inright tc_failure_prf => err ("Type checking failed: reason unknown")
  end.

Definition copland_evidence_tools_front_end : unit := 
  let comname := CommandLine.name tt in
  let comargs := CommandLine.arguments tt in
  let args_spec := [request_arg_spec] in
  let runtime := (
    args_res <- gather_args_stub comname comargs args_spec ;;
    (* Parse the args into the values *)
    request_arg <- unwrap_opt (args_res ![ "req" ]) "Request argument is required." ;;
    request_arg <- unwrap_opt (arg_value request_arg) "Request argument value was not found." ;;
    (* get the request arguments and figure out which approach to apply *)
    req_json <- from_string request_arg ;;
    match JSON_get_string STR_ACTION req_json with
    | res v => 
      if dec_eq v STR_APPSUMM then
        appr_req <- from_JSON req_json ;;
        appr_res <- handle_appr_summary appr_req ;;
        res (to_string (to_JSON appr_res))
      else if dec_eq v STR_TYPECHK then
        typechk_req <- from_JSON req_json ;;
        tc_res <- handle_typecheck typechk_req ;;
        res (to_string (to_JSON tc_res))
      else
        err ("Unknown action type in request: " ++ v)
    | err e => err ("Error parsing request JSON: " ++ e)
    end
  ) in
  match runtime with
  | res resp_str => TextIO.printLn resp_str
  | err e => TextIO.printLn_err ("Error in Copland Evidence Tools Execution: " ++ e)
  end.

Local Close Scope map_scope.
Local Close Scope string_scope.

Separate CakeML_Extraction copland_evidence_tools_front_end.