From CLITools Require Import CLI_Tools.
From EasyBakeCakeML Require Import
  EasyBakeCakeML
  ExtrCakeMLNativeString
  ExtrCakeMLNat
  CakeML_Stdlib.All.
From CoplandSpec Require Import Term_Defs Attestation_Session Interface.
From RocqCandy Require Import All.
From CoplandEvidenceTools Require Import 
  Appraisal_Summary
  Interface.

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


Definition handle_AppraisalSummary (req : AppraisalSummaryRequest) 
    : Result AppraisalSummaryResponse string :=
  let '(mkAppSummReq sess (evc rwv evt)) := req in
  app_summ <- do_AppraisalSummary evt rwv (ats_context sess) ;;
  res (mkAppSummResp (fold_appsumm app_summ) app_summ).

Definition wrap_args (req : string) : Result string string :=
  json_val <- from_string req ;;
  req_val <-  from_JSON json_val ;;
  (* Handle the request *)
  resp_val <- handle_AppraisalSummary req_val ;;
  res (to_string (to_JSON resp_val)).

Definition copland_evidence_tools_front_end : unit := 
  let comname := CommandLine.name tt in
  let comargs := CommandLine.arguments tt in
  let args_spec := [request_arg_spec] in
  let runtime := (
    args_res <- gather_args_stub comname comargs args_spec ;;
    (* Parse the args into the values *)
    request_arg <- unwrap_opt (args_res ![ "req" ]) "Request argument is required." ;;
    request_arg <- unwrap_opt (arg_value request_arg) "Request argument value was not found." ;;
    wrap_args request_arg
  ) in
  match runtime with
  | res resp_str => TextIO.printLn resp_str
  | err e => TextIO.printLn_err ("Error in Copland Evidence Tools Execution: " ++ e)
  end.

Local Close Scope map_scope.
Local Close Scope string_scope.

Separate CakeML_Extraction copland_evidence_tools_front_end.