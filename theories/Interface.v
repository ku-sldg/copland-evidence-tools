From CoplandSpec Require Import Term_Defs Attestation_Session Interface Appraisal.

Record AppraisalSummaryRequest := 
  mkAppSummReq {
    appsummreq_att_sess : Attestation_Session;
    appsummreq_Evidence: Evidence;
  }.

Record AppraisalSummaryResponse := 
  mkAppSummResp {
    appsummresp_success: bool;
    appsummresp_summary: AppraisalSummary;
  }.

Global Instance Jsonifiable_AppraisalSummaryRequest `{Jsonifiable Evidence, Jsonifiable Attestation_Session}: Jsonifiable AppraisalSummaryRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_APPSUMM));
    (STR_ATTEST_SESS, (to_JSON (appsummreq_att_sess req)));
    (STR_EVIDENCE, (to_JSON (appsummreq_Evidence req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_ev <- JSON_get_Object STR_EVIDENCE j ;;

  att_sess <- from_JSON temp_att_sess ;;
  ev <- from_JSON temp_ev ;;
  res (mkAppSummReq att_sess ev)));
solve_json.
Qed.

Global Instance Jsonifiable_AppraisalSummaryResponse `{Jsonifiable AppraisalSummary}: Jsonifiable AppraisalSummaryResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_APPSUMM));
    (STR_SUCCESS, (JSON_Boolean (appsummresp_success resp)));
    (STR_PAYLOAD, (to_JSON (appsummresp_summary resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_appsumm <- JSON_get_Object STR_PAYLOAD resp ;;

  appsumm <- from_JSON temp_appsumm ;;
  res (mkAppSummResp temp_success appsumm))); solve_json.
Qed.

Record TypeCheckRequest :=
  mkTypeCheckReq {
    tychk_req_att_sess : Attestation_Session;
    tychk_req_term : Term;
    tychk_req_ev : Evidence;
  }.

Definition STR_TYPECHK : string := "TypeCheck".

Global Instance Jsonifiable_TypeCheckRequest `{Jsonifiable Evidence, Jsonifiable Attestation_Session, Jsonifiable Term}: Jsonifiable TypeCheckRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_TYPECHK));
    (STR_ATTEST_SESS, (to_JSON (tychk_req_att_sess req)));
    (STR_TERM, (to_JSON (tychk_req_term req)));
    (STR_EVIDENCE, (to_JSON (tychk_req_ev req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_term <- JSON_get_Object STR_TERM j ;;
  temp_ev <- JSON_get_Object STR_EVIDENCE j ;;
  att_sess <- from_JSON temp_att_sess ;;
  term <- from_JSON temp_term ;;
  ev <- from_JSON temp_ev ;;
  res (mkTypeCheckReq att_sess term ev))); solve_json.
Qed.

Record TypeCheckResponse :=
  mkTypeCheckResp {
    tychk_resp_success : bool;
    tychk_type : option EvidenceT;
  }.

(* TODO: Backport this! *)
Definition STR_OPT_BODY : string := "Option_Body".
Definition err_str_invalid_json_option : string := "Invalid JSON for option type.".
Global Opaque err_str_invalid_json_option.
Global Instance Jsonifiable_option {A} `{Jsonifiable A} : Jsonifiable (option A).
eapply Build_Jsonifiable with
(to_JSON := fun opt =>
  match opt with
  | None => JSON_Object []
  | Some v => JSON_Object [(STR_OPT_BODY, to_JSON v)]
  end)
(from_JSON := (fun j =>
  match j with
  | JSON_Object [] => res None
  | JSON_Object [(STR_OPT_BODY, v)] => v' <- from_JSON v ;; res (Some v')
  | _ => err err_str_invalid_json_option
  end)).
simpl_json; ff;
try (erewrite <- Heq in *);
try (erewrite canonical_jsonification in *); ff.
Defined.

Global Instance Jsonifiable_TypeCheckResponse `{Jsonifiable (option EvidenceT), Jsonifiable EvidenceT}: Jsonifiable TypeCheckResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_TYPECHK));
    (STR_SUCCESS, (JSON_Boolean (tychk_resp_success resp)));
    (STR_PAYLOAD, (to_JSON (tychk_type resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_type <- JSON_get_Object STR_PAYLOAD resp ;;
  tychk_type <- from_JSON temp_type ;;
  res (mkTypeCheckResp temp_success tychk_type))).
simpl_json; destruct a; ff.
Qed.