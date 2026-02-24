Test that Typechecking Succeeds as expected
  $ copland_evidence_tools --req "$(cat Test_Req.json)"
  { "TYPE": "RESPONSE", "ACTION": "APPSUMM", "SUCCESS": true, "PAYLOAD": { "attest": { "magic_appr": [{ "EvidenceT_CONSTRUCTOR": "asp_evt", "EvidenceT_BODY": ["P0", { "ASP_ID": "magic_appr", "ASP_ARGS": {  } }, { "EvidenceT_CONSTRUCTOR": "asp_evt", "EvidenceT_BODY": ["P0", { "ASP_ID": "attest", "ASP_ARGS": {  } }, { "EvidenceT_CONSTRUCTOR": "mt_evt" }] }] }, { "RawEv": ["I_am_Result_of_Magic_Appr!"] }] } } }
